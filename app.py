#!/usr/bin/env python3
"""
Email Validator Pro — a standalone port of the Node backend's validator.

This mirrors `backend/services/emailValidation.js` (plus
`backend/services/blocklists.js`) so an address grades the same way here as it
does in the dashboard. It is meant for testing the engine on its own, from a
Streamlit UI, without needing Postgres or Redis.

The pipeline is the same three layers, in the same order:

    syntax     well-formedness, offline
    blocklist  disposable -> invalid, alias/forwarding -> risky (offline, fail-fast)
    DNS        MX (or the implicit A/AAAA host), and the SPF record
    SMTP       a raw RCPT TO probe; never sends a message, and hangs up

Honesty rule (identical to the Node engine): a layer that cannot reach a
conclusion reports 'unknown', never 'invalid'. A mailbox that might be real must
never be reported invalid, because the user acts on that by dropping the address.

Run:  streamlit run app.py
"""

import io
import json
import os
import random
import re
import socket
import string
import time
from collections import OrderedDict
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timedelta

import dns.exception
import dns.resolver
import pandas as pd
import requests
import streamlit as st


# ==================== CONFIG ====================

# Every network phase is capped at 5s, matching the Node engine. A resolver that
# stalls or a server that accepts the socket then says nothing must not hold a
# thread; one slow host would otherwise set the pace for the whole list.
DNS_TIMEOUT_MS = 5000
SMTP_CONNECT_TIMEOUT = 5.0
SMTP_IDLE_TIMEOUT = 5.0
FETCH_TIMEOUT = 15

MX_CACHE_TTL = 10 * 60        # seconds
MX_CACHE_MAX = 2000

# Strict mode — the least forgiving reading, and the default, matching Node. With
# it on, an ambiguous 5xx at RCPT TO is a bounce; the exceptions (an SPF-publishing
# domain, a probe-rejection, a timeout) live in classify_rcpt.
# EMAIL_VALIDATION_STRICT=0 restores the honesty rule.
STRICT = os.environ.get("EMAIL_VALIDATION_STRICT", "1") != "0"
PROBE_FROM = os.environ.get("EMAIL_VALIDATION_FROM", "postmaster@example.com").strip()
# Concurrency for the domain pool (1..20, default 6), the same knob as Node.
CONCURRENCY = max(1, min(20, int(os.environ.get("EMAIL_VALIDATION_CONCURRENCY", "6") or 6)))
SMTP_DISABLED = os.environ.get("EMAIL_VALIDATION_SMTP") == "0"

STATUS_VALID = "valid"
STATUS_INVALID = "invalid"
STATUS_RISKY = "risky"
STATUS_UNKNOWN = "unknown"

RESOLVER = dns.resolver.Resolver()
RESOLVER.lifetime = DNS_TIMEOUT_MS / 1000.0


class DnsError(Exception):
    """A lookup failure carrying an `err.code`-style tag, so the caller can tell
    unroutable (ENOTFOUND/ENODATA) from merely unresolvable right now (ETIMEOUT)."""

    def __init__(self, code):
        super().__init__(code)
        self.code = code


# ==================== BLOCKLISTS (port of services/blocklists.js) ====================
# The validator's cheapest verdicts are the ones it never has to look up. The
# lists are fetched once a day into a local file and read in-process, and the
# validator consults them before it touches the network at all (the pre-filter).

_APP_DIR = os.path.dirname(os.path.abspath(__file__))

BL_SOURCES = {
    "disposable": "https://raw.githubusercontent.com/disposable/disposable-email-domains/master/domains.txt",
    # The forwarding list is disposable PLUS alias/forwarding services; only the
    # alias part is kept, so a domain is either disposable or alias, never both.
    "alias": "https://raw.githubusercontent.com/disposable/disposable-email-domains/master/domains_forwarding.txt",
    "whitelist": "https://raw.githubusercontent.com/disposable/disposable/master/whitelist.txt",
}
BL_CACHE_PATH = os.environ.get("BLOCKLIST_CACHE_PATH", os.path.join(_APP_DIR, "data", "email-blocklists.json"))
BL_REFRESH_MS = 24 * 60 * 60 * 1000
BL_RETENTION_MS = 30 * 24 * 60 * 60 * 1000
BL_MAX_DROP_RATIO = 0.20
BL_VERSION = 1

_BL_EFFECTIVE = {"disposable": set(), "alias": set()}
_BL_LOADED = False
_BL_LAST_UPDATED = 0


def _iso_to_ms(iso):
    """Parse an ISO-8601 UTC timestamp to epoch milliseconds (the JS Date.parse shape)."""
    s = str(iso).replace("Z", "+00:00")
    return int(datetime.fromisoformat(s).timestamp() * 1000)


def _ms_to_iso(ms):
    return datetime.utcfromtimestamp(ms / 1000.0).strftime("%Y-%m-%dT%H:%M:%S.000Z")


def bl_empty_state():
    return {"version": BL_VERSION, "updated_at": None, "lists": {"disposable": [], "alias": []},
            "retired": {"disposable": {}, "alias": {}}, "whitelist": []}


def bl_normalize_state(raw):
    s = bl_empty_state()
    if isinstance(raw, dict):
        if isinstance(raw.get("updated_at"), str):
            s["updated_at"] = raw["updated_at"]
        lists = raw.get("lists") or {}
        if isinstance(lists.get("disposable"), list):
            s["lists"]["disposable"] = lists["disposable"]
        if isinstance(lists.get("alias"), list):
            s["lists"]["alias"] = lists["alias"]
        retired = raw.get("retired") or {}
        if isinstance(retired.get("disposable"), dict):
            s["retired"]["disposable"] = retired["disposable"]
        if isinstance(retired.get("alias"), dict):
            s["retired"]["alias"] = retired["alias"]
        if isinstance(raw.get("whitelist"), list):
            s["whitelist"] = [str(d).lower() for d in raw["whitelist"] if str(d)]
    return s


def bl_compute_list_update(prev_list, next_list, prev_retired, now,
                           retention_ms=BL_RETENTION_MS, max_drop_ratio=BL_MAX_DROP_RATIO):
    """Fold one freshly fetched list into the previous one under both guards.

    Returns {"aborted": True, ...} when the fetch would drop too much, else the
    new list plus the updated retention map. `retired` keeps a dropped domain for
    a while so a transient upstream removal does not unblock a domain that was
    blocked yesterday."""
    prev = set(prev_list or [])
    nxt = set(next_list or [])

    if len(nxt) == 0:
        return {"aborted": True, "reason": "empty", "removed": len(prev), "prevSize": len(prev), "ratio": 1.0}

    removed = [d for d in prev if d not in nxt]
    ratio = (len(removed) / len(prev)) if prev else 0.0
    if ratio > max_drop_ratio:
        return {"aborted": True, "reason": "delta", "removed": len(removed), "prevSize": len(prev), "ratio": ratio}

    retired = dict(prev_retired or {})
    # A domain that left the list starts its retention clock; one that came back
    # is live again and stops being retained.
    for d in removed:
        if d not in retired:
            retired[d] = datetime.utcfromtimestamp(now / 1000.0).isoformat(timespec="milliseconds") + "Z"
    for d in nxt:
        retired.pop(d, None)

    cutoff = now - retention_ms
    for d in list(retired.keys()):
        try:
            ts = _iso_to_ms(retired[d])
        except Exception:
            ts = 0
        if ts < cutoff:
            del retired[d]

    return {"aborted": False, "list": list(nxt), "retired": retired,
            "removed": len(removed), "prevSize": len(prev_list or []), "ratio": ratio}


def bl_parse_domains(text):
    out = set()
    for line in str(text or "").split("\n"):
        d = line.strip().lower()
        if not d or d.startswith("#"):
            continue
        out.add(d)
    return out


def bl_apply_state(state):
    """Turn a stored state into the two effective sets the validator queries:
    upstream plus still-retained domains, minus the whitelist, alias disjoint."""
    global _BL_EFFECTIVE, _BL_LAST_UPDATED
    whitelist = set(state.get("whitelist") or [])

    disposable = set(state["lists"]["disposable"]) | set((state["retired"].get("disposable") or {}).keys())
    for w in whitelist:
        disposable.discard(w)

    alias = set(state["lists"]["alias"]) | set((state["retired"].get("alias") or {}).keys())
    for d in disposable:
        alias.discard(d)
    for w in whitelist:
        alias.discard(w)

    _BL_EFFECTIVE = {"disposable": disposable, "alias": alias}
    _BL_LAST_UPDATED = _iso_to_ms(state["updated_at"]) if state.get("updated_at") else 0


def bl_read_state():
    try:
        with open(BL_CACHE_PATH, "r", encoding="utf-8") as f:
            return bl_normalize_state(json.load(f))
    except Exception:
        return bl_empty_state()


def bl_write_state(state):
    # Atomic on the same filesystem: a crash mid-write can never leave a
    # half-parsed cache behind for the next process to read.
    os.makedirs(os.path.dirname(BL_CACHE_PATH), exist_ok=True)
    tmp = f"{BL_CACHE_PATH}.{os.getpid()}.tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        f.write(json.dumps(state))
    os.replace(tmp, BL_CACHE_PATH)


def bl_fetch_text(url):
    r = requests.get(url, timeout=FETCH_TIMEOUT)
    if r.status_code != 200:
        raise RuntimeError(f"HTTP {r.status_code}")
    return r.text


def bl_refresh(now=None):
    """Fetch both lists, apply the guards, and — only if they pass — write and
    swap in the new cache. Never throws for a guarded abort; a total network
    failure does propagate so the caller can log it."""
    now = now if now is not None else int(time.time() * 1000)
    prev = bl_read_state()

    disp_text = bl_fetch_text(BL_SOURCES["disposable"])
    alias_text = bl_fetch_text(BL_SOURCES["alias"])
    try:
        white_text = bl_fetch_text(BL_SOURCES["whitelist"])
    except Exception:
        white_text = ""

    next_disposable = bl_parse_domains(disp_text)
    next_alias_raw = bl_parse_domains(alias_text)
    for d in next_disposable:
        next_alias_raw.discard(d)
    whitelist = bl_parse_domains(white_text)

    results = {
        "disposable": bl_compute_list_update(prev["lists"]["disposable"], list(next_disposable), prev["retired"]["disposable"], now),
        "alias": bl_compute_list_update(prev["lists"]["alias"], list(next_alias_raw), prev["retired"]["alias"], now),
    }

    aborted = [k for k, r in results.items() if r["aborted"]]
    if aborted:
        return {"updated": False, "aborted": True, "abortedLists": aborted, "results": results}

    state = {
        "version": BL_VERSION,
        "updated_at": datetime.utcfromtimestamp(now / 1000.0).isoformat(timespec="milliseconds") + "Z",
        "lists": {"disposable": sorted(results["disposable"]["list"]), "alias": sorted(results["alias"]["list"])},
        "retired": {"disposable": results["disposable"]["retired"], "alias": results["alias"]["retired"]},
        "whitelist": sorted(whitelist),
    }
    bl_write_state(state)
    bl_apply_state(state)
    return {"updated": True, "aborted": False, "results": results, "state": state}


def bl_ensure_loaded():
    """Populate the in-memory sets. Cheap after the first call. When the cache is
    missing the first refresh is awaited so the very first run is not decided on
    an empty list; when it is merely stale it is refreshed too (best-effort)."""
    global _BL_LOADED
    if _BL_LOADED:
        return
    state = bl_read_state()
    bl_apply_state(state)
    _BL_LOADED = True

    stale = (not state.get("updated_at")) or (int(time.time() * 1000) - _BL_LAST_UPDATED > BL_REFRESH_MS)
    if stale:
        if not state.get("updated_at"):
            bl_refresh()  # first run: await, so we never decide on an empty list
        else:
            try:
                bl_refresh()
            except Exception:
                pass


def _parent_suffix_match(domain, domain_set):
    """Parent-suffix membership, so `mail.throwaway.com` matches a `throwaway.com` entry."""
    d = str(domain or "").lower()
    if not d or not domain_set:
        return False
    parts = d.split(".")
    for i in range(len(parts) - 1):
        if ".".join(parts[i:]) in domain_set:
            return True
    return False


def bl_is_blocklisted(domain, kind):
    return _parent_suffix_match(domain, _BL_EFFECTIVE["alias" if kind == "alias" else "disposable"])


def bl_status():
    return {"loaded": _BL_LOADED,
            "updated_at": datetime.utcfromtimestamp(_BL_LAST_UPDATED / 1000.0).isoformat(timespec="seconds") + "Z" if _BL_LAST_UPDATED else None,
            "disposable": len(_BL_EFFECTIVE["disposable"]), "alias": len(_BL_EFFECTIVE["alias"]),
            "cache_path": BL_CACHE_PATH}


# ==================== ADDRESS SIGNALS ====================
# Facts about an address that are not a verdict on their own — a throwaway
# domain, a privacy alias, a consumer provider, a shared desk, a missing SPF
# record — but that decide how a positive handshake should be read.

# A small built-in fallback so the first run — or an offline host — still catches
# the obvious throwaway providers without waiting on a download. The daily
# blocklist is the real source; this set only ever adds to it.
FALLBACK_DISPOSABLE = {
    '0-mail.com', '0815.ru', '0clickemail.com', '0wnd.net', '0wnd.org',
    '1fsdfdsfsdf.tk', '1pad.de', '2fdgdfgdfgdf.tk', '10minutemail.com',
    '20minutemail.com', '30minutemail.com', 'guerrillamail.com', 'guerrillamail.net',
    'guerrillamailblock.com', 'grr.la', 'sharklasers.com', 'mailinator.com',
    'mailinator.net', 'yopmail.com', 'yopmail.fr', 'trashmail.com', 'tempmail.net',
    'tempmail.org', 'tempmail.com', 'throwawaymail.com', 'throwaway.email',
    'getnada.com', 'dispostable.com', 'maildrop.cc', 'mailnesia.com', 'mohmal.com',
    'temp-mail.org', 'tempmailo.com', 'tempinbox.com', 'moakt.com', 'mailcatch.com',
    'spamgourmet.com', 'lite14.com', 'mailsac.com', 'inboxbear.com', 'harakirimail.com',
    'filzmail.com', 'trbvm.com', 'mt2009.com', 'fakeinbox.com', 'getairmail.com',
    'discard.email', 'emailondeck.com', 'spam4.me', 'vomoto.com', 'veryrealemail.com',
    'tempr.email', 'mytrashmail.com', 'spambog.com', 'trashmail.net', 'mailforspam.com',
}

# Privacy alias / forwarding services (Apple Hide My Email, SimpleLogin, Firefox
# Relay, DuckDuckGo, addy.io…). These forward to a real inbox, so they rarely
# bounce — flagging them is about the mailbox being unconfirmable, not fake.
FALLBACK_ALIAS = {
    'privaterelay.appleid.com', 'icloud.com',
    'simplelogin.com', 'simplelogin.co', 'simplelogin.io', 'slmail.me',
    'passinbox.com', 'passmail.net', 'aleeas.com',
    'mozmail.com', 'relay.firefox.com',
    'duck.com', 'anonaddy.com', 'anonaddy.me', 'addy.io',
    'forwardemail.net', '33mail.com', 'burnermail.io', 'erine.email',
    'improvmx.com', 'coremail.com',
}

# Consumer providers. A confirmed mailbox is still a real contact, but the domain
# is never catch-all-checked and the panel flags it so a bulk cold send stays deliberate.
FREE_EMAIL_DOMAINS = {
    'gmail.com', 'googlemail.com', 'yahoo.com', 'hotmail.com', 'outlook.com',
    'aol.com', 'icloud.com', 'protonmail.com', 'proton.me', 'zoho.com',
    'yandex.com', 'mail.com', 'gmx.com', 'gmx.net', 'live.com', 'msn.com',
    'comcast.net', 'verizon.net', 'tutanota.com', 'tuta.com', 'fastmail.com',
}

# Shared desks (info@, sales@). A server that accepts one is not confirming a person.
ROLE_PREFIXES = {
    'info', 'admin', 'contact', 'hello', 'support', 'sales', 'editor', 'editors',
    'office', 'team', 'press', 'media', 'webmaster', 'help', 'enquiries', 'inquiries',
    'mail', 'service', 'submissions', 'news', 'newsroom',
}


def is_disposable(domain):
    return _parent_suffix_match(domain, FALLBACK_DISPOSABLE) or bl_is_blocklisted(domain, "disposable")


def is_alias(domain):
    return _parent_suffix_match(domain, FALLBACK_ALIAS) or bl_is_blocklisted(domain, "alias")


def is_free(domain):
    return str(domain or "").lower() in FREE_EMAIL_DOMAINS


def is_role(local):
    return str(local or "").lower() in ROLE_PREFIXES


# ==================== LAYER 1: SYNTAX ====================

LOCAL_RE = re.compile(r"^[A-Za-z0-9!#$%&'*+/=?^_`{|}~-]+(?:\.[A-Za-z0-9!#$%&'*+/=?^_`{|}~-]+)*$")
LABEL_RE = re.compile(r"^[A-Za-z0-9](?:[A-Za-z0-9-]{0,61}[A-Za-z0-9])?$")


def check_syntax(raw):
    """Well-formedness, offline. Not a regex one-liner: the point is a reason the
    user can act on ("missing @", "bad domain label"), not a single "invalid"."""
    email = str(raw or "").strip()
    if not email:
        return {"ok": False, "reason": "No email address was given."}
    if len(email) > 254:
        return {"ok": False, "reason": "This address is too long — the limit is 254 characters."}
    if re.search(r"\s", email):
        return {"ok": False, "reason": "The address contains a space."}

    at = email.rfind("@")
    if at == -1:
        return {"ok": False, "reason": "The address is missing an @ sign."}
    if email.find("@") != at:
        return {"ok": False, "reason": "The address has more than one @ sign."}

    local = email[:at]
    domain = email[at + 1:].lower()

    if not local:
        return {"ok": False, "reason": "Nothing comes before the @ sign."}
    if len(local) > 64:
        return {"ok": False, "reason": "The part before the @ is too long — the limit is 64 characters."}
    if not LOCAL_RE.match(local):
        return {"ok": False, "reason": "The part before the @ contains an invalid character."}
    if not domain:
        return {"ok": False, "reason": "Nothing comes after the @ sign."}
    if len(domain) > 253:
        return {"ok": False, "reason": "The domain is too long — the limit is 253 characters."}
    if "." not in domain:
        return {"ok": False, "reason": "The domain is missing a dot, so it cannot be a real email domain."}

    labels = domain.split(".")
    for label in labels:
        if not label:
            return {"ok": False, "reason": "The domain has two dots in a row."}
        if not LABEL_RE.match(label):
            return {"ok": False, "reason": f"The domain part “{label}” is not valid."}

    tld = labels[-1]
    # A numeric final label is an IP literal written without brackets, which is not
    # a hostname; and a one-letter TLD does not exist in the wild.
    if len(tld) < 2:
        return {"ok": False, "reason": "The domain ends in a single letter, which is not a real domain ending."}
    if re.match(r"^\d+$", tld):
        return {"ok": False, "reason": "The domain ends in numbers instead of a real domain ending."}

    return {"ok": True, "email": email, "local": local, "domain": domain}


# ==================== LAYER 2: DNS ====================

_MX_CACHE = OrderedDict()


def _mx_cache_get(domain):
    ent = _MX_CACHE.get(domain)
    if ent is None:
        return None
    at, hosts = ent
    if time.time() - at > MX_CACHE_TTL:
        _MX_CACHE.pop(domain, None)
        return None
    return hosts


def _mx_cache_set(domain, hosts):
    _MX_CACHE.pop(domain, None)
    _MX_CACHE[domain] = (time.time(), hosts)
    while len(_MX_CACHE) > MX_CACHE_MAX:
        _MX_CACHE.popitem(last=False)


def _resolve(domain, rtype):
    """dns.resolver.resolve with the shared 5s cap, normalized to DnsError codes."""
    try:
        return RESOLVER.resolve(domain, rtype, lifetime=DNS_TIMEOUT_MS / 1000.0)
    except dns.resolver.NXDOMAIN:
        raise DnsError("ENOTFOUND")
    except dns.resolver.NoAnswer:
        raise DnsError("ENODATA")
    except dns.exception.Timeout:
        raise DnsError("ETIMEOUT")
    except dns.exception.DNSException:
        raise DnsError("EIO")


def resolve_mx_hosts(domain):
    """Where mail for `domain` should be delivered, highest priority first. When
    no MX exists, RFC 5321 makes the A/AAAA record the implicit mail host, so
    that is tried before giving up. Raises DnsError: ENOTFOUND/ENODATA
    (definitively unroutable) vs ETIMEOUT (merely unresolvable right now) —
    those two lead to opposite verdicts."""
    cached = _mx_cache_get(domain)
    if cached is not None:
        return cached

    hosts = []
    try:
        ans = _resolve(domain, "MX")
        recs = sorted(((int(r.preference), str(r.exchange).rstrip(".")) for r in ans),
                      key=lambda x: (x[0], x[1]))
        hosts = [h for _, h in recs if h]
    except DnsError as err:
        if err.code not in ("ENODATA", "ENOTFOUND"):
            raise
        # No MX — fall through to the implicit-host check below.

    if not hosts:
        has_address = False
        for rtype in ("A", "AAAA"):
            try:
                addrs = _resolve(domain, rtype)
                if addrs and len(addrs):
                    has_address = True
                    break
            except DnsError as err:
                # A missing AAAA on an IPv4-only name is normal; only a timeout or a
                # hard NXDOMAIN matters, and either is handled by the caller.
                if err.code in ("ETIMEOUT", "ENOTFOUND"):
                    raise
        if not has_address:
            raise DnsError("ENOTFOUND")
        hosts = [domain]

    _mx_cache_set(domain, hosts)
    return hosts


def has_spf_record(domain):
    """The domain's SPF record — True, False or None.

    False means the domain answered and publishes no SPF record; None means the
    lookup itself failed, so the answer is unknown. The distinction matters:
    "no SPF" is treated as evidence of an unmaintained domain, and that call must
    never rest on a temporary DNS blip."""
    try:
        for rdata in RESOLVER.resolve(domain, "TXT", lifetime=DNS_TIMEOUT_MS / 1000.0):
            joined = "".join(s.decode("utf-8", "ignore") for s in rdata.strings).lower()
            if "v=spf1" in joined:
                return True
        return False
    except dns.resolver.NXDOMAIN:
        return False
    except dns.resolver.NoAnswer:
        return False
    except dns.exception.DNSException:
        return None


# ==================== LAYER 3: SMTP RCPT PROBE ====================

def clean_server_text(text):
    """Turn a server reply into one short, human phrase: strip the status code,
    the extended code and any bracketed address, and collapse to a single line."""
    s = str(text or "")
    s = re.sub(r"^\s*\d{3}[ -]*", "", s)
    s = re.sub(r"\b\d\.\d+\.\d+\b", "", s)
    s = re.sub(r"<[^>]*>", "", s)
    s = re.sub(r"\s+", " ", s)
    s = re.sub(r"^[\s:;-]+|[\s.;-]+$", "", s)
    return s.strip()


def looks_like_unknown_mailbox(text):
    """Does a 5xx at RCPT mean "this mailbox does not exist"? Only rejections that
    name the mailbox (a 5.1.x enhanced code, or the usual wording) are a dead
    address; anything else is left unconfirmed."""
    t = str(text or "").lower()
    if re.search(r"\b5\.1\.[0-9]\b", t):
        return True
    return re.search(
        r"\b(no such user|user unknown|unknown user|user not found|no such (mailbox|recipient|user)"
        r"|recipient (address )?(rejected|not found)|mailbox (unavailable|not found|does not exist)"
        r"|address (rejected|not found)|does not exist|unknown recipient)\b", t) is not None


def looks_like_probe_rejection(text):
    """Whether a 5xx is really about *our probe* rather than the recipient — a
    server can defer its sender-policy check to RCPT TO, so an SPF/DKIM/DMARC
    failure aimed at our MAIL FROM arrives dressed as a recipient rejection."""
    t = str(text or "").lower()
    return (re.search(r"\bspf\b[^.]*\b(fail|softfail|error|denied|not authoriz|no valid|none)", t) is not None
            or re.search(r"sender policy framework", t) is not None
            or re.search(r"not authoriz", t) is not None
            or re.search(r"\b(dkim|dmarc|arc)\b[^.]*\b(fail|error|reject|none)", t) is not None
            or re.search(r"authentication (failed|required|error)", t) is not None)


def classify_rcpt(code, text, strict=False, spf=None):
    """Grade a RCPT TO reply. The code is the first authority (RFC 5321 §4.2.3):
    only the codes that are about the recipient end a mailbox's life. A 5xx aimed
    at our probe is left unconfirmed unless strict mode — with the SPF exception."""
    clean = clean_server_text(text)
    t = str(text or "").lower()

    def graded(status, reason):
        return {"status": status, "reason": reason, "code": code}

    if code == 250:
        return graded(STATUS_VALID, "This mailbox exists and can receive mail.")
    if code == 251:
        return graded(STATUS_VALID, "Not hosted here, but the server will forward to the right place.")
    # 252 accepts the mail but admits it could not confirm the mailbox — the usual
    # shape of a catch-all — so it is held risky, never laundered into "valid".
    if code == 252:
        return graded(STATUS_RISKY, "The server will accept the message but could not confirm the mailbox exists — often an accept-all.")

    if 200 <= code < 300:
        return graded(STATUS_VALID, "The server accepts mail for this address.")

    # 3xx means "more input needed". 354 is a reply to DATA, which this probe never
    # sends, so it cannot be read as an answer about the mailbox.
    if 300 <= code < 400:
        return graded(STATUS_UNKNOWN, "The server asked for the message body, which this check never sends, so the mailbox was not confirmed.")

    if 400 <= code < 500:
        return graded(STATUS_RISKY, "The server is temporarily unavailable (busy, rate-limiting or restarting) — retry later."
                      if code == 421 else "The mailbox is temporarily unavailable (greylisted, busy or over quota) — retry later.")

    if 500 <= code < 600:
        # A full mailbox answers with a 5xx, but the address itself is real.
        if code == 552 or re.search(r"(storage allocation|mailbox full|over ?quota|quota exceeded)", t):
            return graded(STATUS_RISKY, "The mailbox is over its storage quota — a real address that is full for now.")
        # 551 and 553 are definitive negatives about the recipient no matter how
        # the text is worded, so they are read by code rather than guessed at.
        if code == 551:
            return graded(STATUS_INVALID, "The recipient is not local to this server and it has no forwarding address — undeliverable.")
        if code == 553:
            return graded(STATUS_INVALID, "The server rejected the mailbox name — the address is not acceptable here.")
        # A sender-policy failure aimed at our probe says nothing about the mailbox.
        if looks_like_probe_rejection(text):
            return graded(STATUS_UNKNOWN, f"The server rejected the test sender (“{clean}”), so this address could not be checked."
                          if clean else "The server rejected the test sender, so this address could not be checked.")
        # Every other 5xx is ambiguous alone: the text breaks the tie.
        if looks_like_unknown_mailbox(text):
            return graded(STATUS_INVALID, f"This mailbox does not exist — the mail server replied “{clean}”."
                          if clean else "This mailbox does not exist.")
        # The honesty rule leaves an ambiguous 5xx unconfirmed; strict mode condemns
        # it — except when the domain publishes SPF, where a refusal aimed at our
        # probe is far more likely an IP block than a dead mailbox, so it is risky.
        if strict and spf is True:
            return graded(STATUS_RISKY, f"The server would not check this address (“{clean}”), but the domain publishes an SPF record, so it is only unconfirmed."
                          if clean else "The server would not check this address, but the domain publishes an SPF record, so it is only unconfirmed.")
        if strict:
            return graded(STATUS_INVALID, f"The mail server would not accept mail for this address (“{clean}”), so it is treated as a bounce."
                          if clean else "The mail server would not accept mail for this address, so it is treated as a bounce.")
        return graded(STATUS_UNKNOWN, f"The mail server refused to check this address (“{clean}”), so it could not be confirmed."
                      if clean else "The mail server refused to check this address, so it could not be confirmed.")

    return graded(STATUS_UNKNOWN, f"The mail server gave an unexpected reply (code {code}).")


def _write(sock, line):
    sock.sendall((line + "\r\n").encode("utf-8", "ignore"))


def _read_reply(sock):
    """Read one SMTP reply. Only the final line of a multi-line reply (the one
    whose separator is a space) is a complete answer. Raises socket.timeout if
    the server goes silent."""
    buf = b""
    while True:
        chunk = sock.recv(4096)
        if not chunk:
            return None, ""
        buf += chunk
        while b"\n" in buf:
            raw, buf = buf.split(b"\n", 1)
            line = raw.decode("utf-8", "ignore").rstrip("\r")
            m = re.match(r"^(\d{3})([ -])(.*)$", line)
            if not m:
                continue
            if m.group(2) == " ":
                return int(m.group(1)), m.group(3).strip()


def probe_smtp(host, email, from_email, helo, strict, spf):
    """Ask one mail server whether it would accept mail for this address — the
    minimum conversation: connect, EHLO, MAIL FROM, RCPT TO, hang up. Never sends
    a message. `refused` marks a server that turned *us* away, which the domain
    layer weighs against SPF."""
    result = {"status": STATUS_UNKNOWN, "reason": "The mail server could not be reached.", "code": None, "refused": False}
    sock = None
    try:
        sock = socket.create_connection((host, 25), timeout=SMTP_CONNECT_TIMEOUT)
        sock.settimeout(SMTP_IDLE_TIMEOUT)
        step = "greeting"
        while True:
            try:
                code, text = _read_reply(sock)
            except (socket.timeout, TimeoutError):
                return {**result, "reason": "The mail server did not respond in time."}
            if code is None:
                return result
            if step == "greeting":
                # A 5xx before we say anything is the server refusing *us*, not a
                # verdict on the mailbox. `refused` lets the domain layer weigh it
                # against SPF.
                if code >= 500:
                    return {**result, "reason": "The mail server refused the connection.", "refused": True}
                step = "ehlo"
                _write(sock, f"EHLO {helo}")
            elif step == "ehlo":
                # Some servers only speak HELO. Either way the next step is the same.
                step = "mailfrom"
                _write(sock, f"MAIL FROM:<{from_email}>")
            elif step == "mailfrom":
                if code >= 500:
                    # Our probe sender was rejected. Says nothing about the recipient.
                    return {**result, "reason": "The mail server rejected the test message, so this address could not be checked."}
                step = "rcpt"
                _write(sock, f"RCPT TO:<{email}>")
            elif step == "rcpt":
                return classify_rcpt(code, text, strict, spf)
    except ConnectionRefusedError:
        return {**result, "reason": "The mail server refused the connection.", "refused": True}
    except (socket.timeout, TimeoutError):
        return {**result, "reason": "The mail server did not respond in time."}
    except OSError:
        return result
    finally:
        if sock is not None:
            try:
                sock.sendall(b"QUIT\r\n")
            except Exception:
                pass
            try:
                sock.close()
            except Exception:
                pass


# ==================== ORCHESTRATION ====================

def probe_from_address():
    return str(os.environ.get("EMAIL_VALIDATION_FROM", PROBE_FROM) or "postmaster@example.com").strip()


def blank(email, **kw):
    r = {"email": email, "status": STATUS_UNKNOWN, "reason": "", "detail": "", "code": None,
         "disposable": False, "alias": False, "free": False, "role": False,
         "spf": None, "catch_all": False, "mx": ""}
    r.update(kw)
    return r


def pre_filter(syntax):
    """The offline blocklist layer, decided before any DNS or SMTP work: a
    throwaway domain is dropped whole (invalid); an alias/forwarding service is
    flagged risky because its mailbox cannot be confirmed but rarely bounces.
    Returns None when the domain is neither, so the caller falls through to DNS."""
    free = is_free(syntax["domain"])
    role = is_role(syntax["local"])

    if is_disposable(syntax["domain"]):
        return {"status": STATUS_INVALID,
                "reason": "This is a disposable (throwaway) email domain, so the address should not be sent to.",
                "detail": "blocklist", "disposable": True, "alias": False, "free": free, "role": role}

    if is_alias(syntax["domain"]):
        return {"status": STATUS_RISKY,
                "reason": "This is an email alias or forwarding service, so the mailbox behind it cannot be confirmed.",
                "detail": "blocklist", "disposable": False, "alias": True, "free": free, "role": role}

    return None


def validate_email(raw_email, from_email=None, smtp=True, helo=None, strict=STRICT):
    """Check one address through all three layers, stopping at the first
    definitive answer (the single-address counterpart of validate_batch)."""
    from_email = from_email or PROBE_FROM
    syntax = check_syntax(raw_email)
    if not syntax["ok"]:
        return blank(raw_email, status=STATUS_INVALID, reason=syntax["reason"], detail="syntax")

    block = pre_filter(syntax)
    if block:
        return {**blank(raw_email), **block}

    try:
        hosts = resolve_mx_hosts(syntax["domain"])
    except DnsError as err:
        if err.code in ("ENOTFOUND", "ENODATA"):
            return blank(raw_email, status=STATUS_INVALID,
                         reason=f"The domain “{syntax['domain']}” has no mail server, so it cannot receive email.", detail="dns")
        return blank(raw_email, status=STATUS_UNKNOWN,
                     reason=f"The domain “{syntax['domain']}” could not be looked up — this is usually a temporary DNS problem.", detail="dns")

    spf = has_spf_record(syntax["domain"])
    if not smtp:
        return blank(raw_email, status=STATUS_RISKY, detail="dns", spf=spf, mx=hosts[0] if hosts else "",
                     reason="The domain has a mail server, but the mailbox itself was not checked.")

    outcome = check_mailbox(syntax["email"], hosts, from_email, helo or "localhost", strict, spf)
    if outcome.get("refused") and spf is False:
        outcome = {"status": STATUS_INVALID, "detail": "smtp",
                   "reason": "The mail server refused the connection and the domain publishes no SPF record, so the address is treated as undeliverable."}
    return {**blank(raw_email), **outcome, "disposable": False, "alias": False,
            "free": is_free(syntax["domain"]), "role": is_role(syntax["local"]),
            "spf": spf, "mx": hosts[0] if hosts else ""}


def check_mailbox(email, hosts, from_email, helo, strict=STRICT, spf=None):
    """The handshake for one contact, most-preferred MX host first, giving up
    after a few rather than walking a long MX chain one timeout at a time. Only a
    definitive answer stops the walk; a deferral or a silent host falls through."""
    last = None
    for host in hosts[:3]:
        result = probe_smtp(host, email, from_email, helo, strict, spf)
        if result["status"] in (STATUS_VALID, STATUS_INVALID):
            return {**result, "detail": "smtp"}
        last = result
    return {**(last or {"status": STATUS_UNKNOWN, "reason": "This mailbox could not be confirmed."}), "detail": "smtp"}


def probe_catch_all(hosts, domain, from_email, helo):
    """Ask a domain once about an address that cannot exist. If the server accepts
    it anyway, every "yes" it gives is worthless — this is the single most
    important upgrade over a per-address handshake."""
    junk = "zz" + "".join(random.choices(string.ascii_lowercase + string.digits, k=24))
    address = f"{junk}@{domain}"
    for host in hosts[:3]:
        result = probe_smtp(host, address, from_email, helo, False, None)
        if result["status"] == STATUS_VALID:
            return True       # accepts a random address
        if result["status"] == STATUS_INVALID:
            return False      # a real server rejecting fakes
    return False              # could not confirm either way — treat as not catch-all


def valid_reason(base, free, role, spf):
    """Let a positive result carry the signals that shaped it, so the sentence
    never claims more than a bare "mailbox confirmed"."""
    notes = []
    if free:
        notes.append("free email provider")
    if role:
        notes.append("role address")
    if spf is False:
        notes.append("domain publishes no SPF record")
    return f"{base} ({'; '.join(notes)})" if notes else base


# ==================== PER-DOMAIN WORKER ====================
# DNS, SPF and catch-all are checked ONCE per domain; domains run in parallel and
# emails on the same domain run one after another (polite to the mail server).
# Returns its rows rather than mutating shared state, so the caller merges them.

def check_domain(domain, items, cfg):
    rows = []
    try:
        hosts = resolve_mx_hosts(domain)
    except DnsError as err:
        unroutable = err.code in ("ENOTFOUND", "ENODATA")
        reason = (f"The domain “{domain}” has no mail server, so it cannot receive email."
                  if unroutable else
                  f"The domain “{domain}” could not be looked up — this is usually a temporary DNS problem.")
        for email, _local in items:
            rows.append(blank(email, status=(STATUS_INVALID if unroutable else STATUS_UNKNOWN),
                              reason=reason, detail="dns"))
        return rows

    mx = hosts[0] if hosts else ""
    free = is_free(domain)
    disposable = False  # disposable/alias were decided at the blocklist layer

    spf = has_spf_record(domain)
    # A free provider always accepts its own users, so catch-all could only say "yes".
    do_smtp = cfg["smtp"]
    catch_all = probe_catch_all(hosts, domain, cfg["from_email"], cfg["helo"]) if (do_smtp and not free) else False

    for email, local in items:
        role = is_role(local)
        if not do_smtp:
            outcome = {"status": STATUS_RISKY, "reason": "The domain has a mail server, but the mailbox itself was not checked.", "detail": "dns"}
        else:
            try:
                outcome = check_mailbox(email, hosts, cfg["from_email"], cfg["helo"], cfg["strict"], spf)
            except Exception:
                outcome = {"status": STATUS_UNKNOWN, "reason": "The check could not be completed.", "detail": "smtp"}

        # Refused connection + no SPF: nothing about this domain says real mail —
        # no sender policy, and its MX turned the connection away. The owner treats
        # that pairing as a dead address. A timeout is deliberately NOT included.
        if outcome.get("refused") and spf is False:
            outcome = {"status": STATUS_INVALID, "detail": "smtp",
                       "reason": "The mail server refused the connection and the domain publishes no SPF record, so the address is treated as undeliverable."}

        # A catch-all said yes to a random address, so its yes to this one proves
        # nothing — downgrade a would-be "valid" to risky rather than launder it.
        if outcome["status"] == STATUS_VALID and catch_all:
            outcome = {"status": STATUS_RISKY,
                       "reason": "The domain accepts mail for every address (catch-all), so this mailbox cannot be confirmed.",
                       "detail": outcome.get("detail"), "code": outcome.get("code")}
        elif outcome["status"] == STATUS_VALID:
            outcome = {**outcome, "reason": valid_reason(outcome["reason"], free, role, spf)}

        rows.append({**outcome, "email": email, "disposable": disposable, "alias": False,
                     "free": free, "role": role, "spf": spf, "catch_all": catch_all, "mx": mx})
    return rows


def validate_batch(emails, cfg, on_progress=None):
    """The three-layer run over a list of addresses, grouped by domain, in
    first-seen order (the standalone counterpart of runValidation)."""
    bl_ensure_loaded()

    results = OrderedDict()
    groups = OrderedDict()
    for e in emails:
        syntax = check_syntax(e)
        if not syntax["ok"]:
            results[e] = blank(e, status=STATUS_INVALID, reason=syntax["reason"], detail="syntax")
            continue
        block = pre_filter(syntax)
        if block:
            results[e] = {**blank(e), **block}
            continue
        groups.setdefault(syntax["domain"], []).append((e, syntax["local"]))

    total = len(emails)
    if on_progress:
        on_progress(list(results.values()), len(results), total)

    def safe_check(domain, items):
        try:
            return check_domain(domain, items, cfg)
        except Exception as ex:  # one bad domain must never crash the whole run
            return [blank(e, status=STATUS_UNKNOWN, reason=f"The check could not be completed: {str(ex)[:60]}")
                    for e, _ in items]

    with ThreadPoolExecutor(max_workers=cfg["workers"]) as ex:
        futures = [ex.submit(safe_check, domain, items) for domain, items in groups.items()]
        for fut in as_completed(futures):
            for row in fut.result():
                results[row["email"]] = row
            if on_progress:
                on_progress(list(results.values()), len(results), total)

    return [results[e] for e in emails]


# ==================== DISPLAY MAPPING ====================

DELIVERABILITY = {STATUS_VALID: "Deliverable", STATUS_INVALID: "Not Deliverable",
                  STATUS_RISKY: "Risky", STATUS_UNKNOWN: "Unknown"}
SEND_REC = {STATUS_VALID: "Send", STATUS_RISKY: "Send in small batch",
            STATUS_UNKNOWN: "Hold and re-check", STATUS_INVALID: "Do not send"}

# The columns merged back into the uploaded CSV (Primary_*/Secondary_*).
FIELDS = ["Status", "Deliverability", "Send_Recommendation", "Reason", "Detail", "Code",
          "Disposable", "Alias", "Free", "Role", "SPF", "Catch-All", "MX"]


def _yn(v):
    return "Yes" if v else "No"


def _spf(v):
    return "Yes" if v is True else ("No" if v is False else "Unknown")


def to_row(r):
    return {
        "Email": r["email"],
        "Status": r["status"],
        "Deliverability": DELIVERABILITY.get(r["status"], "Unknown"),
        "Send_Recommendation": SEND_REC.get(r["status"], "Hold and re-check"),
        "Reason": r.get("reason", ""),
        "Detail": r.get("detail", ""),
        "Code": r.get("code") if r.get("code") is not None else "",
        "Disposable": _yn(r.get("disposable")),
        "Alias": _yn(r.get("alias")),
        "Free": _yn(r.get("free")),
        "Role": _yn(r.get("role")),
        "SPF": _spf(r.get("spf")),
        "Catch-All": _yn(r.get("catch_all")),
        "MX": r.get("mx", ""),
    }


# ==================== UI ====================

def load_css():
    try:
        with open("style.css") as f:
            st.markdown(f"<style>{f.read()}</style>", unsafe_allow_html=True)
    except Exception:
        pass


def format_time(seconds):
    return str(timedelta(seconds=int(seconds)))


def color_status(val):
    return {
        "Deliverable": "background-color: #d4edda; color: #155724",
        "Risky": "background-color: #fff3cd; color: #856404",
        "Unknown": "background-color: #e2e3e5; color: #383d41",
    }.get(val, "background-color: #f8d7da; color: #155724")


def style_table(df):
    sty = df.style
    if hasattr(sty, "map"):
        return sty.map(color_status, subset=["Deliverability"])
    return sty.applymap(color_status, subset=["Deliverability"])


@st.cache_data(ttl=300)
def port25_works():
    try:
        socket.create_connection(("gmail-smtp-in.l.google.com", 25), timeout=8).close()
        return True
    except OSError:
        return False


def split_cell(cell):
    return [p.strip() for p in str(cell).split(" * ")] if not pd.isna(cell) else []


def ordered_unique(items):
    seen, out = set(), []
    for it in items:
        if it and it not in seen:
            seen.add(it)
            out.append(it)
    return out


def process_csv_with_live_output(uploaded, email_column, cfg):
    uploaded.seek(0)
    df = pd.read_csv(uploaded)
    emails = ordered_unique(
        e.lower() for cell in df[email_column] for e in split_cell(cell)
    )

    total = len(emails)
    progress = st.progress(0.0)
    live_table = st.empty()
    started = time.time()
    tick = [0]

    def on_progress(rows, done, _total):
        display = pd.DataFrame([to_row(r) for r in rows])
        progress.progress(min(done / total, 1.0) if total else 1.0)
        # Redraw the table every few updates, not every row, so the UI keeps up.
        tick[0] += 1
        if tick[0] % 5 == 0 or done == total:
            live_table.dataframe(style_table(display), use_container_width=True, height=500)

    final = validate_batch(emails, cfg, on_progress)
    display_rows = [to_row(r) for r in final]
    val = {r["Email"]: r for r in display_rows}

    # Merge back into the original file (Primary_* and Secondary_* columns, as before)
    primaries, secondaries = [], []
    for cell in df[email_column]:
        parts = [p.lower() for p in split_cell(cell)] if not pd.isna(cell) else []
        primaries.append(parts[0] if parts else "")
        secondaries.append(parts[1] if len(parts) > 1 else "")
    for prefix, col in (("Primary", primaries), ("Secondary", secondaries)):
        df[f"{prefix}_Email"] = col
        for k in FIELDS:
            df[f"{prefix}_{k}"] = [val[e][k] if e in val else "" for e in col]

    buffer = io.StringIO()
    df.to_csv(buffer, index=False)
    safe = pd.DataFrame([{"Email": r["Email"]} for r in display_rows if r["Deliverability"] == "Deliverable"])
    return buffer.getvalue(), safe.to_csv(index=False), pd.DataFrame(display_rows)


def main():
    st.set_page_config(page_title="Email Validator Pro", layout="centered")
    load_css()
    st.markdown("<p class='h1 h'>Email <span>Validator</span></p>", unsafe_allow_html=True)

    can_smtp = port25_works() and not SMTP_DISABLED
    if can_smtp:
        st.success("Port 25 is open: mailbox checks will run.")
    else:
        st.warning("SMTP is disabled (port 25 blocked, or EMAIL_VALIDATION_SMTP=0), so mailboxes "
                   "cannot be confirmed. Results will show **Unknown** instead of guessing. Run on a "
                   "host with port 25 open to get real mailbox checks.")

    with st.expander("Settings", expanded=not can_smtp):
        mail_from = st.text_input("Your real sending address (MAIL FROM)", value=PROBE_FROM,
                                  placeholder="you@yourdomain.com",
                                  help="Use an address on your own domain. Fake senders get rejected.")
        helo = st.text_input("Your server hostname (HELO)", value=socket.getfqdn())
        workers = st.slider("Domains checked in parallel", 1, 20, CONCURRENCY)
        strict = st.checkbox("Strict mode", value=STRICT,
                             help="Treat an ambiguous 5xx as a bounce. Off = the honesty rule (leave it unknown).")

    bl = bl_status()
    st.caption(f"Blocklists: {bl['disposable']:,} disposable, {bl['alias']:,} alias — cache: {bl['cache_path']}")

    uploaded = st.file_uploader("Choose your CSV file", type=["csv"],
                                help="Multiple emails per cell can be separated by ' * '")

    if uploaded:
        try:
            uploaded.seek(0)
            preview = pd.read_csv(uploaded, nrows=10)
            st.dataframe(preview, use_container_width=True)
            email_column = st.selectbox("Select Email Column", preview.columns.tolist())

            if st.button("Start Validation", type="primary"):
                if can_smtp and not re.match(r"^[^@\s]+@[^@\s]+\.[^@\s]+$", mail_from.strip() or ""):
                    st.error("Enter your real sending address in Settings first.")
                    st.stop()
                cfg = {"smtp": can_smtp, "from_email": (mail_from.strip() or PROBE_FROM),
                       "helo": (helo.strip() or socket.getfqdn()), "workers": workers, "strict": strict}
                with st.spinner("Processing..."):
                    uploaded.seek(0)
                    out_csv, safe_csv, _ = process_csv_with_live_output(uploaded, email_column, cfg)
                if out_csv:
                    st.session_state.output_csv = out_csv
                    st.session_state.safe_csv = safe_csv
                    st.success("Validation Completed!")
        except Exception as e:
            st.error(f"Error: {e}")

    if st.session_state.get("output_csv"):
        st.download_button("Download Full Results CSV", data=st.session_state.output_csv,
                           file_name="validated_results.csv", mime="text/csv", type="primary")
        st.download_button("Download SAFE-TO-SEND list only (Deliverable)", data=st.session_state.safe_csv,
                           file_name="safe_to_send.csv", mime="text/csv")


if __name__ == "__main__":
    main()

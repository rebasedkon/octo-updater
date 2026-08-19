"""
Octo Updater — a standalone updater for the OctoWoW client: game files,
mods, tweaks and addons. Standard library, optional 'certifi' for TLS;
Python 3.10+.
"""

import json
import hashlib
import os
import sys
import ssl
import re
import subprocess
import urllib.request
from urllib.parse import urlsplit
import shutil
import stat
import struct
import time
import math
import threading
import queue
from functools import cache
import tkinter as tk
from tkinter import filedialog
from pathlib import Path

# ──────────────────────────────────────────────────────────────────────────────
#  Constants
# ──────────────────────────────────────────────────────────────────────────────

UPDATER_VERSION  = "1.3"
SERVER           = "https://octowow.st"
UA               = f"OctoUpdater/{UPDATER_VERSION}"
DOWNLOAD_RETRY   = 5
DOWNLOAD_TIMEOUT = 10    # seconds without any data before a transfer aborts

# Where the app lives: next to the .exe when frozen (PyInstaller), otherwise
# next to this script — never the current working directory, which varies with
# how the app was launched. This anchors the default game folder.
if getattr(sys, "frozen", False):
    APP_DIR = os.path.dirname(os.path.abspath(sys.executable))
else:
    APP_DIR = os.path.dirname(os.path.abspath(__file__))


def _default_app_data_dir() -> str:
    base = os.environ.get("LOCALAPPDATA")
    if base:
        path = os.path.join(base, "OctoUpdater")
        try:
            os.makedirs(path, exist_ok=True)
            return path
        except OSError:
            pass
    return APP_DIR


APP_DATA_DIR = _default_app_data_dir()

CONFIG_FILE = os.path.join(APP_DATA_DIR, "config.json")

# First-run default game folder, anchored to the app dir (not the CWD).
DEFAULT_GAME_DIR = os.path.join(APP_DIR, "OctoWoW")


def _relocate_legacy_data():
    # Old config (<1.3: octo_updater_config.json beside the app) becomes
    # config.json in APP_DATA_DIR. Rename + relocate, only when the old name
    # exists and the new path doesn't (idempotent). The legacy game-hash cache
    # is no longer used and is deleted by _migrate_1_3.
    old_name, new = "octo_updater_config.json", CONFIG_FILE
    for old in (os.path.join(APP_DIR, old_name),
                os.path.join(APP_DATA_DIR, old_name)):
        if old == new or not os.path.exists(old) or os.path.exists(new):
            continue
        try:
            shutil.move(old, new)
            sys.stderr.write(f"[data] moved {old_name} -> {new}\n")
            break
        except OSError as e:
            sys.stderr.write(f"[data] could not move {old_name}: {e}\n")

# News tab: the latest announcement (forum 2, full post) fills the left panel,
# the patch-notes list (forum 4) fills the right.
NEWS_FEATURED_URL = f"{SERVER}/forum/octonews.php?forum=2&mode=full"
PATCHNOTES_URL    = f"{SERVER}/forum/octonews.php?mode=list&forum=4&limit=8"
NEWS_TIMEOUT      = 8
NEWS_CACHE_TTL    = 300

# Design dimensions, authored at 96 DPI (100% scaling). At startup the app
# multiplies these — and every other hard-coded pixel value, via self._px() —
# by a single DPI scale factor, so the whole fixed-pixel layout scales as a
# unit instead of point-fonts overflowing fixed geometry on high-DPI displays.
WIN_W, WIN_H = 1000, 700
FOOT_H       = 130

C_BG         = "#120e1a"
C_PANEL      = "#161120"
C_PANEL_BDR  = "#261d3a"
C_HDR        = "#0d0a14"
C_DIVIDER    = "#2a2142"
C_GOLD       = "#c8922a"
C_GOLD_LT    = "#e8b84b"
C_PURPLE     = "#8a4fa5"
C_GREEN_BTN  = "#4a7c2f"
C_GREEN_HOV  = "#5a9438"
C_TEXT       = "#d8d4cc"
C_TEXT_DIM   = "#7a7670"
C_LOG_BG     = "#0f0b16"
C_OK         = "#6abf69"
C_ERR        = "#bf6969"
C_MOD_HL     = "#a8b83c"   # olive-green highlight for installed mods

# Parchment palette for the featured news post
C_PARCH       = "#e9dcb8"
C_PARCH_BAND  = "#ddcda0"
C_PARCH_LINE  = "#c3b083"
C_PARCH_TITLE = "#7c5a12"
C_PARCH_TEXT  = "#3a352a"
C_PARCH_DIM   = "#8b8064"
C_PARCH_LINK  = "#a3561c"
C_PARCH_EDGE  = "#b7a678"

FONT_BODY   = ("Segoe UI", 9)
FONT_MONO   = ("Consolas", 9)
FONT_VER    = ("Segoe UI", 8)


# ──────────────────────────────────────────────────────────────────────────────
#  Secure networking
# ──────────────────────────────────────────────────────────────────────────────

# Hardened TLS: verify the server certificate against the system trust store,
# require the hostname to match, and refuse anything below TLS 1.2. This is
# the primary defence against a man-in-the-middle tampering with downloads.
SSL_CTX = ssl.create_default_context()
SSL_CTX.check_hostname = True
SSL_CTX.verify_mode = ssl.CERT_REQUIRED
# Trust certifi's curated roots *in addition to* the system store, so a stale
# or incomplete Windows root store (Python's ssl uses a static snapshot and
# never triggers Windows' on-demand root update) can't break verification.
# If certifi isn't bundled, fall back to the system store alone.
try:
    import certifi
    SSL_CTX.load_verify_locations(certifi.where())
except Exception:
    pass
try:
    SSL_CTX.minimum_version = ssl.TLSVersion.TLSv1_2
except (AttributeError, ValueError):
    pass

# Binaries may only be fetched from these hosts. TLS already stops a MITM from
# impersonating them; this additionally stops a tampered API response from
# redirecting a download (e.g. a mod DLL) to an unexpected host.
ALLOWED_DOWNLOAD_HOSTS = {
    "octowow.st",
    "dl.octowow.st",
    "github.com",
    "raw.githubusercontent.com",
    "objects.githubusercontent.com",
    "release-assets.githubusercontent.com",
    "codeberg.org",
}


def _check_url(url: str, allowed_hosts):
    """Enforce HTTPS and (optionally) an allowlist on a URL."""
    parts = urlsplit(url)
    if parts.scheme != "https":
        raise RuntimeError(f"Refusing non-HTTPS URL: {url}")
    if allowed_hosts is not None:
        host = (parts.hostname or "").lower()
        if host not in allowed_hosts:
            raise RuntimeError(f"Refusing download from unexpected host: {host}")


class _HttpsOnlyRedirectHandler(urllib.request.HTTPRedirectHandler):
    """Require every redirect target to stay HTTPS (blocks an https→http
    downgrade). The host allowlist is deliberately *not* re-applied on
    redirects: an allowlisted host controls its own redirects — legitimately
    to its CDN (e.g. octowow.st→dl.octowow.st, github.com→codeload) — and TLS
    protects wherever it lands. The allowlist's job is to vet the *initial*
    URL (against a tampered API response), which secure_urlopen still does."""
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        _check_url(newurl, None)   # HTTPS-only, no host check
        return super().redirect_request(req, fp, code, msg, headers, newurl)


# Shared opener with the hardened TLS context and the HTTPS-only redirect
# guard, built once.
_SECURE_OPENER = urllib.request.build_opener(
    urllib.request.HTTPSHandler(context=SSL_CTX),
    _HttpsOnlyRedirectHandler())


def secure_urlopen(req, timeout, allowed_hosts=None):
    """urlopen wrapper that enforces HTTPS + an optional host allowlist on the
    initial URL, keeps redirects on HTTPS, and uses the hardened TLS context.
    `req` may be a URL string or a urllib Request."""
    url = req.full_url if isinstance(req, urllib.request.Request) else req
    _check_url(url, allowed_hosts)
    return _SECURE_OPENER.open(req, timeout=timeout)


# Serializes all config read-modify-write cycles across the many worker
# threads (mods, addons, caches) and the main thread, so concurrent updates
# can't clobber each other. Reentrant so update_config() can call save.
_CONFIG_LOCK = threading.RLock()


def load_config() -> dict:
    try:
        with open(CONFIG_FILE) as f:
            return json.load(f)
    except FileNotFoundError:
        return {}
    except Exception as e:
        sys.stderr.write(f"[config] failed to read {CONFIG_FILE}: {e}\n")
        return {}


def _atomic_write(path: str, text: str):
    """Write via a temp file + atomic rename so a crash mid-write can never
    leave a truncated/corrupt file at `path`."""
    tmp = path + ".tmp"
    with open(tmp, "w") as f:
        f.write(text)
        f.flush()
        os.fsync(f.fileno())
    os.replace(tmp, path)


def save_config(data: dict):
    with _CONFIG_LOCK:
        try:
            _atomic_write(CONFIG_FILE, json.dumps(data, indent=2))
        except Exception as e:
            sys.stderr.write(f"[config] failed to write {CONFIG_FILE}: {e}\n")


def update_config(mutator):
    """Load the current on-disk config under the lock, apply `mutator(cfg)`,
    save atomically, and return the result. Every config change — main thread
    or worker — should go through this so no stale in-memory snapshot can
    overwrite keys another thread just persisted."""
    with _CONFIG_LOCK:
        cfg = load_config()
        mutator(cfg)
        save_config(cfg)
        return cfg


def ensure_dir(path):
    Path(path).mkdir(parents=True, exist_ok=True)


# ── logging ─────────────────────────────────────────────────────────────────
# One thread-safe log sink for the whole app. Any function — worker thread or
# main — calls log(); the GUI drains _LOG_Q on the main thread (see
# OctoUpdaterApp._poll) and renders each line. This keeps all Tk access on the
# main thread without threading a log_fn argument through every function.
_LOG_Q: queue.Queue = queue.Queue()


def log(msg: str, tag: str = ""):
    """Append a line to the app log. Thread-safe; safe to call before the GUI
    exists (the queue just buffers until it's drained)."""
    _LOG_Q.put((msg, tag))


def remove_wdb(client_dir: str):
    """Delete the client's WDB folder (server-data cache, safe to drop)."""
    wdb = os.path.join(client_dir, "WDB")
    if not os.path.isdir(wdb):
        return
    try:
        shutil.rmtree(wdb)
        log("WDB cache cleared.", "dim")
    except Exception as e:
        log(f"Could not clear WDB: {e}", "err")


def get_client_version(out_dir: str) -> str:
    """Read version + build from fixed offsets in the client's WoW.exe."""
    exe_path = os.path.join(out_dir, "WoW.exe")
    if not os.path.exists(exe_path):
        return ""
    try:
        # Read only the two small fields, not the whole ~5 MB binary.
        with open(exe_path, "rb") as f:
            f.seek(0x00437bfc)
            build   = f.read(4).decode("utf-8", errors="replace").rstrip("\x00")
            f.seek(0x00437c04)
            version = f.read(6).decode("utf-8", errors="replace").rstrip("\x00")
        return f"{version} ({build})"
    except Exception:
        return ""


def fmt_size(num_bytes: float) -> str:
    """Human-readable size: KB, MB, GB. Uses binary (1024) steps but the
    familiar KB/MB/GB labels. Truncated, not rounded, so 8.7998 GiB reads as
    '8.79 GB' instead of rounding up to 8.80 and overstating the size."""
    if num_bytes < 1024 ** 2:
        return f"{int(num_bytes / 1024)} KB"
    if num_bytes < 1024 ** 3:
        return f"{int(num_bytes / 1024 ** 2 * 10) / 10:.1f} MB"
    return f"{int(num_bytes / 1024 ** 3 * 100) / 100:.2f} GB"


def fmt_speed(bytes_per_sec: float) -> str:
    if bytes_per_sec < 1024 * 1024:
        return f"{bytes_per_sec / 1024:.0f} KB/s"
    return f"{bytes_per_sec / 1024 / 1024:.1f} MB/s"


# ──────────────────────────────────────────────────────────────────────────────
#  Torrent-based client sync (aria2c)
# ──────────────────────────────────────────────────────────────────────────────
# Client files are synced over BitTorrent with aria2c, fetched on first use.
# The download is differential: only files that are missing or the wrong size
# are pulled.

CLIENT_TORRENT_URL = "https://dl.octowow.st/download/client.torrent"

# Pinned aria2 Windows build. aria2 is GPLv2+, fetched and run unmodified; only
# aria2c.exe is used. The sha256 is of the release .zip (verified once).
ARIA2_ZIP_URL    = ("https://github.com/aria2/aria2/releases/download/"
                    "release-1.37.0/aria2-1.37.0-win-32bit-build1.zip")
ARIA2_ZIP_SHA256 = "35f6514cc5dd7e98a87b3c4c2d25a0754b9b063dbe59bc0f22d483464f61e5b6"
ARIA2C_PATH      = os.path.join(APP_DATA_DIR, "aria2c.exe")

# The torrent's top-level folder name: aria2 writes files under <dir>/<name>/…,
# so a junction <staging>/client → the real client dir lands them in place.
TORRENT_NAME       = "client"
TORRENT_STAGING_DIR = os.path.join(APP_DATA_DIR, "torrent-root")
PRISTINE_WOW_PATH  = os.path.join(APP_DATA_DIR, "base-WoW.exe")

# The pristine (unpatched) WoW.exe carries 0xa1 at this offset; a patched one
# carries 0xb8 (see the locale patch). Used to cache a clean base for re-patch.
_LOCALE_ASSERT_OFFSET = 0x1b2115

# Game-language (WoW.exe locale) patch
# The language is switched by patching three spots in WoW.exe. 
# LOCALE_NAMES is the exe's built-in 8-slot locale table (at
# 0x45591c - index*8). Selectable languages map to a slot index; ruRU and ptBR
# reuse the unused zhTW / xxYY slots and rename them. Offsets/bytes verified
# against the pristine base-WoW.exe.
_LOCALE_TAG_OFFSET   = 0x1b2115                 # the 0xa1/0xb8 assert instruction
_LOCALE_INDEX_OFFSET = 0x253c
_LOCALE_NAME_OFFSET  = lambda i: 0x45591c - i * 8
LOCALE_NAMES = ["enUS", "koKR", "frFR", "deDE",
                "zhCN", "zhTW", "esES", "xxYY"]
# selectable code -> (slot index, display label), in menu order
LOCALES = {
    "enUS": (0, "English"),
    "deDE": (3, "Deutsch"),
    "ruRU": (5, "Русский"),
    "zhCN": (4, "中文 (简体)"),
    "esES": (6, "Español"),
    "ptBR": (7, "Português (BR)"),
}
DEFAULT_LOCALE = "enUS"


def locale_patches(locale: str):
    """The three WoW.exe byte edits that force the given game language, as
    (offset, bytes) tuples applied on top of the pristine base."""
    if locale not in LOCALES:
        locale = DEFAULT_LOCALE
    idx, _ = LOCALES[locale]
    carrier = LOCALE_NAMES[idx]                 # exe slot name at this index
    return [
        # assert instruction: mov eax, <carrier as reversed dword> (was mov eax,[imm])
        (_LOCALE_TAG_OFFSET,
         bytes([0xb8]) + bytes(carrier, "latin1")[::-1]),
        # locale index: mov esi, <index>; jmp +0x1f
        (_LOCALE_INDEX_OFFSET,
         bytes([0xbe, idx, 0x00, 0x00, 0x00, 0xeb, 0x1f])),
        # rename the slot's locale-name string to the selected tag
        (_LOCALE_NAME_OFFSET(idx), bytes(locale, "latin1")),
    ]


_NO_WINDOW = getattr(subprocess, "CREATE_NO_WINDOW", 0)


def ensure_aria2c(log_fn=log) -> str:
    """Return the path to aria2c.exe, downloading + checksum-verifying it into
    APP_DATA_DIR on first use. Raises on failure."""
    if os.path.exists(ARIA2C_PATH):
        return ARIA2C_PATH
    log_fn("Fetching aria2c (one-time, ~2.5 MB)…", "acct")
    req = urllib.request.Request(ARIA2_ZIP_URL, headers={"User-Agent": UA})
    with secure_urlopen(req, timeout=60, allowed_hosts=ALLOWED_DOWNLOAD_HOSTS) as r:
        data = r.read()
    digest = hashlib.sha256(data).hexdigest()
    if digest != ARIA2_ZIP_SHA256:
        raise RuntimeError(
            f"aria2 checksum mismatch (got {digest[:12]}…); refusing to run it")
    import zipfile, io
    with zipfile.ZipFile(io.BytesIO(data)) as zf:
        name = next((n for n in zf.namelist()
                     if n.lower().endswith("aria2c.exe")), None)
        if not name:
            raise RuntimeError("aria2c.exe not found in the aria2 archive")
        exe = zf.read(name)
    ensure_dir(APP_DATA_DIR)
    tmp = ARIA2C_PATH + ".part"
    with open(tmp, "wb") as f:
        f.write(exe)
    os.replace(tmp, ARIA2C_PATH)
    log_fn("aria2c ready.", "ok")
    return ARIA2C_PATH


def _bdecode(buf: bytes, pos: int = 0):
    """Minimal bencode decoder → (value, next_pos). Strings stay bytes."""
    ch = buf[pos]
    if ch == 0x69:                                   # i<int>e
        end = buf.index(b"e", pos)
        return int(buf[pos + 1:end]), end + 1
    if ch == 0x6c:                                   # l<items>e
        lst, p = [], pos + 1
        while buf[p] != 0x65:
            v, p = _bdecode(buf, p)
            lst.append(v)
        return lst, p + 1
    if ch == 0x64:                                   # d<pairs>e
        d, p = {}, pos + 1
        while buf[p] != 0x65:
            k, p = _bdecode(buf, p)
            v, p = _bdecode(buf, p)
            d[k] = v
        return d, p + 1
    colon = buf.index(b":", pos)                     # <len>:<bytes>
    n = int(buf[pos:colon])
    start = colon + 1
    return buf[start:start + n], start + n


def fetch_torrent(url: str = CLIENT_TORRENT_URL) -> tuple:
    """Download the .torrent → (raw_bytes, files). `files` is a list of
    (path_parts, length). The raw bytes' SHA-1 is the client 'version'."""
    req = urllib.request.Request(url, headers={"User-Agent": UA})
    with secure_urlopen(req, timeout=DOWNLOAD_TIMEOUT,
                        allowed_hosts=ALLOWED_DOWNLOAD_HOSTS) as r:
        raw = r.read()
    decoded, _ = _bdecode(raw)
    info = decoded.get(b"info", {})
    files = [([p.decode("latin1") for p in f.get(b"path", [])],
              int(f.get(b"length", 0)))
             for f in info.get(b"files", [])]
    return raw, files


def torrent_version(raw: bytes) -> str:
    """SHA-1 of the whole .torrent file — the client 'version'. Changes whenever
    the torrent is re-rolled, so it's what we compare to detect a new build and
    decide whether aria2's resume state is stale. An occasional re-check when
    only the announce/date changed (content unchanged) is harmless."""
    return hashlib.sha1(raw).hexdigest()


@cache
def _torrent_excluded_files() -> frozenset:
    """Lower-cased basenames of every file the Mods tab installs, across all
    mods — the client-root files the torrent sync leaves to the mod system.

    The torrent ships several of them (VfPatcher.dll, nampower.dll, d3d9.dll,
    …), but the Mods tab is the single source of truth for installing /
    disabling / versioning them, so the sync must never fetch, re-add, or flag
    them. Computed once and memoized (MODS_REGISTRY is static at import)."""
    return frozenset(
        os.path.basename(f).lower()
        for mod in MODS_REGISTRY
        for f in mod.get("installed_files", [])
    )


def _is_torrent_excluded(parts) -> bool:
    return len(parts) == 1 and parts[0].lower() in _torrent_excluded_files()


def _torrent_skip(parts, ignore_speech: bool) -> bool:
    """Files the sync must leave alone: mod-owned client-root files, plus
    speech.MPQ when the user opted to keep a custom one (Settings)."""
    if _is_torrent_excluded(parts):
        return True
    return ignore_speech and bool(parts) and parts[-1].lower() == "speech.mpq"


def torrent_selection(client_dir: str, files, drop_mismatched=False,
                      ignore_speech=False):
    """1-indexed list of torrent files that are missing or the wrong size on
    disk (aria2 --select-file), plus whether any were entirely missing."""
    need, missing = [], False
    for i, (parts, length) in enumerate(files):
        if _torrent_skip(parts, ignore_speech):
            continue
        dest = os.path.join(client_dir, *parts)
        try:
            size = os.path.getsize(dest)
        except OSError:
            missing = True
            need.append(i + 1)
            continue
        if size != length:
            # oversized/corrupt file poisons resume — drop it; a short file is
            # kept so aria2 can resume it
            if drop_mismatched or size > length:
                try:
                    os.remove(dest)
                except OSError:
                    pass
            need.append(i + 1)
    return need, missing


def torrent_all_selection(files, ignore_speech=False) -> list:
    """1-indexed list of every non-mod file in the torrent. Used for an
    integrity pass: aria2 --check-integrity verifies each selected file's piece
    hashes and re-downloads only the bad/missing pieces — catching same-size but
    corrupted files that the size-based torrent_selection can't."""
    return [i + 1 for i, (parts, _) in enumerate(files)
            if not _torrent_skip(parts, ignore_speech)]


def torrent_tree_intact(client_dir: str, files, ignore_speech=False) -> bool:
    for parts, length in files:
        if _torrent_skip(parts, ignore_speech):
            continue
        try:
            if os.path.getsize(os.path.join(client_dir, *parts)) != length:
                return False
        except OSError:
            return False
    return True


# Legacy leftovers the current client no longer ships. Locale data folders are
# matched by name; the old patch archives by name AND exact size, so a player
# mod that reused one of these names is never deleted.
_LOCALE_DATA_DIRS = {
    "enus", "engb", "encn", "entw", "kokr", "frfr", "dede", "zhcn",
    "zhtw", "eses", "esmx", "ruru", "ptbr", "ptpt", "itit",
}
_LEGACY_ARCHIVES = {
    "patch-6.mpq": 451195806,
    "patch-7.mpq": 175256564,
    "patch-8.mpq": 484649870,
    "patch-9.mpq": 506808141,
    "patch-a.mpq": 241751337,
}


def prune_stale_client_files(client_dir: str, files) -> list:
    """Remove legacy Data/<locale>/ folders and known old-client patch MPQs the
    current torrent no longer ships. Folders are removed by name (unless the torrent
    still uses them); archives only when the name AND the exact size match a known
    legacy one. Returns removed names."""
    data_dir = os.path.join(client_dir, "Data")
    if not os.path.isdir(data_dir):
        return []
    # what the current torrent puts directly in Data/ (.mpq files and subdirs)
    expected, used_dirs = set(), set()
    for parts, _length in files:
        if not parts or parts[0] != "Data":
            continue
        if len(parts) == 2 and parts[1].lower().endswith(".mpq"):
            expected.add(parts[1].lower())
        elif len(parts) >= 3:
            used_dirs.add(parts[1].lower())

    removed = []
    for name in os.listdir(data_dir):
        lc, full = name.lower(), os.path.join(data_dir, name)
        if os.path.isdir(full):
            if lc in _LOCALE_DATA_DIRS and lc not in used_dirs:
                try:
                    shutil.rmtree(full)
                    removed.append(name + "/")
                except OSError:
                    pass
            continue
        if not lc.endswith(".mpq") or lc in expected:
            continue
        try:
            size = os.path.getsize(full)
        except OSError:
            continue
        if _LEGACY_ARCHIVES.get(lc) == size:
            try:
                os.remove(full)
                removed.append(name)
            except OSError:
                pass
    return removed


# Downloadable MPQ content patches (not shipped with the client). Each is
# a single HTTP file with a `<url>.sha256` sidecar; an update is available when
# that published sha differs from the on-disk file's.
MPQ_PATCHES = [
    {
        "file": "patch-O.mpq",
        "name": "Octo Raid Visuals",
        "description": "Adds ground markers and sounds for boss abilities in raids.",
        "url":  "https://dl.octowow.st/client/latest/Data/patch-O.mpq",
    },
]


def mpq_patch_for(filename: str):
    """The registry entry whose file matches `filename` (case-insensitive)."""
    lc = filename.lower()
    return next((e for e in MPQ_PATCHES if e["file"].lower() == lc), None)


def sha256_file(path: str) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest().lower()


def fetch_mpq_sha256(url: str) -> str:
    """The published SHA256 of an MPQ patch, from its `<url>.sha256` sidecar."""
    req = urllib.request.Request(url + ".sha256", headers={"User-Agent": UA})
    with secure_urlopen(req, timeout=NEWS_TIMEOUT,
                        allowed_hosts=ALLOWED_DOWNLOAD_HOSTS) as r:
        return r.read().decode("ascii", "ignore").strip().split()[0].lower()


def download_mpq_patch(entry: dict, data_dir: str, on_progress=None):
    """Download the patch into <data_dir>/<file>, verifying its published
    SHA256. Writes to a .part file and renames on success. on_progress(done,
    total) is called as bytes arrive."""
    url = entry["url"]
    want = fetch_mpq_sha256(url)
    ensure_dir(data_dir)
    tmp = os.path.join(data_dir, entry["file"] + ".part")
    h = hashlib.sha256()
    req = urllib.request.Request(url, headers={"User-Agent": UA})
    with secure_urlopen(req, timeout=DOWNLOAD_TIMEOUT,
                        allowed_hosts=ALLOWED_DOWNLOAD_HOSTS) as r:
        total = int(r.headers.get("Content-Length") or 0)
        done  = 0
        with open(tmp, "wb") as f:
            while True:
                chunk = r.read(256 * 1024)
                if not chunk:
                    break
                f.write(chunk)
                h.update(chunk)
                done += len(chunk)
                if on_progress:
                    on_progress(done, total)
    if h.hexdigest().lower() != want:
        try:
            os.remove(tmp)
        except OSError:
            pass
        raise RuntimeError("checksum verification failed")
    os.replace(tmp, os.path.join(data_dir, entry["file"]))


def clear_torrent_resume_state():
    """Delete aria2's saved control (.aria2) and metadata (.torrent) files in
    the staging dir. They pin a specific torrent revision (info-hash) and record
    which pieces are 'done', so a stale one causes an 'info hash mismatch' error
    after the client torrent is re-rolled, or blocks re-downloading a file the
    user deleted. Safe to call when nothing is there."""
    try:
        for name in os.listdir(TORRENT_STAGING_DIR):
            if name.endswith((".aria2", ".torrent")):
                try:
                    os.remove(os.path.join(TORRENT_STAGING_DIR, name))
                except OSError:
                    pass
    except OSError:
        pass


def refresh_pristine_wow(client_dir: str):
    """Cache the freshly-synced (unpatched) WoW.exe as the pristine base, so a
    later re-patch always starts from clean bytes."""
    exe = os.path.join(client_dir, "WoW.exe")
    try:
        with open(exe, "rb") as f:
            f.seek(_LOCALE_ASSERT_OFFSET)
            pristine = f.read(1) == b"\xa1"
        if pristine:
            shutil.copyfile(exe, PRISTINE_WOW_PATH)
            log("Cached pristine WoW.exe base.", "dim")
    except OSError:
        pass


def read_pristine_wow(client_dir: str) -> bytes:
    """The clean base to patch from: the cached pristine exe if present, else
    the on-disk WoW.exe."""
    if os.path.exists(PRISTINE_WOW_PATH):
        with open(PRISTINE_WOW_PATH, "rb") as f:
            return f.read()
    with open(os.path.join(client_dir, "WoW.exe"), "rb") as f:
        return f.read()


def _ensure_torrent_junction(client_dir: str) -> str:
    """Point <staging>/client at client_dir via an NTFS junction (no admin) so
    aria2 writes the torrent's files straight into the real client dir. Returns
    the staging dir to pass as aria2 --dir."""
    staging = TORRENT_STAGING_DIR
    ensure_dir(staging)
    link   = os.path.join(staging, TORRENT_NAME)
    target = os.path.abspath(client_dir)
    try:
        if os.path.isdir(link) and \
                os.path.abspath(os.path.realpath(link)) == target:
            return staging
    except OSError:
        pass
    # remove a stale junction/link (rmdir drops the reparse point, not its
    # target's contents) then recreate it
    try:
        os.rmdir(link)
    except OSError:
        try:
            os.remove(link)
        except OSError:
            pass
    r = subprocess.run(["cmd", "/c", "mklink", "/J", link, target],
                       capture_output=True, text=True, creationflags=_NO_WINDOW)
    if not os.path.isdir(link):
        raise RuntimeError("could not create download junction: "
                           + (r.stderr or r.stdout or "").strip())
    return staging


_SIZE_UNITS = {"B": 1, "KiB": 1024, "MiB": 1024 ** 2,
               "GiB": 1024 ** 3, "TiB": 1024 ** 4}
_UNIT = "|".join(_SIZE_UNITS)              # B|KiB|MiB|GiB|TiB
_SIZE = rf"[\d.]+(?:{_UNIT})"              # e.g. 8.8GiB
_FRAC = rf"({_SIZE})/({_SIZE})\((\d+)%\)"  # done/total(percent%)
_ARIA_FRAC = re.compile(_FRAC)
_ARIA_DL   = re.compile(rf"DL:({_SIZE})")
# During --check-integrity aria2 prints the hash-check progress in a separate
# field, e.g. '… [Checksum:#f66a3e 236MiB/1.5GiB(15%)]', while the leading
# completed/total stays at 0%/0B (a complete client downloads nothing). Read the
# Checksum fraction so the bar tracks the check instead of freezing at 0.
_ARIA_CHK  = re.compile(rf"Checksum:#\w+\s+{_FRAC}")


def _to_bytes(s: str) -> float:
    m = re.match(rf"^([\d.]+)({_UNIT})$", s.strip())
    return float(m.group(1)) * _SIZE_UNITS[m.group(2)] if m else 0.0


def parse_aria_progress(line: str):
    """Parse an aria2 summary line like '1.2GiB/8.8GiB(13%) … DL:5.0MiB' →
    {progress, done, total, bps, checking}, or None for non-progress lines.
    A checksum-check line is preferred over the (idle) download fraction."""
    chk = _ARIA_CHK.search(line)
    m   = chk or _ARIA_FRAC.search(line)
    if not m:
        return None
    dl = _ARIA_DL.search(line)
    return {"progress": int(m.group(3)) / 100.0,
            "done":  _to_bytes(m.group(1)),
            "total": _to_bytes(m.group(2)),
            "bps":   _to_bytes(dl.group(1)) if dl else 0.0,
            "checking": chk is not None}


# The currently-running aria2c child, so it can be killed when the app quits
# (a daemon worker thread dying would otherwise orphan it, still downloading
# headless). --stop-with-process is aria2's own belt-and-suspenders for this,
# but it's unreliable on Windows — hence the explicit kill too.
_active_aria2: "subprocess.Popen | None" = None
_active_aria2_lock = threading.Lock()


def stop_aria2c():
    """Terminate the running aria2c child, if any. Safe to call from any thread
    (e.g. the app's close handler)."""
    global _active_aria2
    with _active_aria2_lock:
        proc, _active_aria2 = _active_aria2, None
    if proc and proc.poll() is None:
        try:
            proc.terminate()
        except Exception:
            pass


def run_aria2c(client_dir, select_files=None, check_integrity=False,
               on_progress=None, should_cancel=None, log_fn=log):
    """Sync the client torrent into client_dir with aria2c (leech-only). Blocks
    until aria2c exits; raises on a non-zero exit or cancellation. Calls
    on_progress(dict) per update and should_cancel()->bool to abort.

    aria2 is handed the .torrent URL (not a local copy), so it always fetches
    the server's current torrent at download time — no chance of running a stale
    local .torrent if the user starts the update long after the verify."""
    global _active_aria2
    exe     = ensure_aria2c(log_fn)
    staging = _ensure_torrent_junction(client_dir)
    args = [
        exe,
        f"--dir={staging}",
        # aria2 exits when this PID (the updater) does — stops an orphaned
        # download if we're killed before the explicit stop_aria2c() runs.
        f"--stop-with-process={os.getpid()}",
        "--seed-time=0",
        f"--check-integrity={'true' if check_integrity else 'false'}",
        "--bt-remove-unselected-file=false",
        "--continue=true",
        "--allow-overwrite=true",
        "--auto-file-renaming=false",
        "--file-allocation=none",
        "--disk-cache=128M",
        "--stream-piece-selector=inorder",
        "--max-tries=0",
        "--retry-wait=5",
        "--bt-stop-timeout=120",
        "--auto-save-interval=15",
        "--summary-interval=1",
        "--human-readable=false",
        "--truncate-console-readout=false",
        "--console-log-level=warn",
        "--enable-dht=true",
        "--bt-enable-lpd=true",
        "--max-connection-per-server=8",
        "--split=16",
        "--min-split-size=1M",
    ]
    if select_files:
        args.append("--select-file=" + ",".join(str(i) for i in select_files))
    args.append(CLIENT_TORRENT_URL)

    proc = subprocess.Popen(args, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, text=True,
                            bufsize=1, creationflags=_NO_WINDOW)
    with _active_aria2_lock:
        _active_aria2 = proc
    try:
        for line in proc.stdout:
            if should_cancel and should_cancel():
                proc.terminate()
                raise RuntimeError("Cancelled")
            line = line.strip()
            if not line:
                continue
            p = parse_aria_progress(line)
            if p:
                # aria2's console readout floods idle '0B/total(0%)' lines (no
                # bytes, no checksum) between the once-a-second summary blocks
                # that carry the real figure. Drop the idle ones so they can't
                # stomp progress back to 0 under the UI's latest-wins draining.
                informative = (p["done"] or p["progress"]
                               or p["bps"] or p["checking"])
                if on_progress and informative:
                    on_progress(p)
            else:
                log_fn(f"[aria2] {line}", "dim")
    finally:
        try:
            proc.stdout.close()
        except Exception:
            pass
        with _active_aria2_lock:
            if _active_aria2 is proc:
                _active_aria2 = None
    code = proc.wait()
    if code != 0:
        raise RuntimeError(f"aria2c exited with code {code}")


class VerifyWorker:
    def __init__(self, out_dir: str, log_q: queue.Queue, prog_q: queue.Queue):
        self.out_dir = out_dir
        self.log_q   = log_q
        self.prog_q  = prog_q
        self._cancel = False

    def cancel(self):
        self._cancel = True

    def log(self, msg, tag=""):
        self.log_q.put((msg, tag))

    def progress(self, value, label=""):
        self.prog_q.put((value, label))

    def run(self):
        try:
            self.log("Checking for updates…", "acct")
            raw, files = fetch_torrent()
            self.log("Checking game files…", "acct")

            # aria2 selects by size (a patched WoW.exe keeps the torrent's size,
            # so it's never flagged); need == files missing or wrong-sized.
            ignore_speech = bool(load_config().get("ignore_speech", False))
            need, _missing = torrent_selection(self.out_dir, files,
                                               ignore_speech=ignore_speech)
            have_exe = os.path.exists(os.path.join(self.out_dir, "WoW.exe"))

            if have_exe and not need:
                self.log("Everything is up to date!", "ok")
                self.log_q.put(("__UP_TO_DATE__", ""))
            else:
                self.log("Update available.", "acct")
                self.log_q.put(("__UPDATE_NEEDED__", ""))
        except Exception as e:
            self.log(f"Verification failed: {e}", "err")
            self.log_q.put(("__UPDATE_NEEDED__", ""))


class UpdateWorker:
    def __init__(self, out_dir: str, log_q: queue.Queue, prog_q: queue.Queue,
                 check_integrity: bool = False, overwrite_config: bool = False):
        self.out_dir = out_dir
        self.log_q   = log_q
        self.prog_q  = prog_q
        self._cancel = False
        # Integrity mode: aria2 hash-checks every file's pieces and repairs
        # them (catches same-size corruption size-based selection misses).
        self.check_integrity  = check_integrity
        # Write a fresh Config.wtf on a reconcile.
        self.overwrite_config = overwrite_config

    def cancel(self):
        self._cancel = True

    def log(self, msg: str, tag: str = ""):
        self.log_q.put((msg, tag))

    def progress(self, value: float, label: str = ""):
        self.prog_q.put((value, label))

    def build_tweaks(self, buf, tweaks: dict | None = None):
        if tweaks is None:
            tweaks = load_tweaks_config()

        fov_deg = tweaks.get("fieldOfView", TWEAKS_DEFAULTS["fieldOfView"])
        fov     = fov_deg * (math.pi / 180.0)
        flags   = struct.unpack_from("<H", buf, 0x126)[0] | 0x20

        nameplate = float(tweaks.get("nameplateRange", TWEAKS_DEFAULTS["nameplateRange"]))
        far_clip  = float(tweaks.get("farClip",        TWEAKS_DEFAULTS["farClip"]))
        frill     = float(tweaks.get("frillDistance",  TWEAKS_DEFAULTS["frillDistance"]))
        cam_dist  = float(tweaks.get("cameraDistance", TWEAKS_DEFAULTS["cameraDistance"]))
        snd_bg    = 0x27 if tweaks.get("soundInBackground", TWEAKS_DEFAULTS["soundInBackground"]) else 0x14

        always_loot = tweaks.get("alwaysAutoLoot", TWEAKS_DEFAULTS["alwaysAutoLoot"])
        locale      = tweaks.get("locale", TWEAKS_DEFAULTS["locale"])

        # fmt: off
        return [
            ("gameLanguage", "bytes", None, locale_patches(locale)),
            ("largeAddress",          "uint16", 0x126,     flags),
            ("fieldOfView",           "float",  0x4089b4,  fov),
            ("cameraDistance",        "float",  0x4089a4,  cam_dist),
            ("farClip",               "float",  0x40fed8,  far_clip),
            ("frillDistance",         "float",  0x467958,  frill),
            ("nameplateRange",        "float",  0x40c448,  nameplate),
            ("soundInBackground",     "int8",   0x3a4869,  snd_bg),
            ("alwaysAutoLoot", "bytes", None, [
                (0x0c1ecf, bytes([0x75 if always_loot else 0x74])),
                (0x0c2b25, bytes([0x75 if always_loot else 0x74])),
            ]),
            # cameraSkipFix is baked into the torrent's WoW.exe, so we don't
            # apply it. skillUiGateHijack and octowowUrlAllowlist below are
            # baked in too, but the official launcher still applies these 2
            # specific patches, so we mirror it in case the Octo devs drop them
            # from WoW.exe again.
            ("octowowUrlAllowlist", "bytes", None, [
                (0x45ccd8, bytes([
                    0x6f,0x63,0x74,0x6f,0x77,0x6f,0x77,0x2e,0x73,0x74,
                    0x00,0x00,0x00,0x00,0x00,0x00,
                ])),
            ]),
            ("skillUiGateHijack", "bytes", None, [
                (0x002ddf90, bytes([
                    0x55,0x8b,0xec,0x83,0xec,0x08,0x53,0x56,0x57,0x8b,0x3d,0x60,0xab,0xce,0x00,0x83,
                    0xff,0xff,0x89,0x55,0xfc,0x89,0x4d,0xf8,0x74,0x79,0x8b,0x75,0x08,0x8b,0x15,0x58,
                    0xab,0xce,0x00,0x8b,0xc7,0x23,0xc6,0x8d,0x04,0x40,0x8b,0x4c,0x82,0x08,0xf6,0xc1,
                    0x01,0x8d,0x44,0x82,0x04,0x75,0x04,0x85,0xc9,0x75,0x05,0x33,0xc9,0x8d,0x49,0x00,
                    0xf6,0xc1,0x01,0x75,0x4e,0x85,0xc9,0x74,0x4a,0x39,0x31,0x74,0x13,0x8b,0xc7,0x23,
                    0xc6,0x8d,0x04,0x40,0x8d,0x04,0x82,0x8b,0x00,0x03,0xc1,0x8b,0x48,0x04,0xeb,0xe0,
                    0x8b,0x59,0x1c,0x8b,0x71,0x18,0x33,0xff,0x85,0xdb,0x7e,0x27,0x8d,0x64,0x24,0x00,
                    0x8b,0x4e,0x0c,0x8b,0x56,0x08,0x6a,0x00,0x6a,0x00,0x51,0x8b,0x4d,0xf8,0x52,0x8b,
                    0x55,0xfc,0xe8,0xb9,0xfd,0xff,0xff,0x84,0xc0,0x75,0x13,0x47,0x83,0xc6,0x20,0x3b,
                    0xfb,0x7c,0xdd,0x5f,0x5e,0x33,0xc0,0x5b,0x8b,0xe5,0x5d,0xc2,0x04,0x00,0x5f,0x8b,
                    0xc6,0x5e,0x5b,0x8b,0xe5,0x5d,0xc2,0x04,0x00,0x90,0x90,0x90,0x90,0x90,0x90,0x90,
                ])),
            ]),
        ]
        # fmt: on

    def patch_exe(self, tweaks: dict | None = None):
        exe = os.path.join(self.out_dir, "WoW.exe")
        if not os.path.exists(exe):
            raise RuntimeError(f"WoW.exe not found in {self.out_dir}")
        self.log("\nApplying binary tweaks to WoW.exe…")
        # Patch the pristine (unpatched) base rather than the on-disk exe, so a
        # re-patch (tweak or language change) never stacks on patched bytes.
        buf = bytearray(read_pristine_wow(self.out_dir))
        for label, kind, offset, value in self.build_tweaks(buf, tweaks):
            self.log(f"  {label}", "dim")
            if kind == "float":
                struct.pack_into("<f",  buf, offset, value)
            elif kind == "int8":
                struct.pack_into("<b",  buf, offset, value)
            elif kind == "uint16":
                struct.pack_into("<H",  buf, offset, value)
            elif kind == "bytes":
                for off, data in value:
                    buf[off: off + len(data)] = data
        with open(exe, "wb") as f:
            f.write(buf)
        self.log("WoW.exe patched.", "ok")

    def run(self):
        # The selection is recomputed here from the live torrent so an
        # interrupted sync always resumes against the current file set.
        try:
            self.log("\nStarting client sync…\n", "acct")
            self.progress(0.0, "Preparing…")
            raw, files = fetch_torrent()
            version = torrent_version(raw)

            # aria2's saved control state pins a torrent revision and its
            # completed pieces. When the torrent was re-rolled (new identity) or
            # the folder changed, that state is stale — an 'info hash mismatch'
            # error, or skipped re-downloads. Clear it and (for a new revision)
            # drop wrong-sized files so they re-fetch clean.
            cfg = load_config()
            stale = (cfg.get("active_torrent_hash") != version or
                     cfg.get("active_client_dir") != os.path.abspath(self.out_dir))
            if stale:
                clear_torrent_resume_state()
                update_config(lambda c: c.update({
                    "active_torrent_hash": version,
                    "active_client_dir": os.path.abspath(self.out_dir)}))

            # Config.wtf is user game config, not in the torrent — (re)write it
            # on a reconcile (overwrite_config), or when missing.
            cfg_wtf = os.path.join(self.out_dir, "WTF", "Config.wtf")
            if self.overwrite_config or not os.path.exists(cfg_wtf):
                write_config_wtf(self.out_dir)

            # WoW.exe on disk is patched, so an integrity check always flags it
            # and re-fetches its pieces over the network. Restore the cached
            # pristine base first: the check then passes with no re-download when
            # the client is unchanged (aria2 still repairs it if the torrent's
            # WoW.exe genuinely changed). It's re-patched after the check.
            wow_path = os.path.join(self.out_dir, "WoW.exe")
            if (self.check_integrity and os.path.exists(PRISTINE_WOW_PATH)
                    and os.path.exists(wow_path)):
                shutil.copyfile(PRISTINE_WOW_PATH, wow_path)

            # speech.MPQ is left unverified/un-updated when the user keeps a
            # custom one (Settings → Ignore speech.mpq).
            ignore_speech = bool(load_config().get("ignore_speech", False))
            if self.check_integrity:
                # Full piece-hash verify + repair of every non-mod file — aria2
                # re-hashes them and re-fetches only the bad/missing pieces.
                need, missing = torrent_all_selection(
                    files, ignore_speech=ignore_speech), False
            else:
                need, missing = torrent_selection(
                    self.out_dir, files, drop_mismatched=stale,
                    ignore_speech=ignore_speech)
            # A file the user deleted leaves its pieces marked done in the
            # control file, so aria2 skips it forever — clear resume state.
            if missing:
                clear_torrent_resume_state()
            wow_downloaded = any(files[i - 1][0] == ["WoW.exe"] for i in need)

            if need:
                self.log(
                    (f"Verifying {len(need)} file(s) via torrent…"
                     if self.check_integrity
                     else f"Syncing {len(need)} file(s) via torrent…"), "acct")

                def _prog(p):
                    label = f"{fmt_size(p['done'])} / {fmt_size(p['total'])}"
                    if p["bps"]:
                        label += "   •   " + fmt_speed(p["bps"])
                    frac = p["done"] / p["total"] if p["total"] else 0.0
                    self.progress(min(frac, 1.0), label)

                run_aria2c(self.out_dir, select_files=need,
                           check_integrity=self.check_integrity,
                           on_progress=_prog,
                           should_cancel=lambda: self._cancel, log_fn=self.log)
            else:
                self.log("All game files already present.", "dim")

            if self._cancel:
                self.log("\nUpdate cancelled.", "err")
                self.progress(0.0, "Cancelled")
                self.log_q.put(("__ERROR__", ""))
                return

            self.progress(1.0, "Verifying…")
            if not torrent_tree_intact(self.out_dir, files,
                                       ignore_speech=ignore_speech):
                self.log("\n✗  Download incomplete — click Update to finish.", "err")
                self.log_q.put(("__ERROR__", ""))
                return

            self.log("\nDownload complete.", "ok")
            remove_wdb(self.out_dir)

            # Drop legacy leftovers the current torrent no longer ships
            for gone in prune_stale_client_files(self.out_dir, files):
                self.log(f"Removed legacy file: {gone}", "dim")

            # Cache the fresh pristine exe, then patch WoW.exe from that
            # clean base — but only when the sync actually (re)downloaded it.
            refresh_pristine_wow(self.out_dir)
            if wow_downloaded:
                self.progress(1.0, "Patching…")
                self.patch_exe()
            else:
                self.log("\nWoW.exe unchanged — skipping patch.", "dim")

            self.progress(1.0, "")
            self.log("\n✓  Everything is up to date!", "ok")
            client_ver = get_client_version(self.out_dir)
            if client_ver:
                self.log(f"Client version: {client_ver}", "dim")
                self.log_q.put((f"__VERSION__{client_ver}", ""))
            else:
                self.log("Could not read client version from WoW.exe", "dim")
            self.log_q.put(("__DONE__", ""))

        except Exception as e:
            self.log(f"\n✗  {e}", "err")
            self.progress(0.0, "")
            self.log_q.put(("__ERROR__", ""))


def write_config_wtf(client_dir: str, tweaks: dict | None = None):
    """Write a fresh Config.wtf from scratch, overwriting any existing one.
    Never raises — logs the error if the file can't be written (read-only,
    locked by a running game, or an unwritable folder)."""
    if tweaks is None:
        tweaks = load_tweaks_config()
    far_clip  = tweaks.get("farClip",        TWEAKS_DEFAULTS["farClip"])
    cam_dist  = tweaks.get("cameraDistance", TWEAKS_DEFAULTS["cameraDistance"])
    nameplate = tweaks.get("nameplateRange", TWEAKS_DEFAULTS["nameplateRange"])
    fov_deg   = tweaks.get("fieldOfView",    TWEAKS_DEFAULTS["fieldOfView"])
    fov_rad   = round(fov_deg * math.pi / 180.0, 6)
    bg_sound  = 1 if tweaks.get("soundInBackground",
                                TWEAKS_DEFAULTS["soundInBackground"]) else 0

    di  = _get_display_info_safe()
    srv = "octowow.st"
    vars_ = {
        "realmList": srv, "patchList": srv,
        "readTOS": 1, "readEULA": 1,
        "profanityFilter": 0,
        "gxResolution": f"{di['width']}x{di['height']}",
        "gxWindow": 1, "gxMaximize": 1,
        "gxVSync": 0,
        "gxColorBits": 24, "gxDepthBits": 24,
        "gxRefresh": di["refresh_rate"],
        "gxMultisampleQuality": 0, "gxMultisample": 2,
        "hwDetect": 0,
        "pixelShaders": 1, "M2UsePixelShaders": 1,
        "specular": 1,
        "anisotropic": 16, "trilinear": 1,
        "lod": 0, "lodDist": 100,
        "texLodBias": 0,
        "shadowLevel": 0,
        "particleDensity": 1,
        "fullAlpha": 1,
        "SmallCull": 0.01,
        "farClip": far_clip,
        "DistCull": 888.8,
        "frillDensity": 128,
        "unitDrawDist": 300,
        "weatherDensity": 3,
        "FoV": fov_rad,
        "NameplateRange": nameplate,
        "CameraDistanceMax": cam_dist,
        "cameraDistanceMaxFactor": 1,
        "scriptMemory": 512000,
        "uiScale": 1,
        "mouseSpeed": 1,
        "autoSelfCast": 1,
        "movie": 0,
        "movieSubtitle": 1,
        "checkAddonVersion": 0,
        "minimapZoom": 0, "minimapInsideZoom": 0,
        "EnableErrorSpeech": 0,
        "SoundZoneMusicNoDelay": 1,
        "SoundMaxHardwareChannels": 64,
        "SoundSoftwareChannels": 64,
        "UncapSounds": 1,
        "BackgroundSound": bg_sound,
        "NP_NameplateDistance": nameplate,
        "NP_SpellQueueWindowMs": 150,
        "NP_EnableAuraCastEvents": 1,
        "NP_EnableAutoAttackEvents": 1,
        "NP_EnableSpellStartEvents": 1,
        "NP_EnableSpellGoEvents": 1,
        "NP_EnableSpellHealEvents": 1,
        "NP_QueueCastTimeSpells": 0,
        "NP_QueueInstantSpells": 0,
        "NP_QueueChannelingSpells": 0,
        "NP_QueueTargetingSpells": 0,
        "NP_QueueSpellsOnCooldown": 0,
        "NP_ChatBubbleDistance": 60,
        "NP_ChatBubblesWhisper": 1,
        "NP_ChatBubblesRaid": 1,
        "NP_ChatBubblesBattleground": 1,
        "ChatBubblesParty": 1,
    }
    try:
        cfg_dir = os.path.join(client_dir, "WTF")
        ensure_dir(cfg_dir)
        with open(os.path.join(cfg_dir, "Config.wtf"), "w",
                  encoding="utf-8") as f:
            for k, v in vars_.items():
                f.write(f'SET {k} "{v}"\n')
        log("Config.wtf written.", "ok")
    except Exception as e:
        log(f"Could not write Config.wtf: {e}", "err")


def update_config_wtf(client_dir: str, tweaks: dict):
    cfg_path = os.path.join(client_dir, "WTF", "Config.wtf")
    if not os.path.exists(cfg_path):
        write_config_wtf(client_dir, tweaks)
        return

    far_clip  = tweaks.get("farClip",        TWEAKS_DEFAULTS["farClip"])
    cam_dist  = tweaks.get("cameraDistance", TWEAKS_DEFAULTS["cameraDistance"])
    nameplate = tweaks.get("nameplateRange", TWEAKS_DEFAULTS["nameplateRange"])
    fov_deg   = tweaks.get("fieldOfView",    TWEAKS_DEFAULTS["fieldOfView"])
    fov_rad   = round(fov_deg * math.pi / 180.0, 6)
    bg_sound  = 1 if tweaks.get("soundInBackground",
                                TWEAKS_DEFAULTS["soundInBackground"]) else 0
    updates = {
        "farClip":              str(far_clip),
        "CameraDistanceMax":    str(cam_dist),
        "NP_NameplateDistance": str(nameplate),
        "FoV":                  str(fov_rad),
        "NameplateRange":       str(nameplate),
        "BackgroundSound":      str(bg_sound),
    }

    with open(cfg_path, "r", encoding="utf-8") as f:
        lines = f.readlines()

    updated_keys = set()
    new_lines = []
    for line in lines:
        matched = False
        for key, val in updates.items():
            if line.strip().lower().startswith(f"set {key.lower()} "):
                new_lines.append("SET " + key + ' "' + val + '"\n')
                updated_keys.add(key)
                matched = True
                break
        if not matched:
            new_lines.append(line)

    for key, val in updates.items():
        if key not in updated_keys:
            new_lines.append("SET " + key + ' "' + val + '"\n')

    with open(cfg_path, "w", encoding="utf-8") as f:
        f.writelines(new_lines)

    log(f"  Config.wtf updated: farClip={far_clip}, CameraDistanceMax={cam_dist}, "
        f"NameplateRange={nameplate}, NP_NameplateDistance={nameplate}, "
        f"FoV={fov_rad}", "dim")


# ──────────────────────────────────────────────────────────────────────────────
#  Mods definition & engine
# ──────────────────────────────────────────────────────────────────────────────

# Registry order == install order: VanillaFixes first (it provides the
# loader the other mods rely on). The UI sorts alphabetically for display.
MODS_REGISTRY = [
    {
        "id":          "VanillaFixes",
        "essential": True,
        "name":        "VanillaFixes",
        "description": "Eliminates stuttering and animation lag and enables mod loading. Required by other mods.",
        "repo_url":    "https://github.com/hannesmann/vanillafixes",
        "source": {
            "kind":          "github_release",
            "owner":         "hannesmann",
            "repo":          "vanillafixes",
            "asset_pattern": "vanillafixes-*.zip",
            "prefer_no":     "-dxvk",
            "extract_map":   {"VfPatcher.dll": "VfPatcher.dll",
                              "VanillaFixes.exe": "VanillaFixes.exe"},
        },
        "register_dll":    None,   # the DLL loader itself
        "installed_files": ["VfPatcher.dll", "VanillaFixes.exe"],
    },
    {
        "id":          "ClassicAPI",
        "essential": True,
        "name":        "ClassicAPI",
        "description": "Expands the addon API with functions from later WoW versions.",
        "repo_url":    "https://github.com/brues-code/ClassicAPI",
        "source": {
            "kind":          "github_release",
            "owner":         "brues-code",
            "repo":          "ClassicAPI",
            "asset_pattern": "ClassicAPI.dll",
            "prefer_no":     None,
            "extract_map":   None,
        },
        "register_dll":    "ClassicAPI.dll",
        "installed_files": ["ClassicAPI.dll"],
    },
    {
        "id":          "AuctionQueryThrottle",
        "essential": True,
        "name":        "AuctionQueryThrottle",
        "description": "Removes the fixed 5-second wait between auction house searches.",
        "repo_url":    "https://github.com/brues-code/AuctionQueryThrottle",
        "source": {
            "kind":          "github_release",
            "owner":         "brues-code",
            "repo":          "AuctionQueryThrottle",
            "asset_pattern": "AuctionQueryThrottle.dll",
            "prefer_no":     None,
            "extract_map":   None,
        },
        "register_dll":    "AuctionQueryThrottle.dll",
        "installed_files": ["AuctionQueryThrottle.dll"],
    },
    {
        "id":          "dxvk",
        "essential": True,
        "name":        "DXVK",
        "description": "Enables Vulkan-based rendering for improved performance.",
        "repo_url":    "https://github.com/doitsujin/dxvk",
        "source": {
            "kind":          "github_release",
            "owner":         "doitsujin",
            "repo":          "dxvk",
            "asset_pattern": "dxvk-[0-9]*.tar.gz",
            "prefer_no":     "-native",
            "extract_map":   {"dxvk-*/x32/d3d9.dll": "d3d9.dll"},
            "post_install":  ["write_dxvk_conf"],
        },
        "register_dll":    None,   # d3d9.dll auto-loads as a DirectX proxy
        "installed_files": ["d3d9.dll", "dxvk.conf"],
    },
    {
        "id":          "nampower",
        "essential": True,
        "name":        "Nampower",
        "description": "Reduces input lag and expands the addon API.",
        "repo_url":    "https://github.com/Emyrk/nampower",
        "source": {
            "kind":          "github_release",
            "owner":         "Emyrk",
            "repo":          "nampower",
            "asset_pattern": "nampower.dll",
            "prefer_no":     None,
            "extract_map":   None,
        },
        "register_dll":    "nampower.dll",
        "installed_files": ["nampower.dll"],
    },
    {
        "id":          "SuperWoW",
        "essential": True,
        "name":        "SuperWoW",
        "description": "Adds new features, including healing combat text, chat links of spells and recipes, and expands the addon API.",
        "repo_url":    "https://github.com/balakethelock/SuperWoW",
        "source": {
            "kind":          "github_release",
            "owner":         "balakethelock",
            "repo":          "SuperWoW",
            "asset_pattern": "SuperWoW*.zip",
            "prefer_no":     None,
            # SuperWoW keeps a static "Release" tag and edits it in place, so
            # the version comes from the asset filename (e.g. …2.2.zip), not
            # the tag.
            "version_from":  "asset",
            "extract_map":   {"SuperWoWhook.dll": "SuperWoWhook.dll"},
        },
        "register_dll":    "SuperWoWhook.dll",
        "installed_files": ["SuperWoWhook.dll"],
    },
    {
        "id":          "transmogfix",
        "essential": True,
        "name":        "TransmogFix",
        "description": "Prevents frame drops on character death caused by the server-side transmogrification durability recalculation.",
        "repo_url":    "https://codeberg.org/MarcelineVQ/WeirdUtils",
        "source": {
            "kind":          "direct_file",
            "url":           "https://codeberg.org/MarcelineVQ/WeirdUtils/releases/download/v0.7.0/transmogfix.dll",
            "dest":          "transmogfix.dll",
            "pinned_version": "v0.7.0",
        },
        "register_dll":    "transmogfix.dll",
        "installed_files": ["transmogfix.dll"],
    },
    {
        "id":          "UnitXP_SP3",
        "essential": True,
        "name":        "UnitXP_SP3",
        "description": "Adds new features, including frame limiter, improved targeting, and anti-aliased combat text, and expands the addon API.",
        "repo_url":    "https://codeberg.org/konaka/UnitXP_SP3",
        "source": {
            "kind":          "codeberg_release",
            "owner":         "konaka",
            "repo":          "UnitXP_SP3",
            "asset_pattern": "UnitXP_SP3 v*.zip",
            "prefer_no":     "-debug",
            "extract_map":   {"UnitXP_SP3.dll": "UnitXP_SP3.dll"},
        },
        "register_dll":    "UnitXP_SP3.dll",
        "installed_files": ["UnitXP_SP3.dll"],
    },
    {
        "id":          "VanillaHelpers",
        "essential": True,
        "name":        "VanillaHelpers",
        "description": "Increases the maximum supported texture resolution and improves memory allocation.",
        "repo_url":    "https://github.com/isfir/VanillaHelpers",
        "source": {
            "kind":          "github_release",
            "owner":         "isfir",
            "repo":          "VanillaHelpers",
            "asset_pattern": "VanillaHelpers.dll",
            "prefer_no":     None,
            "extract_map":   None,
        },
        "register_dll":    "VanillaHelpers.dll",
        "installed_files": ["VanillaHelpers.dll"],
    },
    {
        "id":          "VanillaMultiMonitorFix",
        "essential": False,
        "name":        "VanillaMultiMonitorFix",
        "description": "Fixes incorrect game resolution on multi-monitor setups with different resolutions. Set the desired monitor's index in VMMFix_preferred_monitor.txt; use ShowAllDisplayDevices.exe to find the index.",
        "repo_url":    "https://github.com/Mates1500/VanillaMultiMonitorFix",
        "source": {
            "kind":          "github_release",
            "owner":         "Mates1500",
            "repo":          "VanillaMultiMonitorFix",
            "asset_pattern": "release.zip",
            "prefer_no":     None,
            "extract_map":   {"VanillaMultiMonitorFix.dll":
                              "VanillaMultiMonitorFix.dll",
                              "VMMFix_preferred_monitor.txt":
                              "VMMFix_preferred_monitor.txt",
                              "ShowAllDisplayDevices.exe":
                              "ShowAllDisplayDevices.exe"},
        },
        "register_dll":    "VanillaMultiMonitorFix.dll",
        "installed_files": ["VanillaMultiMonitorFix.dll",
                            "VMMFix_preferred_monitor.txt",
                            "ShowAllDisplayDevices.exe"],
    },
    {
        "id":          "no1600x1200",
        "essential": False,
        "name":        "No1600x1200",
        "description": "Fixes incorrect game resolution when your monitor native resolution isn't detected or 1600x1200 is listed as the maximum.",
        "repo_url":    "https://github.com/RetroCro/TurtleWoW-Mods",
        "source": {
            "kind":          "direct_file",
            "url":           "https://raw.githubusercontent.com/RetroCro/TurtleWoW-Mods/refs/heads/main/Archive/DLL%20BACKUP/no1600x1200.dll",
            "dest":          "no1600x1200.dll",
            "pinned_version": "1.0",
        },
        "register_dll":    "no1600x1200.dll",
        "installed_files": ["no1600x1200.dll"],
    },
]

GITHUB_API = "https://api.github.com"

# Self-update: the updater checks its own GitHub releases once a day.
UPDATER_REPO      = "rebasedkon/octo-updater"
UPDATER_CHECK_TTL = 86400   # 1 day, cached in the config file


def _parse_version(v: str) -> tuple:
    """'v1.2.0' → (1, 2, 0); non-numeric parts become 0."""
    parts = []
    for p in (v or "").strip().lstrip("vV").split("."):
        digits = "".join(ch for ch in p if ch.isdigit())
        parts.append(int(digits) if digits else 0)
    return tuple(parts) or (0,)


def fetch_updater_latest_tag(force: bool = False) -> str | None:
    """Latest release tag of the updater's own repo, cached for a day. Returns
    None when there are no releases yet (GitHub 404) or on any error."""
    now = time.time()
    if not force:
        entry = load_config().get("updater_release_cache", {})
        if (entry.get("tag") is not None
                and (now - entry.get("timestamp", 0)) < UPDATER_CHECK_TTL):
            return entry["tag"]
    try:
        req = urllib.request.Request(
            f"{GITHUB_API}/repos/{UPDATER_REPO}/releases/latest",
            headers={"User-Agent": UA})
        with secure_urlopen(req, timeout=10) as r:
            tag = json.load(r).get("tag_name")
    except Exception:
        return None
    if tag:
        update_config(lambda c: c.__setitem__(
            "updater_release_cache", {"timestamp": now, "tag": tag}))
    return tag


def updater_update_available(latest_tag: str) -> bool:
    if not latest_tag:
        return False
    a, b = _parse_version(latest_tag), _parse_version(UPDATER_VERSION)
    n = max(len(a), len(b))               # zero-pad so 1.1 == 1.1.0
    a += (0,) * (n - len(a))
    b += (0,) * (n - len(b))
    return a > b


def _codeberg_latest(owner: str, repo: str, raise_errors=False) -> dict | None:
    url = f"https://codeberg.org/api/v1/repos/{owner}/{repo}/releases?limit=10&pre-release=false"
    try:
        req = urllib.request.Request(url, headers={"User-Agent": UA})
        with secure_urlopen(req, timeout=10) as r:
            releases = json.load(r)
        for rel in releases:
            if not rel.get("prerelease", False) and not rel.get("draft", False):
                return rel
        return releases[0] if releases else None
    except Exception as e:
        if raise_errors:
            raise RuntimeError(_describe_net_error(e)) from e
        return None


DXVK_CONF_CONTENT = """# Low latency - limit queued frames - helps input lag
d3d9.maxFrameLatency = 1
# Forces clamp for AF through DXVK - if you see grass textures shimmering or shaking try false
d3d9.clampNegativeLodBias = True
# Disable logging for performance
dxvk.logLevel = none
# Overrides synchronization interval (Vsync) for presentation.
# Setting this to 0 disables vertical synchronization entirely.
# A positive value 'n' will enable Vsync and repeat the same
# image n times, and a negative value will have no effect.
#
# Value -1 uses the application's setting
d3d9.presentInterval = -1
# VanillaFix handles DPI awareness; avoid double-scaling
d3d9.dpiAware = False
# Enable GPL if supported to reduce stuttering (NVIDIA 473.33+, AMD 24.6.1+)
dxvk.enableGraphicsPipelineLibrary = Auto
# Track pipeline lifetimes to reduce memory usage
dxvk.trackPipelineLifetime = True
# Limit compiler threads to reduce memory usage
dxvk.numCompilerThreads = 2
"""


def _write_dxvk_conf(client_dir: str):
    path = os.path.join(client_dir, "dxvk.conf")
    with open(path, "w", encoding="utf-8") as f:
        f.write(DXVK_CONF_CONTENT)
    log("  Wrote dxvk.conf")


def _github_latest(owner: str, repo: str, raise_errors=False) -> dict | None:
    url = f"{GITHUB_API}/repos/{owner}/{repo}/releases/latest"
    try:
        req = urllib.request.Request(url, headers={"User-Agent": UA})
        with secure_urlopen(req, timeout=10) as r:
            return json.load(r)
    except Exception as e:
        if raise_errors:
            raise RuntimeError(_describe_net_error(e)) from e
        return None


def _pick_asset(assets: list, pattern: str, prefer_no) -> dict | None:
    import fnmatch
    candidates = [a for a in assets if fnmatch.fnmatch(a["name"], pattern)]
    if prefer_no:
        preferred = [a for a in candidates if prefer_no not in a["name"]]
        if preferred:
            candidates = preferred
    return candidates[0] if candidates else None


def _release_version(mod: dict, rel: dict) -> str | None:
    """Version string for a github/codeberg release. Normally the tag name —
    but some mods (e.g. SuperWoW) keep a static tag and edit the release in
    place, so their tag never changes. For those, derive the version from the
    matched asset instead: its filename embeds the real version."""
    src = mod["source"]
    if src.get("version_from") == "asset":
        asset = _pick_asset(rel.get("assets", []), src["asset_pattern"],
                            src.get("prefer_no"))
        if asset and asset.get("name"):
            import re
            m = re.search(r"\d+(?:[._]\d+)+", asset["name"])
            return m.group(0) if m else asset["name"]
    return rel.get("tag_name")


def fetch_mod_latest_version(mod: dict) -> str | None:
    src  = mod["source"]
    kind = src["kind"]
    if kind == "github_release":
        rel = _github_latest(src["owner"], src["repo"])
        if rel:
            return _release_version(mod, rel)
    elif kind == "codeberg_release":
        rel = _codeberg_latest(src["owner"], src["repo"])
        if rel:
            return _release_version(mod, rel)
    elif kind in ("direct_file", "direct_tar"):
        return src.get("pinned_version")
    return None


_MOD_VERSION_CACHE_TTL = 3600


def _slim_release(rel: dict) -> dict:
    """Reduce an API release object to the fields the updater actually uses,
    so the persisted cache stays small."""
    return {
        "tag_name": rel.get("tag_name"),
        "assets": [{"name": a.get("name"),
                    "size": a.get("size", 0),
                    "browser_download_url": a.get("browser_download_url")}
                   for a in rel.get("assets", [])],
    }


def _fetch_release_cached(mod: dict, force: bool = False) -> dict | None:
    """Latest-release lookup backed by a persistent cache in the config file
    ({"mod_release_cache": {mod_id: {"timestamp": epoch, "release": {…}}}}),
    so restarts within the TTL don't re-hit the GitHub/Codeberg APIs."""
    src  = mod["source"]
    kind = src["kind"]
    if kind not in ("github_release", "codeberg_release"):
        return None
    mid = mod["id"]
    now = time.time()
    if not force:
        entry = load_config().get("mod_release_cache", {}).get(mid)
        if entry and (now - entry.get("timestamp", 0)) < _MOD_VERSION_CACHE_TTL:
            return entry.get("release")
    if kind == "github_release":
        rel = _github_latest(src["owner"], src["repo"])
    else:
        rel = _codeberg_latest(src["owner"], src["repo"])
    if rel is None:
        return None
    rel = _slim_release(rel)
    update_config(lambda c: c.setdefault("mod_release_cache", {}).__setitem__(
        mid, {"timestamp": now, "release": rel}))
    return rel


def fetch_mod_latest_version_cached(mod: dict, force: bool = False) -> str | None:
    src  = mod["source"]
    kind = src["kind"]
    if kind in ("direct_file", "direct_tar"):
        return src.get("pinned_version")
    rel = _fetch_release_cached(mod, force=force)
    if rel:
        return _release_version(mod, rel)
    return None


def install_mod(mod: dict, client_dir: str, release: dict | None = None) -> list:
    src     = mod["source"]
    written = []

    if src["kind"] == "codeberg_release":
        rel = release if release is not None else \
            _codeberg_latest(src["owner"], src["repo"], raise_errors=True)
        if not rel:
            raise RuntimeError("no release found on Codeberg")
        import fnmatch
        assets = rel.get("assets", [])
        asset  = next(
            (a for a in assets if fnmatch.fnmatch(a["name"], src["asset_pattern"])
             and (not src.get("prefer_no") or src["prefer_no"] not in a["name"])),
            None
        )
        if not asset:
            raise RuntimeError(
                f"No matching asset '{src['asset_pattern']}' in {mod['id']} release")
        log(f"  Downloading {asset['name']} ({asset['size']//1024} KB)...")
        req = urllib.request.Request(asset["browser_download_url"],
                                     headers={"User-Agent": UA})
        with secure_urlopen(req, timeout=120,
                            allowed_hosts=ALLOWED_DOWNLOAD_HOSTS) as r:
            data = r.read()
        if src.get("extract_map") is None:
            dest_rel = asset["name"]
            dest     = os.path.join(client_dir, dest_rel)
            os.makedirs(os.path.dirname(dest) or client_dir, exist_ok=True)
            with open(dest, "wb") as f:
                f.write(data)
            written.append(dest_rel)
            log(f"  Installed {dest_rel}")
        else:
            import zipfile
            tmp_path = os.path.join(client_dir, f"_mod_tmp_{mod['id']}.zip")
            try:
                with open(tmp_path, "wb") as f:
                    f.write(data)
                with zipfile.ZipFile(tmp_path) as zf:
                    for zip_path, dest_rel in src["extract_map"].items():
                        try:
                            zip_data = zf.read(zip_path)
                        except KeyError:
                            log(f"  Warning: {zip_path} not in zip, skipping")
                            continue
                        dest = os.path.join(client_dir, dest_rel)
                        os.makedirs(os.path.dirname(dest) or client_dir, exist_ok=True)
                        with open(dest, "wb") as f:
                            f.write(zip_data)
                        written.append(dest_rel)
                        log(f"  Installed {dest_rel}")
            finally:
                if os.path.exists(tmp_path):
                    os.unlink(tmp_path)

    elif src["kind"] == "github_release":
        rel = release if release is not None else \
            _github_latest(src["owner"], src["repo"], raise_errors=True)
        if not rel:
            raise RuntimeError("no release found on GitHub")
        asset = _pick_asset(rel.get("assets", []), src["asset_pattern"], src["prefer_no"])
        if not asset:
            raise RuntimeError(
                f"No matching asset '{src['asset_pattern']}' in {mod['id']} release")
        log(f"  Downloading {asset['name']} ({asset['size']//1024} KB)...")
        req = urllib.request.Request(asset["browser_download_url"],
                                     headers={"User-Agent": UA})
        with secure_urlopen(req, timeout=120,
                            allowed_hosts=ALLOWED_DOWNLOAD_HOSTS) as r:
            data = r.read()

        if src.get("extract_map") is None:
            dest_rel = asset["name"]
            dest     = os.path.join(client_dir, dest_rel)
            os.makedirs(os.path.dirname(dest) or client_dir, exist_ok=True)
            with open(dest, "wb") as f:
                f.write(data)
            written.append(dest_rel)
            log(f"  Installed {dest_rel}")
        elif asset["name"].endswith(".tar.gz") or asset["name"].endswith(".tgz"):
            import tarfile, io, fnmatch as _fnmatch
            with tarfile.open(fileobj=io.BytesIO(data), mode="r:gz") as tf:
                all_names = tf.getnames()
                for pattern, dest_rel in src["extract_map"].items():
                    matched = (
                        pattern if pattern in all_names
                        else next(
                            (n for n in all_names if _fnmatch.fnmatch(n, pattern)),
                            None
                        )
                    )
                    if matched is None:
                        log(f"  Warning: no file matching '{pattern}' in tar, skipping")
                        continue
                    f_obj    = tf.extractfile(tf.getmember(matched))
                    tar_data = f_obj.read()
                    dest = os.path.join(client_dir, dest_rel)
                    os.makedirs(os.path.dirname(dest) or client_dir, exist_ok=True)
                    with open(dest, "wb") as f:
                        f.write(tar_data)
                    written.append(dest_rel)
                    log(f"  Installed {dest_rel}")
        else:
            import zipfile
            tmp_path = os.path.join(client_dir, f"_mod_tmp_{mod['id']}.zip")
            try:
                with open(tmp_path, "wb") as f:
                    f.write(data)
                with zipfile.ZipFile(tmp_path) as zf:
                    for zip_path, dest_rel in src["extract_map"].items():
                        try:
                            zip_data = zf.read(zip_path)
                        except KeyError:
                            log(f"  Warning: {zip_path} not found in zip, skipping")
                            continue
                        dest = os.path.join(client_dir, dest_rel)
                        os.makedirs(os.path.dirname(dest) or client_dir, exist_ok=True)
                        with open(dest, "wb") as f:
                            f.write(zip_data)
                        written.append(dest_rel)
                        log(f"  Installed {dest_rel}")
            finally:
                if os.path.exists(tmp_path):
                    os.unlink(tmp_path)

    elif src["kind"] == "direct_tar":
        log(f"  Downloading {src['url'].split('/')[-1]}...")
        req = urllib.request.Request(src["url"], headers={"User-Agent": UA})
        with secure_urlopen(req, timeout=120,
                            allowed_hosts=ALLOWED_DOWNLOAD_HOSTS) as r:
            data = r.read()
        import tarfile, io as _io, fnmatch as _fnmatch
        with tarfile.open(fileobj=_io.BytesIO(data), mode="r:gz") as tf:
            all_names = tf.getnames()
            for pattern, dest_rel in src["extract_map"].items():
                matched = pattern if pattern in all_names else next(
                    (n for n in all_names if _fnmatch.fnmatch(n, pattern)), None)
                if matched is None:
                    log(f"  Warning: no file matching '{pattern}' in tar, skipping")
                    continue
                tar_data = tf.extractfile(tf.getmember(matched)).read()
                dest = os.path.join(client_dir, dest_rel)
                os.makedirs(os.path.dirname(dest) or client_dir, exist_ok=True)
                with open(dest, "wb") as f:
                    f.write(tar_data)
                written.append(dest_rel)
                log(f"  Installed {dest_rel}")
        if src.get("pinned_version"):
            mod["_resolved_version"] = src["pinned_version"]

    elif src["kind"] == "direct_file":
        url = src["url"]
        log(f"  Downloading {url.rsplit('/', 1)[-1]}...")
        req = urllib.request.Request(url, headers={"User-Agent": UA})
        with secure_urlopen(req, timeout=120,
                            allowed_hosts=ALLOWED_DOWNLOAD_HOSTS) as r:
            data = r.read()

        if src.get("extract_map") is None:
            dest_rel = src["dest"]
            dest     = os.path.join(client_dir, dest_rel)
            os.makedirs(os.path.dirname(dest) or client_dir, exist_ok=True)
            with open(dest, "wb") as f:
                f.write(data)
            written.append(dest_rel)
            log(f"  Installed {dest_rel}")
        elif url.endswith(".tar.gz") or url.endswith(".tgz"):
            import tarfile, io, fnmatch as _fnmatch
            with tarfile.open(fileobj=io.BytesIO(data), mode="r:gz") as tf:
                all_names = tf.getnames()
                for pattern, dest_rel in src["extract_map"].items():
                    matched = (
                        pattern if pattern in all_names
                        else next(
                            (n for n in all_names if _fnmatch.fnmatch(n, pattern)),
                            None
                        )
                    )
                    if matched is None:
                        log(f"  Warning: no file matching '{pattern}' in tar, skipping")
                        continue
                    f_obj    = tf.extractfile(tf.getmember(matched))
                    tar_data = f_obj.read()
                    dest = os.path.join(client_dir, dest_rel)
                    os.makedirs(os.path.dirname(dest) or client_dir, exist_ok=True)
                    with open(dest, "wb") as f:
                        f.write(tar_data)
                    written.append(dest_rel)
                    log(f"  Installed {dest_rel}")
        else:
            import zipfile
            tmp_path = os.path.join(client_dir, f"_mod_tmp_{mod['id']}.zip")
            try:
                with open(tmp_path, "wb") as f:
                    f.write(data)
                with zipfile.ZipFile(tmp_path) as zf:
                    for zip_path, dest_rel in src["extract_map"].items():
                        try:
                            zip_data = zf.read(zip_path)
                        except KeyError:
                            log(f"  Warning: {zip_path} not in zip, skipping")
                            continue
                        dest = os.path.join(client_dir, dest_rel)
                        os.makedirs(os.path.dirname(dest) or client_dir, exist_ok=True)
                        with open(dest, "wb") as f:
                            f.write(zip_data)
                        written.append(dest_rel)
                        log(f"  Installed {dest_rel}")
            finally:
                if os.path.exists(tmp_path):
                    os.unlink(tmp_path)

        if src.get("pinned_version"):
            mod["_resolved_version"] = src["pinned_version"]

    for hook in src.get("post_install", []):
        if hook == "write_dxvk_conf":
            _write_dxvk_conf(client_dir)
            written.append("dxvk.conf")

    return written


def uninstall_mod(mod: dict, client_dir: str):
    cfg   = load_config()
    state = cfg.get("mods", {}).get(mod["id"], {})
    files = state.get("installed_files", mod.get("installed_files", []))
    for rel in files:
        full = os.path.join(client_dir, rel)
        if os.path.exists(full):
            os.remove(full)
            log(f"  Removed {rel}")


def _dlls_txt_path(client_dir: str) -> str:
    return os.path.join(client_dir, "dlls.txt")


def add_dll(client_dir: str, name: str):
    path  = _dlls_txt_path(client_dir)
    lines = open(path).read().splitlines() if os.path.exists(path) else []
    if any(l.strip().lower() == name.lower() for l in lines):
        return
    lines = [l for l in lines if l.strip()] + [name]
    with open(path, "w") as f:
        f.write("\n".join(lines) + "\n")


def remove_dll(client_dir: str, name: str):
    path = _dlls_txt_path(client_dir)
    if not os.path.exists(path):
        return
    lines = [l for l in open(path).read().splitlines()
             if l.strip().lower() != name.lower()]
    if not lines:
        os.remove(path)
    else:
        with open(path, "w") as f:
            f.write("\n".join(lines) + "\n")


def mod_installed_files_present(mod: dict, client_dir: str) -> bool:
    cfg   = load_config()
    state = cfg.get("mods", {}).get(mod["id"], {})
    files = state.get("installed_files", [])
    return bool(files) and all(
        os.path.exists(os.path.join(client_dir, f)) for f in files)


def mod_supports_update_check(mod: dict) -> bool:
    return mod["source"]["kind"] not in ("direct_file", "direct_tar")


def mod_update_available(mod: dict, state: dict, live: dict | None) -> bool:
    if not mod_supports_update_check(mod):
        return False
    if not state.get("enabled", False):
        return False
    if state.get("ignore_updates", False):
        return False
    installed_ver = state.get("installed_version")
    if not installed_ver:
        return False
    latest_ver = (live or {}).get("latest_version")
    if not latest_ver:
        return False
    return latest_ver != installed_ver


# ──────────────────────────────────────────────────────────────────────────────
#  Addons definition & engine  (installs via git-archive zips pinned to a
#  commit sha, so no full git client is needed)
# ──────────────────────────────────────────────────────────────────────────────

ADDONS_URL          = f"{SERVER}/api/addons.json"
ADDONS_CATALOG_TTL  = 86400   # 1 day, persisted in the config file
ADDON_SHA_CACHE_TTL = 3600
ADDONS_VERIFY_TTL   = 300     # skip re-verify on tab switches within this

# Curated recommended addons: {folder_name: git_url}. Every entry carries
# its git link explicitly, so a recommended addon always appears — even if
# addons.json renames or drops it. Where the link differs from the catalog,
# it's a deliberate fork preference.
RECOMMENDED_ADDONS = {
    "AtlasLoot":            "https://github.com/Otari98/AtlasLoot",
    "aux-addon":            "https://github.com/OldManAlpha/aux-addon",
    "BetterCharacterStats": "https://github.com/pepopo978/BetterCharacterStats",
    "DoiteAuras":           "https://github.com/deceius/DoiteAuras",
    "FlightTracker":        "https://github.com/Lexxoi/FlightTracker",
    "InstanceJournal":      "https://github.com/Arthur-Helias/InstanceJournal",
    "ItemRack":             "https://github.com/Otari98/ItemRack",
    "LevelRange-Octo":      "https://github.com/Dusk-92/LevelRange-Octo",
    "Magnify":              "https://github.com/paokkerkir/Magnify",
    "ModernMapMarkers":     "https://github.com/tilare/ModernMapMarkers",
    "NampowerSettings":     "https://github.com/Dusk-92/NampowerSettings",
    "PallyPowerTW":         "https://github.com/ShikawaLePaladin/PallyPowerTW",
    "pfQuest":              "https://github.com/The-Kludge-Bureau/pfQuest",
    "pfQuest-turtle":       "https://github.com/KameleonUK/pfQuest-turtle",
    "pfUI":                 "https://github.com/brues-code/pfUI",
    "ShaguDPS":             "https://github.com/shagu/ShaguDPS",
    "SUCC-bag":             "https://github.com/Otari98/SUCC-bag",
    "SuperAPI":             "https://github.com/balakethelock/SuperAPI",
    "SuperCleveRoidMacros": "https://github.com/brues-code/SuperCleveRoidMacros",
    "Tmog":                 "https://github.com/Otari98/Tmog",
    "TrinketMenu":          "https://github.com/jrc13245/TrinketMenu",
    "TurtleCalendar":       "https://github.com/Wayoff333/TurtleCalendar",
    "TurtleMail":           "https://github.com/sica42/TurtleMail",
    "UnitXP_SP3_Addon":     "https://github.com/rebasedkon/UnitXP_SP3_Addon",
    "WhatsTraining_Turtle": "https://github.com/rebasedkon/WhatsTraining_Turtle",
}

# Never shown in the updater, even when present in addons.json.
BLOCKED_ADDONS = {
    "SuperMacro",        # SuperMacro - SuperWoW Support
    "Rested",            # Rested XP (hazlema)
    "LevelRange-Turtle", # LevelRange [Turtle] — LevelRange-Octo replaces it
    "CleveRoidMacros",   # SuperCleveRoidMacros replaces it
    "BlizzPlates",       # Blizzard Plates
    "PallyPower",        # CosminPOP PallyPower — PallyPowerTW replaces it
}


def _same_git_repo(a, b) -> bool:
    """Compare git URLs ignoring a trailing '.git' / slash and case."""
    def norm(u):
        u = (u or "").rstrip("/")
        return (u[:-4] if u.endswith(".git") else u).lower()
    return norm(a) == norm(b)

ADDON_GIT_HOSTS = ("github.com", "gitlab.com", "gitea.com", "codeberg.org")

ADDON_ZIP_HOSTS = {"github.com", "codeload.github.com", "gitlab.com",
                   "gitea.com", "codeberg.org"}


def addons_path(client_dir: str) -> str:
    return os.path.join(client_dir, "Interface", "AddOns")


def is_allowed_git_url(url: str) -> bool:
    try:
        parts = urlsplit(url)
    except ValueError:
        return False
    if parts.scheme != "https":
        return False
    host = (parts.hostname or "").lower()
    return any(host == h or host.endswith("." + h) for h in ADDON_GIT_HOSTS)


def _slim_addon_catalog(catalog: list) -> list:
    """Keep only the catalog fields the updater actually uses, so the
    persisted cache stays small."""
    slim = []
    for a in catalog:
        toc = a.get("toc") or {}
        slim.append({
            "name":        a.get("name"),
            "git":         a.get("git"),
            "branch":      a.get("branch"),
            "ref":         a.get("ref"),
            "description": a.get("description"),
            "toc": {k: toc[k] for k in ("Title", "Notes", "Interface")
                    if k in toc},
        })
    return slim


def fetch_addons_catalog(force=False) -> list:
    """Addon catalog, cached in the config file for a day
    ({"addons_catalog_cache": {"timestamp": epoch, "catalog": […]}})."""
    now = time.time()
    if not force:
        entry = load_config().get("addons_catalog_cache", {})
        if (entry.get("catalog") is not None
                and (now - entry.get("timestamp", 0)) < ADDONS_CATALOG_TTL):
            return entry["catalog"]
    req = urllib.request.Request(ADDONS_URL, headers={"User-Agent": UA})
    with secure_urlopen(req, timeout=10) as r:
        catalog = _slim_addon_catalog(json.load(r))
    update_config(lambda c: c.__setitem__(
        "addons_catalog_cache", {"timestamp": now, "catalog": catalog}))
    return catalog


def read_toc_file(path: str) -> dict:
    """Parse '## Key: Value' metadata lines from a WoW addon .toc file."""
    toc = {}
    try:
        with open(path, "r", encoding="utf-8", errors="replace") as f:
            content = f.read()
    except OSError:
        return toc
    if content.startswith("\ufeff"):   # strip UTF-8 BOM
        content = content[1:]
    for line in content.splitlines():
        if not line.startswith("## "):
            continue
        key, sep, value = line[3:].partition(":")
        if sep:
            toc[key.strip()] = value.strip()
    return toc


def parse_wow_colored(text: str):
    """Split a string containing WoW colour escapes (|cAARRGGBB … |r) into
    [(segment, "#rrggbb" | None), …] for rendering."""
    import re
    segments = []
    color = None
    pos = 0
    for m in re.finditer(r"\|c[0-9a-fA-F]{8}|\|r", text):
        if m.start() > pos:
            segments.append((text[pos:m.start()], color))
        tok = m.group(0)
        color = f"#{tok[4:]}" if tok.startswith("|c") else None
        pos = m.end()
    if pos < len(text):
        segments.append((text[pos:], color))
    return [(t, c) for t, c in segments if t]


def strip_wow_colors(text: str) -> str:
    return "".join(t for t, _c in parse_wow_colored(text))


def _git_parts(git_url: str):
    """→ (kind, repo_url, owner, repo, api_base); kind ∈ github/gitlab/gitea.
    Handles path prefixes like octowow.st/git/<owner>/<repo>."""
    parts = urlsplit(git_url)
    host  = (parts.hostname or "").lower()
    segs  = [s for s in parts.path.split("/") if s]
    if len(segs) < 2:
        raise ValueError(f"Unsupported git URL: {git_url}")
    owner, repo = segs[-2], segs[-1]
    if repo.endswith(".git"):
        repo = repo[:-4]
    prefix   = "/".join(segs[:-2])
    origin   = f"https://{parts.netloc}"
    repo_url = origin + (f"/{prefix}" if prefix else "") + f"/{owner}/{repo}"
    if host == "github.com" or host.endswith(".github.com"):
        return "github", repo_url, owner, repo, GITHUB_API
    if host == "gitlab.com" or host.endswith(".gitlab.com"):
        return "gitlab", repo_url, owner, repo, f"{origin}/api/v4"
    api = origin + (f"/{prefix}" if prefix else "") + "/api/v1"
    return "gitea", repo_url, owner, repo, api


def _api_json(url: str, timeout=10):
    req = urllib.request.Request(url, headers={"User-Agent": UA})
    with secure_urlopen(req, timeout=timeout) as r:
        return json.load(r)


def _describe_net_error(e: Exception) -> str:
    """Human-readable cause for a failed API request."""
    import urllib.error
    if isinstance(e, urllib.error.HTTPError):
        if e.code == 403:
            return "API rate limit exceeded — try again in 1 hour"
        if e.code == 404:
            return "repository or branch not found"
        host = (e.url or "").split("/")[2] if (e.url or "").count("/") >= 2 \
            else "server"
        return f"HTTP {e.code} from {host}"
    if isinstance(e, urllib.error.URLError):
        return f"network error ({e.reason})"
    return str(e)


def describe_install_error(e: Exception) -> str:
    """Map an install/update failure to a message the user can act on."""
    import zipfile
    import urllib.error
    if isinstance(e, (urllib.error.HTTPError, urllib.error.URLError)):
        return _describe_net_error(e)
    if isinstance(e, OSError) and getattr(e, "errno", None) in (2, 13, 22):
        # The archive/file vanished or got locked mid-operation — on Windows
        # that's almost always the antivirus quarantining the download.
        return ("Blocked by antivirus — open Settings (⚙) → "
                "'Add game folder to Defender exclusions', then retry")
    if isinstance(e, zipfile.BadZipFile):
        return ("Downloaded archive is corrupted (possibly blocked by "
                "antivirus) — retry, or use Settings (⚙) → "
                "'Add game folder to Defender exclusions'")
    return str(e)


def addon_remote_sha(git_url: str, branch=None, ref=None,
                     force=False, raise_errors=False) -> str | None:
    """Latest commit sha of a repo's branch (or pinned ref), cached in the
    config file so repeated verifies don't burn API quota. Returns None on
    failure — or raises with a readable cause when raise_errors is set."""
    key = f"{git_url}#{ref or branch or ''}"
    now = time.time()
    if not force:
        entry = load_config().get("addon_sha_cache", {}).get(key)
        if entry and (now - entry.get("timestamp", 0)) < ADDON_SHA_CACHE_TTL:
            return entry.get("sha")

    kind, _repo_url, owner, repo, api = _git_parts(git_url)
    pin = ref or branch          # explicit branch/ref when the caller has one
    sha = None
    try:
        if kind == "github":
            if pin:
                sha = _api_json(
                    f"{api}/repos/{owner}/{repo}/commits/{pin}").get("sha")
            else:
                lst = _api_json(
                    f"{api}/repos/{owner}/{repo}/commits?per_page=1")
                sha = lst[0].get("sha") if lst else None
        elif kind == "gitlab":
            from urllib.parse import quote
            proj = quote(f"{owner}/{repo}", safe="")
            if pin:
                sha = _api_json(
                    f"{api}/projects/{proj}/repository/commits/"
                    f"{quote(pin, safe='')}").get("id")
            else:
                lst = _api_json(
                    f"{api}/projects/{proj}/repository/commits?per_page=1")
                sha = lst[0].get("id") if lst else None
        else:  # gitea / codeberg
            q = f"?sha={pin}&limit=1" if pin else "?limit=1"
            lst = _api_json(f"{api}/repos/{owner}/{repo}/commits{q}")
            sha = lst[0].get("sha") if lst else None
    except Exception as e:
        if raise_errors:
            raise RuntimeError(_describe_net_error(e)) from e
        return None
    if sha:
        update_config(lambda c: c.setdefault("addon_sha_cache", {}).__setitem__(
            key, {"timestamp": now, "sha": sha}))
    return sha


def addon_cached_sha(git_url: str, branch=None, ref=None):
    """Cached remote sha regardless of age — never touches the network."""
    key = f"{git_url}#{ref or branch or ''}"
    entry = load_config().get("addon_sha_cache", {}).get(key)
    return entry.get("sha") if entry else None


def addon_zip_url(git_url: str, sha: str) -> str:
    kind, repo_url, _owner, repo, _api = _git_parts(git_url)
    if kind == "gitlab":
        return f"{repo_url}/-/archive/{sha}/{repo}-{sha}.zip"
    return f"{repo_url}/archive/{sha}.zip"


def _rmtree_force(path):
    """Like shutil.rmtree, but also removes read-only files. Plain rmtree
    raises PermissionError on Windows when it meets a read-only file (e.g. a
    .git object store from a manual clone, or a read-only addon shipped in an
    old zip); this clears the read-only bit and retries."""
    def handler(func, p, _exc):
        os.chmod(p, stat.S_IWRITE)
        func(p)
    if sys.version_info >= (3, 12):
        shutil.rmtree(path, onexc=handler)      # onerror deprecated in 3.12
    else:
        shutil.rmtree(path, onerror=handler)


def install_addon_files(client_dir: str, folder: str, git_url: str, sha: str):
    """Download the repo archive at `sha` and unpack it into
    Interface/AddOns/<folder>, atomically replacing any existing copy."""
    url = addon_zip_url(git_url, sha)
    log(f"  Downloading {folder} @ {sha[:10]}…")
    req = urllib.request.Request(url, headers={"User-Agent": UA})
    with secure_urlopen(req, timeout=120,
                        allowed_hosts=ADDON_ZIP_HOSTS) as r:
        data = r.read()

    import zipfile
    import io
    dest_root = os.path.join(addons_path(client_dir), folder)
    tmp_root  = dest_root + ".tmp_install"
    tmp_abs   = os.path.abspath(tmp_root)
    if os.path.isdir(tmp_root):
        _rmtree_force(tmp_root)
    try:
        with zipfile.ZipFile(io.BytesIO(data)) as zf:
            for info in zf.infolist():
                if info.is_dir():
                    continue
                # Strip the archive's top-level "<repo>-<sha>/" directory and
                # normalise separators (a zip entry may use "/" or "\").
                parts = [p for p in info.filename.replace("\\", "/").split("/")[1:]
                         if p not in ("", ".")]
                if not parts or ".." in parts:
                    continue
                target = os.path.join(tmp_root, *parts)
                # Defence in depth: never write outside the target folder even
                # if the guards above are somehow bypassed.
                if not os.path.abspath(target).startswith(tmp_abs + os.sep):
                    continue
                os.makedirs(os.path.dirname(target), exist_ok=True)
                with zf.open(info) as src, open(target, "wb") as dst:
                    shutil.copyfileobj(src, dst)
        if os.path.isdir(dest_root):
            _rmtree_force(dest_root)
        os.replace(tmp_root, dest_root)
    except BaseException:
        # Never leave a half-written ".tmp_install" behind on failure
        if os.path.isdir(tmp_root):
            try:
                _rmtree_force(tmp_root)
            except Exception:
                pass
        raise
    log(f"  Installed addon {folder}")


# ── pfUI "Default" profile patch ─────────────────────────────────────────────
# pfUI ships a set of built-in design profiles. After every pfUI install/update
# we add a curated "Default" profile and make it the firstrun default. Because
# an update overwrites pfUI's files, the patch is re-applied each time and is
# idempotent (marked blocks are replaced, not duplicated).

# The curated profile (JSON captured from a configured pfUI, profile renamed to
# "Default"). Loaded as a Python dict and emitted as a Lua table at patch time.
PFUI_DEFAULT_PROFILE = json.loads(r'''
{"appearance":{"border":{"default":"-1"},"castbar":{"castbarcolor":"1,0.796,0.251,0.8"},"cd":{"debuffs":"1","font":"Interface\\AddOns\\pfUI\\fonts\\Myriad-Pro.ttf","milliseconds":"0"},"infight":{"health":"0"},"minimap":{"arrowscale":"2"}},"buffs":{"hidelist":"","showoverflow":"1","showspillover":"1"},"castbar":{"focus":{"showicon":"1","showtimer":"0"},"player":{"hide_blizz":"0","hide_pfui":"1","showtimer":"0"},"target":{"showicon":"1","showtimer":"0"}},"character":{"inventory":{"durability":"0"},"reputation":{"repRequired":"0"}},"disabled":{"actionbar":"1","addonbuttons":"0","addoncompat":"0","addons":"0","afkcam":"0","autoshift":"0","autovendor":"0","bags":"1","bgscore":"0","bubbles":"1","buff":"1","buffwatch":"0","castbar":"0","chat":"1","chatcopy":"0","combopoints":"0","cooldown":"0","custom":"0","easteregg":"0","energytick":"0","eqcompare":"0","equipmentmanager":"0","farmmode":"0","feigndeath":"0","firstrun":"0","focus":"0","gm":"0","group":"0","gryphons":"0","hdgraphic":"0","hoverbind":"0","hunterbar":"0","infight":"0","innervatecall":"0","itemclick":"0","itemcount":"1","loot":"1","macrotweak":"0","map":"0","mapcolors":"0","mapreveal":"0","marktracking":"0","minimap":"0","mirrortimers":"0","mouseover":"0","nameplates":"0","nampower":"0","panel":"0","pet":"0","pettarget":"0","pixelperfect":"0","player":"0","questitem":"0","raid":"0","roll":"1","screenshot":"0","sellvalue":"0","share":"0","skin":"0","skin_Auctionhouse":"0","skin_Barbershop":"0","skin_Battlefield":"0","skin_Battlefield Minimap":"0","skin_Battlefield Score":"0","skin_Books":"0","skin_Character":"0","skin_Coin Pickup":"0","skin_Color Picker":"0","skin_Dress Up Frame":"0","skin_Everlook Broadcasting":"0","skin_Flightmaster":"1","skin_Friends":"1","skin_GM Survey":"0","skin_Game Menu":"0","skin_Gossip and Quest":"1","skin_Guild Registrar":"0","skin_Guild Tabard":"0","skin_Help":"0","skin_Inspect":"0","skin_KeyBindings":"0","skin_Macro":"0","skin_Mailbox":"1","skin_Merchant":"1","skin_Opacity":"0","skin_Options - Interface":"0","skin_Options - New":"0","skin_Options - Sound":"0","skin_Options - Video":"0","skin_Pet Stable Master":"0","skin_Petition":"0","skin_Popup Dialogs":"0","skin_Profession":"1","skin_Quest Log":"1","skin_Quest Timer":"0","skin_RaidUI":"0","skin_Readycheck":"0","skin_Spellbook":"1","skin_Stack Split":"0","skin_Talents":"1","skin_Tooltips":"0","skin_Trade":"1","skin_Trainer":"1","skin_Transmog":"0","skin_Turtle LFT":"0","skin_Turtle Shop":"0","skin_TurtleCalendar":"0","skin_TurtleMail":"0","skin_Tutorial":"0","socialmod":"0","superwow":"0","swingtimer":"0","target":"0","targettarget":"0","targettargettarget":"0","thirdparty":"0","thirdparty-vanilla":"0","tooltip":"0","totems":"0","tracking":"0","turtle-wow":"0","uf_tukui":"0","unitxp":"0","unlock":"0","unusable":"0","updatenotify":"0","whisperproxy":"0","xpbar":"1"},"global":{"autosell":"1","font_blizzard":"1","font_unit":"Interface\\AddOns\\pfUI\\fonts\\Myriad-Pro.ttf","font_unit_name":"Interface\\AddOns\\pfUI\\fonts\\Continuum.ttf","profile":"Default"},"gui":{"showdisabled":"0"},"nameplates":{"barcombatstate":"0","ccombatnothreat":"0","ccombatofftank":"0","ccombatstun":"0","ccombatthreat":"0","debuffanim":"1","debuffs":{"blacklist":"#Mana Attuned#Mercenary","filter":"blacklist","showstacks":"1"},"debuffsize":"20","guessdebuffs":"1","outcombatstate":"0","overlap":"1","spellname":"1"},"panel":{"left":{"center":"none","left":"none","right":"none"},"other":{"minimap":"time"},"right":{"center":"none","left":"none","right":"none"},"seconds":"0"},"position":{"TicketStatusFrame":{"anchor":"CENTER","parent":"UIParent","xpos":1100,"ypos":300},"WorldMapFrame":{"alpha":1,"anchor":"TOPLEFT","scale":0.69999998807907104,"xpos":1434,"ypos":-150},"pfFocus":{"anchor":"CENTER","parent":"UIParent","xpos":-200,"ypos":220},"pfFocusCastbar":{"anchor":"CENTER","parent":"UIParent","xpos":-200,"ypos":162},"pfGroup1":{"anchor":"TOP","parent":"UIParent","scale":1,"xpos":-468,"ypos":-135},"pfGroup2":{"anchor":"TOP","parent":"UIParent","xpos":-468,"ypos":-210},"pfGroup3":{"anchor":"TOP","parent":"UIParent","xpos":-468,"ypos":-285},"pfGroup4":{"anchor":"TOP","parent":"UIParent","xpos":-468,"ypos":-360},"pfMarkTracking":{"anchor":"CENTER","parent":"UIParent","xpos":270,"ypos":270},"pfPartyPet1":{"scale":0.90000000000000002},"pfPartyPet2":{"scale":0.90000000000000002},"pfPartyPet3":{"scale":0.90000000000000002},"pfPartyPet4":{"scale":0.90000000000000002},"pfPet":{"anchor":"CENTER","parent":"UIParent","scale":1,"xpos":-490,"ypos":338},"pfPlayer":{"anchor":"CENTER","parent":"UIParent","xpos":-445,"ypos":380},"pfRaidCluster":{"anchor":"CENTER","parent":"UIParent","xpos":-1420,"ypos":-120},"pfSwingTimerMainhand":{"anchor":"CENTER","parent":"UIParent","xpos":0,"ypos":-252},"pfSwingTimerRanged":{"anchor":"CENTER","parent":"UIParent","xpos":0,"ypos":-228},"pfTarget":{"anchor":"CENTER","parent":"UIParent","xpos":-215,"ypos":380},"pfTargetCastbar":{"anchor":"CENTER","parent":"UIParent","xpos":-215,"ypos":290},"pfTargetTarget":{"anchor":"CENTER","parent":"UIParent","scale":0.90000000000000002,"xpos":-116,"ypos":385},"pfTargetTargetTarget":{"anchor":"CENTER","parent":"UIParent","scale":0.90000000000000002,"xpos":-8,"ypos":385},"pfTooltipAnchor":{"anchor":"CENTER","parent":"UIParent","xpos":720,"ypos":-386},"pfTotems":{"anchor":"CENTER","parent":"UIParent","xpos":-482,"ypos":334}},"thirdparty":{"statcompare":{"enable":"1"},"wim":{"enable":"0"}},"tooltip":{"position":"free","vendor":{"showalways":"0"}},"unitframes":{"abbrevnum":"0","always2dportrait":"1","animation_speed":"1","castbardecimals":"1","custombgcolor":"0.502,0.2,0.2,1","customcolor":"0.055,0.749,0,1","druidmanaheight":"2","druidmanatext":"0","fallback":{"debuff_ind_range":"0"},"focus":{"buffs":"BOTTOMLEFT","buffsize":"18","cooldown_anim":"1","debuff_ind_range":"0","debuffs":"BOTTOMLEFT","debuffsize":"20","hitindicatorfont":"Interface\\AddOns\\pfUI\\fonts\\Myriad-Pro.ttf","hitindicatorsize":"16","portrait":"right","powercolor":"0","txthpright":"health"},"focustarget":{"debuff_ind_range":"0"},"group":{"buffs":"off","debuff_ind_range":"0","height":"22","txthpright":"none","width":"144"},"grouppet":{"debuff_ind_range":"0"},"grouptarget":{"debuff_ind_range":"0","visible":"0"},"nampower_buffs":"1","pet":{"debuff_ind_range":"0"},"player":{"buffs":"off","debuff_ind_range":"0","debuffs":"off","display_spellpower":"0","height":"26","hitindicator":"1","hitindicatorfont":"Interface\\AddOns\\pfUI\\fonts\\Myriad-Pro.ttf","hitindicatorsize":"16","portrait":"left","powercolor":"0","txthpright":"health","txtpowerright":"power","width":"150"},"ptarget":{"debuff_ind_range":"0"},"raid":{"debuff_ind_range":"0"},"rangecheck_mode":"unitxp","rangechecki":"4","spellqueue":"0","swingtimerattackspeed":"1","swingtimerfontsize":"14","swingtimerlabel":"0","swingtimermhcolor":"0.31,0.596,1,1","swingtimerrangedcolor":"0.686,0.447,1,1","swingtimerwidth":"192","target":{"buffperrow":"7","buffs":"BOTTOMLEFT","buffsize":"18","cooldown_anim":"1","debuff_ind_range":"0","debuffperrow":"6","debuffs":"BOTTOMLEFT","debuffsize":"22","height":"26","hitindicator":"1","hitindicatorfont":"Interface\\AddOns\\pfUI\\fonts\\Myriad-Pro.ttf","hitindicatorsize":"16","portrait":"right","powercolor":"0","showPVP":"1","txthpright":"health","txtpowerright":"power","width":"150"},"track_group":"1","ttarget":{"debuff_ind_range":"0","portrait":"off","powercolor":"0"},"tttarget":{"debuff_ind_range":"0","portrait":"off"}},"version":"999.999.999"}
''')


def _lua_value(v, indent: int = 0) -> str:
    """Serialize a JSON-derived value to a pfUI-style Lua literal."""
    if isinstance(v, dict):
        pad, cpad = " " * (indent + 2), " " * indent
        items = "".join(f'{pad}["{k}"] = {_lua_value(val, indent + 2)},\n'
                        for k, val in v.items())
        return "{\n" + items + cpad + "}"
    if isinstance(v, bool):
        return "true" if v else "false"
    if isinstance(v, (int, float)):
        return repr(v)
    s = str(v).replace("\\", "\\\\").replace('"', '\\"')
    return f'"{s}"'


_PFUI_MARK_BEGIN = "-- OCTO_UPDATER_DEFAULT_PROFILE_BEGIN"
_PFUI_MARK_END   = "-- OCTO_UPDATER_DEFAULT_PROFILE_END"
_PFUI_CHAT_BEGIN = "-- OCTO_UPDATER_CHAT_SKIP_BEGIN"
_PFUI_CHAT_END   = "-- OCTO_UPDATER_CHAT_SKIP_END"

# Strips any Octo Updater injected block, regardless of which marker pair.
_PFUI_STRIP_RE = r"[ \t]*-- OCTO_UPDATER_[A-Z_]+?_BEGIN.*?-- OCTO_UPDATER_[A-Z_]+?_END\n?"


def patch_pfui_default_profile(client_dir: str):
    """Add the curated 'Default' profile to a freshly installed/updated pfUI
    and make it the firstrun default. Idempotent; degrades gracefully if
    pfUI's file layout has changed."""
    import re

    base = os.path.join(addons_path(client_dir), "pfUI")
    profiles_lua = os.path.join(base, "env", "profiles.lua")
    firstrun_lua = os.path.join(base, "modules", "firstrun.lua")
    if not os.path.exists(profiles_lua):
        return

    # 1) profiles.lua — append (or replace) a marked block defining Default.
    block = (f"{_PFUI_MARK_BEGIN}\n"
             f"local octo_default = {_lua_value(PFUI_DEFAULT_PROFILE)}\n"
             f'pfUI_profiles["Default"] = octo_default\n'
             f"{_PFUI_MARK_END}\n")
    try:
        with open(profiles_lua, encoding="utf-8", errors="replace") as f:
            txt = f.read()
        txt = re.sub(re.escape(_PFUI_MARK_BEGIN) + r".*?"
                     + re.escape(_PFUI_MARK_END) + r"\n?", "", txt, flags=re.S)
        with open(profiles_lua, "w", encoding="utf-8") as f:
            f.write(txt.rstrip() + "\n\n" + block)
        log("  pfUI: 'Default' profile installed.")
    except OSError as e:
        log(f"  pfUI: could not patch profiles.lua ({e})")
        return

    # 2) pfUI.lua — use 'Default' (not 'Modern') as the fresh-install config,
    #    so the very first login already lands in the Default profile.
    pfui_lua = os.path.join(base, "pfUI.lua")
    if os.path.exists(pfui_lua):
        try:
            with open(pfui_lua, encoding="utf-8", errors="replace") as f:
                pf = f.read()
            old = 'CopyTable(pfUI_profiles["Modern"]) or {}'
            if old in pf:
                pf = pf.replace(
                    old, 'CopyTable(pfUI_profiles["Default"]) or {}', 1)
                with open(pfui_lua, "w", encoding="utf-8") as f:
                    f.write(pf)
                log("  pfUI: 'Default' set as the fresh-install profile.")
        except OSError as e:
            log(f"  pfUI: could not patch pfUI.lua ({e})")

    # 3) firstrun.lua — add a 'Default' button, make it the fallback profile,
    #    and skip the chat wizard steps whenever the chat module is disabled.
    if not os.path.exists(firstrun_lua):
        return
    try:
        with open(firstrun_lua, encoding="utf-8", errors="replace") as f:
            fr = f.read()

        # Remove any previous injections (idempotent re-apply after updates).
        fr = re.sub(_PFUI_STRIP_RE, "", fr, flags=re.S)

        # When the chat module is disabled (e.g. the "Default" profile), the
        # chat firstrun steps can't apply anything, so pre-mark them done to
        # keep them from showing. Injected right after the step table is made.
        chat_skip = (
            f"  {_PFUI_CHAT_BEGIN}\n"
            "  if pfUI_config and pfUI_config.disabled"
            ' and pfUI_config.disabled.chat == "1" then\n'
            "    pfUI_init = pfUI_init or {}\n"
            '    pfUI_init["chat_right"] = true\n'
            '    pfUI_init["chat_position"] = true\n'
            '    pfUI_init["chat_channels"] = true\n'
            "  end\n"
            f"  {_PFUI_CHAT_END}\n")
        chat_anchor = "  pfUI.firstrun.steps = {}\n"
        if chat_anchor in fr:
            fr = fr.replace(chat_anchor, chat_anchor + chat_skip, 1)

        # Insert a Default button just before the built-in "Modern" button.
        button = (
            f"    {_PFUI_MARK_BEGIN}\n"
            '    f.Default = CreateFrame("Button", nil, f, "UIPanelButtonTemplate")\n'
            "    f.Default:SetWidth(250)\n"
            "    f.Default:SetHeight(20)\n"
            '    f.Default:SetPoint("BOTTOM", 0, 120)\n'
            "    f.Default:SetTextColor(1,1,1)\n"
            '    f.Default:SetText("Default (recommended)")\n'
            "    f.Default:SetScript(\"OnClick\", function()\n"
            '      _G["pfUI_config"] = CopyTable(pfUI_profiles["Default"])\n'
            '      pfUI_init.selected_profile = "Default"\n'
            "      pfUI:LoadConfig()\n"
            "      ReloadUI()\n"
            "    end)\n"
            "    SkinButton(f.Default)\n"
            f"    {_PFUI_MARK_END}\n\n")
        anchor = '    f.Modern = CreateFrame("Button"'
        if anchor in fr:
            fr = fr.replace(anchor, button + anchor, 1)

        # Make Default the profile used when the user doesn't pick one.
        fr = fr.replace('pfUI_init.selected_profile or "Modern"',
                        'pfUI_init.selected_profile or "Default"')

        with open(firstrun_lua, "w", encoding="utf-8") as f:
            f.write(fr)
        log("  pfUI: 'Default' added to the firstrun profile picker.")
    except OSError as e:
        log(f"  pfUI: could not patch firstrun.lua ({e})")


# ──────────────────────────────────────────────────────────────────────────────
#  Tweaks definition
# ──────────────────────────────────────────────────────────────────────────────

TWEAKS_DEFAULTS = {
    "locale":          DEFAULT_LOCALE,
    "alwaysAutoLoot":  True,
    "nameplateRange":  41,
    "fieldOfView":     110,
    "farClip":         777,
    "frillDistance":   120,
    "cameraDistance":  50,
    "soundInBackground": True,
}

TWEAKS_ITEMS = [
    (None, "GENERAL", "section", False, None, None, None, None, None),

    ("locale",            "Game Language",    "dropdown", False, None,
     None,
     None, None, None),

    ("alwaysAutoLoot",    "Auto Loot",        "checkbox", True,  None,
     "Reverses the auto-loot behavior to always auto-loot.",
     None, None, None),

    ("nameplateRange",    "Nameplate Range",          "number",   False, None,
     "Distance at which nameplates are visible. [0 - 41]",
     0, 41, 1),

    (None, "CAMERA", "section", False, None, None, None, None, None),

    ("fieldOfView",       "Field of View",            "number",   False, None,
     "Recommended values by aspect ratio: [4:3 = 90] [16:9 = 110] [21:9 = 150] [32:9 = 180]",
     90, 180, 5),

    ("cameraDistance",    "Camera Distance",          "number",   False, None,
         "Maximum camera zoom-out distance. [50 - 100]",
         50, 100, 1),

    (None, "GRAPHICS", "section", False, None, None, None, None, None),

    ("farClip",           "World Distance",          "number",   False, None,
     "Terrain and world objects rendering distance. [100 - 10,000]",
     100, 10000, 1),

    ("frillDistance",     "Ground Clutter Distance",  "number",   False, None,
     "Grass and small rocks rendering distance. [0 - 300]",
     0, 300, 1),

    (None, "SOUND", "section", False, None, None, None, None, None),

    ("soundInBackground", "Sound in Background",        "checkbox", True,  None,
     "Allows game sounds to play in the background.",
     None, None, None),
]


# {tweak_id: (min, max)} for every numeric tweak — the single source of
# truth for clamping, wherever the value is read from the UI.
TWEAKS_LIMITS = {t[0]: (t[6], t[7]) for t in TWEAKS_ITEMS
                 if t[0] is not None and t[2] == "number"}


_FOV_REFS = [
    (4  / 3,   90),
    (16 / 9,  110),
    (21 / 9,  150),
    (32 / 9,  180),
]


def fov_default_for_display() -> int:
    try:
        info  = _get_display_info_safe()
        ratio = info["width"] / info["height"] if info["height"] else 16 / 9
    except Exception:
        ratio = 16 / 9

    if ratio <= _FOV_REFS[0][0]:
        return _FOV_REFS[0][1]
    if ratio >= _FOV_REFS[-1][0]:
        return _FOV_REFS[-1][1]
    for i in range(len(_FOV_REFS) - 1):
        r0, f0 = _FOV_REFS[i]
        r1, f1 = _FOV_REFS[i + 1]
        if r0 <= ratio <= r1:
            t   = (ratio - r0) / (r1 - r0)
            raw = f0 + t * (f1 - f0)
            return round(round(raw / 5) * 5)
    return 110


def _get_display_info_safe() -> dict:
    import ctypes
    ENUM_CURRENT_SETTINGS = -1

    class DEVMODE(ctypes.Structure):
        _fields_ = [
            ("dmDeviceName",         ctypes.c_wchar * 32),
            ("dmSpecVersion",        ctypes.c_ushort),
            ("dmDriverVersion",      ctypes.c_ushort),
            ("dmSize",               ctypes.c_ushort),
            ("dmDriverExtra",        ctypes.c_ushort),
            ("dmFields",             ctypes.c_ulong),
            ("dmPositionX",          ctypes.c_long),
            ("dmPositionY",          ctypes.c_long),
            ("dmDisplayOrientation", ctypes.c_ulong),
            ("dmDisplayFixedOutput", ctypes.c_ulong),
            ("dmColor",              ctypes.c_short),
            ("dmDuplex",             ctypes.c_short),
            ("dmYResolution",        ctypes.c_short),
            ("dmTTOption",           ctypes.c_short),
            ("dmCollate",            ctypes.c_short),
            ("dmFormName",           ctypes.c_wchar * 32),
            ("dmLogPixels",          ctypes.c_ushort),
            ("dmBitsPerPel",         ctypes.c_ulong),
            ("dmPelsWidth",          ctypes.c_ulong),
            ("dmPelsHeight",         ctypes.c_ulong),
            ("dmDisplayFlags",       ctypes.c_ulong),
            ("dmDisplayFrequency",   ctypes.c_ulong),
        ]

    dm = DEVMODE()
    dm.dmSize = ctypes.sizeof(DEVMODE)
    ctypes.windll.user32.EnumDisplaySettingsW(
        None, ENUM_CURRENT_SETTINGS, ctypes.byref(dm))
    return {"width": dm.dmPelsWidth, "height": dm.dmPelsHeight,
            "refresh_rate": dm.dmDisplayFrequency}


def load_tweaks_config() -> dict:
    cfg     = load_config()
    stored  = cfg.get("tweaks", {})
    defaults = dict(TWEAKS_DEFAULTS)
    defaults["fieldOfView"] = fov_default_for_display()
    return {k: stored.get(k, v) for k, v in defaults.items()}


def save_tweaks_config(values: dict):
    update_config(lambda c: c.__setitem__("tweaks", values))

# ──────────────────────────────────────────────────────────────────────────────
#  News feed
# ──────────────────────────────────────────────────────────────────────────────


def _strip_html(raw: str) -> str:
    """Reduce forum HTML to readable plain text for a Tk widget."""
    import re
    import html as html_mod
    txt = re.sub(r"(?is)<(script|style)[^>]*>.*?</\1>", "", raw)
    txt = re.sub(r"(?i)<br\s*/?>", "\n", txt)
    txt = re.sub(r"(?i)<li[^>]*>", "\n• ", txt)
    txt = re.sub(r"(?i)</(p|div|li|ul|ol|h[1-6]|tr|blockquote)>", "\n", txt)
    txt = re.sub(r"<[^>]+>", "", txt)
    txt = html_mod.unescape(txt)
    txt = re.sub(r"[ \t]+", " ", txt)
    txt = re.sub(r" ?\n ?", "\n", txt)
    txt = re.sub(r"\n{3,}", "\n\n", txt)
    return txt.strip()


def _format_news_date(iso: str) -> str:
    from datetime import datetime
    try:
        return datetime.fromisoformat(iso).strftime("%d %b %Y")
    except Exception:
        return iso


def fetch_patch_notes() -> list:
    """Patch-notes list → [{id, title, date, body, url?, author?}, …]"""
    req = urllib.request.Request(PATCHNOTES_URL, headers={"User-Agent": UA})
    with secure_urlopen(req, timeout=NEWS_TIMEOUT) as r:
        data = json.load(r)
    items = data.get("items", [])
    # The feed lists topics in forum order — show newest first (ISO dates
    # with a fixed offset sort correctly as strings).
    items.sort(key=lambda it: it.get("date", ""), reverse=True)
    return items


def fetch_featured_post() -> dict | None:
    """Latest announcements-forum post → {id, title, author?, date, url, html}"""
    req = urllib.request.Request(NEWS_FEATURED_URL, headers={"User-Agent": UA})
    with secure_urlopen(req, timeout=NEWS_TIMEOUT) as r:
        data = json.load(r)
    return data if isinstance(data, dict) and data.get("id") else None

# ──────────────────────────────────────────────────────────────────────────────
#  GUI
# ──────────────────────────────────────────────────────────────────────────────


class SlimScrollbar(tk.Canvas):
    """Flat minimal scrollbar (the native tk.Scrollbar can't be themed on
    Windows). Speaks the standard set()/command scrollbar protocol."""

    def __init__(self, parent, command=None, width=10,
                 bg=C_PANEL, thumb="#3a2f55", thumb_hover=C_GOLD, **kw):
        super().__init__(parent, width=width, bg=bg,
                         highlightthickness=0, bd=0, **kw)
        self.command      = command
        self._thumb       = thumb
        self._thumb_hover = thumb_hover
        self._first       = 0.0
        self._last        = 1.0
        self._drag_off    = None
        self._hover       = False
        self.bind("<Configure>", lambda e: self._redraw())
        self.bind("<Button-1>",  self._click)
        self.bind("<B1-Motion>", self._drag)
        self.bind("<Enter>",     lambda e: self._set_hover(True))
        self.bind("<Leave>",     lambda e: self._set_hover(False))

    def set(self, first, last):
        self._first, self._last = float(first), float(last)
        self._redraw()

    def _set_hover(self, on):
        self._hover = on
        self._redraw()

    def _redraw(self):
        self.delete("all")
        if self._last - self._first >= 1.0:
            return
        h  = self.winfo_height()
        w  = self.winfo_width()
        y0 = int(self._first * h)
        y1 = max(int(self._last * h), y0 + 24)
        self.create_rectangle(
            2, y0, w - 2, y1,
            fill=self._thumb_hover if self._hover else self._thumb,
            outline="")

    def _click(self, e):
        h  = self.winfo_height() or 1
        y0 = self._first * h
        y1 = self._last * h
        self._drag_off = (e.y - y0) if y0 <= e.y <= y1 else (y1 - y0) / 2
        self._drag(e)

    def _drag(self, e):
        h     = self.winfo_height() or 1
        span  = self._last - self._first
        first = max(0.0, min((e.y - (self._drag_off or 0)) / h, 1.0 - span))
        if self.command:
            self.command("moveto", first)

class OctoUpdaterApp(tk.Tk):
    def __init__(self):
        super().__init__()

        # ── DPI scaling ────────────────────────────────────────────────────
        # With awareness declared (see _enable_dpi_awareness) Windows reports
        # the real DPI. Derive one scale factor from it and drive everything
        # off it: fonts via Tk's own point→pixel scaling, and every hard-coded
        # pixel value via self._px(). At 100% the factor is 1.0 and _px() is an
        # exact identity, so nothing changes; only high-DPI diverges.
        self._sc = max(1.0, self.winfo_fpixels("1i") / 96.0)
        # tk scaling is pixels-per-point; DPI/72 == _sc * 96/72. Setting it
        # explicitly keeps point-fonts growing by exactly _sc regardless of
        # what Tk defaulted to.
        self.tk.call("tk", "scaling", self._sc * 96.0 / 72.0)
        # Bake the factor into the shared design constants once, up front, so
        # the ~40 WIN_W/WIN_H/FOOT_H references downstream need no changes.
        global WIN_W, WIN_H, FOOT_H
        WIN_W  = self._px(WIN_W)
        WIN_H  = self._px(WIN_H)
        FOOT_H = self._px(FOOT_H)

        # Keep the window hidden until it's positioned and fully built, so it
        # never flashes at the default top-left corner before centering.
        self.withdraw()

        # Move a pre-1.3 config/cache from beside the .exe into the per-user
        # data dir before anything reads them, so first-run detection and
        # load_config() below see the relocated files (see _relocate_legacy_data).
        _relocate_legacy_data()

        # Detect first run before anything writes the config.
        self._first_run  = not os.path.exists(CONFIG_FILE)
        # Set when the user adds a Defender exclusion via Settings; checked at
        # the next reconcile to skip the auto-prompt (so a manual add isn't
        # double-prompted), then reset — so each folder change offers one unless
        # the user just added it themselves.
        self._av_excluded = False
        self._cfg        = load_config()
        # Pending reconcile mode (None = none): _offer_reconcile surfaces the
        # Update button and the Update the user clicks runs an integrity pass
        # instead of a routine size-based sync. "full" also writes a fresh
        # Config.wtf (folder change / first run); "keep-config" leaves Config.wtf.
        self._pending_reconcile = self._cfg.get("pending_reconcile") or None
        self._running    = False
        # True only after a verify/update confirmed the client files are up
        # to date. PLAY is gated on this AND on no mod being in an error state.
        self._client_ready = False
        self._worker: UpdateWorker | None = None
        self._log_q:  queue.Queue = queue.Queue()
        self._prog_q: queue.Queue = queue.Queue()
        # Session log lives in memory; the "Show logs" window renders it.
        self._log_buffer: list = []
        self._logwin = None
        self._logwin_text = None
        self._settings_overlay = None
        # Guards against triggering the default-mods / recommended-addons
        # auto-install more than once per app session (e.g. verify firing
        # twice in quick succession).
        self._default_mods_install_started = False
        self._default_addons_install_started = False

        # Game folder path — shared by the Settings modal. A change takes
        # effect only once Settings is closed (see _close_settings), so no
        # live trace fires mid-edit.
        self._game_path = tk.StringVar(
            value=os.path.normpath(self._cfg.get("out_dir", DEFAULT_GAME_DIR)))

        # Count of mods with an update available — shown as a badge on the
        # MODS nav tab.
        self._mod_updates_count = 0

        # Addons state
        self._addons_status = {"state": "idle", "addons": {}, "available": []}
        self._addons_busy = False
        # True only while addons are actually downloading/installing (not
        # during a verify) — gates the PLAY button, like mods installs do.
        self._addons_installing = False
        self._addons_verified_ts = 0.0
        self._addon_updates_count = 0
        self._mpq_updates_count = 0
        self._mpq_busy = None
        # {folder: {"error": msg, "git": url}} for failed installs/updates —
        # survives the post-operation rescan so rows can show what went wrong.
        self._addon_errors = {}
        self._addon_sections_open = {"INSTALLED": True, "AVAILABLE": True}

        # News feed cache (featured post and announcements cached separately)
        self._feat_ts    = 0.0
        self._patch_ts    = 0.0
        self._patch_items = None
        self._featured   = None

        # Scrollable list canvases that respond to the mouse wheel whenever
        # the pointer is anywhere over them (not just over the scrollbar).
        self._wheel_canvases: list = []
        self.bind_all("<MouseWheel>", self._on_mousewheel)

        self.title("Octo Updater")
        self.resizable(False, False)
        self.configure(bg=C_BG)

        # Center on screen up front. WIN_W/WIN_H are fixed, so we can position
        # the window in a single geometry call (no need to map-then-measure).
        sw = self.winfo_screenwidth()
        sh = self.winfo_screenheight()
        x  = (sw - WIN_W) // 2
        y  = (sh - WIN_H) // 2
        self.geometry(f"{WIN_W}x{WIN_H}+{x}+{y}")

        self._build()

        out_dir = self._cfg.get("out_dir", DEFAULT_GAME_DIR)
        if not os.path.exists(out_dir):
            def _wipe(c):
                c.pop("mods", None)
                c.pop("addons", None)
            self._cfg = update_config(_wipe)

        live_ver = get_client_version(out_dir)
        if live_ver:
            self._client_ver_var.set(live_ver)
        self.protocol("WM_DELETE_WINDOW", self._on_close)
        self._poll()
        # Run any one-time migrations for a freshly-installed updater version
        # (and stamp octo_updater_version) before verifying. It runs
        # synchronously, so a v1.3 re-patch is settled before verify reads
        # WoW.exe, and the normal verify below still runs — an upgrading user
        # never misses a pending client update.
        self._new_version_installed()
        # On first run, defer verification until Settings is closed (see
        # _close_settings). If a reconcile was offered on a previous run but
        # never applied, restore the Update button instead of a routine verify.
        # Otherwise run the routine launch verify.
        if self._first_run:
            pass
        elif self._pending_reconcile:
            self.after(300, self._offer_reconcile)
        else:
            self.after(300, self._start_verify)
        self.after(600, self._load_news)
        # Check mod updates at launch too — but only once mods have actually
        # been used (mod_release_cache exists). On a first run or right after a
        # game-folder change nothing is installed yet, so there's nothing to
        # check; the MODS tab will do it when opened.
        if self._cfg.get("mod_release_cache"):
            self.after(900, lambda: threading.Thread(
                target=self._load_mods_state, daemon=True).start())
        # Same parity for addons: background verify at launch (feeds the
        # ADDONS tab badge), but only once addons were initialized for this
        # folder — never on a first run / fresh folder.
        if self._cfg.get("addons") is not None:
            self.after(1500, self._addons_verify)
        # MPQ patches: check installed known patches for updates at launch so
        # the tab badge shows without opening the tab (no-op if none installed).
        if not self._first_run and self._game_path.get().strip():
            self.after(1700, self._mpq_check)
        # Daily self-update check (cached), last so it never delays the rest.
        self.after(2000, lambda: threading.Thread(
            target=self._check_updater_update, daemon=True).start())
        # First launch: open Settings so the user sets the game folder etc.
        if self._first_run:
            self.after(500, self._open_settings)

        # Everything is positioned and built — reveal the centered window.
        self.deiconify()

    def _px(self, *vals):
        """Scale design pixels (authored at 96 DPI) to the current DPI. Returns
        an int for one arg, a tuple for several — handy for canvas coordinate
        lists. Exact identity when the scale factor is 1.0 (100% scaling)."""
        if len(vals) == 1:
            return round(vals[0] * self._sc)
        return tuple(round(v * self._sc) for v in vals)

    # ── build ─────────────────────────────────────────────────────────────────

    def _on_close(self):
        """Hide the window first so the close feels instant
        Config/caches are already saved at write time,
        and the worker threads are daemons, so nothing blocks the exit."""
        try:
            self.withdraw()
        except Exception:
            pass
        # A download's aria2c child isn't a daemon thread — kill it explicitly
        # so it can't keep syncing headless after the window is gone.
        stop_aria2c()
        self.quit()

    def _add_tooltip(self, widget, text: str):
        """Attach a small hover tooltip to a widget."""
        state = {"win": None}

        def show(_e=None):
            if state["win"] is not None:
                return
            x = widget.winfo_rootx() + self._px(12)
            y = widget.winfo_rooty() + widget.winfo_height() + self._px(4)
            tw = tk.Toplevel(self)
            tw.wm_overrideredirect(True)
            tw.wm_geometry(f"+{x}+{y}")
            tk.Label(tw, text=text, font=("Segoe UI", 9),
                     fg=C_TEXT, bg="#0f0b16",
                     highlightthickness=1, highlightbackground=C_PANEL_BDR,
                     padx=self._px(6), pady=self._px(2)).pack()
            state["win"] = tw

        def hide(_e=None):
            if state["win"] is not None:
                state["win"].destroy()
                state["win"] = None

        widget.bind("<Enter>", show, add="+")
        widget.bind("<Leave>", hide, add="+")

    def _on_mousewheel(self, event):
        # Panels are stacked, so several list canvases share the same screen
        # region — only the one inside the active tab's panel should scroll.
        active = getattr(self, "_active_panel", None)
        active_prefix = (str(active) + ".") if active is not None else None
        for cv in list(self._wheel_canvases):
            try:
                if not cv.winfo_ismapped():
                    continue
                if active_prefix and not str(cv).startswith(active_prefix):
                    continue
                wx, wy = cv.winfo_rootx(), cv.winfo_rooty()
                if (wx <= event.x_root <= wx + cv.winfo_width()
                        and wy <= event.y_root <= wy + cv.winfo_height()):
                    # When the content fits entirely in view, Tk would still
                    # happily shift it around — ignore the wheel instead.
                    first, last = cv.yview()
                    if last - first < 1.0:
                        cv.yview_scroll(int(-event.delta / 120), "units")
                    return
            except tk.TclError:
                self._wheel_canvases.remove(cv)

    def _draw_nav_tab(self, tab: str, hover: bool = False):
        """Render a nav tab on the header canvas; the active tab's text gets
        a soft glow (dim gold halo layers behind the bright text)."""
        cv = self._hdr_canvas
        tag = f"nav_{tab}"
        cv.delete(tag)
        cx, cy = self._nav_pos[tab], self._px(54)
        font = ("Segoe UI", 11, "bold")
        if tab == self._active_tab:
            for r, col in ((self._px(2), "#42340f"), (self._px(1), "#7a5c1d")):
                for dx, dy in ((-r, 0), (r, 0), (0, -r), (0, r),
                               (-r, -r), (r, -r), (-r, r), (r, r)):
                    cv.create_text(cx + dx, cy + dy, text=tab,
                                   font=font, fill=col, tags=tag)
            cv.create_text(cx, cy, text=tab, font=font, fill=C_GOLD_LT,
                           tags=tag)
        else:
            cv.create_text(cx, cy, text=tab, font=font,
                           fill=C_GOLD_LT if hover else C_TEXT, tags=tag)

        # Update-counter badges
        count = 0
        if tab == "MODS":
            count = self._mod_updates_count
        elif tab == "ADDONS":
            count = self._addon_updates_count
        elif tab == "MPQ":
            count = self._mpq_updates_count
        if count:
            bx = cx + self._nav_text_w[tab] // 2 + self._px(11)
            by = cy - self._px(11)
            # Canvas oval, not a ● glyph: the oval gives exact geometric
            # control so the number always centers, consistently across OSes.
            # (A filled-circle glyph antialiases nicely but its disk isn't
            # centered in the glyph box — by a font-specific amount — so the
            # number drifts off-centre and can't be corrected reliably.)
            r8 = self._px(8)
            cv.create_oval(bx - r8, by - r8, bx + r8, by + r8,
                           fill=C_GOLD, outline="", tags=tag)
            cv.create_text(bx, by, text=str(count),
                           font=("Segoe UI", 8, "bold"),
                           fill="#1a1408", tags=tag)

    def _switch_tab(self, tab: str):
        if tab == self._active_tab:
            return
        prev = self._active_tab
        self._active_tab = tab
        self._draw_nav_tab(prev)
        self._draw_nav_tab(tab)

        PANEL_TOP = self._px(119)
        PANEL_H   = WIN_H - PANEL_TOP - FOOT_H - self._px(10)

        # Panels stay mapped and stacked; switching tabs only raises the
        # active one. place_forget()/place() would unmap and remap the whole
        # widget tree of a populated panel (hundreds of widgets) every
        # switch — a visible synchronous stall.
        panels = {"NEWS":   self._news_panel,
                  "TWEAKS": self._tweaks_panel_frame,
                  "ADDONS": self._addons_panel_frame,
                  "MODS":   self._mods_panel_frame,
                  "MPQ":    self._mpq_panel_frame}
        target = panels.get(tab, self._news_panel)
        if not target.winfo_ismapped():
            target.place(x=self._px(40), y=PANEL_TOP,
                         width=WIN_W - self._px(80), height=PANEL_H)
        target.tkraise()
        self._active_panel = target

        if tab == "MODS":
            threading.Thread(target=self._load_mods_state, daemon=True).start()
        elif tab == "TWEAKS":
            self._refresh_tweaks_panel()
        elif tab == "ADDONS":
            self._addons_verify()
        elif tab == "MPQ":
            self._mpq_check()
        else:
            self._load_news()

    def _build(self):
        self._bg_canvas = tk.Canvas(self, width=WIN_W, height=WIN_H,
                                    bg=C_BG, highlightthickness=0)
        self._bg_canvas.place(x=0, y=0)
        self._draw_bg()

        self._build_header()
        self._build_panel()
        self._build_footer()

    def _draw_bg(self):
        c = self._bg_canvas
        bloom_cx, bloom_cy = WIN_W - self._px(80), self._px(80)
        for i in range(40, 0, -1):
            r  = self._px(i * 9)
            alpha_frac = (40 - i) / 40
            r_val = int(0x12 + alpha_frac * (0x2e - 0x12))
            g_val = int(0x0e + alpha_frac * (0x18 - 0x0e))
            b_val = int(0x1a + alpha_frac * (0x50 - 0x1a))
            col = f"#{r_val:02x}{g_val:02x}{b_val:02x}"
            c.create_oval(bloom_cx - r, bloom_cy - r,
                          bloom_cx + r, bloom_cy + r,
                          fill=col, outline="")

        c.create_line(0, WIN_H - self._px(1), WIN_W, WIN_H - self._px(1),
                      fill=C_PANEL_BDR)

    def _build_header(self):
        HDR_H = self._px(108)

        hdr = tk.Canvas(self, width=WIN_W, height=HDR_H,
                        bg=C_BG, highlightthickness=0)
        hdr.place(x=0, y=0, width=WIN_W, height=HDR_H)
        self._hdr_canvas = hdr

        # Same corner bloom as the main background (identical coordinates
        # and colors) so the header blends seamlessly with the body instead
        # of sitting as a darker separated band.
        bloom_cx, bloom_cy = WIN_W - self._px(80), self._px(80)
        for i in range(40, 0, -1):
            r = self._px(i * 9)
            alpha_frac = (40 - i) / 40
            r_val = int(0x12 + alpha_frac * (0x2e - 0x12))
            g_val = int(0x0e + alpha_frac * (0x18 - 0x0e))
            b_val = int(0x1a + alpha_frac * (0x50 - 0x1a))
            col = f"#{r_val:02x}{g_val:02x}{b_val:02x}"
            hdr.create_oval(bloom_cx - r, bloom_cy - r,
                            bloom_cx + r, bloom_cy + r,
                            fill=col, outline="")

        import tkinter.font as tkfont

        self._logo_y = HDR_H // 2 - self._px(6)
        self._draw_logo()

        # Point-sized font: Tk scales it by tk-scaling, so measure() below
        # already returns device pixels at the current DPI.
        nav_font = tkfont.Font(family="Segoe UI", size=11, weight="bold")
        tabs = ["NEWS", "TWEAKS", "ADDONS", "MODS", "MPQ"]
        self._active_tab  = "NEWS"
        self._nav_pos     = {}
        self._nav_text_w  = {}
        self._hdr_regions = {}
        x = self._px(240)
        for tab in tabs:
            w = nav_font.measure(tab) + self._px(36)
            self._nav_pos[tab]     = x + w // 2
            self._nav_text_w[tab]  = nav_font.measure(tab)
            self._hdr_regions[tab] = (x, 0, x + w, HDR_H)
            x += w
            self._draw_nav_tab(tab)

        self._hdr_regions["gear"] = (WIN_W - self._px(36), self._px(2),
                                     WIN_W - self._px(2), self._px(34))
        self._draw_gear()

        # The wordmark is a clickable header element too (opens the repo).
        lb = hdr.bbox("logo")
        if lb:
            self._hdr_regions["logo"] = (lb[0] - self._px(4), lb[1] - self._px(4),
                                         lb[2] + self._px(6), lb[3] + self._px(4))
            self._logo_cx = (lb[0] + lb[2]) // 2
        else:
            self._logo_cx = self._px(127)
        # "Update available!" label under the wordmark, shown once the daily
        # self-update check finds a newer release.
        self._update_available = False
        self._draw_update_label()

        self._hdr_hover = None
        hdr.bind("<Button-1>", self._on_hdr_click)
        hdr.bind("<Motion>",   self._on_hdr_motion)
        hdr.bind("<Leave>",    lambda e: self._on_hdr_motion(None))

        self._clear_wdb_var = tk.BooleanVar(
            value=bool(self._cfg.get("clear_wdb_on_launch", False)))
        self._close_on_launch_var = tk.BooleanVar(
            value=bool(self._cfg.get("close_on_launch", False)))
        self._auto_mods_var = tk.BooleanVar(
            value=bool(self._cfg.get("auto_install_mods", True)))
        self._auto_addons_var = tk.BooleanVar(
            value=bool(self._cfg.get("auto_install_addons", True)))
        self._ignore_speech_var = tk.BooleanVar(
            value=bool(self._cfg.get("ignore_speech", False)))
        # Deferred "install missing" pending from turning an auto-install
        # option on in Settings — applied on close (see _close_settings).
        self._auto_mods_retrigger = False
        self._auto_addons_retrigger = False

    def _draw_logo(self, hover: bool = False):
        cv = self._hdr_canvas
        cv.delete("logo")
        cv.create_text(self._px(24), self._logo_y, text="Octo Updater",
                       font=("Segoe UI", 24, "bold"),
                       fill="#b478d9" if hover else "#9a5cbf",
                       anchor="w", tags="logo")

    def _draw_update_label(self, hover: bool = False):
        cv = self._hdr_canvas
        cv.delete("upd_label")
        self._hdr_regions.pop("update", None)
        if not self._update_available:
            return
        cv.create_text(self._logo_cx, self._logo_y + self._px(26),
                       text="Update available!",
                       font=("Segoe UI", 10, "bold"),
                       fill=C_GOLD_LT if hover else C_GOLD,
                       anchor="n", tags="upd_label")
        lb = cv.bbox("upd_label")
        if lb:
            self._hdr_regions["update"] = (lb[0] - self._px(4), lb[1] - self._px(2),
                                           lb[2] + self._px(4), lb[3] + self._px(2))

    def _draw_gear(self, hover: bool = False):
        cv = self._hdr_canvas
        cv.delete("gear_icon")
        cv.create_text(WIN_W - self._px(10), self._px(8), text="⚙",
                       font=("Segoe UI", 13),
                       fill=C_GOLD if hover else C_TEXT_DIM,
                       anchor="ne", tags="gear_icon")

    def _hdr_hit(self, x, y):
        for name, (x0, y0, x1, y1) in self._hdr_regions.items():
            if x0 <= x <= x1 and y0 <= y <= y1:
                return name
        return None

    def _on_hdr_motion(self, event):
        name = self._hdr_hit(event.x, event.y) if event is not None else None
        if name == self._hdr_hover:
            return
        prev = self._hdr_hover
        self._hdr_hover = name
        if prev in self._nav_pos:
            self._draw_nav_tab(prev)
        if name in self._nav_pos:
            self._draw_nav_tab(name, hover=True)
        if "gear" in (prev, name):
            self._draw_gear(hover=(name == "gear"))
        if "logo" in (prev, name):
            self._draw_logo(hover=(name == "logo"))
        if "update" in (prev, name):
            self._draw_update_label(hover=(name == "update"))
        self._hdr_canvas.configure(cursor="hand2" if name else "")

    def _on_hdr_click(self, event):
        name = self._hdr_hit(event.x, event.y)
        if name == "gear":
            self._open_settings(event)
        elif name in ("logo", "update"):
            self._open_url("https://github.com/rebasedkon/octo-updater")
        elif name in self._nav_pos:
            self._switch_tab(name)

    def _check_updater_update(self):
        """Background daily check of the updater's own GitHub releases; shows
        the 'Update available!' header label if a newer version exists."""
        try:
            tag = fetch_updater_latest_tag()
        except Exception:
            tag = None
        if updater_update_available(tag):
            def show():
                self._update_available = True
                self._draw_update_label()
            self.after(0, show)

    def _build_panel(self):
        PANEL_TOP  = self._px(109)
        PANEL_BOT  = FOOT_H
        PANEL_H    = WIN_H - PANEL_TOP - PANEL_BOT
        PAD        = self._px(40)

        panel = tk.Frame(self, bg=C_BG)
        panel.place(x=PAD, y=PANEL_TOP + self._px(10),
                    width=WIN_W - PAD * 2,
                    height=PANEL_H - self._px(20))
        self._news_panel = panel
        self._active_panel = panel   # NEWS is the initial tab

        inner_w = WIN_W - PAD * 2
        self._news_left_w  = int(inner_w * 0.60)
        self._news_right_w = inner_w - self._news_left_w - self._px(12)

        # Latest announcement — parchment panel (left)
        feat = tk.Frame(panel, bg=C_PARCH)
        feat.place(x=0, y=0, width=self._news_left_w, relheight=1.0)
        self._feat_frame = feat

        # Patch-notes list (right)
        ann = tk.Frame(panel, bg=C_PANEL,
                       highlightthickness=1,
                       highlightbackground=C_PANEL_BDR)
        ann.place(x=self._news_left_w + self._px(12), y=0,
                  width=self._news_right_w, relheight=1.0)
        self._patch_frame = ann

        self._render_featured(None, loading=True)
        self._render_patch_notes(None, loading=True)

        self._log_line("Octo Updater  v" + UPDATER_VERSION + "\n", "acct")
        self._log_line("─" * 60 + "\n", "dim")
        self._build_mods_panel()
        self._build_tweaks_panel()
        self._build_addons_panel()
        self._build_mpq_panel()

    # ── news panel ───────────────────────────────────────────────────────────

    def _load_news(self, force=False):
        self._load_featured(force)
        self._load_patch_notes(force)

    def _load_featured(self, force=False):
        now = time.time()
        if (not force and self._featured is not None
                and (now - self._feat_ts) < NEWS_CACHE_TTL):
            return
        self._render_featured(None, loading=True)

        def worker():
            feat, err = None, ""
            try:
                feat = fetch_featured_post()
            except Exception:
                err = "Couldn't reach the news feed."

            def apply():
                self._feat_ts  = time.time()
                self._featured = feat
                self._render_featured(feat, error=err)
            self.after(0, apply)
        threading.Thread(target=worker, daemon=True).start()

    def _load_patch_notes(self, force=False):
        now = time.time()
        if (not force and self._patch_items is not None
                and (now - self._patch_ts) < NEWS_CACHE_TTL):
            return
        self._render_patch_notes(None, loading=True)

        def worker():
            items, err = None, ""
            try:
                items = fetch_patch_notes()
            except Exception:
                err = "Couldn't reach the news feed."

            def apply():
                self._patch_ts    = time.time()
                self._patch_items = items
                self._render_patch_notes(items, error=err)
            self.after(0, apply)
        threading.Thread(target=worker, daemon=True).start()

    def _render_featured(self, post, loading=False, error=""):
        f = self._feat_frame
        for w in f.winfo_children():
            w.destroy()
        f.configure(highlightthickness=1, highlightbackground=C_PARCH_EDGE)

        title = (post or {}).get("title", "")

        # Title band — slightly darker parchment strip
        band = tk.Frame(f, bg=C_PARCH_BAND)
        band.pack(fill="x")
        hdr = tk.Frame(band, bg=C_PARCH_BAND)
        hdr.pack(fill="x", padx=self._px(20), pady=(self._px(16), self._px(12)))
        tk.Label(hdr,
                 text=title.upper() if title else "NEWS",
                 font=("Segoe UI", 13, "bold"),
                 fg=C_PARCH_TITLE, bg=C_PARCH_BAND,
                 wraplength=self._news_left_w - self._px(100),
                 justify="left", anchor="w").pack(side="left",
                                                  fill="x", expand=True)
        rf = tk.Label(hdr, text="⟳", font=("Segoe UI", 14),
                      fg=C_PARCH_DIM, bg=C_PARCH_BAND, cursor="hand2")
        rf.pack(side="right")
        rf.bind("<Button-1>", lambda e: self._load_featured(force=True))
        rf.bind("<Enter>",    lambda e: rf.configure(fg=C_PARCH_LINK))
        rf.bind("<Leave>",    lambda e: rf.configure(fg=C_PARCH_DIM))

        if not post:
            msg = error or ("Loading…" if loading
                            else "No news yet — check back later.")
            tk.Label(f, text=msg, font=("Segoe UI", 10),
                     fg=C_PARCH_DIM, bg=C_PARCH).pack(padx=self._px(20),
                                                      pady=self._px(16),
                                                      anchor="w")
            return

        byline = []
        if post.get("author"):
            byline.append(f"by {post['author']}")
        byline.append(_format_news_date(post.get("date", "")))
        bl = tk.Frame(f, bg=C_PARCH_BAND)
        bl.pack(fill="x")
        tk.Label(bl, text=" · ".join(byline),
                 font=("Segoe UI", 10, "italic"),
                 fg=C_PARCH_DIM, bg=C_PARCH_BAND,
                 anchor="w").pack(fill="x", padx=self._px(20), pady=self._px(10))
        tk.Frame(f, bg=C_PARCH_LINE, height=self._px(1)).pack(fill="x")

        # Pack the link first with side="bottom" so it's always reserved its
        # space; the body Text (which defaults to 24 lines tall) then fills
        # only the remaining area instead of clipping the link off the panel.
        if post.get("url"):
            link = tk.Label(f, text="⧉  Read full post on the forum",
                            font=("Segoe UI", 11),
                            fg=C_PARCH_LINK, bg=C_PARCH,
                            cursor="hand2", anchor="w")
            link.pack(side="bottom", fill="x", padx=self._px(20),
                      pady=(self._px(4), self._px(16)))
            link.bind("<Button-1>",
                      lambda e, u=post["url"]: self._open_url(u))
            link.bind("<Enter>", lambda e: link.configure(fg=C_PARCH_TITLE))
            link.bind("<Leave>", lambda e: link.configure(fg=C_PARCH_LINK))

        body = _strip_html(post.get("html", ""))
        txt = tk.Text(f, bg=C_PARCH, fg=C_PARCH_TEXT, relief="flat",
                      font=("Segoe UI", 11), wrap="word", height=1,
                      padx=self._px(2), pady=self._px(8),
                      spacing2=self._px(4), spacing3=self._px(4),
                      highlightthickness=0, cursor="arrow")
        txt.insert("1.0", body)
        txt.configure(state="disabled")
        txt.pack(fill="both", expand=True, padx=self._px(20),
                 pady=(self._px(8), self._px(2)))

    def _render_patch_notes(self, items, loading=False, error=""):
        f = self._patch_frame
        for w in f.winfo_children():
            w.destroy()

        hdr = tk.Frame(f, bg=C_PANEL)
        hdr.pack(fill="x", padx=self._px(14), pady=(self._px(16), self._px(10)))
        tk.Label(hdr, text="PATCH NOTES",
                 font=("Segoe UI", 12, "bold"),
                 fg=C_GOLD, bg=C_PANEL).pack(side="left")
        rf = tk.Label(hdr, text="⟳", font=("Segoe UI", 14),
                      fg=C_TEXT_DIM, bg=C_PANEL, cursor="hand2")
        rf.pack(side="right")
        rf.bind("<Button-1>", lambda e: self._load_patch_notes(force=True))
        rf.bind("<Enter>",    lambda e: rf.configure(fg=C_GOLD))
        rf.bind("<Leave>",    lambda e: rf.configure(fg=C_TEXT_DIM))

        tk.Frame(f, bg=C_DIVIDER, height=self._px(1)).pack(
            fill="x", padx=self._px(14))

        if items is None or error:
            msg = error or ("Loading…" if loading
                            else "Couldn't reach the news feed.")
            tk.Label(f, text=msg, font=FONT_BODY,
                     fg=C_TEXT_DIM, bg=C_PANEL).pack(padx=self._px(14),
                                                     pady=self._px(12),
                                                     anchor="w")
            return
        if not items:
            tk.Label(f, text="No news yet — check back later.",
                     font=FONT_BODY, fg=C_TEXT_DIM,
                     bg=C_PANEL).pack(padx=self._px(14), pady=self._px(12),
                                      anchor="w")
            return

        list_frame = tk.Frame(f, bg=C_PANEL)
        list_frame.pack(fill="both", expand=True, padx=(self._px(14), self._px(4)),
                        pady=(0, self._px(10)))
        canvas = tk.Canvas(list_frame, bg=C_PANEL, highlightthickness=0)
        sb = SlimScrollbar(list_frame, command=canvas.yview, bg=C_PANEL,
                           width=self._px(10))
        self._wheel_canvases.append(canvas)
        inner = tk.Frame(canvas, bg=C_PANEL)
        inner.bind("<Configure>",
                   lambda e: canvas.configure(scrollregion=canvas.bbox("all")))
        canvas.create_window((0, 0), window=inner, anchor="nw",
                             width=self._news_right_w - self._px(40))
        canvas.configure(yscrollcommand=sb.set)
        sb.pack(side="right", fill="y")
        canvas.pack(side="left", fill="both", expand=True)

        wrap_w = self._news_right_w - self._px(50)
        for item in items:
            top = tk.Frame(inner, bg=C_PANEL)
            top.pack(fill="x", pady=(self._px(12), 0))
            tk.Label(top, text=_format_news_date(item.get("date", "")),
                     font=("Segoe UI", 9), fg=C_TEXT_DIM,
                     bg=C_PANEL).pack(side="right", anchor="n")
            tk.Label(top, text=item.get("title", ""),
                     font=("Segoe UI", 11, "bold"),
                     fg=C_GOLD, bg=C_PANEL,
                     wraplength=wrap_w - self._px(85), justify="left",
                     anchor="w").pack(side="left", fill="x", expand=True)

            if item.get("author"):
                tk.Label(inner, text=f"by {item['author']}",
                         font=("Segoe UI", 10, "italic"),
                         fg=C_TEXT_DIM, bg=C_PANEL,
                         anchor="w").pack(fill="x", pady=(self._px(2), 0))

            body = item.get("body", "").strip()
            if len(body) > 260:
                body = body[:260].rstrip() + "…"
            if body:
                tk.Label(inner, text=body, font=("Segoe UI", 10),
                         fg=C_TEXT, bg=C_PANEL,
                         wraplength=wrap_w, justify="left",
                         anchor="w").pack(fill="x", pady=(self._px(5), 0))

            if item.get("url"):
                lnk = tk.Label(inner, text="⧉ Read more",
                               font=("Segoe UI", 10),
                               fg=C_GOLD, bg=C_PANEL,
                               cursor="hand2", anchor="w")
                lnk.pack(fill="x", pady=(self._px(5), 0))
                lnk.bind("<Button-1>",
                         lambda e, u=item["url"]: self._open_url(u))
                lnk.bind("<Enter>", lambda e, w=lnk: w.configure(fg=C_GOLD_LT))
                lnk.bind("<Leave>", lambda e, w=lnk: w.configure(fg=C_GOLD))

            tk.Frame(inner, bg=C_DIVIDER, height=self._px(1)).pack(
                fill="x", pady=(self._px(12), 0))

    # ── tweaks panel ─────────────────────────────────────────────────────────────

    def _build_tweaks_panel(self):
        outer = tk.Frame(self, bg=C_PANEL,
                         highlightthickness=1,
                         highlightbackground=C_PANEL_BDR,
                         highlightcolor=C_PANEL_BDR)
        self._tweaks_panel_frame = outer

        self._tweaks_inner = tk.Frame(outer, bg=C_PANEL)
        self._tweaks_inner.pack(fill="both", expand=True)

        bar = tk.Frame(outer, bg=C_PANEL)
        bar.place(relx=1.0, x=-self._px(16), y=self._px(3), anchor="ne")

        apl = tk.Label(bar, text="Apply", font=("Segoe UI", 11),
                       fg=C_TEXT, bg=C_PANEL_BDR, cursor="hand2",
                       padx=self._px(16), pady=self._px(4))
        apl.bind("<Button-1>", lambda e: self._apply_tweaks())
        apl.bind("<Enter>",    lambda e: apl.configure(bg=C_GOLD, fg="#000"))
        apl.bind("<Leave>",    lambda e: apl.configure(bg=C_PANEL_BDR, fg=C_TEXT))
        self._tweaks_apply_btn = apl

        rst = tk.Label(bar, text="Reset", font=("Segoe UI", 11),
                       fg=C_TEXT, bg=C_PANEL_BDR, cursor="hand2",
                       padx=self._px(16), pady=self._px(4))
        rst.bind("<Button-1>", lambda e: self._reset_tweaks())
        rst.bind("<Enter>",    lambda e: rst.configure(bg=C_GOLD, fg="#000"))
        rst.bind("<Leave>",    lambda e: rst.configure(bg=C_PANEL_BDR, fg=C_TEXT))
        self._tweaks_reset_btn = rst

        self._tweak_widgets: dict = {}
        self._tweak_vars:    dict = {}

        self._build_tweaks_rows()

    def _build_tweaks_rows(self):
        for w in self._tweaks_inner.winfo_children():
            w.destroy()
        self._tweak_widgets = {}
        self._tweak_vars    = {}

        values = load_tweaks_config()
        PAD_X  = self._px(16)

        for (tid, label, kind, recommended, _, desc, mn, mx, step) in TWEAKS_ITEMS:
            if kind == "section":
                tk.Label(self._tweaks_inner, text=label,
                         font=("Segoe UI", 11, "bold"),
                         fg=C_GOLD, bg=C_PANEL,
                         anchor="w").pack(fill="x", padx=PAD_X,
                                          pady=(self._px(10), self._px(2)))
                tk.Frame(self._tweaks_inner, bg=C_DIVIDER, height=self._px(1)).pack(
                    fill="x", padx=PAD_X, pady=(0, self._px(4)))
                continue

            row = tk.Frame(self._tweaks_inner, bg=C_PANEL)
            row.pack(fill="x", padx=PAD_X, pady=self._px(3))

            tk.Label(row, text=label,
                     font=("Segoe UI", 10, "bold"),
                     fg=C_TEXT, bg=C_PANEL,
                     width=22, anchor="w").pack(side="left")

            if kind == "checkbox":
                var = tk.BooleanVar(value=values.get(tid, False))
                var.trace_add("write", self._refresh_tweaks_buttons)
                tk.Checkbutton(row, variable=var,
                               bg=C_PANEL, activebackground=C_PANEL,
                               fg=C_TEXT, selectcolor=C_PANEL,
                               highlightthickness=0, bd=0,
                               relief="flat", cursor="hand2"
                               ).pack(side="left", padx=(self._px(4), self._px(12)))
                self._tweak_vars[tid] = var

            elif kind == "number":
                val = values.get(tid, mn or 0)
                var = tk.StringVar(value=str(int(val)))
                var.trace_add("write", self._refresh_tweaks_buttons)
                entry = tk.Entry(row, textvariable=var,
                                 bg="#18181e", fg=C_TEXT,
                                 insertbackground=C_GOLD,
                                 relief="flat", font=FONT_MONO,
                                 width=7,
                                 highlightthickness=1,
                                 highlightbackground=C_PANEL_BDR,
                                 highlightcolor=C_GOLD,
                                 justify="center")
                entry.pack(side="left", padx=(self._px(4), self._px(12)),
                           ipady=self._px(3))
                self._tweak_vars[tid]   = var
                self._tweak_widgets[tid] = entry

                def _clamp(e, t=tid, lo=mn, hi=mx):
                    try:
                        v = int(float(self._tweak_vars[t].get()))
                        if lo is not None: v = max(lo, v)
                        if hi is not None: v = min(hi, v)
                        self._tweak_vars[t].set(str(v))
                    except ValueError:
                        self._tweak_vars[t].set(str(TWEAKS_DEFAULTS.get(t, lo or 0)))
                entry.bind("<FocusOut>", _clamp)
                entry.bind("<Return>",   _clamp)

            elif kind == "dropdown":
                cur = values.get(tid, TWEAKS_DEFAULTS.get(tid))
                if cur not in LOCALES:
                    cur = DEFAULT_LOCALE
                var = tk.StringVar(value=cur)           # holds the locale code
                var.trace_add("write", self._refresh_tweaks_buttons)
                mb = tk.Menubutton(
                    row, text=LOCALES[cur][1], font=("Segoe UI", 10),
                    fg=C_TEXT, bg="#18181e", activebackground=C_PANEL_BDR,
                    activeforeground=C_TEXT, relief="flat", cursor="hand2",
                    width=15, anchor="w", padx=self._px(8), pady=self._px(2),
                    highlightthickness=1, highlightbackground=C_PANEL_BDR)
                menu = tk.Menu(mb, tearoff=0, bg=C_PANEL, fg=C_TEXT,
                               activebackground=C_GOLD, activeforeground="#000")
                for code, (_i, label) in LOCALES.items():
                    menu.add_command(
                        label=label,
                        command=lambda c=code, v=var: v.set(c))
                mb["menu"] = menu
                mb.pack(side="left", padx=(self._px(4), self._px(12)))
                var.trace_add(
                    "write",
                    lambda *_a, m=mb, v=var: m.configure(
                        text=LOCALES.get(v.get(), (0, v.get()))[1]))
                self._tweak_vars[tid] = var

            if desc:
                tk.Label(row, text=desc,
                         font=("Segoe UI", 10), fg=C_TEXT_DIM, bg=C_PANEL,
                         wraplength=self._px(520), justify="left", anchor="w"
                         ).pack(side="left", fill="x", expand=True)

        self._refresh_tweaks_buttons()

    def _refresh_tweaks_buttons(self, *args):
        """Show Apply only when the UI differs from the saved config and
        Reset only when values are custom (differ from the defaults); paint
        out-of-range number entries red."""
        if not getattr(self, "_tweak_vars", None):
            return

        any_bad = False
        for tid, entry in self._tweak_widgets.items():
            lo, hi = TWEAKS_LIMITS.get(tid, (None, None))
            try:
                v = int(float(self._tweak_vars[tid].get()))
                bad = ((lo is not None and v < lo) or
                       (hi is not None and v > hi))
            except ValueError:
                bad = True
            any_bad = any_bad or bad
            entry.configure(fg=C_ERR if bad else C_TEXT)

        ui       = self._get_tweaks_from_ui()
        saved    = load_tweaks_config()
        defaults = dict(TWEAKS_DEFAULTS)
        defaults["fieldOfView"] = fov_default_for_display()

        def norm(d):
            def one(k):
                default = TWEAKS_DEFAULTS.get(k)
                if isinstance(default, bool):
                    return bool(d.get(k))
                if isinstance(default, str):
                    return str(d.get(k, default))
                return int(d.get(k, 0))
            return {k: one(k) for k in ui}

        # An out-of-range entry always counts as a change: _get_tweaks_from_ui
        # clamps it, and the clamped value can coincide with the saved one
        # (e.g. saved 180, typed 192 → clamps to 180), which would otherwise
        # hide the buttons while the entry still shows an invalid number.
        ui_n   = norm(ui)
        dirty  = any_bad or ui_n != norm(saved)
        custom = any_bad or ui_n != norm(defaults)

        self._tweaks_apply_btn.pack_forget()
        self._tweaks_reset_btn.pack_forget()
        if dirty:
            self._tweaks_apply_btn.pack(side="left")
        if custom:
            self._tweaks_reset_btn.pack(
                side="left", padx=(self._px(8), 0) if dirty else (0, 0))

    def _refresh_tweaks_panel(self):
        values = load_tweaks_config()
        for tid, var in self._tweak_vars.items():
            v = values.get(tid, TWEAKS_DEFAULTS.get(tid))
            if isinstance(var, tk.BooleanVar):
                var.set(bool(v))
            elif isinstance(TWEAKS_DEFAULTS.get(tid), str):
                var.set(v if v in LOCALES else DEFAULT_LOCALE)
            else:
                var.set(str(int(v)) if v is not None else "")

    def _get_tweaks_from_ui(self) -> dict:
        """Read tweak values from the UI, always clamped to their limits —
        an out-of-range entry can never reach the config or the exe patch."""
        result = {}
        for tid, var in self._tweak_vars.items():
            if isinstance(var, tk.BooleanVar):
                result[tid] = var.get()
            elif isinstance(TWEAKS_DEFAULTS.get(tid), str):
                code = var.get()
                result[tid] = code if code in LOCALES else DEFAULT_LOCALE
            else:
                try:
                    v = int(float(var.get()))
                except ValueError:
                    v = TWEAKS_DEFAULTS.get(tid, 0)
                lo, hi = TWEAKS_LIMITS.get(tid, (None, None))
                if lo is not None:
                    v = max(lo, v)
                if hi is not None:
                    v = min(hi, v)
                result[tid] = v
        return result

    def _reset_tweaks(self):
        defaults = dict(TWEAKS_DEFAULTS)
        defaults["fieldOfView"] = fov_default_for_display()
        save_tweaks_config(defaults)
        self._refresh_tweaks_panel()
        out = self._game_path.get().strip()
        if out and os.path.exists(os.path.join(out, "WoW.exe")):
            self._set_btn_busy("Patching…")
            self._status_var.set("Applying tweaks…")
            # Pass the same defaults that were saved
            threading.Thread(target=self._apply_tweaks_worker,
                             args=(out, defaults), daemon=True).start()

    def _apply_tweaks(self):
        values = self._get_tweaks_from_ui()
        save_tweaks_config(values)
        # Write the (possibly clamped) saved values back into the entries so
        # the UI never keeps showing an out-of-range number after Apply.
        self._refresh_tweaks_panel()

        out = self._game_path.get().strip()
        if not out:
            self._log_line("Game folder not set.\n", "err")
            return

        exe = os.path.join(out, "WoW.exe")
        if not os.path.exists(exe):
            self._log_line("WoW.exe not found — run Update first.\n", "err")
            return

        self._log_line("\nApplying tweaks to WoW.exe...\n", "acct")
        self._set_btn_busy("Patching…")
        self._status_var.set("Applying tweaks…")
        threading.Thread(target=self._apply_tweaks_worker,
                         args=(out, values), daemon=True).start()

    def _apply_tweaks_worker(self, client_dir: str, tweaks: dict):
        log_q  = queue.Queue()
        prog_q = queue.Queue()
        worker = UpdateWorker(client_dir, log_q, prog_q)

        def drain():
            try:
                while True:
                    msg, tag = log_q.get_nowait()
                    if msg not in ("__DONE__", "__ERROR__") and not msg.startswith("__"):
                        self.after(0, lambda m=msg, t=tag: self._log_line(
                            (m if m.endswith("\n") else m + "\n"), t))
            except queue.Empty:
                pass

        try:
            worker.patch_exe(tweaks)
            drain()
            update_config_wtf(client_dir, tweaks)

            self._log_line("\nTweaks applied.\n", "ok")
            self.after(0, self._refresh_ready_state)
        except Exception as e:
            drain()
            self._log_line(f"\n✗ Tweak patch failed: {e}\n", "err")

            def _fail_state():
                self._status_var.set("Tweaks failed — check the log")
                self._set_btn_update()
            self.after(0, _fail_state)

    # ── version migrations ─────────────────────────────────────────────────────────

    def _new_version_installed(self):
        """One-time, version-gated migrations run at launch.

        The config key ``octo_updater_version`` records the updater version
        whose migrations have already been applied to this install (absent on
        installs predating this mechanism, < 1.3). When it already matches the
        running ``UPDATER_VERSION`` there's nothing to do.

        Otherwise replay every migration step newer than the stored version,
        then stamp the current one so each runs exactly once. Runs
        synchronously (before the normal startup verify is scheduled), so any
        WoW.exe re-patch is settled before verify reads the exe — no read/write
        race, and the standard verify still runs and can surface a pending
        client update. Future versions add their own ``if from_ver < (x, y): …``
        block below."""
        cfg = load_config()
        if cfg.get("octo_updater_version") == UPDATER_VERSION:
            return

        if not self._first_run:
            from_ver = _parse_version(cfg.get("octo_updater_version", ""))
            if from_ver < (1, 3):
                self._migrate_1_3()

        self._cfg = update_config(
            lambda c: c.__setitem__("octo_updater_version", UPDATER_VERSION))

    def _migrate_1_3(self):
        """1.3: raise the ground-clutter defaults for existing installs.

        frillDistance is a VanillaTweak baked into WoW.exe, so bumping the old
        70 → 120 default needs a re-patch (skipped for a user who already set a
        higher value). frillDensity is a plain Config.wtf value; if it's still
        below 128 we lift it to the new default in place."""
        out = self._game_path.get().strip()

        # frillDistance (VanillaTweak / WoW.exe). Raise to 120 if it's lower
        stored = dict(load_config().get("tweaks", {}))
        if int(stored.get("frillDistance", 70)) < 120:
            stored["frillDistance"] = 120
            save_tweaks_config(stored)
            self._log_line(
                "Ground clutter distance raised to 120 (new default).\n", "acct")
            if out and os.path.exists(os.path.join(out, "WoW.exe")):
                self._log_line("Re-patching WoW.exe for v1.3…\n", "acct")
                self._apply_tweaks_worker(out, load_tweaks_config())

        # frillDensity (Config.wtf value). Raise to 128 if it's lower
        cfg_path = os.path.join(out, "WTF", "Config.wtf") if out else ""
        if cfg_path and os.path.exists(cfg_path):
            try:
                with open(cfg_path, "r", encoding="utf-8") as f:
                    lines = f.readlines()
                changed = False
                for i, line in enumerate(lines):
                    if not line.strip().lower().startswith("set frilldensity "):
                        continue
                    parts = line.split('"')
                    cur = (int(parts[1]) if len(parts) >= 2
                           and parts[1].strip().lstrip("-").isdigit() else None)
                    if cur is not None and cur < 128:
                        lines[i] = 'SET frillDensity "128"\n'
                        changed = True
                    break
                if changed:
                    with open(cfg_path, "w", encoding="utf-8") as f:
                        f.writelines(lines)
                    self._log_line(
                        "Ground clutter density raised to 128 (new default).\n",
                        "acct")
            except Exception as e:
                self._log_line(
                    f"Could not update frillDensity in Config.wtf: {e}\n", "err")

        # dlls.txt cleanup: earlier versions wrongly registered the loader
        # (VfPatcher.dll) and dxvk here — neither is loaded via dlls.txt, so a
        # loader that walks the list would try to load itself / a missing file.
        dlls_path = _dlls_txt_path(out) if out else ""
        if dlls_path and os.path.exists(dlls_path):
            try:
                present = {l.strip().lower()
                           for l in open(dlls_path).read().splitlines()}
                stale = [n for n in ("VfPatcher.dll", "dxvk")
                         if n.lower() in present]
                for n in stale:
                    remove_dll(out, n)
                if stale:
                    self._log_line(
                        f"Removed stale dlls.txt entries: {', '.join(stale)}.\n",
                        "acct")
            except Exception as e:
                self._log_line(f"Could not clean dlls.txt: {e}\n", "err")

        # dxvk.conf: refresh an existing config to the current template
        # (d3d9.presentInterval, no cursor / numBackBuffers). Only when DXVK is
        # actually present — a missing dxvk.conf is left alone.
        if out and os.path.exists(os.path.join(out, "dxvk.conf")):
            _write_dxvk_conf(out)
            self._log_line("dxvk.conf updated to the new defaults.\n", "acct")

        # Legacy game-hash cache: the torrent-based download no longer keeps a
        # per-file SHA-1 cache. Delete the pre-1.3 cache file beside the app.
        stale_cache = os.path.join(APP_DIR, "octo_updater_hash_cache.json")
        try:
            if os.path.exists(stale_cache):
                os.remove(stale_cache)
        except OSError:
            pass

        # Drop the vestigial WoW.exe hash keys from config — unused since the
        # download revamp (verify is size-based, patching reads the pristine
        # base), so they'd otherwise linger in every migrated config.
        self._cfg = update_config(
            lambda c: (c.pop("expected_patched_wow_hash", None),
                       c.pop("original_server_wow_hash", None)))

        self._set_pending_reconcile("keep-config")

    # ── mods panel ───────────────────────────────────────────────────────────────

    def _build_mods_panel(self):
        PAD       = self._px(18)
        PANEL_TOP = self._px(119)
        PANEL_H   = WIN_H - PANEL_TOP - FOOT_H - self._px(10)

        outer = tk.Frame(self, bg=C_PANEL,
                         highlightthickness=1,
                         highlightbackground=C_PANEL_BDR)
        self._mods_panel_frame = outer

        note = tk.Frame(outer, bg=C_PANEL)
        note.pack(fill="x", padx=self._px(16), pady=(self._px(14), self._px(8)),
                  anchor="w")
        tk.Label(note, text="Mods marked with ",
                 font=("Segoe UI", 10), fg=C_TEXT_DIM,
                 bg=C_PANEL).pack(side="left")
        tk.Label(note, text="★", font=("Segoe UI", 10),
                 fg=C_GOLD, bg=C_PANEL).pack(side="left")
        tk.Label(note, text=" are essential",
                 font=("Segoe UI", 10), fg=C_TEXT_DIM,
                 bg=C_PANEL).pack(side="left")

        tk.Frame(outer, bg=C_DIVIDER, height=self._px(1)).pack(
            fill="x", padx=self._px(16), pady=(0, self._px(4)))

        list_frame = tk.Frame(outer, bg=C_PANEL)
        list_frame.pack(fill="both", expand=True, padx=self._px(16))

        canvas = tk.Canvas(list_frame, bg=C_PANEL, highlightthickness=0)
        sb = SlimScrollbar(list_frame, command=canvas.yview, bg=C_PANEL,
                           width=self._px(10))
        self._wheel_canvases.append(canvas)
        self._mods_inner = tk.Frame(canvas, bg=C_PANEL)
        self._mods_inner.bind(
            "<Configure>",
            lambda e: canvas.configure(scrollregion=canvas.bbox("all")))
        mods_win = canvas.create_window((0, 0), window=self._mods_inner,
                                        anchor="nw")
        # Stretch rows to the full canvas width so right-side controls
        # (Ignore updates) sit flush against the scrollbar.
        canvas.bind("<Configure>",
                    lambda e: canvas.itemconfigure(mods_win, width=e.width))
        canvas.configure(yscrollcommand=sb.set)
        sb.pack(side="right", fill="y")
        canvas.pack(side="left", fill="both", expand=True)

        tk.Frame(outer, bg=C_DIVIDER, height=self._px(1)).pack(
            fill="x", padx=self._px(16), pady=(self._px(4), 0))
        foot = tk.Frame(outer, bg=C_PANEL)
        foot.pack(fill="x", padx=self._px(16), pady=(self._px(6), self._px(10)))

        # Packed on demand by _refresh_apply_btn_visibility(): shown only
        # when there are unapplied checkbox changes or a mod is in error.
        self._apply_btn = tk.Label(foot, text="Apply",
                                   font=("Segoe UI", 11),
                                   fg=C_TEXT, bg=C_PANEL_BDR,
                                   cursor="hand2", padx=self._px(16),
                                   pady=self._px(4))
        self._apply_btn.bind("<Button-1>", lambda e: self._apply_mods())
        self._apply_btn.bind("<Enter>",    lambda e: self._apply_btn.configure(bg=C_GOLD, fg="#000"))
        self._apply_btn.bind("<Leave>",    lambda e: self._apply_btn.configure(bg=C_PANEL_BDR, fg=C_TEXT))

        self._mod_row_vars:     dict = {}
        self._mods_state:       list = []
        self._mod_pending_state: dict = {}
        self._render_mod_rows()
        self._refresh_apply_btn_visibility()

    def _render_mod_rows(self):
        cfg      = load_config()
        mods_cfg = cfg.get("mods", {})

        # Essential mods first, then alphabetical within each group.
        mods_sorted = sorted(
            MODS_REGISTRY,
            key=lambda m: (not m.get("essential", False), m["name"].lower()))

        if self._mod_row_vars:
            for mod in mods_sorted:
                mid   = mod["id"]
                state = mods_cfg.get(mid, {})
                live  = next((m for m in self._mods_state if m["id"] == mid), None)
                refs  = self._mod_row_vars.get(mid, {})
                if not refs:
                    continue

                if live is not None and "ver_label" in refs:
                    # Installed mods show their installed version; others
                    # show the latest available.
                    ver = state.get("installed_version") or live.get("latest_version") or "unknown"
                    refs["ver_label"].configure(text=f"  {ver}")

                # Checkbox always reflects config only — never a registry default.
                # A mod only shows checked if it's actually recorded as installed.
                if mid not in self._mod_pending_state:
                    if "enabled" in refs:
                        refs["enabled"].set(state.get("enabled", False))
                    if "ignore" in refs:
                        refs["ignore"].set(state.get("ignore_updates", False))

                has_error = bool(state.get("error"))
                installed = bool(state.get("installed_version"))
                if "name_label" in refs:
                    refs["name_label"].configure(
                        fg=C_ERR if has_error else (C_MOD_HL if installed else C_TEXT))
                if "desc_label" in refs:
                    refs["desc_label"].configure(
                        fg=C_TEXT if state.get("enabled", False) else C_TEXT_DIM)
                if "error_label" in refs:
                    if has_error:
                        refs["error_label"].configure(text=f"  \u26a0  {state['error']}")
                        refs["error_label"].pack(fill="x", pady=(0, self._px(4)))
                    else:
                        refs["error_label"].pack_forget()

                if "update_label" in refs:
                    self._style_mod_action_label(refs["update_label"],
                                                 mod, state, live)
            return

        for w in self._mods_inner.winfo_children():
            w.destroy()
        self._mod_row_vars = {}

        for mod in mods_sorted:
            mid   = mod["id"]
            state = mods_cfg.get(mid, {})
            live  = next((m for m in self._mods_state if m["id"] == mid), {})

            # Installed mods show their installed version; others show latest.
            latest_ver  = state.get("installed_version") or live.get("latest_version") or "unknown"
            # Checkbox reflects only what's actually recorded in config — never
            # a registry default. Pending (not-yet-applied) UI changes still
            # win so an in-progress toggle survives a background re-render.
            enabled     = self._mod_pending_state.get(mid, {}).get("enabled", state.get("enabled", False))
            ignore_upd  = state.get("ignore_updates", False)
            essential   = mod.get("essential", False)
            installed   = bool(state.get("installed_version"))
            # Installed mods are highlighted green; the name is neutral text
            # otherwise (error state overrides to red in the refresh paths).
            name_col    = C_MOD_HL if installed else C_TEXT

            container = tk.Frame(self._mods_inner, bg=C_PANEL)
            container.pack(fill="x")

            row = tk.Frame(container, bg=C_PANEL)
            row.pack(fill="x", pady=self._px(5))

            name_f = tk.Frame(row, bg=C_PANEL, width=self._px(210))
            name_f.pack(side="left", fill="y")
            name_f.pack_propagate(False)
            # Essential mods get a gold star badge; a fixed-width slot keeps
            # the names aligned whether or not the star is present.
            star = tk.Label(name_f, text="★" if essential else "",
                            font=("Segoe UI", 9), fg=C_GOLD, bg=C_PANEL,
                            width=2, anchor="w")
            star.pack(side="left")
            if essential:
                self._add_tooltip(star, "Essential mod")
            name_label = tk.Label(name_f, text=mod["name"],
                                  font=("Segoe UI", 10, "bold"),
                                  fg=name_col, bg=C_PANEL, anchor="w")
            name_label.pack(side="left")
            ver_label = tk.Label(name_f, text=f"  {latest_ver}",
                                 font=("Segoe UI", 9), fg=C_TEXT_DIM, bg=C_PANEL)
            ver_label.pack(side="left")

            enabled_var = tk.BooleanVar(value=enabled)
            tk.Checkbutton(row, variable=enabled_var,
                           bg=C_PANEL, activebackground=C_PANEL,
                           fg=C_TEXT, selectcolor=C_PANEL,
                           highlightthickness=0, bd=0,
                           relief="flat", cursor="hand2",
                           command=lambda m=mid, v=enabled_var: self._toggle_mod(m, v)
                           ).pack(side="left", padx=(self._px(4), self._px(8)))

            # Right-side widgets are packed first so they stay pinned to the
            # panel's right edge; the description then fills the middle.
            ignore_var = tk.BooleanVar(value=ignore_upd)
            ig_f = tk.Frame(row, bg=C_PANEL)
            ig_f.pack(side="right", padx=(self._px(8), 0))
            tk.Checkbutton(ig_f, variable=ignore_var,
                           bg=C_PANEL, activebackground=C_PANEL,
                           fg=C_TEXT, selectcolor=C_PANEL,
                           highlightthickness=0, bd=0,
                           relief="flat", cursor="hand2",
                           command=lambda m=mid, v=ignore_var: self._set_ignore(m, v)
                           ).pack(side="left")
            tk.Label(ig_f, text="Ignore updates",
                     font=("Segoe UI", 9), fg=C_TEXT_DIM, bg=C_PANEL).pack(side="left")

            link = tk.Label(row, text="⧉",
                            font=("Segoe UI", 12), fg=C_TEXT_DIM,
                            bg=C_PANEL, cursor="hand2")
            link.pack(side="right", padx=self._px(4))
            link.bind("<Button-1>", lambda e, u=mod["repo_url"]: self._open_url(u))
            link.bind("<Enter>",    lambda e, l=link: l.configure(fg=C_GOLD))
            link.bind("<Leave>",    lambda e, l=link: l.configure(fg=C_TEXT_DIM))

            update_label = tk.Label(row, text="update",
                                    font=("Segoe UI", 10, "bold"),
                                    fg=C_GOLD, bg=C_PANEL, cursor="hand2")
            update_label.bind("<Button-1>", lambda e, m=mid: self._update_mod(m))
            update_label.bind("<Enter>", lambda e, l=update_label:
                              l.configure(fg=getattr(l, "_hover", C_GOLD_LT)))
            update_label.bind("<Leave>", lambda e, l=update_label:
                              l.configure(fg=getattr(l, "_base", C_GOLD)))
            self._style_mod_action_label(update_label, mod, state, live)

            desc_label = tk.Label(row, text=mod["description"],
                                  font=("Segoe UI", 10),
                                  fg=(C_TEXT if enabled else C_TEXT_DIM),
                                  bg=C_PANEL, wraplength=self._px(400),
                                  justify="left", anchor="w")
            desc_label.pack(side="left", fill="x", expand=True)

            existing_err = state.get("error")
            error_label = tk.Label(container, text="",
                                   font=("Segoe UI", 9), fg=C_ERR,
                                   bg=C_PANEL, anchor="w", padx=self._px(16))
            if existing_err:
                name_label.configure(fg=C_ERR)
                error_label.configure(text=f"  \u26a0  {existing_err}")
                error_label.pack(fill="x", pady=(0, self._px(4)))

            divider = tk.Frame(self._mods_inner, bg=C_DIVIDER, height=self._px(1))
            divider.pack(fill="x", pady=(self._px(2), 0))

            self._mod_row_vars[mid] = {
                "enabled":      enabled_var,
                "ignore":       ignore_var,
                "ver_label":    ver_label,
                "name_label":   name_label,
                "desc_label":   desc_label,
                "error_label":  error_label,
                "update_label": update_label,
            }

    def _load_mods_state(self):
        state = []
        for mod in MODS_REGISTRY:
            try:
                v = fetch_mod_latest_version_cached(mod)
            except Exception:
                v = None
            if v:
                state.append({"id": mod["id"], "latest_version": v})
        self._mods_state = state
        self.after(0, self._render_mod_rows)
        self.after(0, self._refresh_mods_badge)

    def _count_mod_updates(self) -> int:
        mods_cfg = load_config().get("mods", {})
        count = 0
        for mod in MODS_REGISTRY:
            state = mods_cfg.get(mod["id"], {})
            live  = next((m for m in self._mods_state
                          if m["id"] == mod["id"]), None)
            if not state.get("error") and mod_update_available(mod, state, live):
                count += 1
        return count

    def _refresh_mods_badge(self):
        try:
            count = self._count_mod_updates()
        except Exception:
            count = 0
        if count != self._mod_updates_count:
            self._mod_updates_count = count
            self._draw_nav_tab("MODS")

    # The two game-resolution fixes can't coexist: enabling one prompts to
    # replace the other (see _confirm_res_fix_toggle).
    _RES_FIX_CONFLICTS = {"no1600x1200": "VanillaMultiMonitorFix",
                          "VanillaMultiMonitorFix": "no1600x1200"}

    # Per-mod (title, message, confirm) shown when enabling either resolution
    # fix. confirm=True asks Yes/No and only proceeds on Yes; confirm=False is
    # an OK-only acknowledgement that always proceeds.
    _RES_FIX_NOTICE = {
        "no1600x1200": (
            "No1600x1200",
            "No1600x1200 mod may cause the game to crash on launch on some "
            "systems.\n\n"
            "VanillaMultiMonitorFix is the recommended resolution fix. Use "
            "No1600x1200 only if VanillaMultiMonitorFix doesn't solve your "
            "problem.\n\n"
            "Enable No1600x1200 anyway?",
            True),
        "VanillaMultiMonitorFix": (
            "VanillaMultiMonitorFix",
            "Enable this mod only if the game doesn't detect your monitor's "
            "native resolution.\n\n"
            "VanillaMultiMonitorFix may interfere with correct resolution "
            "detection. By default, it's recommended to first try launching the "
            "game with DXVK, which may fix the resolution detection issue.\n\n"
            "Enable VanillaMultiMonitorFix only if you're actually experiencing "
            "resolution issues.",
            False),
    }

    def _toggle_mod(self, mod_id: str, var: tk.BooleanVar):
        # Turning on one of the conflicting resolution fixes needs confirmation
        # before it becomes a pending change.
        if var.get() and mod_id in self._RES_FIX_CONFLICTS:
            if not self._confirm_res_fix_toggle(mod_id, var):
                return   # backed out — var + pending already reset
        self._mod_pending_state.setdefault(mod_id, {})["enabled"] = var.get()
        self._refresh_apply_btn_visibility()

    def _mod_is_on(self, mod_id: str) -> bool:
        """Whether a mod is currently on in the UI: a pending toggle wins,
        otherwise its saved enabled state."""
        pending = self._mod_pending_state.get(mod_id, {})
        if "enabled" in pending:
            return bool(pending["enabled"])
        return bool(load_config().get("mods", {}).get(mod_id, {}).get("enabled"))

    def _confirm_res_fix_toggle(self, mod_id: str, var: tk.BooleanVar) -> bool:
        """Confirm enabling no1600x1200 / VanillaMultiMonitorFix. They conflict,
        so first offer to replace the other one, then show that mod's own notice
        (_RES_FIX_NOTICE). Returns True to proceed, or False if the user backed
        out — in which case the checkbox and pending state are reset to 'off'."""
        from tkinter import messagebox
        other = self._RES_FIX_CONFLICTS[mod_id]
        name  = next(m["name"] for m in MODS_REGISTRY if m["id"] == mod_id)
        oname = next(m["name"] for m in MODS_REGISTRY if m["id"] == other)

        def _cancel():
            var.set(False)
            self._mod_pending_state.pop(mod_id, None)
            self._refresh_apply_btn_visibility()

        # 1) Conflict — only when the other fix is currently on.
        replace_other = self._mod_is_on(other)
        if replace_other and not messagebox.askyesno(
                "Conflicting mods",
                f"{name} and {oname} both affect the game's resolution detection "
                f"and can't be used together — only one can be active at a time.\n\n"
                f"VanillaMultiMonitorFix is recommended if you experience "
                f"resolution issues in the game.\n\n"
                f"Replace {oname} with {name}?",
                parent=self):
            _cancel()
            return False

        # 2) That mod's own notice (crash risk / usage guidance). A confirm
        # notice can still cancel the toggle; an OK-only one just informs.
        title, message, confirm = self._RES_FIX_NOTICE[mod_id]
        if confirm:
            if not messagebox.askyesno(title, message, parent=self):
                _cancel()
                return False
        else:
            messagebox.showinfo(title, message, parent=self)

        # Confirmed — schedule the other fix for removal and untick its box.
        if replace_other:
            self._mod_pending_state.setdefault(other, {})["enabled"] = False
            other_var = self._mod_row_vars.get(other, {}).get("enabled")
            if other_var is not None:
                other_var.set(False)
        return True

    def _set_ignore(self, mod_id: str, var: tk.BooleanVar):
        self._mod_pending_state.setdefault(mod_id, {})["ignore_updates"] = var.get()
        self._refresh_apply_btn_visibility()

    def _refresh_apply_btn_visibility(self):
        """Apply is offered only when there is something to apply: pending
        checkbox changes, or a failed mod the user may want to retry."""
        has_error = any(bool(s.get("error"))
                        for s in load_config().get("mods", {}).values())
        if self._mod_pending_state or has_error:
            if not self._apply_btn.winfo_ismapped():
                self._apply_btn.pack(side="left")
        else:
            self._apply_btn.pack_forget()

    def _open_url(self, url: str):
        import webbrowser
        webbrowser.open(url)

    @staticmethod
    def _style_mod_action_label(lbl, mod, state, live):
        """Drive the per-mod action label: 'retry' (red) when the mod is in
        an error state, 'update' (gold) when a newer version is available,
        hidden otherwise. Both do the same thing — reinstall the mod."""
        if state.get("error"):
            lbl._base, lbl._hover = C_GOLD, C_GOLD_LT
            lbl.configure(text="retry", fg=C_GOLD)
            lbl.pack(side="right", padx=(self._px(2), self._px(8)))
        elif mod_update_available(mod, state, live):
            lbl._base, lbl._hover = C_GOLD, C_GOLD_LT
            lbl.configure(text="update", fg=C_GOLD)
            lbl.pack(side="right", padx=(self._px(2), self._px(8)))
        else:
            lbl.pack_forget()

    def _update_mod(self, mod_id: str):
        """Download and install the newest release of a single mod (the
        per-row "update" label). Runs through the normal apply worker so
        errors/versions are recorded exactly like a manual Apply."""
        out = self._game_path.get().strip()
        if not out:
            return
        mod = next(m for m in MODS_REGISTRY if m["id"] == mod_id)
        self._log_line(f"\nUpdating {mod['name']}...\n", "acct")
        self._set_btn_busy("Installing…")
        self._status_var.set("Downloading mods…")
        threading.Thread(target=self._apply_mods_worker,
                         args=(out, mod_id), daemon=True).start()

    def _apply_mods(self):
        out = self._game_path.get().strip()
        if not out:
            return
        self._apply_btn.configure(text="Applying...", bg="#2a2a32", fg=C_TEXT_DIM)
        self._set_btn_busy("Installing…")
        self._status_var.set("Downloading mods…")
        threading.Thread(target=self._apply_mods_worker,
                         args=(out,), daemon=True).start()

    def _maybe_install_default_addons(self):
        """Auto-install the recommended addons the first time this game
        folder is ready — the same one-shot mechanism as the default mods:
        the absence of the "addons" key in config means "never initialized
        for this folder", and a game-folder change wipes it to re-arm.
        Runs after the default mods finished (chained from the mods apply
        completion) or directly when mods were already initialized."""
        if self._default_addons_install_started:
            return
        if load_config().get("addons") is not None:
            return  # already initialized for this folder

        out = self._game_path.get().strip()
        if not out or not os.path.exists(os.path.join(out, "WoW.exe")):
            return  # game isn't actually installed here yet

        self._default_addons_install_started = True

        # Mark this folder as initialized even if every install fails, so
        # the batch doesn't re-fire on the next verify.
        update_config(lambda c: c.setdefault("addons", {}))

        # "Install recommended addons" (Settings → General): when
        # off, skip the batch install but still verify so the ADDONS tab lists
        # them as available for manual install.
        if not load_config().get("auto_install_addons", True):
            self._addons_verify()
            return

        ap = addons_path(out)
        recs = [{"folder": name, "status": "available", "git": url,
                 "branch": None, "ref": None, "toc": {},
                 "description": None, "error": None}
                for name, url in RECOMMENDED_ADDONS.items()
                if not os.path.isdir(os.path.join(ap, name))]
        if not recs:
            # Nothing to install (e.g. switched to a folder that already has
            # the addons) — still run a verify so the ADDONS tab badge shows
            # any available updates without the user opening the tab.
            self._addons_verify()
            return
        self._log_line("\nInstalling recommended addons...\n", "acct")
        self._addon_apply(recs)

    def _maybe_install_essential_mods(self):
        """Auto-install every mod flagged essential the first time this game
        folder is ready to use — i.e. on a brand-new install, or right after
        the game folder was changed to a new location. Both cases wipe the
        "mods" key from config, which is what this checks for, so once this
        has run (successfully or not — failures are recorded per-mod) it
        won't fire again until the folder changes.

        Reuses the normal apply worker so failures land in config exactly
        like a manual Apply would (per-mod "error" field, mod left disabled,
        installed_version cached the same way)."""
        if self._default_mods_install_started:
            return

        cfg = load_config()
        if cfg.get("mods"):
            return  # already initialized for this folder

        out = self._game_path.get().strip()
        if not out or not os.path.exists(os.path.join(out, "WoW.exe")):
            return  # game isn't actually installed here yet

        self._default_mods_install_started = True

        # "Install essential mods" (Settings → General) gates the
        # full essential set. VanillaFixes is exempt — it's the loader the other
        # mods depend on, so it's always auto-installed.
        auto_mods = cfg.get("auto_install_mods", True)
        for mod in MODS_REGISTRY:
            if mod.get("essential", False) and (auto_mods
                                                or mod["id"] == "VanillaFixes"):
                self._mod_pending_state.setdefault(mod["id"], {})["enabled"] = True

        self._log_line("\nInstalling essential mods...\n", "acct")
        self._set_btn_busy("Installing…")
        self._status_var.set("Downloading mods…")
        threading.Thread(target=self._apply_mods_worker,
                         args=(out,), daemon=True).start()

    def _apply_mods_worker(self, client_dir: str, only_mod_id: str | None = None):
        # Work on a detached copy of the "mods" section; it's merged back into
        # the live config atomically at the end (update_config).
        mods_cfg = load_config().get("mods", {})

        # Registry order is install order (VanillaFixes first).
        ordered = MODS_REGISTRY

        pending = self._mod_pending_state
        # Arm the one-time "DXVK first launch" notice if DXVK gets (re)installed
        # this run — the new d3d9.dll invalidates the shader cache.
        set_dxvk_notice = False

        for mod in ordered:
            mid   = mod["id"]
            if only_mod_id is not None and mid != only_mod_id:
                continue
            state = mods_cfg.get(mid, {})

            # Read enabled/ignore from pending UI changes first, fall back to
            # saved config. No registry-default fallback here: a mod is only
            # ever "enabled" because the user (or the one-time default-mods
            # seed in _maybe_install_essential_mods) explicitly said so.
            enabled    = pending.get(mid, {}).get("enabled",        state.get("enabled", False))
            ignore_upd = pending.get(mid, {}).get("ignore_updates", state.get("ignore_updates", False))

            # A targeted single-mod update/retry always means "install this
            # mod". Without this, retrying a failed install is a no-op: the
            # error handler recorded enabled=False, so needs_install stays
            # False and the mod is skipped (only its error gets cleared).
            if only_mod_id is not None and mid == only_mod_id:
                enabled = True

            installed_ver = state.get("installed_version")
            is_installed  = (bool(installed_ver) and
                             mod_installed_files_present(mod, client_dir))

            needs_install   = enabled and not is_installed
            needs_uninstall = not enabled and is_installed

            needs_version_lookup = needs_install or (enabled and is_installed and not ignore_upd)
            latest_ver  = None
            mod_release = None
            if needs_version_lookup:
                try:
                    if mod["source"]["kind"] in ("github_release", "codeberg_release"):
                        mod_release = _fetch_release_cached(mod)
                        latest_ver  = _release_version(mod, mod_release) if mod_release else None
                    else:
                        latest_ver = fetch_mod_latest_version_cached(mod)
                except Exception:
                    pass

            update_avail = (is_installed and
                            latest_ver is not None and
                            latest_ver != installed_ver and
                            not ignore_upd)
            needs_update = enabled and update_avail

            if not (needs_install or needs_uninstall or needs_update):
                if mid in pending:
                    mods_cfg.setdefault(mid, {}).update({
                        "enabled":        enabled,
                        "ignore_updates": ignore_upd,
                    })
                # A previously failed mod that the user leaves disabled on a
                # later Apply counts as dismissed — clear the error so it
                # stops blocking the PLAY button.
                if not enabled and state.get("error"):
                    mods_cfg.setdefault(mid, {})["error"] = None
                continue

            action = ("Installing" if needs_install else
                      "Updating" if needs_update else "Removing")
            self.after(0, lambda a=action, n=mod["name"]:
                       self._status_var.set(f"{a} {n}…"))

            try:
                if needs_install:
                    log(f"\nInstalling {mod['name']} {latest_ver}...")
                    written = install_mod(mod, client_dir, release=mod_release)
                    if mod.get("register_dll"):
                        add_dll(client_dir, mod["register_dll"])
                    resolved_ver = mod.pop("_resolved_version", None) or latest_ver or "unknown"
                    mods_cfg[mid] = {
                        "enabled":           True,
                        "installed_version": resolved_ver,
                        "installed_files":   written,
                        "ignore_updates":    ignore_upd,
                        "error":             None,
                    }
                    if mid == "dxvk":
                        set_dxvk_notice = True
                    log(f"  \u2713 {mod['name']} installed.")

                elif needs_uninstall:
                    log(f"\nUninstalling {mod['name']}...")
                    uninstall_mod(mod, client_dir)
                    if mod.get("register_dll"):
                        remove_dll(client_dir, mod["register_dll"])
                    mods_cfg[mid] = {
                        "enabled":           False,
                        "installed_version": None,
                        "installed_files":   [],
                        "ignore_updates":    ignore_upd,
                        "error":             None,
                    }
                    log(f"  \u2713 {mod['name']} uninstalled.")

                elif needs_update:
                    log(f"\nUpdating {mod['name']} {installed_ver} \u2192 {latest_ver}...")
                    uninstall_mod(mod, client_dir)
                    written = install_mod(mod, client_dir, release=mod_release)
                    if mod.get("register_dll"):
                        add_dll(client_dir, mod["register_dll"])
                    mods_cfg[mid] = {
                        "enabled":           True,
                        "installed_version": latest_ver,
                        "installed_files":   written,
                        "ignore_updates":    ignore_upd,
                        "error":             None,
                    }
                    if mid == "dxvk":
                        set_dxvk_notice = True
                    log(f"  \u2713 {mod['name']} updated.")

            except Exception as e:
                err = describe_install_error(e)
                log(f"  \u2717 {mod['name']}: {err}")
                mods_cfg[mid] = {
                    "enabled":           False,
                    "installed_version": None,
                    "installed_files":   [],
                    "ignore_updates":    ignore_upd,
                    "error":             err,
                }

        # Merge just the "mods" key into the current on-disk config (which
        # other threads may have written to during this long install), rather
        # than saving our stale whole-config snapshot.
        sorted_mods = dict(sorted(mods_cfg.items(),
                                  key=lambda kv: kv[0].lower()))
        def _merge(c):
            c["mods"] = sorted_mods
            if set_dxvk_notice:
                c["dxvk_notice_pending"] = True
        fresh_cfg  = update_config(_merge)
        fresh_mods = fresh_cfg.get("mods", {})
        # Keep pending checkbox toggles on a targeted single-mod update —
        # they were never applied and would be lost otherwise.
        if only_mod_id is None:
            self._mod_pending_state = {}

        def _do_inplace_update():
            for mod in MODS_REGISTRY:
                mid         = mod["id"]
                state       = fresh_mods.get(mid, {})
                refs        = self._mod_row_vars.get(mid, {})
                if not refs:
                    continue
                has_error   = bool(state.get("error"))
                installed   = bool(state.get("installed_version"))

                if mid not in self._mod_pending_state:
                    refs["enabled"].set(state.get("enabled", False))
                    refs["ignore"].set(state.get("ignore_updates", False))

                live = next((m for m in self._mods_state if m["id"] == mid), {})
                ver  = state.get("installed_version") or live.get("latest_version") or "unknown"
                if "ver_label" in refs:
                    refs["ver_label"].configure(text=f"  {ver}")

                if "name_label" in refs:
                    refs["name_label"].configure(
                        fg=C_ERR if has_error else (C_MOD_HL if installed else C_TEXT))

                if "desc_label" in refs:
                    refs["desc_label"].configure(
                        fg=C_TEXT if state.get("enabled", False) else C_TEXT_DIM)

                if "error_label" in refs:
                    if has_error:
                        refs["error_label"].configure(
                            text=f"  \u26a0  {state['error']}")
                        refs["error_label"].pack(fill="x", pady=(0, self._px(4)))
                    else:
                        refs["error_label"].pack_forget()

                if "update_label" in refs:
                    self._style_mod_action_label(refs["update_label"],
                                                 mod, state, live)

            self._apply_btn.configure(text="Apply", bg=C_PANEL_BDR, fg=C_TEXT)
            self._refresh_apply_btn_visibility()
            self._refresh_mods_badge()
            # Fresh setup chain: once the default mods finished installing,
            # the recommended addons follow (no-op if already initialized).
            self._maybe_install_default_addons()

            # Any mod in an error state (download blocked, API limit, AV
            # deleted the archive, …) — bring the MODS tab up so the error
            # is visible. PLAY stays disabled via _refresh_ready_state.
            if any(bool(s.get("error")) for s in fresh_mods.values()):
                self._switch_tab("MODS")
            self._refresh_ready_state()

        self.after(0, _do_inplace_update)

    # ── addons panel ─────────────────────────────────────────────────────────

    def _build_addons_panel(self):
        outer = tk.Frame(self, bg=C_PANEL,
                         highlightthickness=1,
                         highlightbackground=C_PANEL_BDR,
                         highlightcolor=C_PANEL_BDR)
        self._addons_panel_frame = outer

        top = tk.Frame(outer, bg=C_PANEL)
        top.pack(fill="x", padx=self._px(16), pady=(self._px(4), 0))
        self._addon_filter_var = tk.StringVar()
        self._addon_filter_job = None
        self._addon_filter_var.trace_add(
            "write", self._on_addon_filter_changed)
        ent = tk.Entry(top, textvariable=self._addon_filter_var,
                       bg="#2b2244", fg=C_TEXT, insertbackground=C_GOLD,
                       relief="flat", font=("Segoe UI", 10), width=24,
                       highlightthickness=1,
                       highlightbackground="#4a3c6e",
                       highlightcolor=C_GOLD)
        tk.Label(top, text="⌕", font=("Segoe UI", 18),
                 fg=C_TEXT, bg=C_PANEL).pack(side="right")
        ent.pack(side="right", ipady=self._px(4), padx=(0, self._px(6)))

        legend = tk.Frame(top, bg=C_PANEL)
        legend.pack(side="left")
        tk.Label(legend, text="Addons marked with ",
                 font=("Segoe UI", 10), fg=C_TEXT_DIM,
                 bg=C_PANEL).pack(side="left")
        tk.Label(legend, text="★", font=("Segoe UI", 10),
                 fg=C_GOLD, bg=C_PANEL).pack(side="left")
        tk.Label(legend, text=" are recommended",
                 font=("Segoe UI", 10), fg=C_TEXT_DIM,
                 bg=C_PANEL).pack(side="left")

        list_frame = tk.Frame(outer, bg=C_PANEL)
        list_frame.pack(fill="both", expand=True, padx=(self._px(16), self._px(4)))
        canvas = tk.Canvas(list_frame, bg=C_PANEL, highlightthickness=0)
        sb = SlimScrollbar(list_frame, command=canvas.yview, bg=C_PANEL,
                           width=self._px(10))
        self._wheel_canvases.append(canvas)
        self._addons_canvas = canvas
        self._addons_win    = None
        canvas.bind("<Configure>",
                    lambda e: self._addons_win is not None
                    and canvas.itemconfigure(self._addons_win, width=e.width))
        canvas.configure(yscrollcommand=sb.set)
        sb.pack(side="right", fill="y")
        canvas.pack(side="left", fill="both", expand=True)
        self._reset_addons_inner()

        tk.Frame(outer, bg=C_DIVIDER, height=self._px(1)).pack(
            fill="x", padx=self._px(16), pady=(self._px(4), 0))
        foot = tk.Frame(outer, bg=C_PANEL)
        foot.pack(fill="x", padx=self._px(16), pady=(self._px(8), self._px(12)))
        foot.columnconfigure(0, weight=1)
        foot.columnconfigure(1, weight=1)
        foot.columnconfigure(2, weight=1)

        chk = tk.Label(foot, text="⟳  Check for updates",
                       font=("Segoe UI", 10), fg=C_TEXT_DIM, bg=C_PANEL,
                       cursor="hand2")
        chk.grid(row=0, column=0, sticky="w")
        chk.bind("<Button-1>", lambda e: self._addons_verify(force=True))
        chk.bind("<Enter>", lambda e: chk.configure(fg=C_GOLD))
        chk.bind("<Leave>", lambda e: chk.configure(fg=C_TEXT_DIM))

        add = tk.Label(foot, text="+  Add custom git addon",
                       font=("Segoe UI", 10, "bold"), fg="#d76f9e",
                       bg=C_PANEL, cursor="hand2")
        add.grid(row=0, column=1)
        add.bind("<Button-1>", lambda e: self._open_custom_addon_dialog())
        add.bind("<Enter>", lambda e: add.configure(fg="#eb96ba"))
        add.bind("<Leave>", lambda e: add.configure(fg="#d76f9e"))

        self._addons_right_lbl = tk.Label(foot, text="",
                                          font=("Segoe UI", 10, "bold"),
                                          bg=C_PANEL, cursor="hand2")
        self._addons_right_lbl.grid(row=0, column=2, sticky="e")
        self._addons_right_lbl.bind("<Button-1>",
                                    lambda e: self._addon_update_all())

        self._render_addons()

    # ── MPQ panel ────────────────────────────────────────────────────────────

    def _build_mpq_panel(self):
        outer = tk.Frame(self, bg=C_PANEL,
                         highlightthickness=1,
                         highlightbackground=C_PANEL_BDR,
                         highlightcolor=C_PANEL_BDR)
        self._mpq_panel_frame = outer

        list_frame = tk.Frame(outer, bg=C_PANEL)
        list_frame.pack(fill="both", expand=True,
                        padx=(self._px(16), self._px(4)),
                        pady=(self._px(8), self._px(8)))
        canvas = tk.Canvas(list_frame, bg=C_PANEL, highlightthickness=0)
        sb = SlimScrollbar(list_frame, command=canvas.yview, bg=C_PANEL,
                           width=self._px(10))
        self._wheel_canvases.append(canvas)
        self._mpq_canvas = canvas
        self._mpq_win    = None
        canvas.bind("<Configure>",
                    lambda e: self._mpq_win is not None
                    and canvas.itemconfigure(self._mpq_win, width=e.width))
        canvas.configure(yscrollcommand=sb.set)
        sb.pack(side="right", fill="y")
        canvas.pack(side="left", fill="both", expand=True)

        self._mpq_sections_open = {"INSTALLED": True, "AVAILABLE": True}
        self._mpq_installed_rows = []
        self._mpq_available_rows = list(MPQ_PATCHES)
        self._reset_mpq_inner()
        self._render_mpq()

    def _reset_mpq_inner(self):
        cv  = self._mpq_canvas
        old = getattr(self, "_mpq_inner", None)
        if old is not None:
            old.destroy()
        inner = tk.Frame(cv, bg=C_PANEL)
        inner.bind("<Configure>",
                   lambda e: cv.configure(scrollregion=cv.bbox("all")))
        if self._mpq_win is None:
            self._mpq_win = cv.create_window((0, 0), window=inner, anchor="nw",
                                             width=cv.winfo_width() or 1)
        else:
            cv.itemconfigure(self._mpq_win, window=inner)
        cv.yview_moveto(0)
        self._mpq_inner = inner

    def _scan_mpq_patches(self) -> list:
        """Lettered patch archives (patch-<letter>.mpq, case-insensitive) present in the
        game's Data folder, e.g. Patch-A.mpq / patch-b.MPQ. Sorted by letter."""
        out = self._game_path.get().strip()
        data_dir = os.path.join(out, "Data") if out else ""
        found = []
        if data_dir and os.path.isdir(data_dir):
            for name in os.listdir(data_dir):
                if re.fullmatch(r"patch-[a-z]\.mpq", name, re.IGNORECASE):
                    found.append(name)
        found.sort(key=str.lower)
        return found

    def _mpq_check(self):
        """Scan Data/ for lettered patches; for the ones we know (registry),
        compare the on-disk SHA256 to the server's to flag updates. Feeds the
        INSTALLED/AVAILABLE lists and the tab badge; the sha check runs in the
        background so the list appears immediately."""
        installed_files = self._scan_mpq_patches()
        installed_lc    = {f.lower() for f in installed_files}
        self._mpq_installed_rows = [
            {"file": f, "entry": mpq_patch_for(f), "update": False}
            for f in installed_files]
        self._mpq_available_rows = [
            e for e in MPQ_PATCHES if e["file"].lower() not in installed_lc]
        self._render_mpq()

        out = self._game_path.get().strip()
        data_dir = os.path.join(out, "Data") if out else ""
        known = [r for r in self._mpq_installed_rows if r["entry"]]
        if not (known and data_dir):
            self._mpq_updates_count = 0
            self._draw_nav_tab("MPQ")
            return

        def worker():
            results = {}
            for row in known:
                try:
                    server = fetch_mpq_sha256(row["entry"]["url"])
                    local  = sha256_file(os.path.join(data_dir, row["file"]))
                    results[row["file"]] = (server != local)
                except Exception:
                    results[row["file"]] = False

            def apply():
                count = 0
                for row in self._mpq_installed_rows:
                    if row["file"] in results:
                        row["update"] = results[row["file"]]
                        count += bool(row["update"])
                self._mpq_updates_count = count
                self._draw_nav_tab("MPQ")
                self._render_mpq()
            self.after(0, apply)
        threading.Thread(target=worker, daemon=True).start()

    def _render_mpq(self):
        if not hasattr(self, "_mpq_inner"):
            return
        self._reset_mpq_inner()
        installed = getattr(self, "_mpq_installed_rows", [])
        available = getattr(self, "_mpq_available_rows", [])
        busy = getattr(self, "_mpq_busy", None)

        self._mpq_section_header("INSTALLED", installed)
        if self._mpq_sections_open.get("INSTALLED", True):
            for row in installed:
                entry  = row["entry"]
                name   = entry["name"] if entry else row["file"]
                desc   = entry["description"] if entry else ""
                action = ("Update", entry) if (row["update"] and entry) else None
                self._mpq_row(name, row["file"], desc, action,
                              busy == row["file"])

        self._mpq_section_header("AVAILABLE", available)
        if self._mpq_sections_open.get("AVAILABLE", True):
            for entry in available:
                self._mpq_row(entry["name"], entry["file"],
                              entry["description"], ("Install", entry),
                              busy == entry["file"])

    def _mpq_section_header(self, title: str, rows: list):
        f = self._mpq_inner
        is_open = self._mpq_sections_open.get(title, True)
        hdr = tk.Frame(f, bg=C_PANEL)
        hdr.pack(fill="x", pady=(self._px(10), self._px(2)))
        arrow = tk.Label(hdr, text="▾" if is_open else "▸",
                         font=("Segoe UI", 14, "bold"),
                         fg=C_GOLD, bg=C_PANEL, cursor="hand2", width=2)
        arrow.pack(side="left")
        lbl = tk.Label(hdr, text=title, font=("Segoe UI", 12, "bold"),
                       fg=C_GOLD, bg=C_PANEL, cursor="hand2")
        lbl.pack(side="left")
        tk.Label(hdr, text=f"  {len(rows)}", font=("Segoe UI", 10),
                 fg=C_TEXT_DIM, bg=C_PANEL).pack(side="left")

        def toggle(_e=None, t=title):
            self._mpq_sections_open[t] = \
                not self._mpq_sections_open.get(t, True)
            self._render_mpq()
        arrow.bind("<Button-1>", toggle)
        lbl.bind("<Button-1>", toggle)

        if is_open and not rows:
            tk.Label(f, text="Nothing here.", font=("Segoe UI", 10),
                     fg=C_TEXT_DIM, bg=C_PANEL).pack(anchor="w",
                                                     padx=self._px(8))

    def _mpq_row(self, name, filename, description, action, busy):
        """One patch row: name (and filename), an Install/Update button or a
        'Downloading…' label, and the description underneath. `action` is
        (label, registry_entry) or None."""
        f = self._mpq_inner
        box = tk.Frame(f, bg=C_PANEL)
        box.pack(fill="x", pady=self._px(4))
        top = tk.Frame(box, bg=C_PANEL)
        top.pack(fill="x")
        tk.Label(top, text=name, font=("Segoe UI", 11, "bold"),
                 fg=C_TEXT, bg=C_PANEL, anchor="w").pack(side="left",
                                                         padx=self._px(8))
        if filename and filename.lower() != name.lower():
            tk.Label(top, text=f"  {filename}", font=("Segoe UI", 9),
                     fg=C_TEXT_DIM, bg=C_PANEL).pack(side="left")
        if busy:
            tk.Label(top, text="Downloading…", font=("Segoe UI", 10),
                     fg=C_TEXT_DIM, bg=C_PANEL).pack(side="right",
                                                     padx=self._px(8))
        elif action:
            label, entry = action
            btn = tk.Label(top, text=label, font=("Segoe UI", 10, "bold"),
                           fg="#000", bg=C_GOLD, cursor="hand2",
                           padx=self._px(12), pady=self._px(2))
            btn.pack(side="right", padx=self._px(8))
            btn.bind("<Button-1>", lambda e, en=entry: self._mpq_install(en))
            btn.bind("<Enter>", lambda e: btn.configure(bg=C_GOLD_LT))
            btn.bind("<Leave>", lambda e: btn.configure(bg=C_GOLD))
        if description:
            tk.Label(box, text=description, font=("Segoe UI", 10),
                     fg=C_TEXT_DIM, bg=C_PANEL, anchor="w",
                     wraplength=self._px(620), justify="left").pack(
                     fill="x", padx=self._px(8), pady=(self._px(2), 0))

    def _mpq_install(self, entry):
        if getattr(self, "_mpq_busy", None):
            return                                   # one download at a time
        out = self._game_path.get().strip()
        if not out:
            self._log_line("Set the game folder first.\n", "err")
            return
        data_dir = os.path.join(out, "Data")
        self._mpq_busy = entry["file"]
        self._render_mpq()
        self._log_line(f"\nDownloading {entry['name']}…\n", "acct")

        def worker():
            err = None
            try:
                download_mpq_patch(entry, data_dir)
            except Exception as e:
                err = str(e)

            def done():
                self._mpq_busy = None
                if err:
                    self._log_line(f"✗  {entry['name']} failed: {err}\n", "err")
                else:
                    self._log_line(f"✓  {entry['name']} installed.\n", "ok")
                self._mpq_check()                    # re-scan + re-check + badge
            self.after(0, done)
        threading.Thread(target=worker, daemon=True).start()

    # ── addons engine (app side) ─────────────────────────────────────────────

    def _addons_verify(self, force=False, remote_checks=True):
        """Scan Interface/AddOns, match against the catalog, and check every
        tracked addon's remote commit sha (config-cached). With
        remote_checks=False the scan is guaranteed network-free: shas come
        from the cache only (used for post-install/update refreshes)."""
        if self._addons_busy:
            return
        # A recent verify result is already rendered — plain tab switches
        # within the TTL don't need a rescan or a rebuild at all.
        if (not force and self._addons_status["state"] == "done"
                and (time.time() - self._addons_verified_ts)
                < ADDONS_VERIFY_TTL):
            return
        client = self._game_path.get().strip()
        self._addons_busy = True
        had_content = bool(self._addons_status["addons"]
                           or self._addons_status["available"])
        self._addons_status = {**self._addons_status, "state": "verifying"}
        if had_content:
            # Keep showing the existing list while checking in background.
            self._refresh_addons_footer()
        else:
            self._render_addons()

        def worker():
            try:
                catalog = fetch_addons_catalog(force=force)
            except Exception:
                # offline — fall back to whatever the config still holds
                catalog = (load_config().get("addons_catalog_cache", {})
                           .get("catalog") or [])

            available = [{"folder": a.get("name"), "status": "available",
                          "git": a.get("git"), "branch": a.get("branch"),
                          "ref": a.get("ref"), "toc": a.get("toc") or {},
                          "description": a.get("description"), "error": None}
                         for a in catalog
                         if a.get("name") and a["name"] not in BLOCKED_ADDONS]

            # Curated recommendations: apply git-URL overrides on top of the
            # catalog, and synthesize entries for recommended addons the
            # catalog doesn't carry (or has renamed). Overridden forks may
            # use a different default branch, so branch/ref are reset.
            by_name = {a["folder"]: a for a in available}
            for name, override in RECOMMENDED_ADDONS.items():
                rec = by_name.get(name)
                if rec is None:
                    available.append(
                        {"folder": name, "status": "available",
                         "git": override, "branch": None, "ref": None,
                         "toc": {}, "description": None, "error": None})
                elif not _same_git_repo(rec.get("git"), override):
                    rec.update(git=override, branch=None, ref=None)

            addons = {}
            records = load_config().get("addons", {})
            ap = addons_path(client) if client else ""
            if ap and os.path.isdir(ap):
                for name in sorted(os.listdir(ap)):
                    if name.startswith(("Blizzard_", "Turtle_")):
                        continue
                    dirp = os.path.join(ap, name)
                    if not os.path.isdir(dirp):
                        continue
                    rec = {"folder": name, "status": "unknown", "git": None,
                           "branch": None, "ref": None, "toc": {},
                           "description": None, "error": None}
                    toc_path = os.path.join(dirp, f"{name}.toc")
                    if not os.path.exists(toc_path):
                        rec.update(status="invalid",
                                   error="Missing .toc file")
                        addons[name] = rec
                        continue
                    rec["toc"] = read_toc_file(toc_path)
                    avail = next((a for a in available
                                  if a["folder"] == name), None)
                    if avail:
                        rec["description"] = avail["description"]
                    saved = records.get(name)
                    override = RECOMMENDED_ADDONS.get(name)
                    if (saved and saved.get("git") and override
                            and not saved.get("custom")
                            and not _same_git_repo(saved["git"], override)):
                        # Installed from a different repo than the curated fork
                        # — offer an update that migrates to the fork. A
                        # user-added custom addon (saved["custom"]) is left as
                        # the user chose it, even when its name matches a
                        # recommended addon.
                        rec.update(git=override, branch=None, ref=None,
                                   status="outOfDate")
                    elif saved and saved.get("git"):
                        rec.update(git=saved.get("git"),
                                   branch=saved.get("branch"),
                                   ref=saved.get("ref"),
                                   custom=saved.get("custom", False))
                        if remote_checks:
                            remote = addon_remote_sha(
                                rec["git"], rec["branch"], rec["ref"],
                                force=force)
                        else:
                            remote = addon_cached_sha(
                                rec["git"], rec["branch"], rec["ref"])
                            if remote is None:
                                # no cached answer — assume current rather
                                # than hitting the network
                                remote = saved.get("sha")
                        if remote is None:
                            rec.update(status="invalid",
                                       error="Failed to verify")
                        elif remote == saved.get("sha"):
                            rec["status"] = "upToDate"
                        else:
                            rec["status"] = "outOfDate"
                    elif avail:
                        # Known catalog addon installed outside the updater —
                        # offer to take it over via a fresh install.
                        rec.update(git=avail["git"], branch=avail["branch"],
                                   ref=avail["ref"], status="outOfDate")
                    addons[name] = rec

            # Overlay install failures from this session: the rescan drops
            # them (a failed install leaves no folder on disk), so re-attach
            # errors to the matching available row — or synthesize one for a
            # failed custom addon. Errors for now-installed folders are stale
            # and dropped.
            for folder in [f for f in self._addon_errors if f in addons]:
                self._addon_errors.pop(folder, None)
            by_name = {a["folder"]: a for a in available}
            for folder, info in self._addon_errors.items():
                rec = by_name.get(folder)
                if rec is None:
                    rec = {"folder": folder, "status": "available",
                           "git": info.get("git"), "branch": None,
                           "ref": None, "toc": {}, "description": None,
                           "error": None}
                    available.append(rec)
                rec["error"] = info["error"]

            def done():
                changed = (addons != self._addons_status["addons"]
                           or available != self._addons_status["available"])
                self._addons_status = {"state": "done", "addons": addons,
                                       "available": available}
                self._addons_verified_ts = time.time()
                self._addons_busy = False
                self._refresh_addons_badge()
                if changed:
                    self._render_addons()
                else:
                    self._refresh_addons_footer()
            self.after(0, done)
        threading.Thread(target=worker, daemon=True).start()

    def _addon_apply(self, recs):
        """Install/update the given addon records sequentially."""
        client = self._game_path.get().strip()
        if not client or self._addons_busy or not recs:
            return
        self._addons_busy = True
        self._addons_installing = True
        for rec in recs:
            rec["status"] = "downloading"
            self._addons_status["addons"].setdefault(rec["folder"], rec)
        self._render_addons()
        # PLAY is inactive while addons download/install, same as for mods.
        self._set_btn_busy("Installing…")
        self._status_var.set("Downloading addons…")

        def worker():
            for rec in recs:
                self.after(0, lambda n=rec["folder"]:
                           self._status_var.set(f"Installing {n}…"))
                try:
                    if not rec.get("git") or not is_allowed_git_url(rec["git"]):
                        raise RuntimeError("Addon URL is not from an "
                                           "allowed git host")
                    sha = addon_remote_sha(rec["git"], rec.get("branch"),
                                           rec.get("ref"), force=True,
                                           raise_errors=True)
                    if not sha:
                        raise RuntimeError("Could not resolve remote commit")
                    install_addon_files(client, rec["folder"], rec["git"], sha)
                    if rec["folder"] == "pfUI":
                        patch_pfui_default_profile(client)
                    record = {"git": rec["git"], "branch": rec.get("branch"),
                              "ref": rec.get("ref"), "sha": sha}
                    if rec.get("custom"):
                        record["custom"] = True
                    update_config(lambda c, f=rec["folder"], r=record:
                                  c.setdefault("addons", {}).__setitem__(f, r))
                    self._addon_errors.pop(rec["folder"], None)
                    log(f"  ✓ Addon {rec['folder']} installed.")
                except Exception as e:
                    err = describe_install_error(e)
                    log(f"  ✗ Addon {rec['folder']}: {err}")
                    rec.update(status="invalid", error=err)
                    self._addon_errors[rec["folder"]] = {
                        "error": err, "git": rec.get("git")}

            def done():
                self._addons_busy = False
                self._addons_installing = False
                self._addons_verified_ts = 0.0   # make the re-verify run
                self._refresh_ready_state()      # PLAY active again
                # Cache-only refresh: the install itself already resolved and
                # cached the shas — no further API requests are needed.
                self._addons_verify(remote_checks=False)
            self.after(0, done)
        threading.Thread(target=worker, daemon=True).start()

    def _addon_update_all(self):
        recs = [r for r in self._addons_status["addons"].values()
                if r["status"] == "outOfDate"]
        self._addon_apply(recs)

    def _addon_remove(self, folder: str):
        from tkinter import messagebox
        if not messagebox.askyesno(
                "Remove addon",
                f"Delete {folder} and all of its files?"):
            return
        client = self._game_path.get().strip()
        if not client or self._addons_busy:
            return
        try:
            dirp = os.path.join(addons_path(client), folder)
            if os.path.isdir(dirp):
                shutil.rmtree(dirp)
            update_config(lambda c: c.get("addons", {}).pop(folder, None))
            self._log_line(f"Removed addon {folder}\n", "dim")
        except Exception as e:
            self._log_line(f"Failed to remove addon {folder}: {e}\n", "err")
        self._addons_status["addons"].pop(folder, None)
        self._addon_errors.pop(folder, None)
        self._refresh_addons_badge()
        self._render_addons()

    def _open_custom_addon_dialog(self):
        if self._settings_overlay is not None:
            return
        ov = tk.Frame(self, bg="#0a0a0e")
        ov.place(x=0, y=0, width=WIN_W, height=WIN_H)
        ov.bind("<Button-1>", lambda e: self._close_settings())
        self._settings_overlay = ov
        self.bind("<Escape>", lambda e: self._close_settings())

        # Same purple-dark theme as the Settings modal.
        P_BG, P_HDR, P_BDR, P_INP = C_PANEL, C_HDR, C_PANEL_BDR, "#0f0b16"
        MW, MH = self._px(560), self._px(230)
        panel = tk.Frame(ov, bg=P_BG, highlightthickness=1,
                         highlightbackground=P_BDR, highlightcolor=P_BDR)
        panel.place(x=(WIN_W - MW) // 2, y=(WIN_H - MH) // 2 - self._px(20),
                    width=MW, height=MH)

        hdr = tk.Frame(panel, bg=P_HDR, height=self._px(46))
        hdr.pack(fill="x")
        hdr.pack_propagate(False)
        tk.Label(hdr, text="ADD CUSTOM GIT ADDON",
                 font=("Segoe UI", 13, "bold"),
                 fg=C_PURPLE, bg=P_HDR).pack(side="left", padx=self._px(18))
        x_btn = tk.Label(hdr, text="✕", font=("Segoe UI", 12),
                         fg=C_TEXT_DIM, bg=P_HDR, cursor="hand2")
        x_btn.pack(side="right", padx=self._px(16))
        x_btn.bind("<Button-1>", lambda e: self._close_settings())
        x_btn.bind("<Enter>",    lambda e: x_btn.configure(fg=C_TEXT))
        x_btn.bind("<Leave>",    lambda e: x_btn.configure(fg=C_TEXT_DIM))
        tk.Frame(panel, bg=P_BDR, height=self._px(1)).pack(fill="x")

        body = tk.Frame(panel, bg=P_BG)
        body.pack(fill="both", expand=True, padx=self._px(22),
                  pady=(self._px(16), self._px(12)))
        tk.Label(body, text="REPOSITORY URL",
                 font=("Segoe UI", 10, "bold"),
                 fg=C_GOLD, bg=P_BG).pack(anchor="w")
        url_var = tk.StringVar()
        tk.Entry(body, textvariable=url_var, bg=P_INP, fg=C_TEXT,
                 insertbackground=C_GOLD, relief="flat", font=FONT_MONO,
                 highlightthickness=1, highlightbackground=P_BDR,
                 highlightcolor=C_GOLD).pack(fill="x", ipady=self._px(7),
                                             pady=(self._px(6), self._px(6)))
        tk.Label(body,
                 text="Allowed hosts: " + ", ".join(ADDON_GIT_HOSTS),
                 font=("Segoe UI", 9), fg=C_TEXT_DIM, bg=P_BG).pack(anchor="w")
        err = tk.Label(body, text="", font=("Segoe UI", 9),
                       fg=C_ERR, bg=P_BG)
        err.pack(anchor="w")

        def submit():
            url = url_var.get().strip().rstrip("/")
            if url.endswith(".git"):
                url = url[:-4]
            if not is_allowed_git_url(url):
                err.configure(text="URL must be https from an allowed host.")
                return
            folder = url.rsplit("/", 1)[-1]
            if not folder or folder in (".", "..") or "\\" in folder:
                err.configure(text="Could not derive addon folder name.")
                return
            self._close_settings()
            self._log_line(f"\nInstalling custom addon {folder}…\n", "acct")
            self._addon_apply([{"folder": folder, "status": "available",
                                "git": url, "branch": None, "ref": None,
                                "toc": {}, "description": None,
                                "error": None, "custom": True}])

        btn = tk.Label(body, text="Install", font=("Segoe UI", 11, "bold"),
                       fg=C_TEXT, bg=P_BDR, cursor="hand2",
                       padx=self._px(16), pady=self._px(7))
        btn.pack(anchor="e", pady=(self._px(8), 0))
        btn.bind("<Button-1>", lambda e: submit())
        btn.bind("<Enter>", lambda e: btn.configure(bg=C_GOLD, fg="#000"))
        btn.bind("<Leave>", lambda e: btn.configure(bg=P_BDR, fg=C_TEXT))

    # ── addons rendering ─────────────────────────────────────────────────────

    def _reset_addons_inner(self):
        """Replace the whole rows container with a fresh frame. A single
        destroy() tears the old subtree down inside Tk (C code) — far faster
        than destroying hundreds of row widgets one by one from Python."""
        cv  = self._addons_canvas
        old = getattr(self, "_addons_inner", None)
        if old is not None:
            old.destroy()
        inner = tk.Frame(cv, bg=C_PANEL)
        inner.bind("<Configure>",
                   lambda e: cv.configure(scrollregion=cv.bbox("all")))
        if self._addons_win is None:
            self._addons_win = cv.create_window((0, 0), window=inner,
                                                anchor="nw",
                                                width=cv.winfo_width() or 1)
        else:
            cv.itemconfigure(self._addons_win, window=inner)
        cv.yview_moveto(0)
        self._addons_inner = inner

    def _on_addon_filter_changed(self, *_args):
        """Debounce search input — re-render once typing pauses, not on
        every keystroke."""
        if self._addon_filter_job is not None:
            self.after_cancel(self._addon_filter_job)
        self._addon_filter_job = self.after(250, self._apply_addon_filter)

    def _apply_addon_filter(self):
        self._addon_filter_job = None
        self._render_addons()

    def _render_addons(self):
        """Rebuild the addons list. Rows are created in small batches on the
        Tk event loop so a large catalog doesn't freeze the UI."""
        if not hasattr(self, "_addons_inner"):
            return
        self._addons_render_gen = getattr(self, "_addons_render_gen", 0) + 1
        gen = self._addons_render_gen
        self._reset_addons_inner()

        st  = self._addons_status
        flt = self._addon_filter_var.get().strip().lower()
        flt_compact = flt.replace(" ", "")

        def matches(rec):
            if not flt:
                return True
            title = strip_wow_colors((rec.get("toc") or {}).get("Title") or "")
            hay = f"{rec['folder']} {title}".lower()
            # Space-insensitive both ways: "sell value" finds SellValue,
            # "sellvalue" finds "Sell Value".
            return flt in hay or flt_compact in hay.replace(" ", "")

        def keep(lst):
            lst = sorted(lst, key=lambda r: r["folder"].lower())
            return [r for r in lst if matches(r)]

        installed = keep(st["addons"].values())
        # Recommended addons are mixed into Available and marked with a ★
        # badge. Sort recommended first so they surface at the top of the list.
        available = keep(a for a in st["available"]
                         if a["folder"] not in st["addons"])
        available.sort(key=lambda a: (a["folder"] not in RECOMMENDED_ADDONS,
                                      a["folder"].lower()))

        work = []
        for title, rows in (("INSTALLED", installed),
                            ("AVAILABLE", available)):
            work.append(("header", title, rows))
            if self._addon_sections_open.get(title, True):
                work.extend(("row", rec) for rec in rows)
        self._addons_build_queue = work
        self._refresh_addons_footer()
        self._addons_build_step(gen)

    def _addons_build_step(self, gen: int):
        """Create up to one batch of queued headers/rows, then yield to the
        event loop; abandons the queue if a newer render has started."""
        if gen != self._addons_render_gen:
            return
        queue = self._addons_build_queue
        built = 0
        while queue and built < 14:
            item = queue.pop(0)
            if item[0] == "header":
                self._addon_section_header(item[1], item[2])
            else:
                self._addon_row(item[1])
            built += 1
        if queue:
            self.after(1, lambda: self._addons_build_step(gen))

    def _addon_section_header(self, title: str, rows: list):
        f = self._addons_inner
        is_open = self._addon_sections_open.get(title, True)

        hdr = tk.Frame(f, bg=C_PANEL)
        hdr.pack(fill="x", pady=(self._px(10), self._px(2)))
        arrow = tk.Label(hdr, text="▾" if is_open else "▸",
                         font=("Segoe UI", 14, "bold"),
                         fg=C_GOLD, bg=C_PANEL, cursor="hand2", width=2)
        arrow.pack(side="left")
        lbl = tk.Label(hdr, text=title,
                       font=("Segoe UI", 12, "bold"),
                       fg=C_GOLD, bg=C_PANEL, cursor="hand2")
        lbl.pack(side="left")
        tk.Label(hdr, text=f"  {len(rows)}", font=("Segoe UI", 10),
                 fg=C_TEXT_DIM, bg=C_PANEL).pack(side="left")

        def toggle(_e=None, t=title):
            self._addon_sections_open[t] = \
                not self._addon_sections_open.get(t, True)
            self._render_addons()
        arrow.bind("<Button-1>", toggle)
        lbl.bind("<Button-1>", toggle)

        if is_open and not rows:
            msg = ("Verifying…" if self._addons_status["state"] == "verifying"
                   else "Nothing here.")
            tk.Label(f, text=msg, font=("Segoe UI", 10), fg=C_TEXT_DIM,
                     bg=C_PANEL).pack(anchor="w", padx=self._px(8))

    def _addon_row(self, rec: dict):
        f = self._addons_inner
        installed = rec["folder"] in self._addons_status["addons"]
        toc = rec.get("toc") or {}

        warnings = []
        if toc.get("Interface") and toc["Interface"] != "11200":
            warnings.append(f"Made for client {toc['Interface']}")
        # pfUI bundles its own modules, so its .toc dependencies aren't real
        # missing addons — never warn about them.
        if installed and rec["folder"] != "pfUI":
            deps = [d.strip() for d in
                    (toc.get("Dependencies") or "").replace(";", ",").split(",")
                    if d.strip()]
            missing = [d for d in deps
                       if d not in self._addons_status["addons"]]
            if missing:
                warnings.append("Missing deps: " + ", ".join(missing))

        row = tk.Frame(f, bg=C_PANEL)
        row.pack(fill="x", pady=self._px(3))


        # right side first so it stays pinned to the edge
        if installed:
            # Trash can drawn as canvas shapes (handle, lid, tapered body
            # with slats) — same fixed-size approach as the download arrow.
            rm = tk.Canvas(row, width=self._px(20), height=self._px(18),
                           bg=C_PANEL, highlightthickness=0, cursor="hand2")
            rm.pack(side="right", padx=(self._px(8), self._px(2)))
            rm.create_rectangle(*self._px(8, 2, 12, 4), fill="#8a4a4a",
                                outline="", tags="trash")
            rm.create_rectangle(*self._px(4, 4, 16, 6), fill="#8a4a4a",
                                outline="", tags="trash")
            rm.create_polygon(*self._px(5, 8, 15, 8, 14, 16, 6, 16),
                              fill="#8a4a4a", outline="", tags="trash")
            for x in (8, 10, 12):
                rm.create_line(*self._px(x, 10, x, 14), fill=C_PANEL)
            rm.bind("<Button-1>",
                    lambda e, n=rec["folder"]: self._addon_remove(n))
            rm.bind("<Enter>", lambda e, c=rm:
                    c.itemconfigure("trash", fill=C_ERR))
            rm.bind("<Leave>", lambda e, c=rm:
                    c.itemconfigure("trash", fill="#8a4a4a"))
        else:
            # Download arrow drawn as a polygon — exact size and centering,
            # independent of any font, without inflating the row height.
            dl = tk.Canvas(row, width=self._px(20), height=self._px(18),
                           bg=C_PANEL, highlightthickness=0, cursor="hand2")
            dl.pack(side="right", padx=(self._px(8), self._px(2)))
            dl_item = dl.create_polygon(
                *self._px(8, 3, 12, 3, 12, 9, 16, 9, 10, 15, 4, 9, 8, 9),
                fill=C_OK, outline="")
            dl.bind("<Button-1>",
                    lambda e, r=rec: self._addon_apply([dict(r)]))
            dl.bind("<Enter>", lambda e, c=dl, i=dl_item:
                    c.itemconfigure(i, fill="#8fdf8e"))
            dl.bind("<Leave>", lambda e, c=dl, i=dl_item:
                    c.itemconfigure(i, fill=C_OK))

        # Repo link on the right (like the Mods tab), between the status text
        # and the install/remove icon.
        if rec.get("git"):
            repo_url = rec["git"][:-4] if rec["git"].endswith(".git") \
                else rec["git"]
            lnk = tk.Label(row, text="⧉", font=("Segoe UI", 10),
                           fg=C_TEXT_DIM, bg=C_PANEL, cursor="hand2")
            lnk.pack(side="right", padx=(self._px(4), self._px(2)))
            lnk.bind("<Button-1>", lambda e, u=repo_url: self._open_url(u))
            lnk.bind("<Enter>", lambda e, w=lnk: w.configure(fg=C_GOLD))
            lnk.bind("<Leave>", lambda e, w=lnk: w.configure(fg=C_TEXT_DIM))

        status = rec["status"]
        if status == "downloading":
            tk.Label(row, text="downloading…", font=("Segoe UI", 10),
                     fg=C_TEXT_DIM, bg=C_PANEL).pack(side="right", padx=self._px(4))
        elif status == "invalid" or rec.get("error"):
            # Short marker on the right; the full reason gets its own line
            # under the row (long messages would squeeze the description).
            tk.Label(row, text="⛔ Addon error", font=("Segoe UI", 10),
                     fg=C_ERR, bg=C_PANEL).pack(side="right", padx=self._px(4))
        elif status == "outOfDate" and installed:
            upd = tk.Label(row, text="Update", font=("Segoe UI", 10, "bold"),
                           fg=C_GOLD, bg=C_PANEL, cursor="hand2")
            upd.pack(side="right", padx=self._px(4))
            upd.bind("<Button-1>",
                     lambda e, r=rec: self._addon_apply([r]))
            upd.bind("<Enter>", lambda e, w=upd: w.configure(fg=C_GOLD_LT))
            upd.bind("<Leave>", lambda e, w=upd: w.configure(fg=C_GOLD))
        elif warnings:
            tk.Label(row, text=f"⚠ {warnings[0]}", font=("Segoe UI", 10),
                     fg="#d4b43c", bg=C_PANEL).pack(side="right", padx=self._px(4))
        elif status == "upToDate":
            tk.Label(row, text="Up to date", font=("Segoe UI", 10),
                     fg=C_TEXT_DIM, bg=C_PANEL).pack(side="right", padx=self._px(4))
        elif status == "unknown":
            tk.Label(row, text="Not versioned", font=("Segoe UI", 10),
                     fg=C_TEXT_DIM, bg=C_PANEL).pack(side="right", padx=self._px(4))

        # name (WoW colour codes honoured) + repo link
        name_f = tk.Frame(row, bg=C_PANEL, width=self._px(250))
        name_f.pack(side="left", fill="y")
        name_f.pack_propagate(False)
        # Gold ★ badge for recommended addons; fixed-width slot keeps the
        # titles aligned whether or not the star is present.
        is_recommended = rec["folder"] in RECOMMENDED_ADDONS
        star = tk.Label(name_f, text="★" if is_recommended else "",
                        font=("Segoe UI", 9), fg=C_GOLD, bg=C_PANEL,
                        width=2, anchor="w")
        star.pack(side="left")
        if is_recommended:
            self._add_tooltip(star, "Recommended addon")
        title = toc.get("Title") or rec["folder"]
        for seg, col in parse_wow_colored(title)[:6]:
            tk.Label(name_f, text=seg, font=("Segoe UI", 10, "bold"),
                     fg=col or C_TEXT, bg=C_PANEL).pack(side="left")

        desc = strip_wow_colors(toc.get("Notes")
                                or rec.get("description") or "")
        tk.Label(row, text=desc, font=("Segoe UI", 10), fg=C_TEXT_DIM,
                 bg=C_PANEL, wraplength=self._px(430), justify="left",
                 anchor="w").pack(side="left", fill="x", expand=True)

        if rec.get("error"):
            tk.Label(f, text=f"  ⚠  {rec['error']}",
                     font=("Segoe UI", 9), fg=C_ERR, bg=C_PANEL,
                     wraplength=self._px(840), justify="left",
                     anchor="w").pack(fill="x", pady=(0, self._px(3)))

        tk.Frame(f, bg=C_DIVIDER, height=self._px(1)).pack(
            fill="x", pady=(self._px(3), 0))

    def _refresh_addons_badge(self):
        count = sum(1 for r in self._addons_status["addons"].values()
                    if r["status"] == "outOfDate")
        if count != self._addon_updates_count:
            self._addon_updates_count = count
            self._draw_nav_tab("ADDONS")

    def _refresh_addons_footer(self):
        lbl = self._addons_right_lbl
        st  = self._addons_status
        if st["state"] == "verifying" or self._addons_busy:
            lbl.configure(text="Checking…", fg=C_TEXT_DIM, cursor="arrow")
        elif any(r["status"] == "outOfDate"
                 for r in st["addons"].values()):
            lbl.configure(text="Update all", fg=C_OK, cursor="hand2")
        else:
            lbl.configure(text="Everything up to date", fg=C_TEXT_DIM,
                          cursor="arrow")

    # ── footer ────────────────────────────────────────────────────────────────

    def _build_footer(self):
        foot = tk.Frame(self, bg=C_BG, height=FOOT_H)
        foot.place(x=0, y=WIN_H - FOOT_H, width=WIN_W, height=FOOT_H)

        # Bottom-left column: status message on top, PLAY/UPDATE button in
        # the middle, client version at the bottom (with a bottom margin so
        # the content doesn't sit flush against the window edge).
        left = tk.Frame(foot, bg=C_BG)
        left.place(x=self._px(40), y=self._px(6))

        self._status_var = tk.StringVar(value="Ready to update")
        tk.Label(left, textvariable=self._status_var,
                 font=("Segoe UI", 10, "bold"),
                 fg=C_TEXT, bg=C_BG, width=26, anchor="w").pack(anchor="w")

        # Thin halo frame around the button gives a soft glow that follows
        # the button state (gold for UPDATE, green for PLAY).
        self._btn_mode = "update"
        self._btn_glow = tk.Frame(left, bg="#4a3812")
        self._btn_glow.pack(anchor="w", pady=(self._px(6), self._px(6)))
        self._upd_btn = tk.Label(self._btn_glow, text="UPDATE",
                                 font=("Segoe UI", 11, "bold"),
                                 fg="#ffffff", bg=C_GOLD,
                                 cursor="hand2",
                                 width=14, pady=self._px(7),
                                 anchor="center")
        self._upd_btn.pack(padx=self._px(3), pady=self._px(3))
        self._upd_btn.bind("<Button-1>", lambda e: self._btn_click())
        self._upd_btn.bind("<Enter>",    lambda e: self._btn_hover(True))
        self._upd_btn.bind("<Leave>",    lambda e: self._btn_hover(False))

        self._client_ver_var = tk.StringVar(value="")
        tk.Label(left, textvariable=self._client_ver_var,
                 font=FONT_VER, fg=C_TEXT_DIM, bg=C_BG).pack(
                 anchor="w", pady=(0, self._px(36)))

        pb_frame = tk.Frame(foot, bg=C_BG)
        pb_frame.place(x=self._px(250), y=0,
                       width=WIN_W - self._px(250) - self._px(40), height=FOOT_H)

        self._pb_canvas = tk.Canvas(pb_frame,
                                    height=self._px(6), bg=C_BG,
                                    highlightthickness=0)
        self._pb_canvas.pack(fill="x", side="bottom", padx=0,
                             ipady=0, pady=(0, self._px(56)))
        self._pb_width  = WIN_W - self._px(250) - self._px(40)
        self._pb_val    = 0.0

        self._prog_label_var = tk.StringVar(value="")
        tk.Label(pb_frame, textvariable=self._prog_label_var,
                 font=("Segoe UI", 10), fg=C_TEXT, bg=C_BG).pack(
                 side="bottom", pady=(0, self._px(6)))

        tk.Label(foot, text=f"v{UPDATER_VERSION}",
                 font=("Courier New", 8),
                 fg="#555560", bg=C_BG).place(relx=1.0, rely=1.0,
                                              x=self._px(-10), y=self._px(-6),
                                              anchor="se")

        # Align the progress bar's bottom edge exactly with the PLAY/UPDATE
        # button's bottom edge once real geometry is known.
        def _align_pb():
            self.update_idletasks()
            gap = (foot.winfo_rooty() + FOOT_H) - (
                self._btn_glow.winfo_rooty() + self._btn_glow.winfo_height())
            if gap > 0:
                self._pb_canvas.pack_configure(pady=(0, gap))
        self.after(60, _align_pb)

    def _draw_progress(self, value: float):
        self._pb_val = max(0.0, min(1.0, value))
        c = self._pb_canvas
        w = self._pb_width
        c.delete("all")
        if not self._running:
            return
        c.create_rectangle(0, 0, w, self._px(6), fill="#1e1e26", outline="")
        filled = int(w * self._pb_val)
        if filled > 0:
            for x in range(filled):
                t     = x / max(filled - 1, 1)
                r_val = int(0xc8 + t * (0xe8 - 0xc8))
                g_val = int(0x92 + t * (0xb8 - 0x92))
                b_val = int(0x2a + t * (0x4b - 0x2a))
                col   = f"#{r_val:02x}{g_val:02x}{b_val:02x}"
                c.create_line(x, 0, x, self._px(6), fill=col)

    # ── helpers ───────────────────────────────────────────────────────────────

    def _game_folder_changed(self, new_val: str):
        """Wipe all state tied to the previous game folder — the folder-scoped
        config (mods/addons install records) and session TTLs/badges — and
        point everything at new_val. Called from _close_settings when the user
        has switched to a different folder."""
        if os.path.exists(os.path.join(new_val, "WoW.exe")):
            remove_wdb(new_val)

        # Wipe folder-scoped config and set the new path in one atomic merge.
        # This also re-arms the default-mods / recommended-addons auto-install.
        def _wipe(c):
            c["out_dir"] = new_val
            for k in ("mods", "addons"):
                c.pop(k, None)
        self._cfg = update_config(_wipe)

        self._mod_pending_state = {}
        self._default_mods_install_started = False
        self._default_addons_install_started = False
        self._client_ready = False

        # Reset session-level state so nothing from the previous folder is
        # served from memory: addons verify + rendered list, news timers, badges.
        self._addons_verified_ts = 0.0
        self._addons_status = {"state": "idle", "addons": {}, "available": []}
        self._addon_errors = {}
        self._feat_ts = 0.0
        self._patch_ts = 0.0
        self._mod_updates_count = 0
        self._addon_updates_count = 0
        self._mpq_updates_count = 0
        self._mpq_installed_rows = []
        self._mpq_available_rows = list(MPQ_PATCHES)
        self._draw_nav_tab("MODS")
        self._draw_nav_tab("ADDONS")
        self._draw_nav_tab("MPQ")
        self._render_addons()
        self._render_mpq()

        self._log_line("\nGame folder changed — state reset.\n", "acct")

    def _set_pending_reconcile(self, mode):
        """Set the pending-reconcile mode (None / 'full' / 'keep-config') and
        persist it, so a reconcile offered but not applied before quitting is
        still pending next launch."""
        self._pending_reconcile = mode or None
        self._cfg = update_config(
            lambda c: c.__setitem__("pending_reconcile", self._pending_reconcile))

    def _offer_reconcile(self):
        """Surface the Update button for the pending reconcile (mode already
        set) WITHOUT running a verify first. Clicking Update then reconciles:
        an integrity check + WoW.exe re-patch (+ a fresh Config.wtf when the
        mode is 'full') — meaningful even when the game files are already
        intact."""
        self._running = False
        self._client_ready = False
        self._status_var.set("Update available!")
        self._set_btn_update()

    def _prompt_av_exclusion(self):
        """Ask whether to add the current game folder to Windows Defender
        exclusions (some mods can be mistakenly flagged by antivirus)."""
        from tkinter import messagebox
        if messagebox.askyesno(
                "Game folder changed",
                "It is highly recommended to add the game folder to your "
                "antivirus exclusions. Antivirus software may incorrectly "
                "detect some mods as threats and prevent them from being "
                "downloaded or installed properly.\n\n"
                "Do you want to add the game folder to Defender exclusions?",
                parent=self):
            self._allow_through_antivirus()

    def _render_log(self, msg: str, tag: str = ""):
        """Normalize a raw log message (ensure a trailing newline, auto-tag
        when untagged) and append it to the log panel. Main thread only."""
        line = msg if msg.endswith("\n") else msg + "\n"
        if not tag:
            ml = line.lower()
            if "✓" in line or "success" in ml or "complete" in ml or "up to date" in ml:
                tag = "ok"
            elif "✗" in line or "error" in ml or "fail" in ml or "mismatch" in ml:
                tag = "err"
            elif line.strip().startswith("["):
                tag = "acct"
        self._log_line(line, tag)

    def _log_line(self, text: str, tag: str = ""):
        self._log_buffer.append((text, tag))
        txt = self._logwin_text
        if txt is not None:
            try:
                txt.configure(state="normal")
                if tag:
                    txt.insert("end", text, tag)
                else:
                    txt.insert("end", text)
                txt.see("end")
                txt.configure(state="disabled")
            except tk.TclError:
                self._logwin_text = None

    # ── settings ─────────────────────────────────────────────────────────────

    def _open_settings(self, event=None):
        if self._settings_overlay is not None:
            return

        ov = tk.Frame(self, bg="#0a0a0e")
        ov.place(x=0, y=0, width=WIN_W, height=WIN_H)
        ov.bind("<Button-1>", lambda e: self._close_settings())
        self._settings_overlay = ov

        self.bind("<Escape>", lambda e: self._close_settings())

        P_BG, P_HDR, P_BDR, P_INP = C_PANEL, C_HDR, C_PANEL_BDR, "#0f0b16"
        MW, MH = self._px(800), self._px(500)
        panel = tk.Frame(ov, bg=P_BG, highlightthickness=1,
                         highlightbackground=P_BDR, highlightcolor=P_BDR)
        panel.place(x=(WIN_W - MW) // 2, y=(WIN_H - MH) // 2 - self._px(20),
                    width=MW, height=MH)

        hdr = tk.Frame(panel, bg=P_HDR, height=self._px(46))
        hdr.pack(fill="x")
        hdr.pack_propagate(False)
        tk.Label(hdr, text="SETTINGS", font=("Segoe UI", 13, "bold"),
                 fg=C_PURPLE, bg=P_HDR).pack(side="left", padx=self._px(18))
        x_btn = tk.Label(hdr, text="✕", font=("Segoe UI", 12),
                         fg=C_TEXT_DIM, bg=P_HDR, cursor="hand2")
        x_btn.pack(side="right", padx=self._px(16))
        x_btn.bind("<Button-1>", lambda e: self._close_settings())
        x_btn.bind("<Enter>",    lambda e: x_btn.configure(fg=C_TEXT))
        x_btn.bind("<Leave>",    lambda e: x_btn.configure(fg=C_TEXT_DIM))
        tk.Frame(panel, bg=P_BDR, height=self._px(1)).pack(fill="x")

        PADX = self._px(22)
        body = tk.Frame(panel, bg=P_BG)
        body.pack(fill="both", expand=True, padx=PADX,
                  pady=(self._px(16), self._px(12)))

        loc_row = tk.Frame(body, bg=P_BG)
        loc_row.pack(fill="x")
        tk.Label(loc_row, text="GAME FOLDER",
                 font=("Segoe UI", 10, "bold"),
                 fg=C_GOLD, bg=P_BG).pack(side="left")
        opn = tk.Label(loc_row, text="Open folder", font=FONT_BODY,
                       fg=C_TEXT_DIM, bg=P_BG, cursor="hand2")
        opn.pack(side="left", padx=(self._px(16), 0))
        opn.bind("<Button-1>", lambda e: self._open_client_folder())
        opn.bind("<Enter>",    lambda e: opn.configure(fg=C_GOLD))
        opn.bind("<Leave>",    lambda e: opn.configure(fg=C_TEXT_DIM))

        # Same StringVar as the Update tab's Game folder entry — changing it
        # here fires the exact same folder-change mechanics immediately.
        path_row = tk.Frame(body, bg=P_BG)
        path_row.pack(fill="x", pady=(self._px(8), 0))
        ent = tk.Entry(path_row, textvariable=self._game_path,
                       bg=P_INP, fg=C_TEXT, relief="flat", font=FONT_MONO,
                       state="readonly", readonlybackground=P_INP,
                       highlightthickness=1, highlightbackground=P_BDR,
                       highlightcolor=P_BDR)
        ent.pack(side="left", fill="x", expand=True, ipady=self._px(7))
        chg = tk.Label(path_row, text="Change",
                       font=("Segoe UI", 10, "bold"),
                       fg=C_TEXT, bg=P_BDR, cursor="hand2",
                       padx=self._px(16), pady=self._px(7))
        chg.pack(side="left", padx=(self._px(8), 0))
        chg.bind("<Button-1>", lambda e: self._settings_change_dir())
        chg.bind("<Enter>",    lambda e: chg.configure(bg=C_GOLD, fg="#000"))
        chg.bind("<Leave>",    lambda e: chg.configure(bg=P_BDR, fg=C_TEXT))

        # Two equal-width columns via grid, so the right column keeps a fixed
        # position and reaches toward the right edge — regardless of how wide
        # the left column's text is.
        cols = tk.Frame(body, bg=P_BG)
        cols.pack(fill="x", pady=(self._px(20), 0))
        cols.columnconfigure(0, weight=3, uniform="s")
        cols.columnconfigure(1, weight=2, uniform="s")
        lcol = tk.Frame(cols, bg=P_BG)
        lcol.grid(row=0, column=0, sticky="nw")
        rcol = tk.Frame(cols, bg=P_BG)
        rcol.grid(row=0, column=1, sticky="nw")

        tk.Label(lcol, text="DOWNLOAD MIRROR",
                 font=("Segoe UI", 10, "bold"),
                 fg=C_GOLD, bg=P_BG).pack(anchor="w", pady=(0, self._px(4)))
        mir = tk.Frame(lcol, bg=P_BG)
        mir.pack(anchor="w")
        tk.Label(mir, text="●", font=("Segoe UI", 9),
                 fg=C_OK, bg=P_BG).pack(side="left")
        tk.Label(mir, text=" Iceland", font=("Segoe UI", 10, "bold"),
                 fg=C_TEXT, bg=P_BG).pack(side="left")
        self._mirror_status_lbl = tk.Label(mir, text="checking…",
                                           font=("Segoe UI", 9),
                                           fg=C_TEXT_DIM, bg=P_BG)
        self._mirror_status_lbl.pack(side="left", padx=(self._px(8), 0))
        rf = tk.Label(mir, text="⟳", font=("Segoe UI", 11),
                      fg=C_TEXT_DIM, bg=P_BG, cursor="hand2")
        rf.pack(side="left", padx=(self._px(6), 0))
        rf.bind("<Button-1>", lambda e: self._check_mirror_status())
        rf.bind("<Enter>",    lambda e: rf.configure(fg=C_GOLD))
        rf.bind("<Leave>",    lambda e: rf.configure(fg=C_TEXT_DIM))
        self._check_mirror_status()

        tk.Label(lcol, text="TROUBLESHOOTING",
                 font=("Segoe UI", 10, "bold"),
                 fg=C_GOLD, bg=P_BG).pack(anchor="w", pady=(self._px(22), 0))

        def _titem(icon, text, cmd, icon_color=C_GOLD):
            r = tk.Frame(lcol, bg=P_BG, cursor="hand2")
            r.pack(anchor="w", pady=(self._px(12), 0))
            # Monochrome glyphs in a fixed-width slot so all icons line up
            # and read at the same size (color emoji would render larger).
            ic = tk.Label(r, text=icon, font=("Segoe UI Symbol", 11),
                          fg=icon_color, bg=P_BG, width=2, anchor="w")
            ic.pack(side="left")
            tl = tk.Label(r, text=text, font=("Segoe UI", 10),
                          fg=C_TEXT, bg=P_BG)
            tl.pack(side="left")
            for w in (r, ic, tl):
                w.bind("<Button-1>", lambda e: cmd())
                w.bind("<Enter>", lambda e: tl.configure(fg=C_GOLD))
                w.bind("<Leave>", lambda e: tl.configure(fg=C_TEXT))

        _titem("✓", "Verify game files", self._settings_verify)
        _titem("☰", "Show logs", self._show_logs)
        _titem("⛊", "Add game folder to Defender exclusions",
               self._allow_through_antivirus)

        tk.Label(lcol, text="SUPPORT THE DEVELOPER",
                 font=("Segoe UI", 10, "bold"),
                 fg=C_GOLD, bg=P_BG).pack(anchor="w", pady=(self._px(22), 0))
        _titem("♥", "Ko-fi",
               lambda: self._open_url("https://ko-fi.com/rebased"),
               icon_color="#e8615f")
        _titem("☕", "Buy Me a Coffee",
               lambda: self._open_url("https://buymeacoffee.com/rebased"),
               icon_color="#b5854f")

        tk.Label(rcol, text="GENERAL",
                 font=("Segoe UI", 10, "bold"),
                 fg=C_GOLD, bg=P_BG).pack(anchor="w")
        tk.Checkbutton(rcol, text=" Clear WDB on game launch",
                       variable=self._clear_wdb_var,
                       command=self._toggle_clear_wdb,
                       font=("Segoe UI", 10), fg=C_TEXT, bg=P_BG,
                       activebackground=P_BG, activeforeground=C_TEXT,
                       selectcolor=P_INP, highlightthickness=0, bd=0,
                       cursor="hand2").pack(anchor="w", pady=(self._px(10), 0))
        tk.Checkbutton(rcol, text=" Minimize Octo Updater on game launch",
                       variable=self._close_on_launch_var,
                       command=self._toggle_close_on_launch,
                       font=("Segoe UI", 10), fg=C_TEXT, bg=P_BG,
                       activebackground=P_BG, activeforeground=C_TEXT,
                       selectcolor=P_INP, highlightthickness=0, bd=0,
                       cursor="hand2").pack(anchor="w", pady=(self._px(10), 0))
        cb_auto_mods = tk.Checkbutton(
            rcol, text=" Install essential mods",
            variable=self._auto_mods_var, command=self._toggle_auto_mods,
            font=("Segoe UI", 10), fg=C_TEXT, bg=P_BG,
            activebackground=P_BG, activeforeground=C_TEXT,
            selectcolor=P_INP, highlightthickness=0, bd=0, cursor="hand2")
        cb_auto_mods.pack(anchor="w", pady=(self._px(10), 0))
        self._add_tooltip(
            cb_auto_mods,
            "VanillaFixes will always be installed, even when this "
            "option is turned off")
        tk.Checkbutton(rcol, text=" Install recommended addons",
                       variable=self._auto_addons_var,
                       command=self._toggle_auto_addons,
                       font=("Segoe UI", 10), fg=C_TEXT, bg=P_BG,
                       activebackground=P_BG, activeforeground=C_TEXT,
                       selectcolor=P_INP, highlightthickness=0, bd=0,
                       cursor="hand2").pack(anchor="w", pady=(self._px(10), 0))
        cb_ignore_speech = tk.Checkbutton(
            rcol, text=" Ignore speech.mpq",
            variable=self._ignore_speech_var,
            command=self._toggle_ignore_speech,
            font=("Segoe UI", 10), fg=C_TEXT, bg=P_BG,
            activebackground=P_BG, activeforeground=C_TEXT,
            selectcolor=P_INP, highlightthickness=0, bd=0, cursor="hand2")
        cb_ignore_speech.pack(anchor="w", pady=(self._px(10), 0))
        self._add_tooltip(
            cb_ignore_speech,
            "Ignores verification and updates for speech.mpq, allowing custom "
            "speech sounds")

    def _close_settings(self):
        self.unbind("<Escape>")
        if self._settings_overlay is not None:
            self._settings_overlay.destroy()
            self._settings_overlay = None

        # Closing Settings is the "Confirm" action. It needs a reconcile when
        # this is the first run, or the chosen folder now differs from the saved
        # one — the two cases are handled identically from here on.
        new_path  = os.path.normpath(self._game_path.get().strip())
        saved     = os.path.normpath(self._cfg.get("out_dir", ""))
        folder_changed = bool(new_path) and new_path != saved
        needs_reconcile = self._first_run or folder_changed
        self._first_run = False

        if folder_changed:
            self._game_folder_changed(new_path)
        if needs_reconcile:
            self._set_pending_reconcile("full")
            self._offer_reconcile()
            # The reconcile installs mods/addons itself — drop any pending
            # auto-install retriggers so they don't race it.
            self._auto_mods_retrigger = self._auto_addons_retrigger = False
        else:
            # A settings change with no reconcile: apply an auto-install option
            # the user turned on this session (idempotent — no-op if nothing
            # missing).
            if self._auto_mods_retrigger:
                self._auto_mods_retrigger = False
                self._install_missing_essential_mods()
            if self._auto_addons_retrigger:
                self._auto_addons_retrigger = False
                self._install_missing_recommended_addons()

        # Offer a Defender exclusion at each reconcile, unless the user already
        # added one via Settings since the last reconcile. Reset after, so a
        # later reconcile (e.g. another folder change) offers it again.
        if needs_reconcile:
            if not self._av_excluded:
                self._prompt_av_exclusion()
            self._av_excluded = False

    def _open_client_folder(self):
        import subprocess
        path = os.path.normpath(self._game_path.get().strip())
        if os.path.isdir(path):
            # Explicit explorer.exe, not os.startfile: ShellExecute resolves
            # extensionless paths against PATHEXT/.lnk, so a Desktop shortcut
            # named like the folder (e.g. "OctoWoW.lnk") gets *executed*
            # instead of the folder being opened.
            subprocess.Popen(["explorer.exe", path])
            self._log_line(f"Opened folder: {path}\n", "dim")
        else:
            self._log_line(f"Folder not found: {path}\n", "err")

    def _settings_change_dir(self):
        cur     = self._game_path.get()
        initial = cur if os.path.isdir(cur) else os.path.expanduser("~")
        chosen  = filedialog.askdirectory(
            title="Select game client folder",
            initialdir=initial, mustexist=False)
        if chosen:
            # normpath → backslashes; fires the folder-change reset
            self._game_path.set(os.path.normpath(chosen))

    def _settings_verify(self):
        self._close_settings()
        self._verify_game_files()

    def _allow_through_antivirus(self):
        """Add a Windows Defender exclusion for the game folder (asks for
        admin elevation via UAC)."""
        client_dir = os.path.normpath(self._game_path.get().strip())
        if not client_dir or client_dir == ".":
            return
        import ctypes
        cmd = f"Add-MpPreference -ExclusionPath '{client_dir}'"
        r = ctypes.windll.shell32.ShellExecuteW(
            None, "runas", "powershell.exe",
            f'-NoProfile -WindowStyle Hidden -Command "{cmd}"', None, 0)
        if r > 32:
            self._av_excluded = True
            self._log_line(
                f"Requested Defender exclusion for: {client_dir}\n", "ok")
        else:
            self._log_line("Antivirus exclusion cancelled.\n", "err")

    def _maybe_show_aria2_firewall_notice(self):
        """One-time heads-up, shown before the first download, that the bundled
        aria2c downloader may trigger a Windows Firewall prompt — so it doesn't
        look sketchy to a non-technical user. Purely informational; tracked in
        the config so it appears only once."""
        if self._cfg.get("aria2_firewall_notice_shown"):
            return
        from tkinter import messagebox
        messagebox.showinfo(
            "Downloading the game",
            "Octo Updater downloads the game with aria2c, the same tool the "
            "official launcher uses.\n\n"
            "You may be asked to allow aria2c through the firewall. You can "
            "safely reject the request, but download speeds may be slightly "
            "lower.\n\n"
            "This message is shown only once.",
            parent=self)
        self._cfg = update_config(
            lambda c: c.__setitem__("aria2_firewall_notice_shown", True))

    def _check_mirror_status(self):
        lbl = self._mirror_status_lbl
        lbl.configure(text="checking…", fg=C_TEXT_DIM)

        def worker():
            ok = False
            try:
                req = urllib.request.Request(
                    CLIENT_TORRENT_URL, headers={"User-Agent": UA})
                with secure_urlopen(req, timeout=6,
                                    allowed_hosts=ALLOWED_DOWNLOAD_HOSTS):
                    ok = True
            except Exception:
                ok = False

            def upd():
                try:
                    lbl.configure(text="online" if ok else "offline",
                                  fg=C_OK if ok else C_ERR)
                except tk.TclError:
                    pass
            self.after(0, upd)
        threading.Thread(target=worker, daemon=True).start()

    def _toggle_clear_wdb(self):
        val = self._clear_wdb_var.get()
        self._cfg = update_config(
            lambda c: c.__setitem__("clear_wdb_on_launch", val))

    def _toggle_close_on_launch(self):
        val = self._close_on_launch_var.get()
        self._cfg = update_config(
            lambda c: c.__setitem__("close_on_launch", val))

    def _toggle_auto_mods(self):
        val = self._auto_mods_var.get()
        self._cfg = update_config(
            lambda c: c.__setitem__("auto_install_mods", val))
        # Install the missing essential mods only when Settings is closed;
        # turning it back off cancels the pending install.
        self._auto_mods_retrigger = val

    def _toggle_auto_addons(self):
        val = self._auto_addons_var.get()
        self._cfg = update_config(
            lambda c: c.__setitem__("auto_install_addons", val))
        self._auto_addons_retrigger = val

    def _toggle_ignore_speech(self):
        self._cfg = update_config(
            lambda c: c.__setitem__("ignore_speech",
                                    self._ignore_speech_var.get()))

    def _install_missing_essential_mods(self):
        """Install every essential mod not already present. Used when the user
        turns 'Install essential mods' on after the fact."""
        if self._running:
            return
        out = self._game_path.get().strip()
        if not out or not os.path.exists(os.path.join(out, "WoW.exe")):
            return  # no client yet — the fresh-folder auto-install handles it
        mods_cfg = load_config().get("mods", {})
        pending = False
        for mod in MODS_REGISTRY:
            if not mod.get("essential", False):
                continue
            state = mods_cfg.get(mod["id"], {})
            if (state.get("installed_version")
                    and mod_installed_files_present(mod, out)):
                continue  # already installed
            self._mod_pending_state.setdefault(mod["id"], {})["enabled"] = True
            pending = True
        if not pending:
            return
        self._log_line("\nInstalling essential mods...\n", "acct")
        self._set_btn_busy("Installing…")
        self._status_var.set("Downloading mods…")
        threading.Thread(target=self._apply_mods_worker,
                         args=(out,), daemon=True).start()

    def _install_missing_recommended_addons(self):
        """Install every recommended addon not already present. Used when the
        user turns 'Install recommended addons' on afterwards."""
        if self._addons_busy:
            return
        out = self._game_path.get().strip()
        if not out or not os.path.exists(os.path.join(out, "WoW.exe")):
            return
        ap = addons_path(out)
        recs = [{"folder": name, "status": "available", "git": url,
                 "branch": None, "ref": None, "toc": {},
                 "description": None, "error": None}
                for name, url in RECOMMENDED_ADDONS.items()
                if not os.path.isdir(os.path.join(ap, name))]
        if not recs:
            return
        self._log_line("\nInstalling recommended addons...\n", "acct")
        self._addon_apply(recs)

    def _verify_game_files(self):
        """Full integrity pass: aria2 hash-checks every game file's pieces
        against the torrent and re-downloads only the bad/missing ones, then
        re-patches WoW.exe. Catches same-size corruption the routine size-based
        sync can't. Installed mods are left alone."""
        if self._running:
            return
        self._client_ready = False
        self._log_line(
            "\nVerify game files — hash-checking every file against the torrent.\n",
            "acct")
        self._start_update(check_integrity=True)

    def _show_logs(self):
        if self._logwin is not None:
            try:
                self._logwin.deiconify()
                self._logwin.lift()
                self._logwin.focus_force()
                return
            except tk.TclError:
                self._logwin = None
                self._logwin_text = None

        win = tk.Toplevel(self)
        win.title("Octo Updater — Logs")
        LW, LH = self._px(760), self._px(420)
        sw, sh = win.winfo_screenwidth(), win.winfo_screenheight()
        win.geometry(f"{LW}x{LH}+{(sw - LW) // 2}+{(sh - LH) // 2}")
        win.configure(bg=C_BG)

        top = tk.Frame(win, bg=C_BG)
        top.pack(fill="x", padx=self._px(12), pady=(self._px(10), self._px(4)))
        tk.Label(top, text="SESSION LOG", font=("Segoe UI", 9, "bold"),
                 fg=C_GOLD, bg=C_BG).pack(side="left")

        outer = tk.Frame(win, bg=C_BG)
        outer.pack(fill="both", expand=True, padx=self._px(12),
                   pady=(0, self._px(12)))
        sb = SlimScrollbar(outer, bg=C_BG, width=self._px(10))
        sb.pack(side="right", fill="y")
        txt = tk.Text(outer, bg=C_LOG_BG, fg=C_TEXT,
                      insertbackground=C_TEXT, relief="flat",
                      font=FONT_MONO, wrap="word", state="disabled",
                      padx=self._px(10), pady=self._px(8), yscrollcommand=sb.set,
                      cursor="arrow", selectbackground=C_PANEL_BDR)
        txt.pack(side="left", fill="both", expand=True)
        sb.command = txt.yview
        for t, c in (("ok", C_OK), ("err", C_ERR),
                     ("dim", C_TEXT_DIM), ("acct", C_GOLD)):
            txt.tag_config(t, foreground=c)

        txt.configure(state="normal")
        for text, tag in self._log_buffer:
            if tag:
                txt.insert("end", text, tag)
            else:
                txt.insert("end", text)
        txt.see("end")
        txt.configure(state="disabled")

        def _close():
            self._logwin = None
            self._logwin_text = None
            win.destroy()
        win.protocol("WM_DELETE_WINDOW", _close)

        self._logwin = win
        self._logwin_text = txt

    # ── button helpers ───────────────────────────────────────────────────────────

    def _set_btn_play(self):
        self._btn_mode = "play"
        self._upd_btn.configure(text="PLAY", bg=C_GREEN_BTN, fg="#ffffff")
        self._btn_glow.configure(bg="#2b511d")

    def _set_btn_update(self):
        self._btn_mode = "update"
        self._upd_btn.configure(text="UPDATE", bg=C_GOLD, fg="#ffffff")
        self._btn_glow.configure(bg="#4a3812")

    def _set_btn_busy(self, label="…"):
        self._btn_mode = "busy"
        self._upd_btn.configure(text=label, bg="#2a2434", fg=C_TEXT_DIM)
        self._btn_glow.configure(bg="#211c2c")

    def _btn_hover(self, entering: bool):
        if self._btn_mode == "busy":
            return
        if entering:
            col  = C_GREEN_HOV if self._btn_mode == "play" else C_GOLD_LT
            glow = "#397024"   if self._btn_mode == "play" else "#5c4a16"
        else:
            col  = C_GREEN_BTN if self._btn_mode == "play" else C_GOLD
            glow = "#2b511d"   if self._btn_mode == "play" else "#4a3812"
        self._upd_btn.configure(bg=col)
        self._btn_glow.configure(bg=glow)

    def _mods_have_errors(self) -> bool:
        return any(bool(s.get("error"))
                   for s in load_config().get("mods", {}).values())

    def _refresh_ready_state(self):
        """Recompute the footer status/button after an operation finishes.
        PLAY is only offered when the client files are up to date AND no mod
        is in an error state — otherwise the button stays grey and inactive."""
        # Never re-enable PLAY while addons are actively installing — this
        # guards against a stray call during the mods→addons setup chain or a
        # post-install verify flipping the button back on mid-download.
        if self._addons_installing:
            self._set_btn_busy("Installing…")
            self._status_var.set("Downloading addons…")
            return
        if not self._client_ready:
            self._status_var.set("Update available!")
            self._set_btn_update()
            return
        if self._mods_have_errors():
            self._set_btn_busy("PLAY")
            self._status_var.set("Mod errors — check MODS tab")
        else:
            self._set_btn_play()
            self._status_var.set("Everything up to date!")

    def _btn_click(self):
        if self._btn_mode == "play":
            self._launch_game()
        elif self._btn_mode == "update":
            self._start_update()

    def _launch_game(self):
        """Launch the game detached.
        If VanillaFixes is installed use VanillaFixes.exe (it injects dlls then
        starts WoW.exe itself). Otherwise fall back to WoW.exe directly."""
        import subprocess
        client_dir = self._game_path.get().strip()
        cfg        = load_config()
        vf_state   = cfg.get("mods", {}).get("VanillaFixes", {})
        vf_installed = (vf_state.get("enabled") and
                        vf_state.get("installed_version") and
                        os.path.exists(os.path.join(client_dir, "VanillaFixes.exe")))

        if vf_installed:
            exe     = os.path.join(client_dir, "VanillaFixes.exe")
            exe_lbl = "VanillaFixes.exe"
        else:
            exe     = os.path.join(client_dir, "WoW.exe")
            exe_lbl = "WoW.exe"

        if not os.path.exists(exe):
            self._log_line(f"{exe_lbl} not found at: {exe}\n", "err")
            return

        # One-time DXVK first-launch notice (armed when DXVK was installed).
        if cfg.get("dxvk_notice_pending"):
            self._cfg = update_config(
                lambda c: c.pop("dxvk_notice_pending", None))
            from tkinter import messagebox
            messagebox.showinfo(
                "DXVK mod first launch",
                "Initial shader compilation may cause temporary in-game "
                "stuttering during the first launch. This is a normal process "
                "while the game builds its shader cache.\n\n"
                "Users with AMD GPUs experiencing stability issues can switch "
                "to DXVK 2.5.3",
                parent=self)

        if self._cfg.get("clear_wdb_on_launch", False):
            remove_wdb(client_dir)

        try:
            flags = (getattr(subprocess, "DETACHED_PROCESS", 0)
                     | getattr(subprocess, "CREATE_BREAKAWAY_FROM_JOB", 0))
            try:
                subprocess.Popen([exe], cwd=client_dir,
                                 creationflags=flags, close_fds=True)
            except OSError:
                # The job object doesn't permit breakaway — retry without it.
                flags &= ~getattr(subprocess, "CREATE_BREAKAWAY_FROM_JOB", 0)
                subprocess.Popen([exe], cwd=client_dir,
                                 creationflags=flags, close_fds=True)
            self._log_line(f"Launched {exe_lbl}!\n", "ok")
            # Briefly disable PLAY so a double-click can't spawn two clients.
            self._set_btn_busy("PLAY")
            self._status_var.set("Launching...")
            # Optionally minimize (close) the updater to the taskbar shortly after launch
            if self._cfg.get("close_on_launch", False):
                self.after(1000, self.iconify) # self._on_close and return
            self.after(5000, self._refresh_ready_state)
        except Exception as e:
            self._log_line(f"Failed to launch {exe_lbl}: {e}\n", "err")

    # ── verify lifecycle ──────────────────────────────────────────────────────────

    def _start_verify(self):
        out = self._game_path.get().strip()
        if not out:
            self._set_btn_update()
            return
        # Cancel any verify already in flight before swapping the queues, so
        # a stale worker can't keep writing to a queue we no longer poll.
        prev = getattr(self, "_verify_worker", None)
        if prev is not None:
            prev.cancel()
        self._running = True
        self._set_btn_busy("Checking…")
        self._status_var.set("Checking for updates…")
        self._log_q  = queue.Queue()
        self._prog_q = queue.Queue()
        worker = VerifyWorker(out, self._log_q, self._prog_q)
        self._verify_worker = worker
        threading.Thread(target=worker.run, daemon=True).start()

    # ── update lifecycle ──────────────────────────────────────────────────────────

    def _start_update(self, check_integrity: bool = False,
                      overwrite_config: bool = False):
        if self._running:
            return
        if self._pending_reconcile:
            check_integrity  = True
            overwrite_config = (self._pending_reconcile == "full")
            self._set_pending_reconcile(None)
        out = self._game_path.get().strip()
        if not out:
            self._log_line("✗  Please set the game folder first.\n", "err")
            return

        self._cfg = update_config(lambda c: c.__setitem__("out_dir", out))

        self._maybe_show_aria2_firewall_notice()

        self._log_line(f"\nGame folder: {out}\n", "dim")

        self._running = True
        self._set_btn_busy("Verifying…" if check_integrity else "Updating…")
        self._status_var.set("Verifying game files…" if check_integrity
                             else "Updating…")
        self._draw_progress(0.0)
        self._prog_label_var.set("")

        self._log_q  = queue.Queue()
        self._prog_q = queue.Queue()

        self._worker   = UpdateWorker(out, self._log_q, self._prog_q,
                                      check_integrity=check_integrity,
                                      overwrite_config=overwrite_config)

        t = threading.Thread(target=self._worker.run, daemon=True)
        t.start()

    def _finish(self, success: bool):
        self._running = False
        if success:
            self._client_ready = True
            self._draw_progress(1.0)
            self._refresh_ready_state()
            # Game files are confirmed present now — install essential mods
            # if this is a fresh folder (first launch or folder just changed).
            self._maybe_install_essential_mods()
            # When mods were already initialized, the addons chain from
            # _do_inplace_update never runs — trigger it directly.
            if load_config().get("mods"):
                self._maybe_install_default_addons()
        else:
            self._client_ready = False
            self._status_var.set("Update failed — check the log")
            self._draw_progress(0.0)
            self._set_btn_update()

    # ── queue polling ─────────────────────────────────────────────────────────

    def _poll(self):
        try:
            while True:
                msg, tag = self._log_q.get_nowait()
                if msg == "__DONE__":
                    self._finish(True)
                elif msg == "__ERROR__":
                    self._finish(False)
                elif msg == "__UP_TO_DATE__":
                    self._running = False
                    self._client_ready = True
                    self._draw_progress(1.0)
                    self._refresh_ready_state()
                    # Files were already fine (no download needed) — still need
                    # to check whether essential mods should be auto-installed,
                    # e.g. right after switching to a folder that already has
                    # the client but has never had mods installed via this
                    # updater.
                    self._maybe_install_essential_mods()
                    if load_config().get("mods"):
                        self._maybe_install_default_addons()
                elif msg == "__UPDATE_NEEDED__":
                    self._running = False
                    self._client_ready = False
                    self._status_var.set("Update available!")
                    self._draw_progress(0.0)
                    self._set_btn_update()
                elif msg.startswith("__VERSION__"):
                    ver = msg[len("__VERSION__"):]
                    self._client_ver_var.set(ver)
                else:
                    self._render_log(msg, tag)
        except queue.Empty:
            pass

        # Drain the global app-log queue that helper functions write to.
        try:
            while True:
                msg, tag = _LOG_Q.get_nowait()
                self._render_log(msg, tag)
        except queue.Empty:
            pass

        latest = None
        try:
            while True:
                latest = self._prog_q.get_nowait()
        except queue.Empty:
            pass
        if latest is not None:
            val, lbl = latest
            self._draw_progress(val)
            self._prog_label_var.set(lbl)

        self.after(80, self._poll)


# ──────────────────────────────────────────────────────────────────────────────
#  Entry point
# ──────────────────────────────────────────────────────────────────────────────

def _enable_dpi_awareness():
    """Declare DPI awareness before any Tk window is created, so Windows
    reports the true DPI (letting us scale crisply) instead of bitmap-scaling a
    96-DPI render. Prefers Per-Monitor-V2, falling back through older contexts.
    Must run before the Tk root exists; a no-op off Windows / on old Windows."""
    try:
        import ctypes
    except Exception:
        return
    user32 = getattr(ctypes, "windll", None) and ctypes.windll.user32
    if user32 is not None:
        # DPI_AWARENESS_CONTEXT_PER_MONITOR_AWARE_V2 = -4, PER_MONITOR = -3.
        for ctx in (-4, -3):
            try:
                if user32.SetProcessDpiAwarenessContext(ctypes.c_void_p(ctx)):
                    return
            except Exception:
                pass
    try:
        ctypes.windll.shcore.SetProcessDpiAwareness(2)   # per-monitor (8.1+)
        return
    except Exception:
        pass
    try:
        ctypes.windll.user32.SetProcessDPIAware()         # system-aware (Vista+)
    except Exception:
        pass


if __name__ == "__main__":
    _enable_dpi_awareness()
    app = OctoUpdaterApp()
    app.mainloop()
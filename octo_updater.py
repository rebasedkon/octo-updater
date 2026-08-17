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
import urllib.request
from urllib.parse import quote, urlsplit
import shutil
import stat
import struct
import time
import math
import threading
import queue
import tkinter as tk
from tkinter import filedialog
from pathlib import Path

# ──────────────────────────────────────────────────────────────────────────────
#  Constants
# ──────────────────────────────────────────────────────────────────────────────

UPDATER_VERSION  = "1.3.2"
SERVER           = "https://octowow.st"
TORRENT_URL      = "https://dl.octowow.st/download/client.torrent"
UA               = f"OctoUpdater/{UPDATER_VERSION}"
DOWNLOAD_RETRY   = 5
DOWNLOAD_TIMEOUT = 10    # seconds without any data before a transfer aborts
TORRENT_MAX_SIZE = 4 * 1024 * 1024

# Where the app keeps its files: next to the .exe when frozen (PyInstaller),
# otherwise next to this script — never the current working directory, which
# varies with how the app was launched.
if getattr(sys, "frozen", False):
    APP_DIR = os.path.dirname(os.path.abspath(sys.executable))
else:
    APP_DIR = os.path.dirname(os.path.abspath(__file__))

CONFIG_FILE      = os.path.join(APP_DIR, "octo_updater_config.json")

# First-run default game folder, anchored to the app dir (not the CWD).
DEFAULT_OUT_DIR  = os.path.join(APP_DIR, "OctoWoW")

# News feed: announcements come from the forum list endpoint.
NEWS_URL          = f"{SERVER}/forum/octonews.php?mode=list&forum=2&limit=8"
NEWS_FEATURED_URL = f"{SERVER}/forum/octonews.php?forum=35&mode=full"
NEWS_TIMEOUT      = 8
NEWS_CACHE_TTL    = 300

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


def is_wow_running() -> bool:
    """Return whether Windows currently has a WoW.exe process."""
    if os.name != "nt":
        return False
    try:
        import subprocess
        result = subprocess.run(
            ["tasklist", "/FI", "IMAGENAME eq WoW.exe", "/FO", "CSV", "/NH"],
            capture_output=True, text=True, check=False,
            creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0),
            timeout=5)
        return '"wow.exe"' in result.stdout.lower()
    except Exception:
        # A failed process probe must not make the launcher unusable. The
        # atomic replace still provides a precise file-in-use error later.
        return False


def fmt_size(num_bytes: float) -> str:
    """Human-readable size: KB under a megabyte, MB otherwise."""
    if num_bytes < 1024 * 1024:
        return f"{num_bytes / 1024:.0f} KB"
    return f"{num_bytes / 1024 / 1024:.1f} MB"


def fmt_speed(bytes_per_sec: float) -> str:
    if bytes_per_sec < 1024 * 1024:
        return f"{bytes_per_sec / 1024:.0f} KB/s"
    return f"{bytes_per_sec / 1024 / 1024:.1f} MB/s"


def sha1_file(path) -> str:
    h = hashlib.sha1()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest().upper()


CACHE_FILE = os.path.join(APP_DIR, "octo_updater_hash_cache.json")

def load_cache() -> dict:
    try:
        with open(CACHE_FILE) as f:
            return json.load(f)
    except FileNotFoundError:
        return {}
    except Exception as e:
        sys.stderr.write(f"[cache] failed to read {CACHE_FILE}: {e}\n")
        return {}

def save_cache(cache: dict):
    try:
        _atomic_write(CACHE_FILE, json.dumps(cache))
    except Exception as e:
        sys.stderr.write(f"[cache] failed to write {CACHE_FILE}: {e}\n")

# ── HTTPS web-seed updater ─────────────────────────────────────────────────────────────
# OctoWoW retired its JSON manifest in favour of a .torrent.  We use that
# file only as authenticated-over-HTTPS metadata: no peer connections, DHT,
# listening socket, upload, or seeding is implemented.  BEP 19 web-seed URLs
# let us continue fetching individual changed files over ordinary HTTPS.


def _bdecode(data: bytes):
    """Small strict bencode decoder for trusted-size metainfo documents."""
    pos = 0

    def parse(depth=0):
        nonlocal pos
        if depth > 64 or pos >= len(data):
            raise ValueError("Invalid torrent metadata")
        ch = data[pos]
        if ch == ord("i"):
            end = data.find(b"e", pos + 1)
            if end < 0:
                raise ValueError("Unterminated torrent integer")
            raw = data[pos + 1:end]
            if not raw or (raw.startswith(b"-") and len(raw) == 1):
                raise ValueError("Invalid torrent integer")
            pos = end + 1
            return int(raw)
        if ch == ord("l"):
            pos += 1
            out = []
            while pos < len(data) and data[pos] != ord("e"):
                out.append(parse(depth + 1))
            if pos >= len(data):
                raise ValueError("Unterminated torrent list")
            pos += 1
            return out
        if ch == ord("d"):
            pos += 1
            out = {}
            while pos < len(data) and data[pos] != ord("e"):
                key = parse(depth + 1)
                if not isinstance(key, bytes):
                    raise ValueError("Torrent dictionary key is not bytes")
                out[key] = parse(depth + 1)
            if pos >= len(data):
                raise ValueError("Unterminated torrent dictionary")
            pos += 1
            return out
        colon = data.find(b":", pos)
        if colon < 0:
            raise ValueError("Invalid torrent byte string")
        raw_len = data[pos:colon]
        if not raw_len or not raw_len.isdigit():
            raise ValueError("Invalid torrent byte-string length")
        size = int(raw_len)
        pos = colon + 1
        end = pos + size
        if end > len(data):
            raise ValueError("Truncated torrent byte string")
        value = data[pos:end]
        pos = end
        return value

    value = parse()
    if pos != len(data):
        raise ValueError("Trailing data in torrent metadata")
    return value


def _torrent_text(value, label: str) -> str:
    if not isinstance(value, bytes):
        raise ValueError(f"Invalid torrent {label}")
    try:
        return value.decode("utf-8")
    except UnicodeDecodeError as e:
        raise ValueError(f"Torrent {label} is not UTF-8") from e


class TorrentMetadata:
    def __init__(self, raw: bytes):
        doc = _bdecode(raw)
        if not isinstance(doc, dict) or not isinstance(doc.get(b"info"), dict):
            raise ValueError("Torrent has no info dictionary")
        info = doc[b"info"]
        self.metainfo_sha1 = hashlib.sha1(raw).hexdigest()
        self.name = _torrent_text(info.get(b"name"), "name")
        if self.name in ("", ".", "..") or "/" in self.name or "\\" in self.name:
            raise ValueError("Unsafe torrent root name")
        self.piece_length = info.get(b"piece length")
        pieces = info.get(b"pieces")
        if (not isinstance(self.piece_length, int) or self.piece_length <= 0
                or not isinstance(pieces, bytes) or not pieces
                or len(pieces) % 20):
            raise ValueError("Invalid torrent piece table")
        self.pieces = [pieces[i:i + 20] for i in range(0, len(pieces), 20)]

        url_list = doc.get(b"url-list", [])
        if isinstance(url_list, bytes):
            url_list = [url_list]
        if not isinstance(url_list, list):
            raise ValueError("Invalid torrent web-seed list")
        self.web_seeds = []
        for item in url_list:
            url = _torrent_text(item, "web-seed URL")
            _check_url(url, ALLOWED_DOWNLOAD_HOSTS)
            parsed_url = urlsplit(url)
            if parsed_url.username or parsed_url.password or parsed_url.query \
                    or parsed_url.fragment:
                raise ValueError("Unsafe torrent web-seed URL")
            self.web_seeds.append(url)
        if not self.web_seeds:
            raise ValueError("Torrent contains no HTTPS web seed")

        source_files = info.get(b"files")
        if not isinstance(source_files, list) or not source_files:
            raise ValueError("Torrent is not a multi-file client package")
        self.files = []
        seen_paths = set()
        offset = 0
        for entry in source_files:
            if not isinstance(entry, dict) or not isinstance(entry.get(b"length"), int):
                raise ValueError("Invalid torrent file entry")
            length = entry[b"length"]
            parts_raw = entry.get(b"path")
            if length < 0 or not isinstance(parts_raw, list) or not parts_raw:
                raise ValueError("Invalid torrent file path")
            parts = tuple(_torrent_text(p, "path") for p in parts_raw)
            if any(p in ("", ".", "..") or "/" in p or "\\" in p
                   or ":" in p or p[-1:] in (" ", ".") for p in parts):
                raise ValueError("Unsafe path in torrent metadata")
            first_piece = offset // self.piece_length
            last_piece = ((offset + length - 1) // self.piece_length
                          if length else first_piece)
            sig = hashlib.sha256()
            sig.update(str(length).encode("ascii") + b":")
            sig.update(str(offset % self.piece_length).encode("ascii") + b":")
            for piece_hash in self.pieces[first_piece:last_piece + 1]:
                sig.update(piece_hash)
            rel = "/".join(parts)
            key = rel.lower()
            if key in seen_paths:
                raise ValueError("Duplicate path in torrent metadata")
            seen_paths.add(key)
            self.files.append({
                "parts": parts, "rel": rel, "key": key,
                "length": length, "offset": offset,
                "first_piece": first_piece, "last_piece": last_piece,
                "signature": sig.hexdigest(),
            })
            offset += length
        self.total_length = offset
        expected_pieces = ((offset + self.piece_length - 1) // self.piece_length)
        if expected_pieces != len(self.pieces):
            raise ValueError("Torrent piece count does not match its files")
        self.by_key = {f["key"]: f for f in self.files}

    def file_url(self, file_rec: dict, web_seed: str | None = None) -> str:
        base = web_seed or self.web_seeds[0]
        # BEP 19 multi-file mapping: <url-list>/<torrent-name>/<file-path>.
        return (base.rstrip("/") + "/" + quote(self.name, safe="") + "/"
                + "/".join(quote(p, safe="") for p in file_rec["parts"]))

    def files_for_piece(self, piece_index: int) -> list:
        start = piece_index * self.piece_length
        end = min(start + self.piece_length, self.total_length)
        return [f for f in self.files
                if f["offset"] < end and f["offset"] + f["length"] > start]


def fetch_torrent_metadata() -> TorrentMetadata:
    req = urllib.request.Request(TORRENT_URL, headers={"User-Agent": UA})
    with secure_urlopen(req, timeout=DOWNLOAD_TIMEOUT,
                        allowed_hosts=ALLOWED_DOWNLOAD_HOSTS) as response:
        size_header = response.headers.get("Content-Length")
        if size_header and int(size_header) > TORRENT_MAX_SIZE:
            raise RuntimeError("Torrent metadata is unexpectedly large")
        raw = response.read(TORRENT_MAX_SIZE + 1)
    if len(raw) > TORRENT_MAX_SIZE:
        raise RuntimeError("Torrent metadata is unexpectedly large")
    return TorrentMetadata(raw)


def _torrent_owned_paths() -> set:
    """Files controlled by this updater's mod toggles, not by client sync."""
    paths = {"d3d9.dll", "dxvk.conf", "dlls.txt"}
    for mod in globals().get("MODS_REGISTRY", []):
        paths.update(str(p).replace("\\", "/").lower()
                     for p in mod.get("installed_files", []))
    return paths


def _torrent_state() -> dict:
    state = load_config().get("torrent_state", {})
    return state if isinstance(state, dict) else {}


def _save_torrent_state(meta: TorrentMetadata):
    state = {
        "metainfo_sha1": meta.metainfo_sha1,
        "files": {f["key"]: f["signature"] for f in meta.files},
        "layout": {f["key"]: [f["offset"], f["length"]] for f in meta.files},
        "pieces": [p.hex() for p in meta.pieces],
    }
    update_config(lambda c: c.__setitem__("torrent_state", state))


class _TorrentDiskReader:
    """Sequentially reads the torrent's virtual concatenated file stream."""
    def __init__(self, meta: TorrentMetadata, root: str):
        self.meta, self.root = meta, root
        self.file_index = 0
        self.file_offset = 0
        self.handle = None

    def close(self):
        if self.handle is not None:
            self.handle.close()
            self.handle = None

    def _advance(self):
        self.close()
        self.file_index += 1
        self.file_offset = 0

    def consume(self, length: int, collect: bool) -> bytes | None:
        chunks = []
        valid = True
        left = length
        while left and self.file_index < len(self.meta.files):
            rec = self.meta.files[self.file_index]
            available = rec["length"] - self.file_offset
            take = min(left, available)
            if take:
                if collect:
                    try:
                        if self.handle is None:
                            path = os.path.join(self.root, *rec["parts"])
                            self.handle = open(path, "rb")
                            self.handle.seek(self.file_offset)
                        chunk = self.handle.read(take)
                        if len(chunk) != take:
                            valid = False
                        chunks.append(chunk)
                    except OSError:
                        valid = False
                elif self.handle is not None:
                    # A later selected piece in the same file must reopen at
                    # the updated virtual offset, not at the old OS position.
                    self.close()
                self.file_offset += take
                left -= take
            if self.file_offset >= rec["length"]:
                self._advance()
        if left:
            valid = False
        return b"".join(chunks) if collect and valid else (None if collect else b"")


def verify_torrent_files(meta: TorrentMetadata, root: str, excluded: set,
                         cancel_fn, progress_fn) -> list:
    """Full local piece check. Pieces touching mod-owned files are skipped."""
    stale = set()
    for rec in meta.files:
        if rec["key"] in excluded:
            continue
        path = os.path.join(root, *rec["parts"])
        try:
            if os.path.getsize(path) != rec["length"]:
                stale.add(rec["key"])
        except OSError:
            stale.add(rec["key"])

    reader = _TorrentDiskReader(meta, root)
    try:
        for index, expected in enumerate(meta.pieces):
            if cancel_fn():
                raise RuntimeError("Cancelled")
            touched = meta.files_for_piece(index)
            skip = any(f["key"] in excluded or f["key"] in stale for f in touched)
            piece_size = min(meta.piece_length,
                             meta.total_length - index * meta.piece_length)
            data = reader.consume(piece_size, not skip)
            if not skip and (data is None or hashlib.sha1(data).digest() != expected):
                stale.update(f["key"] for f in touched if f["key"] not in excluded)
            if index % 32 == 0 or index + 1 == len(meta.pieces):
                progress_fn((index + 1) / len(meta.pieces))
    finally:
        reader.close()
    return [f for f in meta.files if f["key"] in stale]


def quick_torrent_diff(meta: TorrentMetadata, root: str, excluded: set) -> list:
    """Size-check local files and use prior piece signatures for server deltas."""
    previous = _torrent_state().get("files", {})
    expected_patched_wow = load_config().get("expected_patched_wow_hash", "")
    if not isinstance(previous, dict):
        previous = {}
    stale = []
    for rec in meta.files:
        if rec["key"] in excluded:
            continue
        path = os.path.join(root, *rec["parts"])
        try:
            wrong_size = os.path.getsize(path) != rec["length"]
        except OSError:
            wrong_size = True
        if (not wrong_size and rec["key"] == "wow.exe"
                and expected_patched_wow):
            wrong_size = sha1_file(path) != expected_patched_wow
        changed_upstream = bool(previous) and previous.get(rec["key"]) != rec["signature"]
        if wrong_size or changed_upstream:
            stale.append(rec)
    return stale


def torrent_download_plan(meta: TorrentMetadata, root: str,
                          requested: set, excluded: set) -> tuple:
    """Split an update into whole files and changed pieces.

    Piece patching is safe only when the file kept the same virtual offset and
    length as the previously accepted torrent. Missing/resized/rearranged files
    fall back to an ordinary whole-file HTTPS download.
    """
    state = _torrent_state()
    old_layout = state.get("layout", {})
    old_piece_hex = state.get("pieces", [])
    if not isinstance(old_layout, dict) or not isinstance(old_piece_hex, list):
        old_layout, old_piece_hex = {}, []
    try:
        old_pieces = [bytes.fromhex(p) for p in old_piece_hex]
        if any(len(p) != 20 for p in old_pieces):
            old_pieces = []
    except (TypeError, ValueError):
        old_pieces = []

    full_files = []
    changed_pieces = set()
    for rec in meta.files:
        if rec["key"] not in requested or rec["key"] in excluded:
            continue
        path = os.path.join(root, *rec["parts"])
        try:
            right_size = os.path.getsize(path) == rec["length"]
        except OSError:
            right_size = False
        same_layout = old_layout.get(rec["key"]) == [rec["offset"], rec["length"]]
        if not right_size or not same_layout or not old_pieces:
            full_files.append(rec)
            continue
        rec_changed = []
        for index in range(rec["first_piece"], rec["last_piece"] + 1):
            if index >= len(old_pieces) or old_pieces[index] != meta.pieces[index]:
                rec_changed.append(index)
        if rec_changed:
            changed_pieces.update(rec_changed)
        else:
            # Requested by a full integrity check rather than an upstream
            # metadata delta; without a known bad-piece index, repair it whole.
            full_files.append(rec)
    return full_files, changed_pieces


def verify_torrent_piece_subset(meta: TorrentMetadata, root: str,
                                piece_indexes: set, excluded: set,
                                cancel_fn, progress_fn) -> set:
    """Verify selected pieces after downloads; skip boundaries containing mods."""
    eligible = {i for i in piece_indexes
                if not any(f["key"] in excluded for f in meta.files_for_piece(i))}
    failed = set()
    reader = _TorrentDiskReader(meta, root)
    done = 0
    try:
        for index, expected in enumerate(meta.pieces):
            if cancel_fn():
                raise RuntimeError("Cancelled")
            piece_size = min(meta.piece_length,
                             meta.total_length - index * meta.piece_length)
            wanted = index in eligible
            data = reader.consume(piece_size, wanted)
            if wanted:
                done += 1
                if data is None or hashlib.sha1(data).digest() != expected:
                    failed.add(index)
                progress_fn(done / max(1, len(eligible)))
    finally:
        reader.close()
    return failed


_LEGACY_ARCHIVES = {
    "patch-6.mpq": 451195806,
    "patch-7.mpq": 175256564,
    "patch-8.mpq": 484649870,
    "patch-9.mpq": 506808141,
    "patch-a.mpq": 241751337,
}


def prune_legacy_client_files(meta: TorrentMetadata, root: str):
    """Mirror the official launcher's conservative stale-archive cleanup."""
    expected = {os.path.basename(f["rel"]).lower() for f in meta.files
                if f["rel"].lower().startswith("data/")
                and f["rel"].lower().endswith(".mpq")}
    data_dir = os.path.join(root, "Data")
    for name, old_size in _LEGACY_ARCHIVES.items():
        if name in expected:
            continue
        path = os.path.join(data_dir, name)
        try:
            if os.path.getsize(path) == old_size:
                os.remove(path)
                log(f"Removed obsolete client archive: Data/{name}", "dim")
        except OSError:
            pass


class VerifyWorker:
    def __init__(self, out_dir: str, log_q: queue.Queue, prog_q: queue.Queue,
                 expected_patched_wow_hash: str = "",
                 original_server_wow_hash: str = "",
                 overwrite_config: bool = False):
        self.out_dir = out_dir
        self.log_q   = log_q
        self.prog_q  = prog_q
        self._cancel = False
        self.expected_patched_wow_hash = expected_patched_wow_hash
        self.original_server_wow_hash  = original_server_wow_hash
        self.overwrite_config = overwrite_config
        self._cache: dict = load_cache()

    def cancel(self):
        self._cancel = True

    def log(self, msg, tag=""):
        self.log_q.put((msg, tag))

    def progress(self, value, label=""):
        self.prog_q.put((value, label))

    def run(self):
        try:
            self.progress(0.02, "Fetching update metadata...")
            self.log("Fetching client.torrent metadata...", "acct")
            meta = fetch_torrent_metadata()
            self.log(f"Metadata received ({len(meta.files)} files).", "ok")
            excluded = _torrent_owned_paths()
            state = _torrent_state()
            if state.get("files"):
                self.progress(0.45, "Checking files...")
                stale_nodes = quick_torrent_diff(meta, self.out_dir, excluded)
            else:
                self.log("Performing first full local integrity check...", "dim")
                stale_nodes = verify_torrent_files(
                    meta, self.out_dir, excluded,
                    lambda: self._cancel,
                    lambda p: self.progress(0.08 + p * 0.84,
                                            f"Verifying... {int(p * 100)}%"))

            self.progress(1.0, "")
            save_cache(self._cache)

            # Config.wtf isn't part of client sync — it's user game config.
            # Create it when missing, or overwrite it when the user
            # committed to this folder.
            cfg_wtf = os.path.join(self.out_dir, "WTF", "Config.wtf")
            if self.overwrite_config or not os.path.exists(cfg_wtf):
                write_config_wtf(self.out_dir)

            if stale_nodes:
                total = sum(n["length"] for n in stale_nodes)
                self.log(f"Update available: {len(stale_nodes)} file(s), "
                         f"{fmt_size(total)}.", "acct")
                self.log_q.put(("__UPDATE_NEEDED__", ""))
                self.log_q.put(("__DIFF_TREE__",
                                [n["key"] for n in stale_nodes]))
            else:
                _save_torrent_state(meta)
                self.log("Everything is up to date!", "ok")
                self.log_q.put(("__UP_TO_DATE__", ""))
        except Exception as e:
            self.log(f"Verification failed: {e}", "err")
            self.log_q.put(("__UPDATE_NEEDED__", ""))
            self.log_q.put(("__DIFF_TREE__", None))


class UpdateWorker:
    def __init__(self, out_dir: str, log_q: queue.Queue, prog_q: queue.Queue,
                 expected_patched_wow_hash: str = ""):
        self.out_dir = out_dir
        self.log_q   = log_q
        self.prog_q  = prog_q
        self._cancel = False
        self._cache: dict = load_cache()
        self.expected_patched_wow_hash = expected_patched_wow_hash
        self.original_server_wow_hash  = ""

    def cancel(self):
        self._cancel = True

    def log(self, msg: str, tag: str = ""):
        self.log_q.put((msg, tag))

    def progress(self, value: float, label: str = ""):
        self.prog_q.put((value, label))

    def download(self, url, dest, size, name=""):
        os.makedirs(os.path.dirname(dest), exist_ok=True)
        tmp  = dest + ".tmp"
        name = name or os.path.basename(dest)
        total_str = fmt_size(size) if size else "?"

        for attempt in range(1, DOWNLOAD_RETRY + 1):
            if self._cancel:
                raise RuntimeError("Cancelled")
            try:
                # Resume a previous partial download when one is present.
                got = os.path.getsize(tmp) if os.path.exists(tmp) else 0
                if size and got > size:
                    os.remove(tmp)   # oversized/stale leftover — start clean
                    got = 0

                if size and got == size:
                    self.log("  Finalizing completed temporary download…", "dim")
                    digest = sha1_file(tmp)
                    os.replace(tmp, dest)
                    try:
                        self._cache[dest] = [digest, os.path.getmtime(dest)]
                    except OSError:
                        self._cache.pop(dest, None)
                    return digest

                headers = {"User-Agent": UA}
                mode    = "wb"
                if got:
                    headers["Range"] = f"bytes={got}-"
                    mode = "ab"
                    self.log(f"  Resuming ({fmt_size(got)} / {total_str})…")
                else:
                    self.log(f"  Downloading ({total_str})…")

                req = urllib.request.Request(url, headers=headers)
                downloaded = got
                # Hash on the fly when starting from byte 0 — saves a full
                # re-read of the file for verification. A resumed download
                # can't be hashed incrementally (the prefix wasn't seen).
                hasher = hashlib.sha1() if not got else None
                # Speed sampling over a short sliding window.
                t0 = time.monotonic()
                bytes_at_t0 = downloaded
                speed_str = ""
                with secure_urlopen(req, timeout=DOWNLOAD_TIMEOUT,
                                    allowed_hosts=ALLOWED_DOWNLOAD_HOSTS) as r:
                    status = getattr(r, "status", None) or r.getcode()
                    if got and status != 206:
                        # Server ignored the Range header — start over.
                        downloaded, mode = 0, "wb"
                        hasher = hashlib.sha1()
                        bytes_at_t0 = 0
                    with open(tmp, mode) as f:
                        while True:
                            if self._cancel:
                                raise RuntimeError("Cancelled")
                            chunk = r.read(256 * 1024)
                            if not chunk:
                                break
                            f.write(chunk)
                            if hasher is not None:
                                hasher.update(chunk)
                            downloaded += len(chunk)
                            now = time.monotonic()
                            dt  = now - t0
                            if dt >= 0.5:
                                speed_str = "   •   " + fmt_speed(
                                    (downloaded - bytes_at_t0) / dt)
                                t0, bytes_at_t0 = now, downloaded
                            if size:
                                self.progress(
                                    downloaded / size,
                                    f"{name}   •   {fmt_size(downloaded)}"
                                    f" / {total_str}{speed_str}")

                # A dropped connection looks like a clean EOF — never accept
                # a short file as a finished download.
                if size and downloaded != size:
                    raise IOError("connection lost at "
                                  f"{fmt_size(downloaded)} / {total_str}")

                os.replace(tmp, dest)
                if hasher is not None:
                    digest = hasher.hexdigest().upper()
                    try:
                        # Seed the verify cache so the next verify pass
                        # doesn't need to rehash this file either.
                        self._cache[dest] = [digest, os.path.getmtime(dest)]
                    except OSError:
                        self._cache.pop(dest, None)
                    return digest
                self._cache.pop(dest, None)
                return None
            except Exception as e:
                if self._cancel:
                    raise RuntimeError("Cancelled")
                if getattr(e, "winerror", None) == 32:
                    raise RuntimeError(
                        f"Cannot replace {name} because it is in use. "
                        "Close WoW and any other launcher, then try again. "
                        "The completed download has been kept.") from e
                # Keep tmp — the next attempt resumes from where this one
                # stopped instead of redownloading from zero.
                self.log(f"  Attempt {attempt} failed: {e}", "err")
                if attempt < DOWNLOAD_RETRY:
                    wait = min(2 ** attempt, 10)
                    part = os.path.getsize(tmp) if os.path.exists(tmp) else 0
                    self.progress(
                        (part / size) if size else 0.0,
                        f"{name} — retrying ({attempt}/{DOWNLOAD_RETRY})…")
                    self.log(f"  Retrying in {wait} s…", "dim")
                    time.sleep(wait)
        raise RuntimeError(f"Download failed after {DOWNLOAD_RETRY} attempts: {url}")

    def _download_range(self, url: str, start: int, length: int) -> bytes:
        headers = {
            "User-Agent": UA,
            "Range": f"bytes={start}-{start + length - 1}",
        }
        req = urllib.request.Request(url, headers=headers)
        with secure_urlopen(req, timeout=DOWNLOAD_TIMEOUT,
                            allowed_hosts=ALLOWED_DOWNLOAD_HOSTS) as response:
            status = getattr(response, "status", None) or response.getcode()
            data = response.read(length + 1)
        if status not in (200, 206) or len(data) != length:
            raise IOError(f"Invalid HTTP range response ({status}, {len(data)} bytes)")
        return data

    def patch_torrent_piece(self, meta: TorrentMetadata, piece_index: int,
                            writable_keys: set, excluded: set) -> int:
        """Fetch, hash, then apply one complete piece through file ranges."""
        piece_start = piece_index * meta.piece_length
        piece_end = min(piece_start + meta.piece_length, meta.total_length)
        last_error = None
        for attempt in range(1, DOWNLOAD_RETRY + 1):
            if self._cancel:
                raise RuntimeError("Cancelled")
            try:
                blocks = []
                for rec in meta.files_for_piece(piece_index):
                    start = max(piece_start, rec["offset"])
                    end = min(piece_end, rec["offset"] + rec["length"])
                    rel_start = start - rec["offset"]
                    data = self._download_range(
                        meta.file_url(rec), rel_start, end - start)
                    blocks.append((rec, rel_start, data))
                piece_data = b"".join(data for _rec, _start, data in blocks)
                if hashlib.sha1(piece_data).digest() != meta.pieces[piece_index]:
                    raise IOError("torrent piece hash mismatch")
                # Nothing touches disk until the complete server piece passes
                # its hash, keeping interrupted retries deterministic.
                for rec, rel_start, data in blocks:
                    if rec["key"] in excluded or rec["key"] not in writable_keys:
                        continue
                    dest = os.path.join(self.out_dir, *rec["parts"])
                    with open(dest, "r+b") as handle:
                        handle.seek(rel_start)
                        handle.write(data)
                return len(piece_data)
            except Exception as e:
                last_error = e
                if attempt < DOWNLOAD_RETRY:
                    self.log(f"  Piece {piece_index + 1} attempt {attempt} "
                             f"failed: {e}", "err")
                    time.sleep(min(2 ** attempt, 10))
        raise RuntimeError(
            f"Could not download torrent piece {piece_index + 1}: {last_error}")

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

        # fmt: off
        return [
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
            ("cameraSkipFix", "bytes", None, [
                (0x02ccd0, bytes([
                    0x55,0x8b,0x05,0x48,0x4e,0x88,0x00,0x8b,0x0d,0x44,0x4e,0x88,0x00,0xe9,0x33,0x90,
                    0x32,0x00,0x83,0xc0,0x32,0x83,0xc1,0x32,0x3b,0x0d,0xa8,0xeb,0xc4,0x00,0x7e,0x03,
                    0x83,0xe9,0x01,0x3b,0x05,0xac,0xeb,0xc4,0x00,0x7e,0x03,0x83,0xe8,0x01,0x83,0xe9,
                    0x32,0x83,0xe8,0x32,0x89,0x05,0x48,0x4e,0x88,0x00,0x89,0x0d,0x44,0x4e,0x88,0x00,
                    0x5d,0xeb,0x0d,
                ])),
                (0x02d326, bytes([0xe9,0xb1,0x8a,0x32,0x00])),
                (0x02d334, bytes([0x8b,0x35,0x48,0x4e,0x88,0x00])),
                (0x355d15, bytes([
                    0x83,0xf8,0x32,0x7d,0x03,0x83,0xc0,0x01,0x83,0xf9,0x32,
                    0x7d,0x03,0x83,0xc1,0x01,0xe9,0xb8,0x6f,0xcd,0xff,
                ])),
                (0x355ddc, bytes([
                    0x8d,0x4d,0xf0,0x51,
                    0xff,0x35,0x00,0x4e,0x88,0x00,0xff,0x15,0x50,0xf6,0x7f,0x00,0x8b,0x45,0xf0,0x8b,
                    0x15,0x44,0x4e,0x88,0x00,0xe9,0x35,0x75,0xcd,0xff,
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
        original_hash = sha1_file(exe)
        self.log_q.put((f"__ORIGINAL_HASH__{original_hash}", ""))
        with open(exe, "rb") as f:
            buf = bytearray(f.read())
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
                    if off < 0 or off + len(data) > len(buf):
                        raise RuntimeError(
                            f"Refusing out-of-bounds {label} patch at "
                            f"0x{off:x} for a {len(buf)}-byte WoW.exe")
                    buf[off: off + len(data)] = data
        with open(exe, "wb") as f:
            f.write(buf)
        self.log("WoW.exe patched.", "ok")

        patched_hash = sha1_file(exe)
        self.log_q.put((f"__PATCHED_HASH__{patched_hash}", ""))

    def run(self, diff_nodes=None):
        try:
            if is_wow_running():
                raise RuntimeError(
                    "WoW.exe is currently running. Close the game before updating.")
            self.progress(0.02, "Fetching update metadata…")
            self.log("Fetching client.torrent metadata…")
            meta = fetch_torrent_metadata()
            excluded = _torrent_owned_paths()
            requested = {str(k).replace("\\", "/").lower()
                         for k in (diff_nodes or [])}
            requested.update(f["key"] for f in quick_torrent_diff(
                meta, self.out_dir, excluded))
            if not _torrent_state().get("files") and not requested:
                requested.update(f["key"] for f in verify_torrent_files(
                    meta, self.out_dir, excluded,
                    lambda: self._cancel,
                    lambda p: self.progress(0.03 + p * 0.20,
                                            f"Verifying… {int(p * 100)}%")))
            targets, patch_pieces = torrent_download_plan(
                meta, self.out_dir, requested, excluded)
            writable_keys = requested - excluded
            downloaded_keys = {f["key"] for f in targets}
            for index in patch_pieces:
                downloaded_keys.update(
                    f["key"] for f in meta.files_for_piece(index)
                    if f["key"] in writable_keys)

            self.log("\nStarting HTTPS web-seed update…\n")
            self.log("Peer-to-peer networking and seeding are disabled.", "dim")
            total_bytes = (sum(f["length"] for f in targets)
                           + sum(min(meta.piece_length,
                                     meta.total_length - i * meta.piece_length)
                                 for i in patch_pieces))
            if targets or patch_pieces:
                detail = []
                if targets:
                    detail.append(f"{len(targets)} whole file(s)")
                if patch_pieces:
                    detail.append(f"{len(patch_pieces)} changed piece(s)")
                self.log(f"Downloading {fmt_size(total_bytes)} via HTTPS "
                         f"({', '.join(detail)}).", "acct")
            else:
                self.log("No client files need downloading.", "dim")

            for rec in targets:
                if self._cancel:
                    raise RuntimeError("Cancelled")
                rel = os.path.join(*rec["parts"])
                self.log(f"[file] {rel}", "acct")
                self.download(meta.file_url(rec),
                              os.path.join(self.out_dir, *rec["parts"]),
                              rec["length"], rel)

            if patch_pieces:
                self.log("Applying changed torrent pieces through HTTPS ranges…",
                         "acct")
                patched_bytes = 0
                ordered_pieces = sorted(patch_pieces)
                patch_total = sum(
                    min(meta.piece_length,
                        meta.total_length - i * meta.piece_length)
                    for i in ordered_pieces)
                for number, index in enumerate(ordered_pieces, 1):
                    patched_bytes += self.patch_torrent_piece(
                        meta, index, writable_keys, excluded)
                    self.progress(
                        number / len(ordered_pieces) * 0.85,
                        f"Changed pieces   •   {fmt_size(patched_bytes)}"
                        f" / {fmt_size(patch_total)}")

            affected_pieces = set()
            for rec in targets:
                affected_pieces.update(range(rec["first_piece"],
                                             rec["last_piece"] + 1))
            affected_pieces.update(patch_pieces)
            if affected_pieces:
                self.progress(0.88, "Checking downloaded data…")
                failed = verify_torrent_piece_subset(
                    meta, self.out_dir, affected_pieces, excluded,
                    lambda: self._cancel,
                    lambda p: self.progress(0.88 + p * 0.06,
                                            f"Checking download… {int(p * 100)}%"))
                if failed:
                    retry_keys = {
                        f["key"] for i in failed for f in meta.files_for_piece(i)
                        if f["key"] not in excluded
                    }
                    downloaded_keys.update(retry_keys)
                    self.log("Torrent hash mismatch — redownloading affected files.",
                             "err")
                    for rec in meta.files:
                        if rec["key"] not in retry_keys:
                            continue
                        dest = os.path.join(self.out_dir, *rec["parts"])
                        try:
                            os.remove(dest)
                        except OSError:
                            pass
                        self.download(meta.file_url(rec), dest,
                                      rec["length"], rec["rel"])
                    retry_pieces = {
                        i for rec in meta.files if rec["key"] in retry_keys
                        for i in range(rec["first_piece"], rec["last_piece"] + 1)
                    }
                    failed = verify_torrent_piece_subset(
                        meta, self.out_dir, retry_pieces, excluded,
                        lambda: self._cancel, lambda _p: None)
                    if failed:
                        raise RuntimeError(
                            "Downloaded files did not match the torrent hashes")

            if self._cancel:
                self.log("\nUpdate cancelled.", "err")
                self.progress(0.0, "Cancelled")
                self.log_q.put(("__ERROR__", ""))
                return

            self.log("\nDownload complete.", "ok")
            remove_wdb(self.out_dir)
            prune_legacy_client_files(meta, self.out_dir)

            wow_exe_updated = "wow.exe" in downloaded_keys
            if wow_exe_updated:
                self.progress(0.92, "Patching…")
                self.patch_exe()
            else:
                self.log("\nWoW.exe unchanged — skipping patch.", "dim")
                self.progress(0.95, "")

            # Config.wtf is user config — never written here. It's created when
            # missing during verification and overwritten only on a folder
            # change; a regular update must never touch it.
            self.progress(1.0, "")
            save_cache(self._cache)
            _save_torrent_state(meta)
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
        "frillDensity": 48,
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
        "description": "Eliminates stuttering and animation lag. REQUIRED BY OTHER MODS.",
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
        "register_dll":    "VfPatcher.dll",
        "installed_files": ["VfPatcher.dll", "VanillaFixes.exe"],
    },
    {
        "id":          "ClassicAPI",
        "essential": True,
        "name":        "ClassicAPI",
        "description": "Adds Lua API calls from later WoW versions. Required by addons.",
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
        "id":          "dxvk",
        "essential": True,
        "name":        "dxvk",
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
        "register_dll":    "dxvk",
        "installed_files": ["d3d9.dll", "dxvk.conf"],
    },
    {
        "id":          "nampower",
        "essential": True,
        "name":        "nampower",
        "description": "A client modification that minimizes your input lag if you have higher latency.",
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
        "description": "Expands the client API with backported features from later WoW versions. Required by addons.",
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
        "name":        "transmogfix",
        "description": "A client-side fix that eliminates frame drops caused by the server transmogrification durability workaround.",
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
        "description": "Introduces modern quality-of-life features and improvements.",
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
        "description": "Fixes the client misbehaving on multi-monitor setups with differing resolutions.",
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
                              "VMMFix_preferred_monitor.txt"},
        },
        "register_dll":    "VanillaMultiMonitorFix.dll",
        "installed_files": ["VanillaMultiMonitorFix.dll",
                            "VMMFix_preferred_monitor.txt"],
    },
]

GITHUB_API = "https://api.github.com"
MOD_UA     = f"OctoUpdater/{UPDATER_VERSION}"

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
            headers={"User-Agent": MOD_UA})
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
        req = urllib.request.Request(url, headers={"User-Agent": MOD_UA})
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
# Triple buffering (needed for smooth G-SYNC + RTSS capping) can try lowering backbuffers to 2 if want
dxvk.presentInterval = 0
dxvk.numBackBuffers = 3
# Use hardware mouse for responsiveness
d3d9.cursor = 1
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
        req = urllib.request.Request(url, headers={"User-Agent": MOD_UA})
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
                                     headers={"User-Agent": MOD_UA})
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
                                     headers={"User-Agent": MOD_UA})
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
        req = urllib.request.Request(src["url"], headers={"User-Agent": MOD_UA})
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
        req = urllib.request.Request(url, headers={"User-Agent": MOD_UA})
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
    "_LazyPig":             "https://github.com/Otari98/_LazyPig",
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
    "T-RestedXP":           "https://github.com/whtmst/T-RestedXP",
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
            '    f.Default:SetPoint("BOTTOM", 0, 125)\n'
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
    "alwaysAutoLoot":  True,
    "nameplateRange":  41,
    "fieldOfView":     110,
    "farClip":         777,
    "frillDistance":   70,
    "cameraDistance":  50,
    "soundInBackground": True,
}

TWEAKS_ITEMS = [
    (None, "GENERAL", "section", False, None, None, None, None, None),

    ("alwaysAutoLoot",    "Always auto-loot",        "checkbox", True,  None,
     "Reverses auto-loot behavior to always auto-loot.",
     None, None, None),

    ("nameplateRange",    "Nameplate range",          "number",   False, None,
     "Distance at which nameplates are visible.",
     0, 41, 1),

    (None, "CAMERA", "section", False, None, None, None, None, None),

    ("fieldOfView",       "Field of View",            "number",   False, None,
     "Recommended values for aspect ratios: [4:3 = 90] [16:9 = 110] [21:9 = 150] [32:9 = 180]",
     90, 180, 5),

    ("farClip",           "Render distance",          "number",   False, None,
     "Maximum render distance. May cause crashes. [Vanilla max: 777] [Tweaks max: 10000]",
     100, 10000, 1),

    ("frillDistance",     "Ground clutter distance",  "number",   False, None,
     "Ground clutter render distance. [Vanilla max: 70] [Tweaks max: 300]",
     0, 300, 1),

    ("cameraDistance",    "Camera distance",          "number",   False, None,
     "Maximum camera (zoom out) distance. [Vanilla max: 50] [Tweaks max: 100]",
     50, 100, 1),

    (None, "SOUND", "section", False, None, None, None, None, None),

    ("soundInBackground", "Background sounds",        "checkbox", True,  None,
     "Allows game sounds to play while the game is minimized.",
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


def fetch_news_items() -> list:
    """news.json → [{id, title, date, body, url?, author?}, …]"""
    req = urllib.request.Request(NEWS_URL, headers={"User-Agent": UA})
    with secure_urlopen(req, timeout=NEWS_TIMEOUT) as r:
        data = json.load(r)
    items = data.get("items", [])
    # news.json lists topics in forum order — show newest first (ISO dates
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
        # Keep the window hidden until it's positioned and fully built, so it
        # never flashes at the default top-left corner before centering.
        self.withdraw()

        # Detect first run before anything writes the config.
        self._first_run  = not os.path.exists(CONFIG_FILE)
        # On first run Settings auto-opens with the folder auto-set to the
        # current dir. If the user closes it without changing the folder or
        # adding a Defender exclusion, recommend the exclusion once on close.
        self._first_run_av_pending = self._first_run
        # On first run we don't verify (fetch metadata / touch Config.wtf)
        # until the user closes Settings, so nothing is written to the default
        # folder before they've picked their real game folder. A folder change
        # supersedes this (it verifies the new folder right away).
        self._first_run_verify_pending = self._first_run
        self._cfg        = load_config()
        self._running    = False
        # True only after a verify/update confirmed the client files are up
        # to date. PLAY is gated on this AND on no mod being in an error state.
        self._client_ready = False
        self._worker: UpdateWorker | None = None
        self._log_q:  queue.Queue = queue.Queue()
        self._prog_q: queue.Queue = queue.Queue()
        self._diff_nodes = None
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

        # Game folder path — shared by the Settings modal; changing it fires
        # the folder-change reset via the trace.
        self._path_var = tk.StringVar(
            value=os.path.normpath(self._cfg.get("out_dir", DEFAULT_OUT_DIR)))
        self._last_path_val = os.path.normpath(self._path_var.get().strip())
        self._path_var.trace_add("write", self._on_path_changed)

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
        # {folder: {"error": msg, "git": url}} for failed installs/updates —
        # survives the post-operation rescan so rows can show what went wrong.
        self._addon_errors = {}
        self._addon_sections_open = {"INSTALLED": True, "AVAILABLE": True}

        # News feed cache (featured post and announcements cached separately)
        self._feat_ts    = 0.0
        self._news_ts    = 0.0
        self._news_items = None
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

        out_dir = self._cfg.get("out_dir", DEFAULT_OUT_DIR)
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
        # On first run, defer verification until Settings is closed (see
        # _close_settings / _first_run_verify_pending).
        if not self._first_run:
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
        # Daily self-update check (cached), last so it never delays the rest.
        self.after(2000, lambda: threading.Thread(
            target=self._check_updater_update, daemon=True).start())
        # First launch: open Settings so the user sets the game folder etc.
        if self._first_run:
            self.after(500, self._open_settings)

        # Everything is positioned and built — reveal the centered window.
        self.deiconify()

    # ── build ─────────────────────────────────────────────────────────────────

    def _on_close(self):
        """Hide the window first so the close feels instant
        Config/caches are already saved at write time,
        and the worker threads are daemons, so nothing blocks the exit."""
        try:
            self.withdraw()
        except Exception:
            pass
        self.quit()

    def _add_tooltip(self, widget, text: str):
        """Attach a small hover tooltip to a widget."""
        state = {"win": None}

        def show(_e=None):
            if state["win"] is not None:
                return
            x = widget.winfo_rootx() + 12
            y = widget.winfo_rooty() + widget.winfo_height() + 4
            tw = tk.Toplevel(self)
            tw.wm_overrideredirect(True)
            tw.wm_geometry(f"+{x}+{y}")
            tk.Label(tw, text=text, font=("Segoe UI", 9),
                     fg=C_TEXT, bg="#0f0b16",
                     highlightthickness=1, highlightbackground=C_PANEL_BDR,
                     padx=6, pady=2).pack()
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
        cx, cy = self._nav_pos[tab], 54
        font = ("Segoe UI", 11, "bold")
        if tab == self._active_tab:
            for r, col in ((2, "#42340f"), (1, "#7a5c1d")):
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
        if count:
            bx = cx + self._nav_text_w[tab] // 2 + 11
            by = cy - 11
            # Canvas oval, not a ● glyph: the oval gives exact geometric
            # control so the number always centers, consistently across OSes.
            # (A filled-circle glyph antialiases nicely but its disk isn't
            # centered in the glyph box — by a font-specific amount — so the
            # number drifts off-centre and can't be corrected reliably.)
            cv.create_oval(bx - 8, by - 8, bx + 8, by + 8,
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

        PANEL_TOP = 119
        PANEL_H   = WIN_H - PANEL_TOP - FOOT_H - 10

        # Panels stay mapped and stacked; switching tabs only raises the
        # active one. place_forget()/place() would unmap and remap the whole
        # widget tree of a populated panel (hundreds of widgets) every
        # switch — a visible synchronous stall.
        panels = {"NEWS":   self._news_panel,
                  "TWEAKS": self._tweaks_panel_frame,
                  "ADDONS": self._addons_panel_frame,
                  "MODS":   self._mods_panel_frame}
        target = panels.get(tab, self._news_panel)
        if not target.winfo_ismapped():
            target.place(x=40, y=PANEL_TOP,
                         width=WIN_W - 80, height=PANEL_H)
        target.tkraise()
        self._active_panel = target

        if tab == "MODS":
            threading.Thread(target=self._load_mods_state, daemon=True).start()
        elif tab == "TWEAKS":
            self._refresh_tweaks_panel()
        elif tab == "ADDONS":
            self._addons_verify()
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
        bloom_cx, bloom_cy = WIN_W - 80, 80
        for i in range(40, 0, -1):
            r  = i * 9
            alpha_frac = (40 - i) / 40
            r_val = int(0x12 + alpha_frac * (0x2e - 0x12))
            g_val = int(0x0e + alpha_frac * (0x18 - 0x0e))
            b_val = int(0x1a + alpha_frac * (0x50 - 0x1a))
            col = f"#{r_val:02x}{g_val:02x}{b_val:02x}"
            c.create_oval(bloom_cx - r, bloom_cy - r,
                          bloom_cx + r, bloom_cy + r,
                          fill=col, outline="")

        c.create_line(0, WIN_H - 1, WIN_W, WIN_H - 1, fill=C_PANEL_BDR)

    def _build_header(self):
        HDR_H = 108

        hdr = tk.Canvas(self, width=WIN_W, height=HDR_H,
                        bg=C_BG, highlightthickness=0)
        hdr.place(x=0, y=0, width=WIN_W, height=HDR_H)
        self._hdr_canvas = hdr

        # Same corner bloom as the main background (identical coordinates
        # and colors) so the header blends seamlessly with the body instead
        # of sitting as a darker separated band.
        bloom_cx, bloom_cy = WIN_W - 80, 80
        for i in range(40, 0, -1):
            r = i * 9
            alpha_frac = (40 - i) / 40
            r_val = int(0x12 + alpha_frac * (0x2e - 0x12))
            g_val = int(0x0e + alpha_frac * (0x18 - 0x0e))
            b_val = int(0x1a + alpha_frac * (0x50 - 0x1a))
            col = f"#{r_val:02x}{g_val:02x}{b_val:02x}"
            hdr.create_oval(bloom_cx - r, bloom_cy - r,
                            bloom_cx + r, bloom_cy + r,
                            fill=col, outline="")

        import tkinter.font as tkfont

        self._logo_y = HDR_H // 2 - 6
        self._draw_logo()

        nav_font = tkfont.Font(family="Segoe UI", size=11, weight="bold")
        tabs = ["NEWS", "TWEAKS", "ADDONS", "MODS"]
        self._active_tab  = "NEWS"
        self._nav_pos     = {}
        self._nav_text_w  = {}
        self._hdr_regions = {}
        x = 240
        for tab in tabs:
            w = nav_font.measure(tab) + 36
            self._nav_pos[tab]     = x + w // 2
            self._nav_text_w[tab]  = nav_font.measure(tab)
            self._hdr_regions[tab] = (x, 0, x + w, HDR_H)
            x += w
            self._draw_nav_tab(tab)

        self._hdr_regions["gear"] = (WIN_W - 36, 2, WIN_W - 2, 34)
        self._draw_gear()

        # The wordmark is a clickable header element too (opens the repo).
        lb = hdr.bbox("logo")
        if lb:
            self._hdr_regions["logo"] = (lb[0] - 4, lb[1] - 4,
                                         lb[2] + 6, lb[3] + 4)
            self._logo_cx = (lb[0] + lb[2]) // 2
        else:
            self._logo_cx = 127
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
        # Deferred "install missing" pending from turning an auto-install
        # option on in Settings — applied on close (see _close_settings).
        self._auto_mods_retrigger = False
        self._auto_addons_retrigger = False

    def _draw_logo(self, hover: bool = False):
        cv = self._hdr_canvas
        cv.delete("logo")
        cv.create_text(24, self._logo_y, text="Octo Updater",
                       font=("Segoe UI", 24, "bold"),
                       fill="#b478d9" if hover else "#9a5cbf",
                       anchor="w", tags="logo")

    def _draw_update_label(self, hover: bool = False):
        cv = self._hdr_canvas
        cv.delete("upd_label")
        self._hdr_regions.pop("update", None)
        if not self._update_available:
            return
        cv.create_text(self._logo_cx, self._logo_y + 26,
                       text="Update available!",
                       font=("Segoe UI", 10, "bold"),
                       fill=C_GOLD_LT if hover else C_GOLD,
                       anchor="n", tags="upd_label")
        lb = cv.bbox("upd_label")
        if lb:
            self._hdr_regions["update"] = (lb[0] - 4, lb[1] - 2,
                                           lb[2] + 4, lb[3] + 2)

    def _draw_gear(self, hover: bool = False):
        cv = self._hdr_canvas
        cv.delete("gear_icon")
        cv.create_text(WIN_W - 10, 8, text="⚙", font=("Segoe UI", 13),
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
        PANEL_TOP  = 109
        PANEL_BOT  = FOOT_H
        PANEL_H    = WIN_H - PANEL_TOP - PANEL_BOT
        PAD        = 40

        panel = tk.Frame(self, bg=C_BG)
        panel.place(x=PAD, y=PANEL_TOP + 10,
                    width=WIN_W - PAD * 2,
                    height=PANEL_H - 20)
        self._news_panel = panel
        self._active_panel = panel   # NEWS is the initial tab

        inner_w = WIN_W - PAD * 2
        self._news_left_w  = int(inner_w * 0.60)
        self._news_right_w = inner_w - self._news_left_w - 12

        # Featured forum post — parchment panel (left)
        feat = tk.Frame(panel, bg=C_PARCH)
        feat.place(x=0, y=0, width=self._news_left_w, relheight=1.0)
        self._feat_frame = feat

        # Announcements list (right)
        ann = tk.Frame(panel, bg=C_PANEL,
                       highlightthickness=1,
                       highlightbackground=C_PANEL_BDR)
        ann.place(x=self._news_left_w + 12, y=0,
                  width=self._news_right_w, relheight=1.0)
        self._ann_frame = ann

        self._render_featured(None, loading=True)
        self._render_announcements(None, loading=True)

        self._log_line("Octo Updater  v" + UPDATER_VERSION + "\n", "acct")
        self._log_line("─" * 60 + "\n", "dim")
        self._build_mods_panel()
        self._build_tweaks_panel()
        self._build_addons_panel()

    # ── news panel ───────────────────────────────────────────────────────────

    def _load_news(self, force=False):
        self._load_featured(force)
        self._load_announcements(force)

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

    def _load_announcements(self, force=False):
        now = time.time()
        if (not force and self._news_items is not None
                and (now - self._news_ts) < NEWS_CACHE_TTL):
            return
        self._render_announcements(None, loading=True)

        def worker():
            items, err = None, ""
            try:
                items = fetch_news_items()
            except Exception:
                err = "Couldn't reach the news feed."

            def apply():
                self._news_ts    = time.time()
                self._news_items = items
                self._render_announcements(items, error=err)
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
        hdr.pack(fill="x", padx=20, pady=(16, 12))
        tk.Label(hdr,
                 text=title.upper() if title else "NEWS",
                 font=("Segoe UI", 13, "bold"),
                 fg=C_PARCH_TITLE, bg=C_PARCH_BAND,
                 wraplength=self._news_left_w - 100,
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
                     fg=C_PARCH_DIM, bg=C_PARCH).pack(padx=20, pady=16,
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
                 anchor="w").pack(fill="x", padx=20, pady=10)
        tk.Frame(f, bg=C_PARCH_LINE, height=1).pack(fill="x")

        # Pack the link first with side="bottom" so it's always reserved its
        # space; the body Text (which defaults to 24 lines tall) then fills
        # only the remaining area instead of clipping the link off the panel.
        if post.get("url"):
            link = tk.Label(f, text="⧉  Read full post on the forum",
                            font=("Segoe UI", 11),
                            fg=C_PARCH_LINK, bg=C_PARCH,
                            cursor="hand2", anchor="w")
            link.pack(side="bottom", fill="x", padx=20, pady=(4, 16))
            link.bind("<Button-1>",
                      lambda e, u=post["url"]: self._open_url(u))
            link.bind("<Enter>", lambda e: link.configure(fg=C_PARCH_TITLE))
            link.bind("<Leave>", lambda e: link.configure(fg=C_PARCH_LINK))

        body = _strip_html(post.get("html", ""))
        txt = tk.Text(f, bg=C_PARCH, fg=C_PARCH_TEXT, relief="flat",
                      font=("Segoe UI", 11), wrap="word", height=1,
                      padx=2, pady=8, spacing2=4, spacing3=4,
                      highlightthickness=0, cursor="arrow")
        txt.insert("1.0", body)
        txt.configure(state="disabled")
        txt.pack(fill="both", expand=True, padx=20, pady=(8, 2))

    def _render_announcements(self, items, loading=False, error=""):
        f = self._ann_frame
        for w in f.winfo_children():
            w.destroy()

        hdr = tk.Frame(f, bg=C_PANEL)
        hdr.pack(fill="x", padx=14, pady=(16, 10))
        tk.Label(hdr, text="ANNOUNCEMENTS",
                 font=("Segoe UI", 12, "bold"),
                 fg=C_GOLD, bg=C_PANEL).pack(side="left")
        rf = tk.Label(hdr, text="⟳", font=("Segoe UI", 14),
                      fg=C_TEXT_DIM, bg=C_PANEL, cursor="hand2")
        rf.pack(side="right")
        rf.bind("<Button-1>", lambda e: self._load_announcements(force=True))
        rf.bind("<Enter>",    lambda e: rf.configure(fg=C_GOLD))
        rf.bind("<Leave>",    lambda e: rf.configure(fg=C_TEXT_DIM))

        tk.Frame(f, bg=C_DIVIDER, height=1).pack(fill="x", padx=14)

        if items is None or error:
            msg = error or ("Loading…" if loading
                            else "Couldn't reach the news feed.")
            tk.Label(f, text=msg, font=FONT_BODY,
                     fg=C_TEXT_DIM, bg=C_PANEL).pack(padx=14, pady=12,
                                                     anchor="w")
            return
        if not items:
            tk.Label(f, text="No news yet — check back later.",
                     font=FONT_BODY, fg=C_TEXT_DIM,
                     bg=C_PANEL).pack(padx=14, pady=12, anchor="w")
            return

        list_frame = tk.Frame(f, bg=C_PANEL)
        list_frame.pack(fill="both", expand=True, padx=(14, 4), pady=(0, 10))
        canvas = tk.Canvas(list_frame, bg=C_PANEL, highlightthickness=0)
        sb = SlimScrollbar(list_frame, command=canvas.yview, bg=C_PANEL)
        self._wheel_canvases.append(canvas)
        inner = tk.Frame(canvas, bg=C_PANEL)
        inner.bind("<Configure>",
                   lambda e: canvas.configure(scrollregion=canvas.bbox("all")))
        canvas.create_window((0, 0), window=inner, anchor="nw",
                             width=self._news_right_w - 40)
        canvas.configure(yscrollcommand=sb.set)
        sb.pack(side="right", fill="y")
        canvas.pack(side="left", fill="both", expand=True)

        wrap_w = self._news_right_w - 50
        for item in items:
            top = tk.Frame(inner, bg=C_PANEL)
            top.pack(fill="x", pady=(12, 0))
            tk.Label(top, text=_format_news_date(item.get("date", "")),
                     font=("Segoe UI", 9), fg=C_TEXT_DIM,
                     bg=C_PANEL).pack(side="right", anchor="n")
            tk.Label(top, text=item.get("title", ""),
                     font=("Segoe UI", 11, "bold"),
                     fg=C_GOLD, bg=C_PANEL,
                     wraplength=wrap_w - 85, justify="left",
                     anchor="w").pack(side="left", fill="x", expand=True)

            if item.get("author"):
                tk.Label(inner, text=f"by {item['author']}",
                         font=("Segoe UI", 10, "italic"),
                         fg=C_TEXT_DIM, bg=C_PANEL,
                         anchor="w").pack(fill="x", pady=(2, 0))

            body = item.get("body", "").strip()
            if len(body) > 260:
                body = body[:260].rstrip() + "…"
            if body:
                tk.Label(inner, text=body, font=("Segoe UI", 10),
                         fg=C_TEXT, bg=C_PANEL,
                         wraplength=wrap_w, justify="left",
                         anchor="w").pack(fill="x", pady=(5, 0))

            if item.get("url"):
                lnk = tk.Label(inner, text="⧉ Read more",
                               font=("Segoe UI", 10),
                               fg=C_GOLD, bg=C_PANEL,
                               cursor="hand2", anchor="w")
                lnk.pack(fill="x", pady=(5, 0))
                lnk.bind("<Button-1>",
                         lambda e, u=item["url"]: self._open_url(u))
                lnk.bind("<Enter>", lambda e, w=lnk: w.configure(fg=C_GOLD_LT))
                lnk.bind("<Leave>", lambda e, w=lnk: w.configure(fg=C_GOLD))

            tk.Frame(inner, bg=C_DIVIDER, height=1).pack(fill="x",
                                                         pady=(12, 0))

    # ── tweaks panel ─────────────────────────────────────────────────────────────

    def _build_tweaks_panel(self):
        outer = tk.Frame(self, bg=C_PANEL,
                         highlightthickness=1,
                         highlightbackground=C_PANEL_BDR,
                         highlightcolor=C_PANEL_BDR)
        self._tweaks_panel_frame = outer

        self._tweaks_inner = tk.Frame(outer, bg=C_PANEL)
        self._tweaks_inner.pack(fill="both", expand=True)

        tk.Frame(outer, bg=C_DIVIDER, height=1).pack(fill="x", padx=16)
        foot = tk.Frame(outer, bg=C_PANEL)
        foot.pack(fill="x", padx=16, pady=(6, 10))

        # Packed on demand by _refresh_tweaks_buttons(): Apply appears only
        # when UI values differ from the saved config, Reset only when the
        # saved values differ from the defaults.
        apl = tk.Label(foot, text="Apply", font=("Segoe UI", 11),
                       fg=C_TEXT, bg=C_PANEL_BDR, cursor="hand2",
                       padx=16, pady=4)
        apl.bind("<Button-1>", lambda e: self._apply_tweaks())
        apl.bind("<Enter>",    lambda e: apl.configure(bg=C_GOLD, fg="#000"))
        apl.bind("<Leave>",    lambda e: apl.configure(bg=C_PANEL_BDR, fg=C_TEXT))
        self._tweaks_apply_btn = apl

        rst = tk.Label(foot, text="Reset", font=("Segoe UI", 11),
                       fg=C_TEXT, bg=C_PANEL_BDR, cursor="hand2",
                       padx=16, pady=4)
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
        PAD_X  = 16

        for (tid, label, kind, recommended, _, desc, mn, mx, step) in TWEAKS_ITEMS:
            if kind == "section":
                tk.Label(self._tweaks_inner, text=label,
                         font=("Segoe UI", 11, "bold"),
                         fg=C_GOLD, bg=C_PANEL,
                         anchor="w").pack(fill="x", padx=PAD_X, pady=(10, 2))
                tk.Frame(self._tweaks_inner, bg=C_DIVIDER, height=1).pack(
                    fill="x", padx=PAD_X, pady=(0, 4))
                continue

            row = tk.Frame(self._tweaks_inner, bg=C_PANEL)
            row.pack(fill="x", padx=PAD_X, pady=3)

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
                               ).pack(side="left", padx=(4, 12))
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
                entry.pack(side="left", padx=(4, 12), ipady=3)
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

            if desc:
                tk.Label(row, text=desc,
                         font=("Segoe UI", 10), fg=C_TEXT_DIM, bg=C_PANEL,
                         wraplength=520, justify="left", anchor="w"
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
            return {k: (bool(d.get(k))
                        if isinstance(TWEAKS_DEFAULTS.get(k), bool)
                        else int(d.get(k, 0)))
                    for k in ui}

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
            self._tweaks_reset_btn.pack(side="left",
                                        padx=(8, 0) if dirty else (0, 0))

    def _refresh_tweaks_panel(self):
        values = load_tweaks_config()
        for tid, var in self._tweak_vars.items():
            v = values.get(tid, TWEAKS_DEFAULTS.get(tid))
            if isinstance(var, tk.BooleanVar):
                var.set(bool(v))
            else:
                var.set(str(int(v)) if v is not None else "")

    def _get_tweaks_from_ui(self) -> dict:
        """Read tweak values from the UI, always clamped to their limits —
        an out-of-range entry can never reach the config or the exe patch."""
        result = {}
        for tid, var in self._tweak_vars.items():
            if isinstance(var, tk.BooleanVar):
                result[tid] = var.get()
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
        out = self._path_var.get().strip()
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

        out = self._path_var.get().strip()
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
            exe_path = os.path.join(client_dir, "WoW.exe")

            fresh_cfg        = load_config()
            expected_patched = fresh_cfg.get("expected_patched_wow_hash", "")
            original_server  = fresh_cfg.get("original_server_wow_hash", "")
            local_before     = sha1_file(exe_path) if os.path.exists(exe_path) else ""

            worker.patch_exe(tweaks)
            drain()

            update_config_wtf(client_dir, tweaks)

            local_after = sha1_file(exe_path) if os.path.exists(exe_path) else ""

            def _set_hashes(c):
                c["expected_patched_wow_hash"] = local_after
                if local_before == expected_patched and original_server:
                    c["original_server_wow_hash"] = original_server
                else:
                    c.pop("original_server_wow_hash", None)
            self._cfg = update_config(_set_hashes)

            self._log_line("\nTweaks applied.\n", "ok")
            self.after(0, self._refresh_ready_state)
        except Exception as e:
            drain()
            self._log_line(f"\n✗ Tweak patch failed: {e}\n", "err")

            def _fail_state():
                self._status_var.set("Tweaks failed — check the log")
                self._set_btn_update()
            self.after(0, _fail_state)

    # ── mods panel ───────────────────────────────────────────────────────────────

    def _build_mods_panel(self):
        PAD       = 18
        PANEL_TOP = 119
        PANEL_H   = WIN_H - PANEL_TOP - FOOT_H - 10

        outer = tk.Frame(self, bg=C_PANEL,
                         highlightthickness=1,
                         highlightbackground=C_PANEL_BDR)
        self._mods_panel_frame = outer

        note = tk.Frame(outer, bg=C_PANEL)
        note.pack(fill="x", padx=16, pady=(14, 8), anchor="w")
        tk.Label(note, text="Mods marked with ",
                 font=("Segoe UI", 10), fg=C_TEXT_DIM,
                 bg=C_PANEL).pack(side="left")
        tk.Label(note, text="★", font=("Segoe UI", 10),
                 fg=C_GOLD, bg=C_PANEL).pack(side="left")
        tk.Label(note, text=" are essential",
                 font=("Segoe UI", 10), fg=C_TEXT_DIM,
                 bg=C_PANEL).pack(side="left")

        tk.Frame(outer, bg=C_DIVIDER, height=1).pack(fill="x", padx=16, pady=(0, 4))

        list_frame = tk.Frame(outer, bg=C_PANEL)
        list_frame.pack(fill="both", expand=True, padx=16)

        canvas = tk.Canvas(list_frame, bg=C_PANEL, highlightthickness=0)
        sb = SlimScrollbar(list_frame, command=canvas.yview, bg=C_PANEL)
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

        tk.Frame(outer, bg=C_DIVIDER, height=1).pack(fill="x", padx=16, pady=(4, 0))
        foot = tk.Frame(outer, bg=C_PANEL)
        foot.pack(fill="x", padx=16, pady=(6, 10))

        # Packed on demand by _refresh_apply_btn_visibility(): shown only
        # when there are unapplied checkbox changes or a mod is in error.
        self._apply_btn = tk.Label(foot, text="Apply",
                                   font=("Segoe UI", 11),
                                   fg=C_TEXT, bg=C_PANEL_BDR,
                                   cursor="hand2", padx=16, pady=4)
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

        mods_sorted = sorted(MODS_REGISTRY, key=lambda m: m["name"].lower())

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
                        refs["error_label"].pack(fill="x", pady=(0, 4))
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
            row.pack(fill="x", pady=5)

            name_f = tk.Frame(row, bg=C_PANEL, width=210)
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
                           ).pack(side="left", padx=(4, 8))

            # Right-side widgets are packed first so they stay pinned to the
            # panel's right edge; the description then fills the middle.
            ignore_var = tk.BooleanVar(value=ignore_upd)
            ig_f = tk.Frame(row, bg=C_PANEL)
            ig_f.pack(side="right", padx=(8, 0))
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
            link.pack(side="right", padx=4)
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
                                  bg=C_PANEL, wraplength=400,
                                  justify="left", anchor="w")
            desc_label.pack(side="left", fill="x", expand=True)

            existing_err = state.get("error")
            error_label = tk.Label(container, text="",
                                   font=("Segoe UI", 9), fg=C_ERR,
                                   bg=C_PANEL, anchor="w", padx=16)
            if existing_err:
                name_label.configure(fg=C_ERR)
                error_label.configure(text=f"  \u26a0  {existing_err}")
                error_label.pack(fill="x", pady=(0, 4))

            divider = tk.Frame(self._mods_inner, bg=C_DIVIDER, height=1)
            divider.pack(fill="x", pady=(2, 0))

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

    def _toggle_mod(self, mod_id: str, var: tk.BooleanVar):
        self._mod_pending_state.setdefault(mod_id, {})["enabled"] = var.get()
        self._refresh_apply_btn_visibility()

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
            lbl.pack(side="right", padx=(2, 8))
        elif mod_update_available(mod, state, live):
            lbl._base, lbl._hover = C_GOLD, C_GOLD_LT
            lbl.configure(text="update", fg=C_GOLD)
            lbl.pack(side="right", padx=(2, 8))
        else:
            lbl.pack_forget()

    def _update_mod(self, mod_id: str):
        """Download and install the newest release of a single mod (the
        per-row "update" label). Runs through the normal apply worker so
        errors/versions are recorded exactly like a manual Apply."""
        out = self._path_var.get().strip()
        if not out:
            return
        mod = next(m for m in MODS_REGISTRY if m["id"] == mod_id)
        self._log_line(f"\nUpdating {mod['name']}...\n", "acct")
        self._set_btn_busy("Installing…")
        self._status_var.set("Downloading mods…")
        threading.Thread(target=self._apply_mods_worker,
                         args=(out, mod_id), daemon=True).start()

    def _apply_mods(self):
        out = self._path_var.get().strip()
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

        out = self._path_var.get().strip()
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

        out = self._path_var.get().strip()
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
        # Arm the one-time "DXVK first launch" notice if dxvk gets (re)installed
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
                        refs["error_label"].pack(fill="x", pady=(0, 4))
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
        top.pack(fill="x", padx=16, pady=(4, 0))
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
        ent.pack(side="right", ipady=4, padx=(0, 6))

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
        list_frame.pack(fill="both", expand=True, padx=(16, 4))
        canvas = tk.Canvas(list_frame, bg=C_PANEL, highlightthickness=0)
        sb = SlimScrollbar(list_frame, command=canvas.yview, bg=C_PANEL)
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

        tk.Frame(outer, bg=C_DIVIDER, height=1).pack(fill="x", padx=16,
                                                     pady=(4, 0))
        foot = tk.Frame(outer, bg=C_PANEL)
        foot.pack(fill="x", padx=16, pady=(8, 12))
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
        client = self._path_var.get().strip()
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
                            and not _same_git_repo(saved["git"], override)):
                        # Installed from a different repo than the curated
                        # fork — offer an update that migrates to the fork.
                        rec.update(git=override, branch=None, ref=None,
                                   status="outOfDate")
                    elif saved and saved.get("git"):
                        rec.update(git=saved.get("git"),
                                   branch=saved.get("branch"),
                                   ref=saved.get("ref"))
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
        client = self._path_var.get().strip()
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
        client = self._path_var.get().strip()
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
        MW, MH = 560, 230
        panel = tk.Frame(ov, bg=P_BG, highlightthickness=1,
                         highlightbackground=P_BDR, highlightcolor=P_BDR)
        panel.place(x=(WIN_W - MW) // 2, y=(WIN_H - MH) // 2 - 20,
                    width=MW, height=MH)

        hdr = tk.Frame(panel, bg=P_HDR, height=46)
        hdr.pack(fill="x")
        hdr.pack_propagate(False)
        tk.Label(hdr, text="ADD CUSTOM GIT ADDON",
                 font=("Segoe UI", 13, "bold"),
                 fg=C_PURPLE, bg=P_HDR).pack(side="left", padx=18)
        x_btn = tk.Label(hdr, text="✕", font=("Segoe UI", 12),
                         fg=C_TEXT_DIM, bg=P_HDR, cursor="hand2")
        x_btn.pack(side="right", padx=16)
        x_btn.bind("<Button-1>", lambda e: self._close_settings())
        x_btn.bind("<Enter>",    lambda e: x_btn.configure(fg=C_TEXT))
        x_btn.bind("<Leave>",    lambda e: x_btn.configure(fg=C_TEXT_DIM))
        tk.Frame(panel, bg=P_BDR, height=1).pack(fill="x")

        body = tk.Frame(panel, bg=P_BG)
        body.pack(fill="both", expand=True, padx=22, pady=(16, 12))
        tk.Label(body, text="REPOSITORY URL",
                 font=("Segoe UI", 10, "bold"),
                 fg=C_GOLD, bg=P_BG).pack(anchor="w")
        url_var = tk.StringVar()
        tk.Entry(body, textvariable=url_var, bg=P_INP, fg=C_TEXT,
                 insertbackground=C_GOLD, relief="flat", font=FONT_MONO,
                 highlightthickness=1, highlightbackground=P_BDR,
                 highlightcolor=C_GOLD).pack(fill="x", ipady=7, pady=(6, 6))
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
                                "error": None}])

        btn = tk.Label(body, text="Install", font=("Segoe UI", 11, "bold"),
                       fg=C_TEXT, bg=P_BDR, cursor="hand2", padx=16, pady=7)
        btn.pack(anchor="e", pady=(8, 0))
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
        # Recommended addons are no longer their own section — they're mixed
        # into Available and marked with a ★ badge. Sort recommended first so
        # they surface at the top of the list.
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
        hdr.pack(fill="x", pady=(10, 2))
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
                     bg=C_PANEL).pack(anchor="w", padx=8)

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
        row.pack(fill="x", pady=3)


        # right side first so it stays pinned to the edge
        if installed:
            # Trash can drawn as canvas shapes (handle, lid, tapered body
            # with slats) — same fixed-size approach as the download arrow.
            rm = tk.Canvas(row, width=20, height=18, bg=C_PANEL,
                           highlightthickness=0, cursor="hand2")
            rm.pack(side="right", padx=(8, 2))
            rm.create_rectangle(8, 2, 12, 4, fill="#8a4a4a", outline="",
                                tags="trash")
            rm.create_rectangle(4, 4, 16, 6, fill="#8a4a4a", outline="",
                                tags="trash")
            rm.create_polygon(5, 8, 15, 8, 14, 16, 6, 16,
                              fill="#8a4a4a", outline="", tags="trash")
            for x in (8, 10, 12):
                rm.create_line(x, 10, x, 14, fill=C_PANEL)
            rm.bind("<Button-1>",
                    lambda e, n=rec["folder"]: self._addon_remove(n))
            rm.bind("<Enter>", lambda e, c=rm:
                    c.itemconfigure("trash", fill=C_ERR))
            rm.bind("<Leave>", lambda e, c=rm:
                    c.itemconfigure("trash", fill="#8a4a4a"))
        else:
            # Download arrow drawn as a polygon — exact size and centering,
            # independent of any font, without inflating the row height.
            dl = tk.Canvas(row, width=20, height=18, bg=C_PANEL,
                           highlightthickness=0, cursor="hand2")
            dl.pack(side="right", padx=(8, 2))
            dl_item = dl.create_polygon(
                8, 3, 12, 3, 12, 9, 16, 9, 10, 15, 4, 9, 8, 9,
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
            lnk.pack(side="right", padx=(4, 2))
            lnk.bind("<Button-1>", lambda e, u=repo_url: self._open_url(u))
            lnk.bind("<Enter>", lambda e, w=lnk: w.configure(fg=C_GOLD))
            lnk.bind("<Leave>", lambda e, w=lnk: w.configure(fg=C_TEXT_DIM))

        status = rec["status"]
        if status == "downloading":
            tk.Label(row, text="downloading…", font=("Segoe UI", 10),
                     fg=C_TEXT_DIM, bg=C_PANEL).pack(side="right", padx=4)
        elif status == "invalid" or rec.get("error"):
            # Short marker on the right; the full reason gets its own line
            # under the row (long messages would squeeze the description).
            tk.Label(row, text="⛔ Addon error", font=("Segoe UI", 10),
                     fg=C_ERR, bg=C_PANEL).pack(side="right", padx=4)
        elif status == "outOfDate" and installed:
            upd = tk.Label(row, text="Update", font=("Segoe UI", 10, "bold"),
                           fg=C_GOLD, bg=C_PANEL, cursor="hand2")
            upd.pack(side="right", padx=4)
            upd.bind("<Button-1>",
                     lambda e, r=rec: self._addon_apply([r]))
            upd.bind("<Enter>", lambda e, w=upd: w.configure(fg=C_GOLD_LT))
            upd.bind("<Leave>", lambda e, w=upd: w.configure(fg=C_GOLD))
        elif warnings:
            tk.Label(row, text=f"⚠ {warnings[0]}", font=("Segoe UI", 10),
                     fg="#d4b43c", bg=C_PANEL).pack(side="right", padx=4)
        elif status == "upToDate":
            tk.Label(row, text="Up to date", font=("Segoe UI", 10),
                     fg=C_TEXT_DIM, bg=C_PANEL).pack(side="right", padx=4)
        elif status == "unknown":
            tk.Label(row, text="Not versioned", font=("Segoe UI", 10),
                     fg=C_TEXT_DIM, bg=C_PANEL).pack(side="right", padx=4)

        # name (WoW colour codes honoured) + repo link
        name_f = tk.Frame(row, bg=C_PANEL, width=250)
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
                 bg=C_PANEL, wraplength=430, justify="left",
                 anchor="w").pack(side="left", fill="x", expand=True)

        if rec.get("error"):
            tk.Label(f, text=f"  ⚠  {rec['error']}",
                     font=("Segoe UI", 9), fg=C_ERR, bg=C_PANEL,
                     wraplength=840, justify="left",
                     anchor="w").pack(fill="x", pady=(0, 3))

        tk.Frame(f, bg=C_DIVIDER, height=1).pack(fill="x", pady=(3, 0))

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
        left.place(x=40, y=6)

        self._status_var = tk.StringVar(value="Ready to update")
        tk.Label(left, textvariable=self._status_var,
                 font=("Segoe UI", 10, "bold"),
                 fg=C_TEXT, bg=C_BG).pack(anchor="w")

        # Thin halo frame around the button gives a soft glow that follows
        # the button state (gold for UPDATE, green for PLAY).
        self._btn_mode = "update"
        self._btn_glow = tk.Frame(left, bg="#4a3812")
        self._btn_glow.pack(anchor="w", pady=(6, 6))
        self._upd_btn = tk.Label(self._btn_glow, text="UPDATE",
                                 font=("Segoe UI", 11, "bold"),
                                 fg="#ffffff", bg=C_GOLD,
                                 cursor="hand2",
                                 width=14, pady=7,
                                 anchor="center")
        self._upd_btn.pack(padx=3, pady=3)
        self._upd_btn.bind("<Button-1>", lambda e: self._btn_click())
        self._upd_btn.bind("<Enter>",    lambda e: self._btn_hover(True))
        self._upd_btn.bind("<Leave>",    lambda e: self._btn_hover(False))

        self._client_ver_var = tk.StringVar(value="")
        tk.Label(left, textvariable=self._client_ver_var,
                 font=FONT_VER, fg=C_TEXT_DIM, bg=C_BG).pack(
                 anchor="w", pady=(0, 36))

        pb_frame = tk.Frame(foot, bg=C_BG)
        pb_frame.place(x=250, y=0, width=WIN_W - 250 - 40, height=FOOT_H)

        self._pb_canvas = tk.Canvas(pb_frame,
                                    height=6, bg=C_BG,
                                    highlightthickness=0)
        self._pb_canvas.pack(fill="x", side="bottom", padx=0,
                             ipady=0, pady=(0, 56))
        self._pb_width  = WIN_W - 250 - 40
        self._pb_val    = 0.0

        self._prog_label_var = tk.StringVar(value="")
        tk.Label(pb_frame, textvariable=self._prog_label_var,
                 font=("Segoe UI", 10), fg=C_TEXT, bg=C_BG).pack(
                 side="bottom", pady=(0, 6))

        self._draw_progress(0.0)

        tk.Label(foot, text=f"v{UPDATER_VERSION}",
                 font=("Courier New", 8),
                 fg="#555560", bg=C_BG).place(relx=1.0, rely=1.0,
                                              x=-10, y=-6, anchor="se")

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
        # Hide the bar entirely when idle (0) or finished/full (1) — it only
        # shows while something is actively downloading/updating.
        if self._pb_val <= 0.0 or self._pb_val >= 1.0:
            return
        c.create_rectangle(0, 0, w, 6, fill="#1e1e26", outline="")
        filled = int(w * self._pb_val)
        if filled > 0:
            for x in range(filled):
                t     = x / max(filled - 1, 1)
                r_val = int(0xc8 + t * (0xe8 - 0xc8))
                g_val = int(0x92 + t * (0xb8 - 0x92))
                b_val = int(0x2a + t * (0x4b - 0x2a))
                col   = f"#{r_val:02x}{g_val:02x}{b_val:02x}"
                c.create_line(x, 0, x, 6, fill=col)

    # ── helpers ───────────────────────────────────────────────────────────────

    def _on_path_changed(self, *args):
        """Fires whenever the Game folder entry's value actually changes (typed,
        pasted, or set via Browse…). Resets the hash caches so the next verify
        re-checks every file from scratch and tweaks/mods get re-applied/installed
        against the new folder instead of reusing stale state from the old one."""
        new_val = os.path.normpath(self._path_var.get().strip())
        last_val = os.path.normpath(self._last_path_val)

        if new_val == last_val:
            return

        self._last_path_val = new_val
        if not new_val:
            return

        try:
            if os.path.exists(CACHE_FILE):
                os.remove(CACHE_FILE)
        except Exception:
            pass

        # Only touch WDB when the path is a real client folder — this trace
        # fires on every keystroke while a path is being typed.
        if os.path.exists(os.path.join(new_val, "WoW.exe")):
            remove_wdb(new_val)

        # Wipe folder-scoped config (patched-exe hashes + mods/addons install
        # records) and set the new path — one atomic merge into the live
        # config. This also re-arms the default-mods and recommended-addons
        # auto-install for the new folder.
        def _reset_for_new_folder(c):
            c["out_dir"] = new_val
            for k in ("expected_patched_wow_hash", "original_server_wow_hash",
                      "torrent_state", "mods", "addons"):
                c.pop(k, None)
        self._cfg = update_config(_reset_for_new_folder)

        self._mod_pending_state = {}
        self._default_mods_install_started = False
        self._default_addons_install_started = False
        self._client_ready = False

        # Reset every session-level TTL/state so nothing from the previous
        # folder is served from memory: addons verify + its rendered list,
        # news feed timers, and the nav-tab update badges.
        self._addons_verified_ts = 0.0
        self._addons_status = {"state": "idle", "addons": {}, "available": []}
        self._addon_errors = {}
        self._feat_ts = 0.0
        self._news_ts = 0.0
        self._mod_updates_count = 0
        self._addon_updates_count = 0
        self._draw_nav_tab("MODS")
        self._draw_nav_tab("ADDONS")
        self._render_addons()

        self._diff_nodes = None

        self._log_line(
            "\nGame folder changed — cache reset, everything will be re-verified.\n",
            "acct")

        # This verify covers the new folder — overwrite its Config.wtf with our
        # defaults + realmList. It also supersedes the first-run settings-close
        # verify.
        self._first_run_verify_pending = False
        self.after(100, lambda: self._start_verify(overwrite_config=True))

        # A deliberate folder change already covers the antivirus
        # recommendation, so the first-run settings-close shouldn't ask again.
        self._first_run_av_pending = False
        self._prompt_av_exclusion()

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
        MW, MH = 800, 500
        panel = tk.Frame(ov, bg=P_BG, highlightthickness=1,
                         highlightbackground=P_BDR, highlightcolor=P_BDR)
        panel.place(x=(WIN_W - MW) // 2, y=(WIN_H - MH) // 2 - 20,
                    width=MW, height=MH)

        hdr = tk.Frame(panel, bg=P_HDR, height=46)
        hdr.pack(fill="x")
        hdr.pack_propagate(False)
        tk.Label(hdr, text="SETTINGS", font=("Segoe UI", 13, "bold"),
                 fg=C_PURPLE, bg=P_HDR).pack(side="left", padx=18)
        x_btn = tk.Label(hdr, text="✕", font=("Segoe UI", 12),
                         fg=C_TEXT_DIM, bg=P_HDR, cursor="hand2")
        x_btn.pack(side="right", padx=16)
        x_btn.bind("<Button-1>", lambda e: self._close_settings())
        x_btn.bind("<Enter>",    lambda e: x_btn.configure(fg=C_TEXT))
        x_btn.bind("<Leave>",    lambda e: x_btn.configure(fg=C_TEXT_DIM))
        tk.Frame(panel, bg=P_BDR, height=1).pack(fill="x")

        PADX = 22
        body = tk.Frame(panel, bg=P_BG)
        body.pack(fill="both", expand=True, padx=PADX, pady=(16, 12))

        loc_row = tk.Frame(body, bg=P_BG)
        loc_row.pack(fill="x")
        tk.Label(loc_row, text="GAME FOLDER",
                 font=("Segoe UI", 10, "bold"),
                 fg=C_GOLD, bg=P_BG).pack(side="left")
        opn = tk.Label(loc_row, text="Open folder", font=FONT_BODY,
                       fg=C_TEXT_DIM, bg=P_BG, cursor="hand2")
        opn.pack(side="left", padx=(16, 0))
        opn.bind("<Button-1>", lambda e: self._open_client_folder())
        opn.bind("<Enter>",    lambda e: opn.configure(fg=C_GOLD))
        opn.bind("<Leave>",    lambda e: opn.configure(fg=C_TEXT_DIM))

        # Same StringVar as the Update tab's Game folder entry — changing it
        # here fires the exact same folder-change mechanics immediately.
        path_row = tk.Frame(body, bg=P_BG)
        path_row.pack(fill="x", pady=(8, 0))
        ent = tk.Entry(path_row, textvariable=self._path_var,
                       bg=P_INP, fg=C_TEXT, relief="flat", font=FONT_MONO,
                       state="readonly", readonlybackground=P_INP,
                       highlightthickness=1, highlightbackground=P_BDR,
                       highlightcolor=P_BDR)
        ent.pack(side="left", fill="x", expand=True, ipady=7)
        chg = tk.Label(path_row, text="Change",
                       font=("Segoe UI", 10, "bold"),
                       fg=C_TEXT, bg=P_BDR, cursor="hand2", padx=16, pady=7)
        chg.pack(side="left", padx=(8, 0))
        chg.bind("<Button-1>", lambda e: self._settings_change_dir())
        chg.bind("<Enter>",    lambda e: chg.configure(bg=C_GOLD, fg="#000"))
        chg.bind("<Leave>",    lambda e: chg.configure(bg=P_BDR, fg=C_TEXT))

        tk.Label(body, text="DOWNLOAD MIRROR",
                 font=("Segoe UI", 10, "bold"),
                 fg=C_GOLD, bg=P_BG).pack(anchor="w", pady=(20, 4))
        mir = tk.Frame(body, bg=P_BG)
        mir.pack(fill="x")
        tk.Label(mir, text="●", font=("Segoe UI", 9),
                 fg=C_OK, bg=P_BG).pack(side="left")
        tk.Label(mir, text=" Iceland", font=("Segoe UI", 10, "bold"),
                 fg=C_TEXT, bg=P_BG).pack(side="left")
        self._mirror_status_lbl = tk.Label(mir, text="checking…",
                                           font=("Segoe UI", 9),
                                           fg=C_TEXT_DIM, bg=P_BG)
        self._mirror_status_lbl.pack(side="left", padx=(8, 0))
        rf = tk.Label(mir, text="⟳", font=("Segoe UI", 11),
                      fg=C_TEXT_DIM, bg=P_BG, cursor="hand2")
        rf.pack(side="left", padx=(6, 0))
        rf.bind("<Button-1>", lambda e: self._check_mirror_status())
        rf.bind("<Enter>",    lambda e: rf.configure(fg=C_GOLD))
        rf.bind("<Leave>",    lambda e: rf.configure(fg=C_TEXT_DIM))
        self._check_mirror_status()

        # Two equal-width columns via grid, so the right column keeps a fixed
        # position and reaches toward the right edge — regardless of how wide
        # the left column's text is.
        cols = tk.Frame(body, bg=P_BG)
        cols.pack(fill="x", pady=(22, 0))
        cols.columnconfigure(0, weight=3, uniform="s")
        cols.columnconfigure(1, weight=2, uniform="s")
        lcol = tk.Frame(cols, bg=P_BG)
        lcol.grid(row=0, column=0, sticky="nw")
        rcol = tk.Frame(cols, bg=P_BG)
        rcol.grid(row=0, column=1, sticky="nw")

        tk.Label(lcol, text="TROUBLESHOOTING",
                 font=("Segoe UI", 10, "bold"),
                 fg=C_GOLD, bg=P_BG).pack(anchor="w")

        def _titem(icon, text, cmd, icon_color=C_GOLD):
            r = tk.Frame(lcol, bg=P_BG, cursor="hand2")
            r.pack(anchor="w", pady=(12, 0))
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
                 fg=C_GOLD, bg=P_BG).pack(anchor="w", pady=(22, 0))
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
                       cursor="hand2").pack(anchor="w", pady=(10, 0))
        tk.Checkbutton(rcol, text=" Close Octo Updater on game launch",
                       variable=self._close_on_launch_var,
                       command=self._toggle_close_on_launch,
                       font=("Segoe UI", 10), fg=C_TEXT, bg=P_BG,
                       activebackground=P_BG, activeforeground=C_TEXT,
                       selectcolor=P_INP, highlightthickness=0, bd=0,
                       cursor="hand2").pack(anchor="w", pady=(10, 0))
        cb_auto_mods = tk.Checkbutton(
            rcol, text=" Install essential mods",
            variable=self._auto_mods_var, command=self._toggle_auto_mods,
            font=("Segoe UI", 10), fg=C_TEXT, bg=P_BG,
            activebackground=P_BG, activeforeground=C_TEXT,
            selectcolor=P_INP, highlightthickness=0, bd=0, cursor="hand2")
        cb_auto_mods.pack(anchor="w", pady=(10, 0))
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
                       cursor="hand2").pack(anchor="w", pady=(10, 0))

    def _close_settings(self):
        self.unbind("<Escape>")
        if self._settings_overlay is not None:
            self._settings_overlay.destroy()
            self._settings_overlay = None
        # First run: the user has now committed to a game folder (kept the
        # default). Run the deferred verification against it and (over)write a
        # fresh Config.wtf with our defaults + realmList.
        if self._first_run_verify_pending:
            self._first_run_verify_pending = False
            self.after(100, lambda: self._start_verify(overwrite_config=True))
        # Apply any auto-install option the user turned on this session
        # (idempotent — a no-op when nothing is missing).
        if self._auto_mods_retrigger:
            self._auto_mods_retrigger = False
            self._install_missing_essential_mods()
        if self._auto_addons_retrigger:
            self._auto_addons_retrigger = False
            self._install_missing_recommended_addons()
        # First run: the user accepted the auto-selected folder (never changed
        # it) and never added a Defender exclusion — recommend it now, once.
        if self._first_run_av_pending:
            self._first_run_av_pending = False
            self._prompt_av_exclusion()

    def _open_client_folder(self):
        import subprocess
        path = os.path.normpath(self._path_var.get().strip())
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
        cur     = self._path_var.get()
        initial = cur if os.path.isdir(cur) else os.path.expanduser("~")
        chosen  = filedialog.askdirectory(
            title="Select game client folder",
            initialdir=initial, mustexist=False)
        if chosen:
            # normpath → backslashes; fires the folder-change reset
            self._path_var.set(os.path.normpath(chosen))

    def _settings_verify(self):
        self._close_settings()
        self._verify_game_files()

    def _allow_through_antivirus(self):
        """Add a Windows Defender exclusion for the game folder (asks for
        admin elevation via UAC)."""
        # The user handled the exclusion themselves — no need to prompt again
        # when the first-run Settings window closes.
        self._first_run_av_pending = False
        client_dir = os.path.normpath(self._path_var.get().strip())
        if not client_dir or client_dir == ".":
            return
        import ctypes
        cmd = f"Add-MpPreference -ExclusionPath '{client_dir}'"
        r = ctypes.windll.shell32.ShellExecuteW(
            None, "runas", "powershell.exe",
            f'-NoProfile -WindowStyle Hidden -Command "{cmd}"', None, 0)
        if r > 32:
            self._log_line(
                f"Requested Defender exclusion for: {client_dir}\n", "ok")
        else:
            self._log_line("Antivirus exclusion cancelled.\n", "err")

    def _check_mirror_status(self):
        lbl = self._mirror_status_lbl
        lbl.configure(text="checking…", fg=C_TEXT_DIM)

        def worker():
            ok = False
            try:
                req = urllib.request.Request(
                    TORRENT_URL,
                    headers={"User-Agent": UA})
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

    def _install_missing_essential_mods(self):
        """Install every essential mod not already present. Used when the user
        turns 'Install essential mods' on after the fact."""
        if self._running:
            return
        out = self._path_var.get().strip()
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
        out = self._path_var.get().strip()
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
        """Full re-verification: drop the hash cache and the patched-exe
        bookkeeping so every file is checked against the torrent pieces and
        WoW.exe gets re-downloaded and re-patched (tweaks reapplied). Unlike
        a game-folder change, installed mods are left alone."""
        if self._running:
            return
        try:
            if os.path.exists(CACHE_FILE):
                os.remove(CACHE_FILE)
        except Exception:
            pass
        def _drop_hashes(c):
            c.pop("expected_patched_wow_hash", None)
            c.pop("original_server_wow_hash", None)
            c.pop("torrent_state", None)
        self._cfg = update_config(_drop_hashes)
        self._diff_nodes = None
        self._client_ready = False
        self._log_line(
            "\nVerify game files — cache dropped, re-checking everything.\n",
            "acct")
        self._start_verify()

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
        LW, LH = 760, 420
        sw, sh = win.winfo_screenwidth(), win.winfo_screenheight()
        win.geometry(f"{LW}x{LH}+{(sw - LW) // 2}+{(sh - LH) // 2}")
        win.configure(bg=C_BG)

        top = tk.Frame(win, bg=C_BG)
        top.pack(fill="x", padx=12, pady=(10, 4))
        tk.Label(top, text="SESSION LOG", font=("Segoe UI", 9, "bold"),
                 fg=C_GOLD, bg=C_BG).pack(side="left")

        outer = tk.Frame(win, bg=C_BG)
        outer.pack(fill="both", expand=True, padx=12, pady=(0, 12))
        sb = SlimScrollbar(outer, bg=C_BG)
        sb.pack(side="right", fill="y")
        txt = tk.Text(outer, bg=C_LOG_BG, fg=C_TEXT,
                      insertbackground=C_TEXT, relief="flat",
                      font=FONT_MONO, wrap="word", state="disabled",
                      padx=10, pady=8, yscrollcommand=sb.set,
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
        If VanillaFixes is installed use VanillaFixes.exe (it injects patches then
        starts WoW.exe itself). Otherwise fall back to WoW.exe directly."""
        import subprocess
        client_dir = self._path_var.get().strip()
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

        # One-time DXVK first-launch notice (armed when dxvk was installed).
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
            # Optionally close the updater shortly after launch.
            if self._cfg.get("close_on_launch", False):
                self.after(1000, self._on_close)
                return
            self.after(5000, self._refresh_ready_state)
        except Exception as e:
            self._log_line(f"Failed to launch {exe_lbl}: {e}\n", "err")

    # ── verify lifecycle ──────────────────────────────────────────────────────────

    def _start_verify(self, overwrite_config: bool = False):
        out = self._path_var.get().strip()
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
        self._status_var.set("Verifying…")
        self._draw_progress(0.0)
        self._prog_label_var.set("")
        self._log_q  = queue.Queue()
        self._prog_q = queue.Queue()
        patched_hash  = self._cfg.get("expected_patched_wow_hash", "")
        original_hash = self._cfg.get("original_server_wow_hash", "")
        worker = VerifyWorker(out, self._log_q, self._prog_q, patched_hash,
                              original_hash, overwrite_config=overwrite_config)
        self._verify_worker = worker
        threading.Thread(target=worker.run, daemon=True).start()

    # ── update lifecycle ──────────────────────────────────────────────────────────

    def _start_update(self):
        if self._running:
            return
        out = self._path_var.get().strip()
        if not out:
            self._log_line("✗  Please set the game folder first.\n", "err")
            return

        self._cfg = update_config(lambda c: c.__setitem__("out_dir", out))

        self._log_line(f"\nGame folder: {out}\n", "dim")

        self._running = True
        self._set_btn_busy("Updating…")
        self._status_var.set("Updating…")
        self._draw_progress(0.0)
        self._prog_label_var.set("")

        self._log_q  = queue.Queue()
        self._prog_q = queue.Queue()
        patched_hash   = self._cfg.get("expected_patched_wow_hash", "")
        original_hash  = self._cfg.get("original_server_wow_hash", "")

        self._worker   = UpdateWorker(out, self._log_q, self._prog_q, patched_hash)
        self._worker.original_server_wow_hash = original_hash

        diff = self._diff_nodes
        self._diff_nodes = None
        t = threading.Thread(target=self._worker.run, args=(diff,), daemon=True)
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
                elif msg == "__DIFF_TREE__":
                    self._diff_nodes = tag
                elif msg.startswith("__ORIGINAL_HASH__"):
                    h = msg[len("__ORIGINAL_HASH__"):]
                    self._cfg = update_config(
                        lambda c: c.__setitem__("original_server_wow_hash", h))
                elif msg.startswith("__PATCHED_HASH__"):
                    h = msg[len("__PATCHED_HASH__"):]
                    self._cfg = update_config(
                        lambda c: c.__setitem__("expected_patched_wow_hash", h))
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

if __name__ == "__main__":
    app = OctoUpdaterApp()
    app.mainloop()

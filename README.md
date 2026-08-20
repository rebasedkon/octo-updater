# Octo Updater

A standalone desktop updater and mod manager for the **OctoWoW** client.
It updates and patches the game client, manages community **mods**, **addons**
and **content patches**, applies client **tweaks**, and shows server **news**.

![Octo Updater](screenshot.png)

---

## Features

### Game updates

- Game files are synced over **BitTorrent** using a bundled, checksum-verified
  `aria2c` — only missing or wrong-sized files are downloaded, transfers resume
  automatically, and an optional integrity pass re-checks every piece hash to
  catch same-size corruption.
- Legacy locale folders and old client patch archives are pruned automatically
  after a sync.
- Reads and displays the installed game client version straight from `WoW.exe`.

### Mods

Curated set of client modifications, installed from their official GitHub /
Codeberg releases and registered in `dlls.txt`:

| Mod                    | Purpose                                                                            |
| ----------------------- | ----------------------------------------------------------------------------------- |
| AuctionQueryThrottle    | Removes the fixed 5-second wait between auction house searches                     |
| ClassicAPI              | Adds later-version Lua API calls to the client; required by some addons            |
| DXVK                    | Vulkan-based rendering for better performance                                       |
| Nampower                | Reduces input lag on higher latency; expands the addon API                          |
| No1600x1200             | Fixes incorrect resolution when the monitor's native res isn't detected (optional) |
| SuperWoW                | Backported client API features; required by some addons                            |
| TransmogFix             | Fixes transmog-related frame drops on character death                              |
| UnitXP_SP3              | Frame limiter, improved targeting, anti-aliased combat text, and more              |
| VanillaFixes           | Eliminates stutter and animation lag (also the DLL loader; required by other mods) |
| VanillaHelpers          | Raises the max supported texture resolution and improves memory allocation         |
| VanillaMultiMonitorFix  | Fixes multi-monitor resolution issues (optional)                                   |

- Essential mods auto-install on a fresh game folder, or on any game
  folder when **Install essential mods** is enabled in Settings.
- Per-mod **update** / **retry** actions and an update-count badge on the tab.
- When VanillaFixes is installed, **PLAY** launches through it instead of
  `WoW.exe` directly.

### Tweaks

Patches `WoW.exe` and writes `Config.wtf` for quality-of-life settings,
grouped by category:

- **General** — in-game language (English, Deutsch, Русский, 中文, Español,
  Português), auto-loot, nameplate range.
- **Camera** — field of view (with a recommended value per aspect ratio),
  camera zoom distance.
- **Graphics** — world/terrain render distance, ground clutter distance.
- **Sound** — allow sound to play while the game is in the background.

Invalid values are clamped; Apply/Reset appear only when something changed.

### Addons

- Installs addons directly from Git hosts (**GitHub, GitLab, Gitea, Codeberg**)
  by downloading the repo archive pinned to a commit SHA — no Git client needed.
- Curated **recommended** list plus everything from the server catalog.
- **Add custom git addon** dialog for any allowed host; a custom addon is
  never silently overridden by a same-named recommended one.
- Update detection by comparing the installed commit against the latest,
  one-click **Update** / **Update all**, and an update-count badge.
- pfUI gets a curated **"Default"** profile injected and added to its firstrun
  picker after each install/update.

### MPQ patches

Optional content patches distributed as `.mpq` files, separate from mods and
addons — currently **Octo Raid Visuals**, which adds ground markers and
sounds for boss abilities in raids. Each patch is downloaded over HTTPS and
verified against a published checksum before it's placed in the client's
`Data` folder; the tab flags available updates.

### News

Shows the latest **Announcements** post and the current **Patch Notes** list
from the server's forum feed.

### Settings

Change the game folder, check download mirror status, verify game files,
view session logs, and add the game folder to Defender exclusions. General
options include clearing the client's WDB cache on every game launch,
minimizing Octo Updater when the game launches, auto-installing essential
mods and recommended addons, and keeping a custom `speech.mpq` untouched by
verification/updates.

### Security & robustness

- Hardened TLS (system trust store, hostname check, TLS 1.2+ floor).
- HTTPS-only with per-host allowlists for all downloads; redirects stay HTTPS.
- `aria2c` itself is fetched once and SHA-256-verified before it's ever run.
- Atomic config writes (temp + rename) with a lock — safe against concurrent
  workers and interrupted saves.
- Path-traversal-safe archive extraction.
- DPI-aware layout — the UI scales as a unit on high-DPI displays instead of
  fonts overflowing a fixed-pixel layout.
- Automatic self-update check against this repo's GitHub releases (once a day).

---

## Requirements

- **Windows**, or **Linux via Proton/Wine** — Octo Updater is a Windows build,
  but it runs on Linux under Proton/Wine.
  A couple of Windows-only conveniences (Defender exclusions, DPI-scale
  auto-detection) simply don't apply outside Windows.
- **Python 3.10+** — only if running from source. Runs on the standard
  library, and will also use [`certifi`](https://pypi.org/project/certifi/) if
  installed, for more robust TLS verification on machines with an out-of-date
  root store (otherwise falls back to the system trust store).
- The prebuilt `OctoUpdater.exe` needs nothing installed. `aria2c` is
  downloaded automatically the first time a game update runs.

---

## Usage

### Prebuilt executable

Download `OctoUpdater.exe` from the [latest release](https://github.com/rebasedkon/octo-updater/releases/latest) and
run it. Point the **Game folder** (Settings) at your OctoWoW game folder —
or let the default create one next to the executable — then click **UPDATE**,
and **PLAY** when it finishes.

### From source

```
python octo_updater.py
```

The updater keeps its data in a per-user app-data folder.

---

## Building

Compile a single-file Windows executable with [PyInstaller](https://pyinstaller.org/):

```
pip install pyinstaller certifi
pyinstaller --onefile --windowed --name OctoUpdater --icon OctoUpdater.ico octo_updater.py
```

Installing `certifi` before building bundles an up-to-date CA certificate set
into the executable, so TLS verification works even on machines whose Windows
root store is stale. `aria2c` does not need to be bundled — the app fetches
and verifies it itself on first run.

---

## Support the Developer

If Octo Updater is useful to you, consider supporting its development:

- [Ko-fi](https://ko-fi.com/rebased)
- [Buy Me a Coffee](https://buymeacoffee.com/rebased)

---

## License

See [LICENSE](https://github.com/rebasedkon/octo-updater/blob/main/LICENSE).
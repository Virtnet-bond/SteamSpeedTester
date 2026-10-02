#!/usr/bin/env python3
"""Measure the Steam PoPs reachable from this connection and recommend a region.

Steam lets you pick a download region, but not which server answers you: that
is decided by a priority ranking Valve assigns per region, which has nothing to
do with how fast the server is from where you are. This finds the regions whose
top-ranked server is actually fast for you.

    steam-region-speedtest                 # scan, measure, recommend
    steam-region-speedtest --budget 150    # lighter on traffic
    steam-region-speedtest --json out.json

Needs Python 3.7+ and a Steam install with at least one game; no third-party
packages. It reads depot manifests from your own install and pulls those chunks
from the CDN to measure, which with the defaults is up to a few GB of traffic -
mind metered connections, and run it while nothing else is using the link or
the numbers will be wrong.

Not affiliated with Valve. It only makes the same requests the Steam client
does, but please don't loop it.

Three things that aren't obvious, and that shape the whole design:

- priority_class belongs to the (cell, host) pair, not to the PoP. Steam only
  opens connections to hosts in the winning class of whichever cell you pick,
  so a PoP can be fast and still be unreachable. That's why only the PoPs that
  win somewhere are worth measuring.
- Throughput needs up to ~5s to settle, and that time grows with RTT. A test
  that downloads a fixed amount therefore punishes distant PoPs - by as much as
  17x in practice. This samples the instantaneous rate and drops the ramp.
- A poor cache hit rate measures the origin fill rather than the network, so a
  cold result is thrown away and remeasured with the cache warmed by the first
  pass.
"""

import argparse
import json
import re
import socket
import ssl
import statistics
import struct
import sys
import threading
import time
import urllib.request
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

API = "https://api.steampowered.com/IContentServerDirectoryService/GetServersForSteamPipe/v1/"
STEAM_DIRS = ["~/.local/share/Steam", "~/.steam/steam", "~/.steam/debian-installation",
              "~/Library/Application Support/Steam"]
WIN_DIRS = [r"C:\Program Files (x86)\Steam", r"C:\Program Files\Steam", r"C:\Steam"]
STEAM_REG = r"Software\Valve\Steam"
MANIFEST_MAGIC = 0x71F617D0
HOST_RE = re.compile(r"^cache\d+-(.+)\.steamcontent\.com$")
FALLBACK_CELLS = range(231)  # only used if appinfo.vdf can't be read

CITIES = {
    "ams": "Amsterdam", "atl": "Atlanta", "bkk": "Bangkok", "bog": "Bogota",
    "bom": "Mumbai", "bos": "Boston", "bru": "Brussels", "cph": "Copenhagen",
    "del": "Delhi", "den": "Denver", "dfw": "Dallas", "dub": "Dublin",
    "dxb": "Dubai", "ewr": "Newark", "eze": "Buenos Aires", "fra": "Frankfurt",
    "gru": "Sao Paulo", "hel": "Helsinki", "hkg": "Hong Kong", "iad": "Washington DC",
    "ist": "Istanbul", "jkt": "Jakarta", "jnb": "Johannesburg", "las": "Las Vegas",
    "lax": "Los Angeles", "lhr": "London", "lim": "Lima", "lis": "Lisbon",
    "maa": "Chennai", "mad": "Madrid", "man": "Manchester", "mde": "Medellin",
    "mia": "Miami", "mnl": "Manila", "msp": "Minneapolis", "mxp": "Milan",
    "ord": "Chicago", "osl": "Oslo", "par": "Paris", "phx": "Phoenix",
    "scl": "Santiago", "sea": "Seattle", "sel": "Seoul", "sgp": "Singapore",
    "sha": "Shanghai", "sjc": "San Jose", "slc": "Salt Lake City", "sof": "Sofia",
    "sto": "Stockholm", "syd": "Sydney", "tpe": "Taipei", "tyo": "Tokyo",
    "uio": "Quito", "vie": "Vienna", "waw": "Warsaw", "yvr": "Vancouver",
    "yyz": "Toronto",
}


def city_of(pop):
    return CITIES.get(pop[:3], pop)


# --- region names as they appear in the Steam UI -----------------------------

def _varint(b, i):
    r = s = 0
    while True:
        c = b[i]
        i += 1
        r |= (c & 0x7F) << s
        s += 7
        if not c & 0x80:
            return r, i


def _fields(b):
    i = 0
    while i < len(b):
        k, i = _varint(b, i)
        f, w = k >> 3, k & 7
        if w == 0:
            v, i = _varint(b, i)
        elif w == 2:
            n, i = _varint(b, i)
            v = b[i:i + n]
            i += n
        elif w == 5:
            v, i = b[i:i + 4], i + 4
        elif w == 1:
            v, i = b[i:i + 8], i + 8
        else:
            raise ValueError(f"wire type {w}")
        yield f, v


def _win_reg(value):
    try:
        import winreg
        with winreg.OpenKey(winreg.HKEY_CURRENT_USER, STEAM_REG) as k:
            return winreg.QueryValueEx(k, value)[0]
    except Exception:
        return None


def steam_root():
    cands = []
    if sys.platform == "win32":
        sp = _win_reg("SteamPath")
        if sp:
            cands.append(Path(sp))
        cands += [Path(d) for d in WIN_DIRS]
    cands += [Path(d).expanduser() for d in STEAM_DIRS]
    for p in cands:
        try:
            if (p / "depotcache").is_dir() or (p / "appcache").is_dir():
                return p
        except OSError:
            continue
    sys.exit("Couldn't find a Steam installation.")


def steam_language(root):
    if sys.platform == "win32":
        lang = _win_reg("Language")
        if lang:
            return str(lang)
    for cand in (root.parent / "registry.vdf", root / "registry.vdf"):
        try:
            m = re.search(r'"Language"\s+"(\w+)"', cand.read_text(errors="replace"))
            if m:
                return m.group(1)
        except Exception:
            pass
    return "english"


def load_cell_names(root, lang=None):
    """cell_id -> the label Steam shows in its download region dropdown."""
    f = root / "appcache" / "appinfo.vdf"
    cells = {}
    try:
        data = f.read_bytes()
        if struct.unpack("<I", data[:4])[0] not in (0x07564429, 0x07564428):
            return {}
        off = struct.unpack("<q", data[8:16])[0]
        cnt = struct.unpack("<I", data[off:off + 4])[0]
        tbl, i = [], off + 4
        for _ in range(cnt):
            j = data.index(b"\x00", i)
            tbl.append(data[i:j].decode("utf8", "replace"))
            i = j + 1
        key = struct.pack("<I", tbl.index("loc_name"))
        pat = re.compile(rb"\x00(.{4})\x01" + key + rb"([a-z0-9_]{2,40})\x00", re.S)
        for m in pat.finditer(data):
            idx = struct.unpack("<I", m.group(1))[0]
            if idx < len(tbl) and tbl[idx].isdigit():
                cells[int(tbl[idx])] = m.group(2).decode()
    except Exception:
        return {}

    gui = {}
    lang = lang or steam_language(root)
    for name in (f"steamui_{lang}.txt", "steamui_english.txt"):
        p = root / "public" / name
        if p.is_file():
            try:
                gui.update(re.findall(r'"DownloadRegion_([a-z0-9_]+)"\s+"([^"]*)"',
                                      p.read_text(encoding="utf-8-sig", errors="replace")))
            except Exception:
                pass
        if gui:
            break
    return {c: gui.get(loc, loc.replace("_", " ")) for c, loc in cells.items()}


# --- chunks to pull ----------------------------------------------------------

def parse_manifest(path, min_chunk, want):
    data = path.read_bytes()
    if len(data) < 8 or struct.unpack("<I", data[:4])[0] != MANIFEST_MAGIC:
        return []
    ln = struct.unpack("<I", data[4:8])[0]
    out = []
    for f, v in _fields(data[8:8 + ln]):
        if f != 1:
            continue
        for f2, v2 in _fields(v):
            if f2 != 6:
                continue
            sha = size = None
            for f3, v3 in _fields(v2):
                if f3 == 1:
                    sha = v3.hex()
                elif f3 == 5:
                    size = v3
            if sha and size and size >= min_chunk:
                out.append(sha)
                if len(out) >= want:
                    return out
    return out


def probe(host, depot, sha):
    try:
        with urllib.request.urlopen(
                f"https://{host}/depot/{depot}/chunk/{sha}", timeout=15) as r:
            return r.status == 200
    except Exception:
        return False


def find_chunks(root, pool, min_chunk, probe_host):
    cands = []
    for sub in ("depotcache", "steamapps"):
        d = root / sub
        if d.is_dir():
            cands += list(d.glob("*.manifest"))
    cands.sort(key=lambda p: p.stat().st_size, reverse=True)
    if not cands:
        sys.exit(f"No manifests found under {root}. Install or update a game first.")
    for path in cands[:12]:
        try:
            depot = int(path.name.split("_")[0])
            chunks = parse_manifest(path, min_chunk, pool)
        except Exception:
            continue
        if len(chunks) >= 8 and probe(probe_host, depot, chunks[0]):
            return depot, chunks, path.name
    sys.exit("None of the local depots are still on the CDN. Update a game and retry.")


# --- cell sweep --------------------------------------------------------------

def servers_for_cell(cell, geolocate=False):
    # The edge geolocates the caller and ignores cell_id unless ip_override is
    # set, so every region comes back as this connection's local PoPs.
    # 0.0.0.0 turns that pin off. max_servers and launcher_type match the
    # client, which asks for 32 sources with launcher 0. geolocate=True is the
    # request the client itself makes, used to see whether a pick will stick.
    pin = "" if geolocate else "&ip_override=0.0.0.0"
    url = f"{API}?cell_id={cell}&max_servers=32&launcher_type=0{pin}"
    try:
        with urllib.request.urlopen(url, timeout=10) as r:
            return json.load(r)["response"]["servers"]
    except Exception:
        return []


def top_class_pops(servers):
    """PoPs in the priority class Steam opens for this server list."""
    bycls = {}
    for sv in servers:
        if sv.get("type") != "SteamCache":
            continue
        m = HOST_RE.match(sv.get("host", ""))
        if not m:
            continue
        bycls.setdefault(sv.get("priority_class") or 0, set()).add(m.group(1))
    if not bycls:
        return set()
    return bycls[max(bycls)]


def cell_winners(cells, workers=16):
    """Returns (winner per cell, hosts per PoP, home cell per PoP).

    A PoP's home cell is the one its own servers report. That answers "where
    this PoP is", which is a different question from "which cell to pick to
    reach it" - and the two often disagree.
    """
    win, hosts, home = {}, {}, {}
    cells = list(cells)
    total = len(cells)
    with ThreadPoolExecutor(max_workers=workers) as ex:
        for done, (cell, servers) in enumerate(
                zip(cells, ex.map(servers_for_cell, cells)), 1):
            bycls = {}
            for sv in servers:
                if sv.get("type") != "SteamCache":
                    continue
                m = HOST_RE.match(sv.get("host", ""))
                if not m:
                    continue
                pop = m.group(1)
                hosts.setdefault(pop, set()).add(sv["host"])
                rep = sv.get("cell_id")
                if rep is not None:
                    h = home.setdefault(pop, {})
                    h[rep] = h.get(rep, 0) + 1
                bycls.setdefault(sv.get("priority_class") or 0, []).append(pop)
            if bycls:
                mx = max(bycls)
                win[cell] = (sorted(set(bycls[mx])), mx, len(bycls[mx]))
            if done % 4 == 0 or done == total:
                n = int(24 * done / total)
                print(f"\r  [{'#' * n}{'.' * (24 - n)}] {done}/{total} cells, "
                      f"{len(hosts)} PoPs", end="", flush=True)
    print()
    return win, hosts, {p: max(v, key=v.get) for p, v in home.items()}


# --- measurement -------------------------------------------------------------

def steady(samples, ratio=0.8):
    """Drop the ramp: everything below 80% of the settled rate."""
    if len(samples) < 3:
        return samples, 0
    ref = statistics.median(samples[len(samples) // 2:])
    if ref <= 0:
        return samples, 0
    i = 0
    while i < len(samples) and samples[i] < ratio * ref:
        i += 1
    if len(samples) - i < 2:
        return samples[len(samples) // 2:], len(samples) // 2
    return samples[i:], i


def is_stable(vals, k=4, tol=0.2):
    if len(vals) < k:
        return False
    tail = vals[-k:]
    m = statistics.mean(tail)
    return m > 0 and statistics.pstdev(tail) / m < tol


class Result:
    def __init__(self, pop):
        self.pop = pop
        self.mbps = 0.0
        self.bytes = 0
        self.hits = self.misses = self.errors = 0
        self.secs = self.ramp = 0.0
        self.stable = self.rewarmed = False
        self.ms = self.ms_min = self.hitpct = None


def measure(pop, host, depot, chunks, conns, min_samples, max_secs, max_bytes,
            interval=0.5):
    res = Result(pop)
    ctx = ssl.create_default_context()
    lock = threading.Lock()
    stop = threading.Event()
    st = {"bytes": 0, "idx": 0, "hits": 0, "misses": 0, "errors": 0}

    def worker():
        import http.client
        conn = None
        while not stop.is_set():
            try:
                if conn is None:
                    conn = http.client.HTTPSConnection(host, 443, context=ctx, timeout=20)
                with lock:
                    sha = chunks[st["idx"] % len(chunks)]
                    st["idx"] += 1
                conn.request("GET", f"/depot/{depot}/chunk/{sha}",
                             headers={"Connection": "keep-alive"})
                r = conn.getresponse()
                cache = (r.getheader("x-cache-status") or "").upper()
                with lock:
                    if cache == "HIT":
                        st["hits"] += 1
                    elif cache == "MISS":
                        st["misses"] += 1
                while not stop.is_set():
                    b = r.read(262144)
                    if not b:
                        break
                    with lock:
                        st["bytes"] += len(b)
                else:
                    break
            except Exception:
                with lock:
                    st["errors"] += 1
                try:
                    conn.close()
                except Exception:
                    pass
                conn = None
                if stop.is_set():
                    break
                time.sleep(0.2)
        try:
            conn.close()
        except Exception:
            pass

    threads = [threading.Thread(target=worker, daemon=True) for _ in range(conns)]
    t0 = time.monotonic()
    for t in threads:
        t.start()

    last, samples = 0, []
    while True:
        time.sleep(interval)
        now = time.monotonic() - t0
        with lock:
            cur, errs = st["bytes"], st["errors"]
        samples.append((cur - last) / interval / 1048576)
        last = cur
        if cur >= max_bytes or now >= max_secs:
            break
        if errs > conns * 4 and cur == 0:
            break
        vals, _ = steady(samples)
        if len(vals) >= min_samples and is_stable(vals):
            break

    stop.set()
    res.secs = time.monotonic() - t0
    for t in threads:
        t.join(timeout=5)
    with lock:
        res.bytes, res.hits = st["bytes"], st["hits"]
        res.misses, res.errors = st["misses"], st["errors"]
    if samples:
        vals, cut = steady(samples)
        res.mbps = statistics.median(vals)
        res.ramp = cut * interval
        res.stable = len(vals) >= min_samples and is_stable(vals)
    tot = res.hits + res.misses
    res.hitpct = (100 * res.hits / tot) if tot else None
    return res


def measure_hot(pop, host, depot, chunks, args):
    """Measure with the cache warm - a cold run times the origin, not the link."""
    mb = args.budget * 1048576
    r = measure(pop, host, depot, chunks, args.conns, args.min_samples,
                args.max_secs, mb)
    if r.hitpct is not None and r.hitpct < args.min_hit:
        r2 = measure(pop, host, depot, chunks, args.conns, args.min_samples,
                     args.max_secs, mb)
        r2.rewarmed = True
        return r2
    return r


def tcp_latency(host, port=443, samples=9, timeout=5.0):
    """(median, minimum) TCP handshake time in ms.

    Resolves once up front: passing a hostname to create_connection charges the
    DNS lookup to every sample (measured: 164 ms against a real 13 ms). Nine
    samples because a few is not enough on hosts that queue their accepts - one
    PoP here alternates ~30 ms with 1100 ms spikes and five samples once put the
    median at 1093 ms.
    """
    try:
        ip = socket.getaddrinfo(host, port, socket.AF_INET)[0][4][0]
    except Exception:
        return None, None
    times = []
    for _ in range(samples):
        t0 = time.perf_counter()
        try:
            sk = socket.create_connection((ip, port), timeout=timeout)
            times.append((time.perf_counter() - t0) * 1000)
            sk.close()
        except Exception:
            pass
        time.sleep(0.05)
    return (statistics.median(times), min(times)) if times else (None, None)


# --- output ------------------------------------------------------------------

def table(results, where, pick_cell, names):
    u = max([14] + [len(where[r.pop]) for r in results])
    w = max([15] + [len(names.get(pick_cell[r.pop][0], "?")) for r in results])
    print(f"\n  {'PoP':<10} {'located in':<{u}} {'pick in Steam':<{w}} "
          f"{'MB/s':>7} {'Mbit':>6} {'ms':>5} {'cache':>8}")
    print("  " + "-" * (42 + u + w))
    for r in results:
        cell = pick_cell[r.pop][0]
        cache = f"{r.hitpct:.0f}% hit" if r.hitpct is not None else "-"
        ms = f"{r.ms:.0f}" if r.ms is not None else "-"
        mark = "" if r.stable else " ~"
        if r.hitpct is not None and r.hitpct < 50:
            mark += " !"
        if r.ms and r.ms_min and r.ms > 2.5 * r.ms_min:
            mark += " *"
        print(f"  {r.pop:<10} {where[r.pop]:<{u}} {names.get(cell, '?'):<{w}} "
              f"{r.mbps:>7.1f} {r.mbps * 8.389:>6.0f} {ms:>5} {cache:>8}{mark}")
    print("\n  ~ rate never settled   ! poor cache hit rate   * erratic latency")


def main():
    try:
        sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    except Exception:
        pass
    p = argparse.ArgumentParser(
        description="Measure the Steam PoPs you can actually reach, and pick one.")
    p.add_argument("--conns", type=int, default=16,
                   help="parallel connections per PoP (default 16)")
    p.add_argument("--budget", type=int, default=400,
                   help="MB cap per PoP (default 400; going much lower skews the "
                        "result against distant PoPs)")
    p.add_argument("--max-secs", type=float, default=20.0,
                   help="seconds cap per PoP (default 20)")
    p.add_argument("--min-samples", type=int, default=6,
                   help="settled 0.5s samples needed to accept a measurement (default 6)")
    p.add_argument("--min-hit", type=float, default=70.0,
                   help="cache hit %% below which a PoP is measured again (default 70)")
    p.add_argument("--tie", type=float, default=10.0,
                   help="%% window counted as a tie, broken by latency (default 10)")
    p.add_argument("--pool", type=int, default=128,
                   help="distinct chunks to cycle through (default 128)")
    p.add_argument("--lang", help="language for region names (default: your Steam's)")
    p.add_argument("--json", metavar="FILE", help="write the results to a JSON file")
    p.add_argument("--yes", action="store_true", help="skip the traffic confirmation")
    args = p.parse_args()

    root = steam_root()
    names = load_cell_names(root, args.lang)

    print("Scanning cells to see which PoP wins each one...", flush=True)
    win, hosts, home = cell_winners(sorted(names) if names else FALLBACK_CELLS)
    if not win:
        sys.exit("The API returned no servers.")

    # Which cell to recommend for a PoP: one that exists in the UI, then its
    # home cell, then the one using most hosts, then lowest id just to be stable.
    pick_cell, rank, alts = {}, {}, {}
    for cell, (pops_, cls, nh) in sorted(win.items()):
        for pop in pops_:
            key = (1 if cell in names else 0, 1 if home.get(pop) == cell else 0, nh, -cell)
            alts.setdefault(pop, []).append(cell)
            if pop not in pick_cell or key > rank[pop]:
                pick_cell[pop], rank[pop] = (cell, cls, nh), key

    pops = sorted(pick_cell)
    missing = [p for p in pops if p not in hosts]
    pops = [p for p in pops if p in hosts]
    # A PoP that only wins in unnamed cells can't be picked from the UI.
    hidden = [p for p in pops if pick_cell[p][0] not in names] if names else []
    if names:
        pops = [p for p in pops if pick_cell[p][0] in names]
    if not pops:
        sys.exit("Nothing to measure.")
    print(f"  {len(win)} cells -> {len(pops)} PoPs reachable from your IP")
    if missing:
        print(f"  (no known hosts: {', '.join(missing)})")
    if hidden:
        print(f"  (not selectable in Steam: {', '.join(hidden)})")

    depot, chunks, mname = find_chunks(root, args.pool, 900_000,
                                       sorted(hosts[pops[0]])[0])
    print(f"  depot {depot} ({mname}), {len(chunks)} chunks")

    print(f"\nMeasuring {len(pops)} PoPs: up to {args.budget} MB or "
          f"{args.max_secs:.0f}s each, whichever comes first.")
    print(f"  Worst case {len(pops) * args.budget / 1024:.1f} GB and "
          f"{len(pops) * args.max_secs / 60:.0f} min. Most PoPs stop early, "
          f"and slow ones\n  hit the time cap long before the traffic cap.")
    if not args.yes:
        try:
            if input("Go ahead? [y/N] ").strip().lower() not in ("y", "yes"):
                sys.exit(0)
        except (EOFError, KeyboardInterrupt):
            sys.exit(0)

    results = []
    for i, pop in enumerate(pops, 1):
        host = sorted(hosts[pop])[0]
        print(f"  [{i}/{len(pops)}] {pop:<12} ", end="", flush=True)
        ms, ms_min = tcp_latency(host)
        r = measure_hot(pop, host, depot, chunks, args)
        r.ms, r.ms_min = ms, ms_min
        results.append(r)
        note = "  (remeasured warm)" if r.rewarmed else ""
        if r.hitpct is not None and r.hitpct < args.min_hit:
            note = f"  ({r.hitpct:.0f}% hit, treat with care)"
        lat = f"{r.ms:5.0f} ms" if r.ms is not None else ""
        if r.ms and r.ms_min and r.ms > 2.5 * r.ms_min:
            lat += f" (min {r.ms_min:.0f}, erratic)"
        print(f"{r.mbps:7.1f} MB/s   {lat}{note}")

    results.sort(key=lambda r: -r.mbps)
    where = {r.pop: (names.get(home.get(r.pop)) or city_of(r.pop)) for r in results}
    table(results, where, pick_cell, names)

    top = results[0]
    if top.mbps < 1.0:
        print("\n  Every PoP measured under 1 MB/s. Something is wrong with the "
              "connection\n  or the CDN is refusing us - the ranking below means "
              "nothing.")
    band = [r for r in results if r.mbps >= top.mbps * (1 - args.tie / 100)]
    pick = top
    if len(band) > 1 and top.ms is not None:
        cand = min((r for r in band if r.ms is not None), key=lambda r: r.ms)
        # Only trade throughput for latency when the latency win is real,
        # otherwise a 1 ms edge would cost several MB/s.
        if cand is not top and top.ms - cand.ms >= max(20.0, 0.20 * top.ms):
            pick = cand
        print(f"\n  within {args.tie:.0f}%, so latency decides: " + ", ".join(
            f"{r.pop} ({r.mbps:.0f} MB/s, {r.ms:.0f} ms)" for r in band))

    cell, cls, nh = pick_cell[pick.pop]
    pinned = top_class_pops(servers_for_cell(cell, geolocate=True))
    print(f"\n-> Pick \"{names.get(cell, '?')}\"  (cell {cell})")
    print(f"   You'll be served by {pick.pop} ({where[pick.pop]}): {pick.mbps:.1f} MB/s "
          f"({pick.mbps * 8.389:.0f} Mbit/s)" + (f", {pick.ms:.0f} ms" if pick.ms else ""))
    print(f"   Steam will use {nh} host(s) from class {cls} in that cell.")
    if pinned and pick.pop not in pinned:
        got = ", ".join(sorted(pinned))
        print(f"   Queried the way the Steam client does, this connection is still")
        print(f"   assigned {got} for that region. Confirm the host in")
        print(f"   logs/content_log.txt after changing the download region.")
    if pick is not top:
        print(f"   ({top.pop} is faster at {top.mbps:.1f} MB/s but sits at "
              f"{top.ms:.0f} ms against {pick.ms:.0f} ms)")

    same = sorted({names[c] for c in alts[pick.pop] if c != cell and c in names})
    if same:
        print(f"   {len(same)} other regions reach the same PoP:")
        line = []
        for n in same:
            if line and sum(len(x) + 3 for x in line) + len(n) > 72:
                print("     " + " | ".join(line))
                line = []
            line.append(n)
        if line:
            print("     " + " | ".join(line))

    if args.json:
        Path(args.json).write_text(json.dumps({
            "recommended": {"cell": cell, "region": names.get(cell), "pop": pick.pop},
            "pops": [{
                "pop": r.pop, "located_in": where[r.pop],
                "pick_cell": pick_cell[r.pop][0],
                "pick_region": names.get(pick_cell[r.pop][0]),
                "hosts_in_top_class": pick_cell[r.pop][2],
                "mbytes_s": round(r.mbps, 2), "mbit_s": round(r.mbps * 8.389),
                "latency_ms": round(r.ms) if r.ms else None,
                "latency_min_ms": round(r.ms_min) if r.ms_min else None,
                "hit_pct": round(r.hitpct) if r.hitpct is not None else None,
                "stable": r.stable, "rewarmed": r.rewarmed,
            } for r in results],
        }, indent=2, ensure_ascii=False))
        print(f"   JSON -> {args.json}")


if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        print("\nInterrupted.")
        sys.exit(130)
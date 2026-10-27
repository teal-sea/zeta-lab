#!/usr/bin/env python3
"""Turn hunt #145's run log into `pilot.json`: the cost table and the projection.

Inputs are the JSON lines `pilot.py` appended to WORK/runs.jsonl and the site record
`scripts/72` wrote to WORK/site/<site>/out/results/C<site>.json.  Nothing here launches
Lean.  Every derived number is computed from those records in this file, so `PILOT.md`
and `OWNER_MEMO.md` quote `pilot.json` and the hunt test checks that they do.

Cost model (stated, not fitted to anything beyond this pilot):

* CPU means user + system time from wait4, in seconds.
* A unit's net CPU is its compile CPU minus the median CPU of the warm import-only runs
  with the same imports.  The first import-only run of the session read the Mathlib
  oleans from disk and is excluded as cold; it stays in the log.
* Tower cost: the pilot site's prime shards' CPU net of their import probes, priced two
  ways, per source byte (times each plan tower's Lean text bytes, emitted by scripts/69
  at one representative point per site kind) and flat per tower.  The shards support
  neither over the other (RUNS.md, 22:07 UTC), so the primary projection is the larger.
  Sensitivity models: a least-squares fit a * towers + b * bytes over the scripts/68
  one-tower files and the shards, and, when recorded, one shard recompiled with
  `lean -j1`, priced per byte at one core per process.
* Composite, term and root costs are the pilot site's in-situ costs per composite,
  per nonzero term and per series term (N = 5K), scaled linearly in those counts.
* Import overhead per module is the import-only probe of that module's own imports;
  for other sites it is modelled as the Base probe plus a per-byte cost of the site
  oleans the module loads, fitted from the pilot's probes.
"""
from __future__ import annotations

import argparse
import importlib.util
import json
import math
import os
import time
import re
import statistics as st
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PLAN = json.loads((ROOT / "lean" / "cert" / "rung3_plan2.json").read_text())
# The second attempt's work directory; the first, interrupted at 18:08 UTC mid-site,
# is kept unchanged at rung3-ball-production-pilot (see RUNS.md).
DEFAULT_WORK = Path(os.environ.get("RUNG3_PILOT_WORK", os.path.expanduser("~/.cache/zeta-lab/rung3-ball-production-pilot-2")))
TOWER_MULS = 30
V433 = {"tower_cpu_s_per_atom": 1.2504, "composite_s_per_atom": 0.55,
        "import_cpu_s": round(st.mean([3.075 + 1.498, 3.097 + 1.481, 3.120 + 1.458]), 3),
        "atom_only_core_hours": 175.0}
MAX_SHARD_BYTES = 2_000_000
VCPUS = 32


def _load(name: str, filename: str):
    spec = importlib.util.spec_from_file_location(name, ROOT / "scripts" / filename)
    assert spec is not None and spec.loader is not None
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def cpu(r: dict) -> float:
    return r["user"] + r["system"]


def runs(work: Path) -> list[dict]:
    return [json.loads(line) for line in (work / "runs.jsonl").read_text().splitlines()
            if line.strip()]


def warm_baseline(rs: list[dict], tag: str) -> tuple[float, list[dict], list[dict]]:
    """Median CPU of the warm import-only runs with this tag; the session's first
    import-only run of all is cold and excluded."""
    first = next(i for i, r in enumerate(rs) if r["tag"].endswith("baseline"))
    sel = [r for i, r in enumerate(rs) if r["tag"] == tag and i != first
           and r["returncode"] == 0]
    cold = [r for i, r in enumerate(rs) if r["tag"] == tag and i == first]
    return st.median(cpu(r) for r in sel), sel, cold


def unit(rs: list[dict], tag: str, base_tag: str, n_atoms: int, **match) -> dict:
    base, base_runs, cold = warm_baseline(rs, base_tag)
    sel = [r for r in rs if r["tag"] == tag and r["returncode"] == 0
           and all(r.get(k) == v for k, v in match.items())]
    net = [round(cpu(r) - base, 3) for r in sel]
    out = {
        "tag": tag, "runs": len(sel), "atoms_per_run": n_atoms,
        "cpu_s": [round(cpu(r), 3) for r in sel], "wall_s": [r["wall"] for r in sel],
        "peak_rss_gib": [round(r["peak_rss_bytes"] / 2**30, 2) for r in sel],
        "rss_anon_gib": [round(r["box"].get("lean_max_rss_anon_bytes", 0) / 2**30, 2)
                         for r in sel],
        "load1_mean": [r["box"].get("load1_mean") for r in sel],
        "baseline_tag": base_tag, "baseline_cpu_s": round(base, 3),
        "baseline_runs_cpu_s": [round(cpu(r), 3) for r in base_runs],
        "baseline_cold_cpu_s": [round(cpu(r), 3) for r in cold],
        "net_cpu_s": net,
        "file_bytes": sel[0].get("bytes") if sel else None,
    }
    if net:
        out["mean_net_cpu_s"] = round(st.mean(net), 3)
        out["cpu_s_per_atom"] = round(st.mean(net) / n_atoms, 4)
        out["cpu_s_per_atom_range"] = [round(min(net) / n_atoms, 4), round(max(net) / n_atoms, 4)]
    return out


# --------------------------------------------------------------------------- the site

def classify(path: str) -> str:
    """Module role from its path: root, base, primes-shard, barrel (Primes.lean),
    composites, terms, sums (numbered shards share their stem's role)."""
    name = Path(path).name
    if "/" not in path:
        return "root"
    if name == "Base.lean":
        return "base"
    if name == "Primes.lean":
        return "barrel"
    m = re.fullmatch(r"(Primes|Composites|Terms|Sums)(\d*)\.lean", name)
    if not m:
        return "other"
    return {"Primes": "primes-shard", "Composites": "composites", "Terms": "terms",
            "Sums": "sums"}[m.group(1)]


def module_counts(text: str) -> dict:
    return {
        "towers": len(re.findall(r"^namespace Prime_\d+$", text, re.MULTILINE)),
        "tower_primes": [int(x) for x in re.findall(r"^namespace Prime_(\d+)$", text,
                                                    re.MULTILINE)],
        "composites": len(re.findall(r"lemma evpow_", text)),
        "nonzero_terms": len(re.findall(r"lemma evterm_", text)),
        "terms": len(re.findall(r"lemma hterm_", text)),
        "partial_sum_chunks": len(re.findall(r"lemma ps_", text)),
    }


def _count_log(rec: dict, needle: str) -> int | None:
    """Lines of a module's compile log containing `needle`."""
    log = rec.get("log")
    if not log or not Path(log).is_file():
        return None
    return sum(1 for ln in Path(log).read_text(errors="replace").splitlines() if needle in ln)


def _ck_sha(out: Path, root: str, path: str) -> str | None:
    ck = out / "checkpoints" / root / (path.replace("/", "__") + ".ok.json")
    return json.loads(ck.read_text()).get("sha256") if ck.is_file() else None


def site_section(rs: list[dict], work: Path, site: str) -> dict:
    gen = work / "site" / site / "gen"
    out = work / "site" / site / "out"
    site_root = f"C{site}"
    result = json.loads((out / "results" / f"C{site}.json").read_text())
    compile_run = next(r for r in reversed(rs) if r["tag"] == "site-compile")
    gen_run = next(r for r in reversed(rs) if r["tag"] == "site-generate")
    probes: dict[str, list[dict]] = {}
    for r in rs:
        if r["tag"] == "import-probe" and r["returncode"] == 0:
            probes.setdefault(r["module"], []).append(r)
    procs = compile_run.get("box", {}).get("lean_processes", [])

    def anon_gib(path: str) -> float | None:
        hits = [q["max_rss_anon_bytes"] for q in procs
                if q.get("source") and q["source"].endswith("/" + path)]
        return round(max(hits) / 2**30, 3) if hits else None

    # Each module's window: its checkpoint is written when it ends, and it began `elapsed`
    # seconds before.  The 1-minute load in that window comes from WORK/loadlog.tsv, which
    # a logger outside pilot.py appended every 10 s (epoch, load1, load5, load15, KiB).
    loadlog = []
    if (work / "loadlog.tsv").is_file():
        for line in (work / "loadlog.tsv").read_text().splitlines():
            f = line.split("\t")
            if len(f) == 5:
                loadlog.append((int(f[0]), float(f[1])))

    def load_in(path: str, elapsed: float) -> float | None:
        ck = out / "checkpoints" / site_root / (path.replace("/", "__") + ".ok.json")
        if not ck.is_file():
            return None
        hi = ck.stat().st_mtime
        lo = hi - elapsed
        xs = [l1 for ts, l1 in loadlog if lo <= ts <= hi]
        return round(sum(xs) / len(xs), 1) if xs else None

    mods = []
    for rec in result["modules"]:
        path = rec["path"]
        text = (gen / path).read_text()
        olean = out / Path(path).with_suffix(".olean")
        kind = classify(path)
        pr = probes.get(path, [])
        imp = st.median(cpu(p) for p in pr) if pr else None
        m = {
            "path": path, "kind": kind, "status": rec["status"],
            "bytes": (gen / path).stat().st_size,
            "olean_bytes": olean.stat().st_size if olean.is_file() else None,
            "wall_s": round(rec["elapsed"], 3), "cpu_s": round(rec["user"] + rec["system"], 3),
            "user_s": round(rec["user"], 3), "system_s": round(rec["system"], 3),
            "peak_rss_gib": round(rec["peak_rss_bytes"] / 2**30, 3),
            "sha256": rec.get("sha256") or _ck_sha(out, site_root, path),
            "rss_anon_gib": anon_gib(path),
            "load1_mean": load_in(path, rec["elapsed"]),
            "log_warnings": _count_log(rec, ": warning:"),
            "log_warnings_seq_focus": _count_log(rec, "where `(tac1; tac2)` would suffice"),
            "import_probe_cpu_s": round(imp, 3) if imp is not None else None,
            "import_probe_wall_s": (round(st.median(p["wall"] for p in pr), 3)
                                    if pr else None),
            **{k: v for k, v in module_counts(text).items() if k != "tower_primes"},
        }
        if imp is not None:
            m["net_cpu_s"] = round(m["cpu_s"] - imp, 3)
        m["tower_primes"] = module_counts(text)["tower_primes"]
        mods.append(m)

    def total(kind, key):
        return sum(m[key] for m in mods if m["kind"] == kind and m.get(key) is not None)

    towers = total("primes-shard", "towers")
    comps = total("composites", "composites")
    nz = total("terms", "nonzero_terms")
    K = int(next(b for b in PLAN["big"]["boxes"] if b["id"] == site)["K"])
    N = 5 * K
    insitu = {
        "towers": towers, "composites": comps, "nonzero_terms": nz, "N": N,
        "tower_net_cpu_s": round(total("primes-shard", "net_cpu_s"), 3),
        "cpu_s_per_tower_atom": round(total("primes-shard", "net_cpu_s")
                                      / (towers * TOWER_MULS), 4),
        "cpu_s_per_composite": round(total("composites", "net_cpu_s") / comps, 4),
        "cpu_s_per_nonzero_term": round(total("terms", "net_cpu_s") / nz, 4),
        "root_net_cpu_s": round(total("root", "net_cpu_s"), 3),
        "root_cpu_s_per_series_term": round(total("root", "net_cpu_s") / N, 4),
        "import_cpu_s_total": round(sum(m["import_probe_cpu_s"] or 0 for m in mods), 3),
    }
    cpu_total = sum(m["cpu_s"] for m in mods)
    wall_total = sum(m["wall_s"] for m in mods)
    return {
        "site": site, "K": K, "N": N, "status": result["status"],
        "generate": {k: gen_run[k] for k in ("argv", "cwd", "returncode", "wall", "user",
                                             "system", "peak_rss_bytes")},
        "compile": {k: compile_run[k] for k in ("argv", "cwd", "returncode", "wall", "user",
                                                "system", "peak_rss_bytes", "started",
                                                "load_at_start", "box")},
        "manifest_sha256": compile_run.get("manifest_sha256"),
        "modules": mods, "in_situ": insitu,
        "modules_cpu_s": round(cpu_total, 3), "modules_wall_s": round(wall_total, 3),
        "cores_per_process": round(cpu_total / wall_total, 3),
        "max_peak_rss_gib": max(m["peak_rss_gib"] for m in mods),
        "max_rss_anon_gib": max((m["rss_anon_gib"] or 0) for m in mods),
        "olean_bytes_total": sum(m["olean_bytes"] or 0 for m in mods),
        "log_warnings_total": sum(m["log_warnings"] or 0 for m in mods),
        "log_warnings_seq_focus_total": sum(m["log_warnings_seq_focus"] or 0 for m in mods),
        "source_bytes_total": sum(m["bytes"] for m in mods),
    }


# --------------------------------------------------------------------------- projection

def _sieve(n: int) -> bytearray:
    s = bytearray([1]) * (n + 1)
    s[0:2] = b"\0\0"
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]:
            s[i * i::i] = bytearray(len(s[i * i::i]))
    return s


def tower_bytes_table(max_m: int) -> dict[str, dict[int, int]]:
    """Lean text bytes of each prime's tower at one representative point per kind."""
    g = _load("rung3_ball_generate_for_report", "69_rung3_ball_generate.py")
    ball = g.ball
    small = PLAN["small"]
    big = next(b for b in PLAN["big"]["boxes"] if b["id"] == "B_left_17")
    grid = PLAN["grid"][0]
    x, fx = F(grid["x"]), F(grid["fixed"])
    gre, gim = (x, fx) if grid["segment"] in ("bottom", "top") else (fx, x)
    points = {
        "big": ball.from_box(F(big["re_lo"]), F(big["re_hi"]), F(big["im_lo"]),
                             F(big["im_hi"])),
        "grid": ball.from_box(gre, gre, gim, gim),
        "centre": ball.from_box(F(small["cre"]), F(small["cre"]), F(small["cim"]),
                                F(small["cim"])),
    }
    prime = _sieve(max_m)
    out: dict[str, dict[int, int]] = {}
    for kind, S in points.items():
        out[kind] = {}
        for p in range(2, max_m + 1):
            if prime[p] and p != 5:
                text, _ = g._tower_fragment(p, S, f"Prime_{p}")
                out[kind][p] = len((text.rstrip() + "\n\n").encode())
    return out


def plan_sites() -> list[tuple[str, dict]]:
    return ([("big", b) for b in PLAN["big"]["boxes"]]
            + [("grid", g) for g in PLAN["grid"]]
            + [("centre", PLAN["centre"])])


def pack_count(sizes: list[int], cap: int) -> int:
    n, used = 0, cap + 1
    for s in sizes:
        if used + s > cap:
            n += 1
            used = 0
        used += s
    return n


def projection(towers: dict, site: dict, tower_fit: tuple[float, float],
               import_model: dict, cores_per_process: float) -> dict:
    per_tower, per_byte = tower_fit
    ins = site["in_situ"]
    per_comp, per_term = ins["cpu_s_per_composite"], ins["cpu_s_per_nonzero_term"]
    per_series = ins["root_cpu_s_per_series_term"]
    mods = {m["kind"]: m for m in site["modules"]}
    comp_b = mods["composites"]["bytes"] / ins["composites"]
    term_b = mods["terms"]["bytes"] / site["N"]
    root_b = mods["root"]["bytes"] / site["N"]
    shard_mods = [m for m in site["modules"] if m["kind"] == "primes-shard"]
    olean_per_byte = (sum(m["olean_bytes"] for m in shard_mods)
                      / sum(m["bytes"] for m in shard_mods))
    olean_per_tower = (sum(m["olean_bytes"] for m in shard_mods)
                       / sum(m["towers"] for m in shard_mods))
    other_olean = sum(m["olean_bytes"] or 0 for m in site["modules"]
                      if m["kind"] not in ("primes-shard", "root"))
    max_K = max(s["K"] for _, s in plan_sites())
    prime = _sieve(5 * max_K + 5)
    body_cap = MAX_SHARD_BYTES - 600
    rows, tot = [], {"tower": 0.0, "composite": 0.0, "term": 0.0, "root": 0.0,
                     "import": 0.0, "modules": 0, "tower_text_bytes": 0,
                     "olean_bytes_est": 0.0, "olean_bytes_est_per_tower": 0.0}
    for kind, s in plan_sites():
        K = int(s["K"])
        N = 5 * K
        ms = [m for m in range(2, N + 5) if m % 5]
        primes = [m for m in ms if prime[m]]
        comps = len(ms) - len(primes)
        sizes = [towers[kind][p] for p in primes]
        tb = sum(sizes)
        n_pr = pack_count(sizes, body_cap)
        n_mod = 1 + n_pr + (1 if n_pr > 1 else 0)
        for nbytes in (comps * comp_b, N * term_b):
            k = math.ceil(nbytes / body_cap)
            n_mod += k + (1 if k > 1 else 0)
        rb = N * root_b
        n_mod += 1 if rb <= body_cap else math.ceil(rb / body_cap) + 1
        # the oleans a non-shard module imports: every prime shard's, plus Base, the
        # barrel and the composite and term modules, scaled from the pilot by K
        site_oleans = olean_per_byte * tb + other_olean * K / site["K"]
        imp = (n_pr + 1) * import_model["base_cpu_s"] + \
            (n_mod - n_pr - 1) * (import_model["base_cpu_s"]
                                  + import_model["cpu_s_per_olean_byte"] * site_oleans)
        c = {"tower": per_tower * len(primes) + per_byte * tb,
             "composite": per_comp * comps,
             "term": per_term * 4 * K, "root": per_series * N, "import": imp}
        for k, v in c.items():
            tot[k] += v
        tot["modules"] += n_mod
        tot["tower_text_bytes"] += tb
        tot["olean_bytes_est"] += site_oleans
        tot["olean_bytes_est_per_tower"] += (olean_per_tower * len(primes)
                                             + other_olean * K / site["K"])
        rows.append({"id": s.get("id", "centre"), "kind": kind, "K": K,
                     "primes": len(primes), "composites": comps, "modules": n_mod,
                     "cpu_s": round(sum(c.values()), 1)})
    total_cpu = sum(tot[k] for k in ("tower", "composite", "term", "root", "import"))
    hours = total_cpu / 3600
    walls = {}
    for n in (16, 20, 24):
        cores_one = min(VCPUS, n * 1.0)
        cores_meas = min(VCPUS, n * cores_per_process)
        walls[str(n)] = {"wall_h_one_core_each": round(hours / cores_one, 2),
                         "wall_h_measured_cores_per_process": round(hours / cores_meas, 2)}
    biggest = max(rows, key=lambda r: r["cpu_s"])
    return {
        "core_hours": {k: round(tot[k] / 3600, 2) for k in
                       ("tower", "composite", "term", "root", "import")},
        "total_core_hours": round(hours, 1),
        "modules": tot["modules"],
        "tower_text_gb": round(tot["tower_text_bytes"] / 1e9, 2),
        "olean_gb_est": round(tot["olean_bytes_est"] / 1e9, 1),
        "olean_gb_est_per_tower": round(tot["olean_bytes_est_per_tower"] / 1e9, 1),
        "wall_clock": walls,
        "largest_site": biggest,
        "rates": {"tower_cpu_s_per_tower": per_tower,
                  "tower_cpu_s_per_text_byte": per_byte,
                  "composite_cpu_s": per_comp, "nonzero_term_cpu_s": per_term,
                  "root_cpu_s_per_series_term": per_series, **import_model},
        "sites": rows,
    }


FIRST_ATTEMPT = Path(os.environ.get("RUNG3_PILOT_FIRST_WORK", os.path.expanduser("~/.cache/zeta-lab/rung3-ball-production-pilot")))


def first_attempt_modules(site: dict) -> list[dict]:
    """The four modules the interrupted first attempt checkpointed, beside this run's."""
    ck = FIRST_ATTEMPT / "site" / site["site"] / "out" / "checkpoints" / f"C{site['site']}"
    out = []
    for path in sorted(ck.glob("*.ok.json")) if ck.is_dir() else []:
        r = json.loads(path.read_text())
        now = next((m for m in site["modules"] if m["path"] == r["path"]), None)
        if now is None:
            continue
        c1 = r["user"] + r["system"]
        out.append({"path": r["path"], "sha256": r["sha256"],
                    "same_source": r["sha256"] == now.get("sha256"),
                    "first_cpu_s": round(c1, 3), "first_wall_s": round(r["elapsed"], 3),
                    "first_peak_rss_gib": round(r["peak_rss_bytes"] / 2**30, 3),
                    "cpu_s": now["cpu_s"], "wall_s": now["wall_s"],
                    "cpu_ratio": round(now["cpu_s"] / c1, 3),
                    "wall_ratio": round(now["wall_s"] / r["elapsed"], 3)})
    order = [m["path"] for m in site["modules"]]
    return sorted(out, key=lambda x: order.index(x["path"]))


def generator_replay(site: str, work: Path) -> dict:
    """SHA-256 of every generated source of the site in both attempts' work directories."""
    import hashlib

    def shas(gen: Path) -> dict[str, str]:
        files = sorted(gen.rglob("*.lean"))
        return {str(f.relative_to(gen)): hashlib.sha256(f.read_bytes()).hexdigest()
                for f in files}
    a = shas(FIRST_ATTEMPT / "site" / site / "gen")
    b = shas(work / "site" / site / "gen")
    return {"first_attempt": a, "this_run": b, "identical": a == b and len(b) > 0}


def launch_audit(work_dirs: list[Path]) -> dict:
    """What `scripts/72` was ever asked to compile, and which checkpoint roots exist,
    across both attempts' work directories: the evidence that no production shard ran."""
    manifests, roots, lean_files = set(), set(), set()
    for w in work_dirs:
        log = w / "runs.jsonl"
        if log.is_file():
            for line in log.read_text().splitlines():
                r = json.loads(line) if line.strip() else {}
                argv = r.get("argv") or []
                if any(str(a).endswith("72_rung3_ball_compile.py") for a in argv):
                    manifests.update(Path(a).name for a in argv if str(a).endswith(".json"))
                if argv[:3] == ["lake", "env", "lean"]:
                    lean_files.update(Path(a).name for a in argv if str(a).endswith(".lean"))
        for ck in w.rglob("checkpoints"):
            if ck.is_dir():
                roots.update(d.name for d in ck.iterdir() if d.is_dir())
    return {"work_dirs": [str(w) for w in work_dirs],
            "scripts72_manifests": sorted(manifests),
            "checkpoint_roots": sorted(roots),
            "direct_lean_files": sorted(lean_files)}


def setup_section() -> dict:
    """The Lean environment the pilot ran in, read live from the worktree's lean/."""
    import subprocess
    lean = ROOT / "lean"
    manifest = json.loads((lean / "lake-manifest.json").read_text())
    pkgs = []
    for p in manifest["packages"]:
        d = lean / ".lake" / "packages" / p["name"]

        def git(*a, d=d):
            r = subprocess.run(["git", "-C", str(d), *a], capture_output=True, text=True)
            return r.stdout.strip() if r.returncode == 0 else None
        pkgs.append({"name": p["name"], "manifest_rev": p.get("rev"),
                     "head": git("rev-parse", "HEAD"),
                     "toplevel": git("rev-parse", "--show-toplevel"),
                     "toplevel_is_package": git("rev-parse", "--show-toplevel")
                     == str(d.resolve())})
    built = sorted(x.stem for x in (lean / ".lake" / "build" / "lib" / "lean" / "ZetaLean")
                   .glob("*.olean"))
    toolchain = (lean / "lean-toolchain").read_text().strip()
    ver = subprocess.run([str(Path.home() / ".elan" / "toolchains"
                              / "leanprover--lean4---v4.35.0-rc2" / "bin" / "lean"),
                          "--version"], capture_output=True, text=True).stdout.strip()
    cpu = next(ln.split(":", 1)[1].strip() for ln in open("/proc/cpuinfo")
               if ln.startswith("model name"))
    vcpu = sum(1 for ln in open("/proc/cpuinfo") if ln.startswith("processor"))
    mem_kib = next(int(ln.split()[1]) for ln in open("/proc/meminfo")
                   if ln.startswith("MemTotal:"))
    import shutil
    du = shutil.disk_usage(os.path.expanduser("~"))
    return {"box": {"cpu_model": cpu, "vcpus": vcpu, "mem_total_gib": round(mem_kib / 2**20, 1),
                    "hostname": os.uname().nodename,
                    "disk_total_gb": round(du.total / 1e9, 1),
                    "disk_free_gb": round(du.free / 1e9, 1),
                    "disk_read_at": time.strftime("%Y-%m-%dT%H:%MZ", time.gmtime())},
            "lean_toolchain": toolchain, "lean_version": ver, "packages": pkgs,
            "zetalean_built": built,
            "all_packages_own_toplevel": all(p["toplevel_is_package"] for p in pkgs),
            "all_heads_match_manifest": all(p["head"] == p["manifest_rev"] for p in pkgs)}


def _f(x, nd=2) -> str:
    return "n/a" if x is None else f"{x:,.{nd}f}"


def markdown_tables(p: dict) -> dict[str, str]:
    """The tables PILOT.md and OWNER_MEMO.md quote, rendered from pilot.json alone."""
    v = p["v433_record"]
    t2 = p["tower"]["2"]
    big = p["tower"].get("1801")
    ins = p["site"]["in_situ"]
    comp = p["composite"]
    mods = p["site"]["modules"]
    base = next(m for m in mods if m["kind"] == "base")
    root = next(m for m in mods if m["kind"] == "root")
    rows = [
        "| quantity | v4.33.0-rc2 record | this pilot | ratio |",
        "|---|---|---|---|",
        f"| CPU-s per prime-tower atom, `scripts/68` tower at p = 2, "
        f"{t2['file_bytes'] / 1000:,.0f} KB of text (net of import) | "
        f"{v['tower_cpu_s_per_atom']} | {t2['cpu_s_per_atom']} "
        f"({t2['cpu_s_per_atom_range'][0]} to {t2['cpu_s_per_atom_range'][1]}, "
        f"{t2['runs']} runs) | {t2['cpu_s_per_atom'] / v['tower_cpu_s_per_atom']:.2f} |",
    ]
    labels = {"tower-j1": "with `lean -j1`",
              "tower-Dlinter.all=false": "with Lean's linters off (`-Dlinter.all=false`)"}
    for tag, label in labels.items():
        u = p["tower"].get(tag)
        if u and u.get("cpu_s_per_atom"):
            rows.append(
                f"| CPU-s per prime-tower atom, `scripts/68` tower at p = 2, {label} | "
                f"not measured | {u['cpu_s_per_atom']} ({u['cpu_s_per_atom_range'][0]} to "
                f"{u['cpu_s_per_atom_range'][1]}, {u['runs']} runs) | "
                f"{u['cpu_s_per_atom'] / v['tower_cpu_s_per_atom']:.2f} |")
    if big and big.get("cpu_s_per_atom"):
        rows.append(
            f"| CPU-s per prime-tower atom, `scripts/68` tower at p = 1801, "
            f"{big['file_bytes'] / 1000:,.0f} KB of text | not measured | "
            f"{big['cpu_s_per_atom']} ({big['runs']} runs) | "
            f"{big['cpu_s_per_atom'] / v['tower_cpu_s_per_atom']:.2f} |")
    rows += [
        f"| CPU-s per prime-tower atom in the site's prime shards (p = 2 to 89, "
        f"{ins['towers']} towers) | not measured | {ins['cpu_s_per_tower_atom']} | "
        f"{ins['cpu_s_per_tower_atom'] / v['tower_cpu_s_per_atom']:.2f} |",
        f"| CPU-s per composite atom, `scripts/66`, {comp['atoms_per_run']} atoms "
        f"(net of import) | {v['composite_s_per_atom']} | {comp['cpu_s_per_atom']} "
        f"({comp['runs']} runs) | {comp['cpu_s_per_atom'] / v['composite_s_per_atom']:.2f} |",
        f"| CPU-s per composite in the site's `Composites` module "
        f"({ins['composites']} composites) | not measured | {ins['cpu_s_per_composite']} | "
        f"{ins['cpu_s_per_composite'] / v['composite_s_per_atom']:.2f} |",
        f"| CPU-s per nonzero term in the site's `Terms` module "
        f"({ins['nonzero_terms']} terms) | not measured | {ins['cpu_s_per_nonzero_term']} | |",
        f"| root module net CPU-s (term function, partial sums, assembly; N = {ins['N']}) | "
        f"not measured | {_f(ins['root_net_cpu_s'], 1)} | |",
        f"| import-only CPU-s per module, `Base` imports (median) | "
        f"{v['import_cpu_s']} | {base['import_probe_cpu_s']} | "
        f"{base['import_probe_cpu_s'] / v['import_cpu_s']:.2f} |",
        f"| import-only CPU-s per module, root imports (whole site loaded) | not measured | "
        f"{root['import_probe_cpu_s']} | |",
        f"| peak RSS added by importing the site's other oleans (root probe minus `Base` "
        f"probe), per olean byte imported | not measured | "
        f"{p['import_model']['rss_bytes_per_imported_olean_byte']:.2f} | |",
        f"| peak RSS per process, largest module (wait4) | not recorded | "
        f"{p['site']['max_peak_rss_gib']:.2f} GiB | |",
        f"| of which anonymous, largest module (sampled each second; the rest is "
        f"file-backed olean mappings, shared between processes) | not recorded | "
        f"{p['site']['max_rss_anon_gib']:.2f} GiB | |",
        f"| cores busy per process, site compile at one process (CPU / wall) | "
        f"not recorded | {p['site']['cores_per_process']:.2f} | |",
    ]
    cost = "\n".join(rows)

    mrows = ["| module | towers | composites | terms | source KB | olean MB | wall s | CPU s "
             "| import CPU s | net CPU s | peak RSS GiB | anon RSS GiB | load | warnings |",
             "|---|---|---|---|---|---|---|---|---|---|---|---|---|---|"]
    for m in mods:
        mrows.append(
            f"| `{m['path']}` | {m['towers'] or ''} | {m['composites'] or ''} | "
            f"{m['nonzero_terms'] or ''} | {m['bytes'] / 1000:,.1f} | "
            f"{(m['olean_bytes'] or 0) / 1e6:,.1f} | {m['wall_s']:,.1f} | {m['cpu_s']:,.1f} | "
            f"{_f(m['import_probe_cpu_s'], 1)} | {_f(m.get('net_cpu_s'), 1)} | "
            f"{m['peak_rss_gib']:.2f} | {_f(m.get('rss_anon_gib'))} | "
            f"{_f(m.get('load1_mean'), 0)} | {m.get('log_warnings', '')} |")
    mrows.append(
        f"| **site total** | {ins['towers']} | {ins['composites']} | {ins['nonzero_terms']} | "
        f"{p['site']['source_bytes_total'] / 1000:,.1f} | "
        f"{p['site']['olean_bytes_total'] / 1e6:,.1f} | {p['site']['modules_wall_s']:,.1f} | "
        f"{p['site']['modules_cpu_s']:,.1f} | {ins['import_cpu_s_total']:,.1f} | | | | | "
        f"{p['site']['log_warnings_total']} |")
    modules = "\n".join(mrows)

    frows = ["| fault | change planted | expected refusal | errors at | driver exit | "
             "module refused | modules recompiled |", "|---|---|---|---|---|---|---|"]
    for f in p["faults"]:
        ch = f["fault"]
        if "new_rad" in ch:
            what = (f"`{ch['declaration']}` radius lowered by one unit of its denominator "
                    f"(`{ch['old_rad']}` to `{ch['new_rad']}`)")
        elif "new_r" in ch:
            what = (f"tail radius `r` set {float(F(ch['tail_bound']) - F(ch['new_r'])):.1e} "
                    f"below the tail bound, all {ch['occurrences_replaced']} occurrences")
        else:
            what = (f"`M` set {float(F(ch['u_plus_rad']) - F(ch['new_M'])):.1e} below "
                    f"`u + rad` of the inflated ball")
        at = ", ".join(f"`{d.removeprefix('ZetaLean.DH.Cert.')}`"
                       for d in f["error_declarations"])
        frows.append(f"| {f['tag'][len('fault-'):-len('-outcome')]} | {what} | "
                     f"`{ch['expected_failure']}` | {at} | {f['driver_returncode']} | "
                     f"`{', '.join(f['failed_modules'])}` | {len(f['recompiled'])} |")
    faults = "\n".join(frows)

    crows = ["| probe | eps' stated | u + rad of the centre ball | lean exit |",
             "|---|---|---|---|"]
    for r in p["centre_eps"]:
        crows.append(f"| {r['tag'][len('centre-eps-'):]} | {float(F(r['eps'])):.6e} | "
                     f"{float(F(r['u_plus_rad'])):.6e} | {r['returncode']} |")
    centre = "\n".join(crows)

    pr = p["projection"]
    ch = pr["core_hours"]
    a = p["atom_only"]
    prow = ["| component | core-hours |", "|---|---|",
            f"| prime towers ({a['tower_atoms']:,} atoms) | {ch['tower']:,.1f} |",
            f"| composites | {ch['composite']:,.1f} |",
            f"| term products | {ch['term']:,.1f} |",
            f"| root and partial sums | {ch['root']:,.1f} |",
            f"| imports ({pr['modules']:,} modules) | {ch['import']:,.1f} |",
            f"| **total, projected from this pilot** | **{pr['total_core_hours']:,.1f}** |",
            f"| atom-only, `scripts/67` formula at the `scripts/68` and `scripts/66` rates "
            f"of this box | {a['scripts68_p2_rate_core_hours']:,.1f} |",
            f"| atom-only, `scripts/67` formula at the in-situ rates of this site | "
            f"{a['in_situ_rate_core_hours']:,.1f} |",
            f"| atom-only, `scripts/67` as recorded (v4.33.0-rc2 rates) | "
            f"{a['v433_core_hours']:,.1f} |",
            f"| *oleans left on disk, GB (scaled per tower, or per byte of tower text)* | "
            f"*{pr['olean_gb_est_per_tower']:,.0f} to {pr['olean_gb_est']:,.0f}* |"]
    projection_t = "\n".join(prow)

    wrows = ["| concurrent processes | wall hours, one core per process | "
             f"wall hours at {p['site']['cores_per_process']:.2f} cores per process "
             f"(capped at {VCPUS} vCPU) |", "|---|---|---|"]
    for n, w in pr["wall_clock"].items():
        wrows.append(f"| {n} | {w['wall_h_one_core_each']:,.1f} | "
                     f"{w['wall_h_measured_cores_per_process']:,.1f} |")
    wall = "\n".join(wrows)

    names = {"in_situ_per_byte": "in-situ shard CPU per source byte",
             "in_situ_per_tower": "in-situ shard CPU per tower, flat in the prime",
             "fit_towers_and_bytes": "least-squares fit, per tower plus per byte, over "
                                     "`scripts/68` towers and the shards",
             "j1_shard_per_byte": "`lean -j1` shard CPU per source byte, one core per "
                                  "process"}
    srow = ["| tower cost model | tower core-hours | total core-hours | wall hours at 16 "
            "| wall hours at 24 |", "|---|---|---|---|---|"]
    for name, m in p["projection_models"].items():
        label = names[name] + (" (the request uses this one)"
                               if name == p["projection"]["model"] else "")
        srow.append(f"| {label} | {m['core_hours']['tower']:,.1f} | "
                    f"{m['total_core_hours']:,.1f} | "
                    f"{m['wall_clock']['16']['wall_h_measured_cores_per_process']:,.1f} | "
                    f"{m['wall_clock']['24']['wall_h_measured_cores_per_process']:,.1f} |")
    sensitivity = "\n".join(srow)

    threads = ""
    j = p.get("shard_j1")
    if j:
        threads = "\n".join([
            f"| `{j['module']}` ({j['towers']} towers) | default threads (`scripts/72`) "
            "| `lean -j1` |", "|---|---|---|",
            f"| CPU-s | {j['default_threads_cpu_s']:,.1f} | "
            + ", ".join(f"{c:,.1f}" for c in j["cpu_s"]) + " |",
            f"| wall s | {j['default_threads_wall_s']:,.1f} | "
            + ", ".join(f"{w:,.1f}" for w in j["wall_s"]) + " |",
            f"| CPU-s net of the module's import probe | {j['default_threads_net_cpu_s']:,.1f} "
            f"| {j['net_cpu_s']:,.1f} |",
            f"| net CPU-s per tower atom | "
            f"{j['default_threads_net_cpu_s'] / (j['towers'] * TOWER_MULS):.3f} | "
            f"{j['cpu_s_per_tower_atom']:.3f} |",
            f"| peak RSS GiB (anonymous) | {j['default_threads_peak_rss_gib']:.2f} "
            f"({_f(j['default_threads_rss_anon_gib'])}) | "
            + ", ".join(f"{r:.2f} ({a:.2f})" for r, a in zip(j["peak_rss_gib"],
                                                            j["rss_anon_gib"])) + " |"])

    pm = p["projection_models"]
    totals = [m["total_core_hours"] for m in pm.values()]
    w = pr["wall_clock"]
    box = p["setup"]["box"]
    hl = [
        f"- **Projected CPU for the 215 sites: {pr['total_core_hours']:,.0f} core-hours** "
        f"(the larger of the two in-situ tower models; {min(totals):,.0f} to "
        f"{max(totals):,.0f} across the {len(totals)} models in `PILOT.md` section 4), "
        f"against the "
        f"{a['v433_core_hours']:,.1f} atom-only core-hours `scripts/67` records.",
        f"- **Wall clock on this box, if it were free:** "
        f"{w['16']['wall_h_measured_cores_per_process']:,.0f} hours at 16 processes and "
        f"{w['24']['wall_h_measured_cores_per_process']:,.0f} hours at 24, at the "
        f"{p['site']['cores_per_process']:.2f} cores per process the pilot site used, capped "
        f"at {VCPUS} vCPU; {w['16']['wall_h_one_core_each']:,.0f} and "
        f"{w['24']['wall_h_one_core_each']:,.0f} hours if each process holds one core.",
        f"- **Memory per process:** peak RSS {p['site']['max_peak_rss_gib']:.1f} GiB, of which "
        f"at most {p['site']['max_rss_anon_gib']:.2f} GiB anonymous; the rest is Mathlib's "
        f"oleans mapped from the page cache and shared between processes.",
        f"- **Disk:** {pr['olean_gb_est_per_tower']:,.0f} to {pr['olean_gb_est']:,.0f} GB of "
        f"oleans for the 215 sites (the pilot site's "
        f"{p['site']['olean_bytes_total'] / 1e6:,.0f} MB scaled per tower or per byte of "
        f"tower text), against {box['disk_free_gb']:,.0f} GB free on this box's disk at "
        f"{box['disk_read_at']}.",
        f"- **The assembly's import, untested:** importing the pilot site's other oleans "
        f"raised a probe's peak RSS by {p['import_model']['rss_bytes_per_imported_olean_byte']:.2f}"
        f" bytes per olean byte; at that ratio one process importing every site's oleans "
        f"would map {p['import_model']['rss_bytes_per_imported_olean_byte'] * pr['olean_gb_est_per_tower']:,.0f}"
        f" to {p['import_model']['rss_bytes_per_imported_olean_byte'] * pr['olean_gb_est']:,.0f} GB, "
        f"against this box's {box['mem_total_gib']:,.0f} GiB.",
    ]
    headline = "\n".join(hl)

    lv = []
    tj, tl, j = p["tower"].get("tower-j1"), p["tower"].get("tower-Dlinter.all=false"), \
        p.get("shard_j1")
    if tj and tj.get("cpu_s_per_atom"):
        lv.append(f"- **`lean -j1`:** the `scripts/68` tower cost {tj['cpu_s_per_atom']:.2f} "
                  f"CPU-s per atom against {t2['cpu_s_per_atom']:.2f} under default threads.")
    if j:
        lv.append(f"- **`lean -j1` on `{j['module']}`:** {j['net_cpu_s']:,.0f} CPU-s net of "
                  f"import against {j['default_threads_net_cpu_s']:,.0f} under default threads "
                  f"in the site compile.")
    if tl and tl.get("cpu_s_per_atom"):
        lv.append(f"- **Linters off (`-Dlinter.all=false`):** the `scripts/68` tower cost "
                  f"{tl['cpu_s_per_atom']:.2f} CPU-s per atom against "
                  f"{t2['cpu_s_per_atom']:.2f} with them on.")
    levers = "\n".join("   " + x for x in lv)       # nested under the memo's item 3

    rrows = ["| module | same source | first attempt CPU s (wall s) | this run CPU s "
             "(wall s) | CPU ratio | wall ratio |", "|---|---|---|---|---|---|"]
    for r in p["first_attempt"]:
        rrows.append(f"| `{r['path']}` | {'yes' if r['same_source'] else 'NO'} | "
                     f"{r['first_cpu_s']:,.1f} "
                     f"({r['first_wall_s']:,.1f}) | {r['cpu_s']:,.1f} ({r['wall_s']:,.1f}) | "
                     f"{r['cpu_ratio']:.2f} | {r['wall_ratio']:.2f} |")
    replay = "\n".join(rrows)

    s = p["setup"]
    mathlib = next(q for q in s["packages"] if q["name"] == "mathlib")
    srows = ["| item | value |", "|---|---|",
             f"| box | `{s['box']['hostname']}`: {s['box']['vcpus']} vCPU "
             f"({s['box']['cpu_model']}), {s['box']['mem_total_gib']} GiB, no swap, shared |",
             f"| Lean | `{s['lean_toolchain']}`; {s['lean_version']} |",
             f"| Mathlib | `{mathlib['manifest_rev'][:12]}` (`lean/lake-manifest.json`) |",
             f"| Lake packages | {len(s['packages'])}; every package's git toplevel is the "
             f"package itself: {'yes' if s['all_packages_own_toplevel'] else 'NO'}; every "
             f"HEAD equals its manifest revision: "
             f"{'yes' if s['all_heads_match_manifest'] else 'NO'} |",
             f"| `ZetaLean` modules built | {len(s['zetalean_built'])}: "
             + ", ".join(f"`{m}`" for m in s["zetalean_built"]) + " |"]
    setup = "\n".join(srows)

    gen = p["site"]["generate"]
    comp_run = p["site"]["compile"]
    lines = ["```bash", "# from the worktree root; Lean from elan",
             'export PATH="$HOME/.elan/bin:$PATH"',
             f"cd {gen['cwd']}",
             " ".join(gen["argv"]),
             f"cd {comp_run['cwd']}",
             " ".join(comp_run["argv"]), "```"]
    commands = "\n".join(lines)
    return {"cost": cost, "modules": modules, "faults": faults, "centre": centre,
            "projection": projection_t, "wall": wall, "commands": commands, "setup": setup,
            "sensitivity": sensitivity, "threads": threads, "replay": replay,
            "headline": headline, "levers": levers}


def main(argv: list[str] | None = None) -> None:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--work", default=str(DEFAULT_WORK))
    ap.add_argument("--site", default="B_right_06")
    ap.add_argument("--out", default=str(HERE / "pilot.json"))
    args = ap.parse_args(argv)
    work = Path(args.work)
    rs = runs(work)

    towers = {}
    for r in rs:
        if r["tag"] == "tower" and r["returncode"] == 0:
            towers.setdefault(r["prime"], None)
    tower_units = {str(p): unit(rs, "tower", "tower-baseline", TOWER_MULS, prime=p)
                   for p in sorted(towers)}
    variants = sorted({r["tag"] for r in rs if r["tag"].startswith("tower-")
                       and not r["tag"].startswith("tower-baseline")})
    for tag in variants:
        tower_units[tag] = unit(rs, tag, "tower-baseline" + tag[len("tower"):], TOWER_MULS)
    # composite files of several sizes: the largest is the rate used, the others are kept;
    # ten atoms cost a few CPU-s against an import of 10 to 14 CPU-s, too little signal
    sizes = sorted({r["atoms"] for r in rs if r["tag"] == "composite" and r["returncode"] == 0})
    comp_units = {str(n): unit(rs, "composite", "composite-baseline", n, atoms=n)
                  for n in sizes}
    comp = comp_units[str(max(sizes))]
    site = site_section(rs, work, args.site)

    # tower cost = a * towers + b * text bytes, least squares over the scripts/68 pilots
    # (one tower each) and the site's prime shards (several towers each)
    pts = []
    for p, u in tower_units.items():
        if p.isdigit() and "mean_net_cpu_s" in u:
            r = next(x for x in rs if x["tag"] == "tower" and x["prime"] == int(p))
            pts.append((1, Path(r["file"]).stat().st_size, u["mean_net_cpu_s"],
                        f"scripts/68 tower p={p}"))
    for m in site["modules"]:
        if m["kind"] == "primes-shard" and m.get("net_cpu_s") is not None:
            pts.append((m["towers"], m["bytes"], m["net_cpu_s"], m["path"]))
    s_tt = sum(t * t for t, _, _, _ in pts)
    s_tb = sum(t * b for t, b, _, _ in pts)
    s_bb = sum(b * b for _, b, _, _ in pts)
    s_tc = sum(t * c for t, _, c, _ in pts)
    s_bc = sum(b * c for _, b, c, _ in pts)
    det = s_tt * s_bb - s_tb * s_tb
    if len(pts) >= 2 and det:
        a_fit = (s_tc * s_bb - s_tb * s_bc) / det
        b_fit = (s_tt * s_bc - s_tb * s_tc) / det
        resid = [round(c / (a_fit * t + b_fit * b), 3) for t, b, c, _ in pts]
    else:                       # too few measured units yet (a partial run)
        a_fit = b_fit = None
        resid = [None] * len(pts)

    probes = {m["kind"]: m for m in site["modules"]}
    base_imp = probes["base"]["import_probe_cpu_s"]
    root_imp = probes["root"]["import_probe_cpu_s"]
    site_oleans = sum(m["olean_bytes"] for m in site["modules"]
                      if m["kind"] != "root" and m["olean_bytes"])
    # CPU of importing the site's oleans on top of the Base imports; the difference of two
    # noisy medians can come out negative, and is then priced at zero
    probe_rss = {}
    for r in rs:
        if r["tag"] == "import-probe" and r["returncode"] == 0:
            probe_rss.setdefault(r["module"], []).append(r["peak_rss_bytes"])
    base_rss = st.median(probe_rss[probes["base"]["path"]])
    root_rss = st.median(probe_rss[probes["root"]["path"]])
    import_model = {"base_cpu_s": base_imp,
                    "cpu_s_per_olean_byte": max(0.0, (root_imp - base_imp) / site_oleans),
                    "root_minus_base_cpu_s": round(root_imp - base_imp, 3),
                    "site_olean_bytes_imported_by_root": site_oleans,
                    "base_probe_peak_rss_bytes": base_rss,
                    "root_probe_peak_rss_bytes": root_rss,
                    "rss_bytes_per_imported_olean_byte": round((root_rss - base_rss)
                                                               / site_oleans, 4)}

    max_K = max(s["K"] for _, s in plan_sites())
    tb = tower_bytes_table(5 * max_K + 4)

    # Tower cost models, both from the site's prime shards, CPU net of their import probes:
    # per source byte (times each plan tower's text bytes; a tower's text grows with its
    # prime, about 170 KB at p = 2 and 390 KB at p = 89) and flat per tower.  The shards do
    # not support either over the other (RUNS.md, decision of 22:07 UTC), so both are
    # priced and the primary projection is the larger.  The two-parameter fit (which mixes
    # scripts/68's one-tower files with the shards) and the -j1 shard are sensitivity rows.
    shards = [m for m in site["modules"]
              if m["kind"] == "primes-shard" and m.get("net_cpu_s") is not None]
    shard_net = sum(m["net_cpu_s"] for m in shards)
    r_byte = shard_net / sum(m["bytes"] for m in shards)
    r_tower = shard_net / sum(m["towers"] for m in shards)
    cpp = site["cores_per_process"]
    models = {"in_situ_per_byte": ((0.0, r_byte), cpp),
              "in_situ_per_tower": ((r_tower, 0.0), cpp),
              **({"fit_towers_and_bytes": ((a_fit, b_fit), cpp)} if a_fit is not None
                 else {})}
    j1 = [r for r in rs if r["tag"] == "shard-j1" and r["returncode"] == 0]
    shard_j1 = None
    if j1:
        mod = next(m for m in site["modules"] if m["path"] == j1[0]["module"])
        cpu_j1 = st.median(cpu(r) for r in j1)
        shard_j1 = {"module": mod["path"], "bytes": mod["bytes"], "towers": mod["towers"],
                    "runs": len(j1), "cpu_s": [round(cpu(r), 3) for r in j1],
                    "wall_s": [r["wall"] for r in j1],
                    "peak_rss_gib": [round(r["peak_rss_bytes"] / 2**30, 2) for r in j1],
                    "rss_anon_gib": [round(r["box"].get("lean_max_rss_anon_bytes", 0)
                                           / 2**30, 2) for r in j1],
                    "load_at_start": [r["load_at_start"] for r in j1],
                    "import_probe_cpu_s": mod["import_probe_cpu_s"],
                    "net_cpu_s": round(cpu_j1 - mod["import_probe_cpu_s"], 3),
                    "default_threads_cpu_s": mod["cpu_s"],
                    "default_threads_wall_s": mod["wall_s"],
                    "default_threads_net_cpu_s": mod["net_cpu_s"],
                    "default_threads_peak_rss_gib": mod["peak_rss_gib"],
                    "default_threads_rss_anon_gib": mod["rss_anon_gib"]}
        shard_j1["cpu_s_per_tower_atom"] = round(shard_j1["net_cpu_s"]
                                                 / (mod["towers"] * TOWER_MULS), 4)
        models["j1_shard_per_byte"] = ((0.0, shard_j1["net_cpu_s"] / mod["bytes"]), 1.0)
    projections = {name: projection(tb, site, ab, import_model, c)
                   for name, (ab, c) in models.items()}
    primary = max(("in_situ_per_byte", "in_situ_per_tower"),
                  key=lambda k: projections[k]["total_core_hours"])
    proj = {**projections[primary], "model": primary}

    budget = _load("rung3_ball_atom_budget_for_report", "67_rung3_ball_atom_budget.py")
    counts = budget.plan_atom_counts()
    t68 = tower_units["2"]["cpu_s_per_atom"]
    atom_only = {
        "tower_atoms": counts["tower_atoms"], "other_atoms": counts["other_atoms"],
        "v433_core_hours": V433["atom_only_core_hours"],
        "scripts68_p2_rate_core_hours": round(budget.serial_core_hours(
            counts["tower_atoms"], counts["other_atoms"], tower_rate=t68,
            other_rate=comp["cpu_s_per_atom"]), 1),
        "in_situ_rate_core_hours": round(budget.serial_core_hours(
            counts["tower_atoms"], counts["other_atoms"],
            tower_rate=site["in_situ"]["cpu_s_per_tower_atom"],
            other_rate=site["in_situ"]["cpu_s_per_composite"]), 1),
    }
    pilot = {
        "hunt": 145, "lane": "rung3-pilot", "date": "2026-10-21",
        "v433_record": V433,
        "tower": tower_units, "composite": comp, "composite_by_atoms": comp_units,
        "site": site,
        "tower_cost_fit": {"cpu_s_per_tower": a_fit, "cpu_s_per_text_byte": b_fit,
                           "points": [
            {"towers": t, "bytes": b, "net_cpu_s": c, "unit": n, "ratio_to_fit": q}
            for (t, b, c, n), q in zip(pts, resid)]},
        "import_model": import_model,
        "atom_only": atom_only, "projection": proj,
        "projection_models": {name: {k: v for k, v in pr.items() if k != "sites"}
                              for name, pr in projections.items()},
        "shard_j1": shard_j1,
        "tower_bytes_by_prime": {k: {str(p): v for p, v in d.items()} for k, d in tb.items()},
    }
    for key in ("axioms", "mirror", "faults", "centre_eps", "box", "setup"):
        pilot.setdefault(key, None)
    pilot["axioms"] = next((r for r in reversed(rs) if r["tag"] == "axioms"), None)
    pilot["mirror"] = next((r for r in reversed(rs) if r["tag"] == "mirror"), None)
    pilot["faults"] = [r for r in rs if r["tag"].startswith("fault-")
                       and r["tag"].endswith("-outcome")]
    pilot["fault_runs"] = [r for r in rs if r["tag"].startswith("fault-")
                           and not r["tag"].endswith("-outcome")]
    pilot["centre_eps"] = [r for r in rs if r["tag"].startswith("centre-eps-")]
    pilot["shard_runs"] = [r for r in rs if r["tag"].startswith("shard-")]
    pilot["setup"] = setup_section()
    pilot["launch_audit"] = launch_audit([FIRST_ATTEMPT, work])
    pilot["first_attempt"] = first_attempt_modules(site)
    pilot["generator_replay"] = generator_replay(args.site, work)
    Path(args.out).write_text(json.dumps(pilot, indent=1) + "\n")
    print(f"wrote {args.out}")


if __name__ == "__main__":
    main()

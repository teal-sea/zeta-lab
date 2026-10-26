#!/usr/bin/env python3
"""Hunt #145, 2026-10-26: the pilot site B_right_06 end to end under `--tower whole`.

Generates the site with `scripts/60 --arith ball --shard --tower whole --only B_right_06`,
compiles it with `scripts/72 --jobs 1 --module-jobs 1` (one process, `nice -n 10`, the
load and memory gate before each Lean run), then:

* `faults`: two prime towers with one literal one unit of 2^-64 off (Prime_2's radius
  low, Prime_89's real centre high), each recompiled alone against the clean site's
  `Base`; each must be refused at that tower's `ev_whole`;
* `imports`: an import-only probe of the support modules and one of the site root, for
  the assembly's resident-memory ratio;
* `summarize`: the `whole_site` section of pilot.json, from the run log and scripts/72's
  site record alone.

    .venv/bin/python hunts/rung3_ball_production/whole_pilot.py site|faults|imports|summarize
"""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import os
import re
import subprocess
import sys
import time
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
LEAN = ROOT / "lean"
PY = sys.executable
SITE, ROOTMOD = "B_right_06", "CB_right_06"
DEFAULT_WORK = Path(os.environ.get(
    "RUNG3_WHOLE_WORK", os.path.expanduser("~/.cache/zeta-lab/rung3-ball-production-whole")))


def _decide_pilot():
    spec = importlib.util.spec_from_file_location("rung3_decide_pilot", HERE / "decide_pilot.py")
    assert spec is not None and spec.loader is not None
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


dp = _decide_pilot()


def _env() -> dict:
    return dict(os.environ, PATH=f"{os.path.expanduser('~/.elan/bin')}:{os.environ['PATH']}")


def _log(work: Path, rec: dict) -> None:
    with (work / "runs.jsonl").open("a") as f:
        f.write(json.dumps(rec) + "\n")
    print({k: rec.get(k) for k in ("tag", "returncode", "cpu_s", "wall", "maxrss_kb",
                                   "load1_before")}, flush=True)


def _lean(work: Path, tag: str, src: Path, lean_path: list[Path], timeout: int = 900) -> dict:
    load, mem, waited = dp._gate()
    lp = ":".join(str(p) for p in lean_path)
    cmd = ["nice", "-n", "10", "/usr/bin/time", "-v", "timeout", str(timeout), "lake", "env",
           "sh", "-c", f'LEAN_PATH={lp}:"$LEAN_PATH" exec lean "{src}"']
    t0 = time.time()
    p = subprocess.run(cmd, cwd=LEAN, env=_env(), capture_output=True, text=True)
    rec = {"tag": tag, "file": src.name, "returncode": p.returncode,
           "load1_before": load, "memavail_gib_before": round(mem, 1),
           "gate_wait_s": round(waited, 1), "started_unix": round(t0, 1)}
    for k, pat in dp._TIME.items():
        m = re.search(pat, p.stderr)
        rec[k] = (dp._wall(m.group(1)) if k == "wall" else float(m.group(1))) if m else None
    rec["cpu_s"] = round(rec["user"] + rec["sys"], 2) if rec["user"] is not None else None
    text = src.read_text()
    rec["errors"] = dp._errors(p.stdout + p.stderr, text)
    for e in rec["errors"]:
        stack: list[str] = []
        for l in text.split("\n")[:e["line"]]:
            if l.startswith("namespace "):
                stack.append(l.split()[1])
            elif l.startswith("end ") and stack and l.split()[1] == stack[-1]:
                stack.pop()
        e["namespace"] = stack[-1] if stack else None
    _log(work, rec)
    return rec


def cmd_site(work: Path) -> None:
    gen, out = work / "site" / "gen", work / "site" / "out"
    gen.mkdir(parents=True, exist_ok=True)
    t0 = time.time()
    g = subprocess.run([PY, "scripts/60_rung3_generate.py", "lean/cert/rung3_plan2.json",
                        str(gen), "--arith", "ball", "--shard", "--tower", "whole",
                        "--only", SITE], cwd=ROOT, capture_output=True, text=True)
    _log(work, {"tag": "generate", "returncode": g.returncode, "wall": round(time.time() - t0, 1),
                "stdout_tail": g.stdout[-300:]})
    if g.returncode:
        sys.exit(g.stderr)
    load, mem, waited = dp._gate()
    t0 = time.time()
    c = subprocess.run(["nice", "-n", "10", PY, "scripts/72_rung3_ball_compile.py",
                        "--lean-project", "lean", "--output-root", str(out), "--jobs", "1",
                        "--module-jobs", "1", str(gen / f"{ROOTMOD}.manifest.json")],
                       cwd=ROOT, env=_env(), capture_output=True, text=True)
    _log(work, {"tag": "compile", "returncode": c.returncode, "wall": round(time.time() - t0, 1),
                "load1_before": load, "memavail_gib_before": round(mem, 1),
                "stdout_tail": c.stdout[-600:], "stderr_tail": c.stderr[-600:]})


def _fault_text(gen: Path, prime: int, field: str, delta: F) -> str:
    text = (gen / ROOTMOD / "Primes.lean").read_text()
    ns = f"namespace Prime_{SITE}_{prime}\n"
    start = text.index(ns)
    m = re.compile(r"def Sq_10 : ComplexBall := \(⟨\((-?\d+)(?:/(\d+))? : ℚ\), "
                   r"\((-?\d+)(?:/(\d+))? : ℚ\), \((-?\d+)(?:/(\d+))? : ℚ\)⟩ : ComplexBall\)")
    hit = m.search(text, start)
    assert hit and hit.start() < text.index(f"end Prime_{SITE}_{prime}", start)
    vals = [F(int(hit.group(i)), int(hit.group(i + 1) or 1)) for i in (1, 3, 5)]
    idx = {"cre": 0, "cim": 1, "rad": 2}[field]
    vals[idx] += delta
    back = _decide_pilot().q
    new = f"def Sq_10 : ComplexBall := (⟨{back(vals[0])}, {back(vals[1])}, {back(vals[2])}⟩ : ComplexBall)"
    return text[:hit.start()] + new + text[hit.end():]


FAULTS = {"p2-rad-low": (2, "rad", F(-1, 2**64)), "p89-cre-high": (89, "cre", F(1, 2**64))}


def cmd_faults(work: Path) -> None:
    gen = work / "site" / "gen"
    for tag, (prime, field, delta) in FAULTS.items():
        d = work / "faults" / tag
        d.mkdir(parents=True, exist_ok=True)
        src = d / "FaultPrimes.lean"
        src.write_text(_fault_text(gen, prime, field, delta))
        _lean(work, f"fault:{tag}", src, [d, gen])


def cmd_imports(work: Path) -> None:
    gen = work / "site" / "gen"
    d = work / "imports"
    d.mkdir(parents=True, exist_ok=True)
    (d / "ImportBase.lean").write_text("import ZetaLean.BallCertSupport\n")
    (d / "ImportRoot.lean").write_text(f"import {ROOTMOD}\n")
    for _ in range(2):
        _lean(work, "import:base", d / "ImportBase.lean", [gen])
        _lean(work, "import:root", d / "ImportRoot.lean", [gen])


def _census(work: Path) -> list[dict]:
    seen: dict[str, dict] = {}
    for path in sorted(work.glob("census*.jsonl")):
        for line in path.read_text().splitlines():
            if line:
                rec = json.loads(line)
                seen.setdefault(rec["id"], rec)
    return list(seen.values())


def cmd_census(work: Path, part: int = 0, parts: int = 1) -> None:
    """Every plan-v2 site emitted in whole mode in memory (nothing written but the
    census): module count, source bytes and towers per site.  Emission also runs the
    generator's check that each whole-tower literal equals the staged chain's."""
    spec = importlib.util.spec_from_file_location("rung3_generate_census",
                                                  ROOT / "scripts" / "60_rung3_generate.py")
    assert spec is not None and spec.loader is not None
    gen = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(gen)
    plan = json.loads((LEAN / "cert" / "rung3_plan2.json").read_text())
    need = gen.cell_requirements(plan)
    sites = []
    c = dict(plan["centre"], id="centre", eps=plan["small"]["eps"])
    c["re_lo"] = c["re_hi"] = plan["small"]["cre"]
    c["im_lo"] = c["im_hi"] = plan["small"]["cim"]
    sites.append((c, "centre"))
    for g in plan["grid"]:
        g = dict(g)
        h = g["segment"] in ("bottom", "top")
        g["re_lo"] = g["re_hi"] = g["x"] if h else g["fixed"]
        g["im_lo"] = g["im_hi"] = g["fixed"] if h else g["x"]
        g["beta"], g["beta_need"] = None, str(need[g["id"]]) if g["id"] in need else None
        sites.append((g, "grid"))
    for b in plan["big"]["boxes"]:
        sites.append((dict(b, M=plan["M"]), "big"))
    path = work / f"census.{part}.jsonl"
    done = {r["id"] for r in _census(work)}
    for i, (site, kind) in enumerate(sites):
        if i % parts != part or site["id"] in done:
            continue
        t0 = time.time()
        files, stats = gen.emit_site_modules(site, kind, tower="whole")
        rec = {"id": site["id"], "kind": kind, "K": int(site["K"]),
               "towers": stats["prime_towers"], "modules": len(files),
               "source_bytes": sum(len(t.encode()) for _, t in files),
               "prime_source_bytes": sum(len(t.encode()) for r, t in files
                                         if "/Primes" in r),
               "python_s": round(time.time() - t0, 1)}
        with path.open("a") as f:
            f.write(json.dumps(rec) + "\n")
        print(rec, flush=True)


def cmd_names(work: Path, part: int, parts: int) -> None:
    """Public declaration names of every site in whole mode, for the cross-site check."""
    spec = importlib.util.spec_from_file_location("rung3_generate_names",
                                                  ROOT / "scripts" / "60_rung3_generate.py")
    assert spec is not None and spec.loader is not None
    gen = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(gen)
    back = gen._ball_backend()
    plan = json.loads((LEAN / "cert" / "rung3_plan2.json").read_text())
    need = gen.cell_requirements(plan)
    sites = []
    c = dict(plan["centre"], id="centre", eps=plan["small"]["eps"])
    c["re_lo"] = c["re_hi"] = plan["small"]["cre"]
    c["im_lo"] = c["im_hi"] = plan["small"]["cim"]
    sites.append((c, "centre"))
    for g in plan["grid"]:
        g = dict(g)
        h = g["segment"] in ("bottom", "top")
        g["re_lo"] = g["re_hi"] = g["x"] if h else g["fixed"]
        g["im_lo"] = g["im_hi"] = g["fixed"] if h else g["x"]
        g["beta"], g["beta_need"] = None, str(need[g["id"]]) if g["id"] in need else None
        sites.append((g, "grid"))
    for b in plan["big"]["boxes"]:
        sites.append((dict(b, M=plan["M"]), "big"))
    d = work / "names"
    d.mkdir(parents=True, exist_ok=True)
    path = d / f"names.{part}.jsonl"
    done = {json.loads(l)["id"] for p in d.glob("names.*.jsonl")
            for l in p.read_text().splitlines() if l}
    for i, (site, kind) in enumerate(sites):
        if i % parts != part or site["id"] in done:
            continue
        files, stats = gen.emit_site_modules(site, kind, tower="whole")
        names = back.public_declarations(files)
        primes = sorted(int(n.split(".")[-2].rsplit("_", 1)[1]) for n in names
                        if n.endswith(".pilot_contains_cpow"))
        with path.open("a") as f:
            f.write(json.dumps({"id": site["id"], "names": names, "primes": primes}) + "\n")
        print(site["id"], len(names), len(primes), flush=True)


def namespace_census(work: Path) -> dict:
    """Across the 215 whole-mode sites: no public name repeats.  For the staged default,
    whose tower namespaces are Prime_<p>, the collisions the same towers would make."""
    from collections import Counter
    recs = {}
    for p in sorted((work / "names").glob("names.*.jsonl")):
        for l in p.read_text().splitlines():
            if l:
                r = json.loads(l)
                recs.setdefault(r["id"], r)
    names = Counter(n for r in recs.values() for n in r["names"])
    spec = importlib.util.spec_from_file_location("rung3_generate_staged",
                                                  ROOT / "scripts" / "60_rung3_generate.py")
    gen = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(gen)
    plan = json.loads((LEAN / "cert" / "rung3_plan2.json").read_text())
    site = dict(next(b for b in plan["big"]["boxes"] if b["id"] == SITE), M=plan["M"])
    staged = gen._ball_backend().public_declarations(gen.emit_site_modules(site, "big")[0])
    per_tower = Counter(n.split(".")[-2] for n in staged if ".Prime_" in n)
    k = set(per_tower.values())
    assert len(k) == 1, per_tower
    k = k.pop()
    sites_per_prime = Counter(p for r in recs.values() for p in r["primes"])
    return {"sites": len(recs), "whole_public_names": sum(names.values()),
            "whole_repeated_names": sum(c - 1 for c in names.values() if c > 1),
            "prime_towers": sum(sites_per_prime.values()),
            "distinct_primes": len(sites_per_prime),
            "staged_public_names_per_tower": k,
            "staged_repeated_names": k * sum(c - 1 for c in sites_per_prime.values()),
            "staged_distinct_colliding_names": k * sum(1 for c in sites_per_prime.values()
                                                       if c > 1),
            "staged_sites_sharing_prime_2": sites_per_prime[2]}


def _olean_bytes(out: Path) -> dict[str, int]:
    sizes: dict[str, int] = {}
    for p in sorted(out.rglob("*.olean*")):
        if p.is_file() and not p.is_symlink() and "checkpoints" not in p.parts:
            sizes[str(p.relative_to(out))] = p.stat().st_size
    return sizes


def summarize(work: Path, pilot: dict) -> dict:
    import statistics as st
    recs = [json.loads(l) for l in (work / "runs.jsonl").read_text().splitlines() if l]
    out = work / "site" / "out"
    site = json.loads((out / "results" / f"{ROOTMOD}.json").read_text())
    mods = [{"path": m["path"], "status": m["status"],
             "cpu_s": round(m["user"] + m["system"], 2), "wall_s": round(m["elapsed"], 2),
             "peak_rss_bytes": m["peak_rss_bytes"]} for m in site["modules"]]
    oleans = _olean_bytes(out)
    for m in mods:
        stem = m["path"].removesuffix(".lean")
        m["olean_bytes"] = sum(v for k, v in oleans.items() if k.split(".olean")[0] == stem)
    imp = {t: [r for r in recs if r["tag"] == t] for t in ("import:base", "import:root")}
    base_cpu = st.median(r["cpu_s"] for r in imp["import:base"])
    rss = {t: st.median(r["maxrss_kb"] * 1024 for r in v) for t, v in imp.items()}
    total_olean = sum(oleans.values())
    old = pilot["site"]
    faults = {r["tag"].split(":", 1)[1]: {"returncode": r["returncode"],
                                          "refused": sorted({f"{e['namespace']}.{e['decl']}"
                                                             for e in r["errors"]})}
              for r in recs if r["tag"].startswith("fault:")}
    gen_files = sorted((work / "site" / "gen").rglob("*.lean"))
    return {
        "date": "2026-10-26", "site": SITE, "tower": "whole", "status": site["status"],
        "modules": mods,
        "module_count": len(mods),
        "cpu_s_total": round(sum(m["cpu_s"] for m in mods), 1),
        "wall_s_total": round(sum(m["wall_s"] for m in mods), 1),
        "max_peak_rss_bytes": max(m["peak_rss_bytes"] for m in mods),
        "olean_bytes_total": total_olean,
        "import_cpu_s_median": round(base_cpu, 2),
        "sources": {str(p.relative_to(work / "site" / "gen")):
                    hashlib.sha256(p.read_bytes()).hexdigest() for p in gen_files},
        "source_bytes_total": sum(p.stat().st_size for p in gen_files),
        "faults": faults,
        "import_probe": {"base_peak_rss_bytes": rss["import:base"],
                         "root_peak_rss_bytes": rss["import:root"],
                         "rss_bytes_per_imported_olean_byte":
                             round((rss["import:root"] - rss["import:base"]) / total_olean, 3)},
        "staged_2026_10_21": {"module_count": len(old["modules"]),
                              "cpu_s_total": old["modules_cpu_s"],
                              "wall_s_total": old["modules_wall_s"],
                              "max_peak_rss_gib": old["max_peak_rss_gib"],
                              "olean_bytes_total": old["olean_bytes_total"],
                              "source_bytes_total": old["source_bytes_total"]},
    }


def reproject(ws: dict, pilot: dict, census: list[dict]) -> dict:
    """Production in whole mode from this pilot's in-situ rates and the census.

    CPU per site = modules x import + towers x tower rate + composites x composite rate
    + 4K nonzero terms x term rate + 5K series terms x root rate, every rate net of the
    import from the whole-mode B_right_06 modules.  Oleans two ways: scaled from the pilot
    site by towers, composites and K, or by source byte.  An extrapolation from one site.
    """
    K0 = pilot["site"]["K"]
    imp = ws["import_cpu_s_median"]
    m = {x["path"].split("/")[-1]: x for x in ws["modules"]}
    comps0 = pilot["site"]["in_situ"]["composites"]
    rates = {"import_cpu_s": imp,
             "tower_cpu_s": (m["Primes.lean"]["cpu_s"] - imp) / 23,
             "composite_cpu_s": (m["Composites.lean"]["cpu_s"] - imp) / comps0,
             "nonzero_term_cpu_s": (m["Terms.lean"]["cpu_s"] - imp) / (4 * K0),
             "root_cpu_s_per_series_term": (m["CB_right_06.lean"]["cpu_s"] - imp) / (5 * K0)}
    ol = {"base": m["Base.lean"]["olean_bytes"],
          "per_tower": m["Primes.lean"]["olean_bytes"] / 23,
          "per_composite": m["Composites.lean"]["olean_bytes"] / comps0,
          "per_K": (m["Terms.lean"]["olean_bytes"] + m["CB_right_06.lean"]["olean_bytes"]) / K0}
    per_src = ws["olean_bytes_total"] / ws["source_bytes_total"]
    comps = {r["id"]: r["composites"] for r in pilot["projection"]["sites"]}
    rows = []
    for c in census:
        K = c["K"]
        cpu = (c["modules"] * imp + c["towers"] * rates["tower_cpu_s"]
               + comps[c["id"]] * rates["composite_cpu_s"]
               + 4 * K * rates["nonzero_term_cpu_s"] + 5 * K * rates["root_cpu_s_per_series_term"])
        olean = (ol["base"] + c["towers"] * ol["per_tower"]
                 + comps[c["id"]] * ol["per_composite"] + K * ol["per_K"])
        rows.append({"id": c["id"], "cpu_s": round(cpu, 1), "olean_bytes": round(olean),
                     "olean_bytes_by_source": round(per_src * c["source_bytes"]),
                     "modules": c["modules"]})
    total_cpu_h = sum(r["cpu_s"] for r in rows) / 3600
    ob = sorted([sum(r["olean_bytes"] for r in rows), sum(r["olean_bytes_by_source"] for r in rows)])
    ratio = ws["import_probe"]["rss_bytes_per_imported_olean_byte"]
    big = max(rows, key=lambda r: r["cpu_s"])
    return {
        "sites": len(rows), "towers": sum(c["towers"] for c in census),
        "modules": sum(r["modules"] for r in rows),
        "source_gb": round(sum(c["source_bytes"] for c in census) / 1e9, 3),
        "rates": {k: round(v, 4) for k, v in rates.items()},
        "total_core_hours": round(total_cpu_h, 1),
        "olean_gb": [round(x / 1e9, 2) for x in ob],
        "assembly_import_rss_gb": [round(ratio * x / 1e9, 2) for x in ob],
        "assembly_base_rss_gb": round(ws["import_probe"]["base_peak_rss_bytes"] / 1e9, 2),
        "largest_site": big,
        "max_site_olean_gb": round(max(max(r["olean_bytes"], r["olean_bytes_by_source"])
                                       for r in rows) / 1e9, 3),
        "wall_h_32_cores": round(total_cpu_h / 32, 2),
        "staged_total_core_hours": pilot["projection"]["total_core_hours"],
        "staged_olean_gb": [pilot["projection"]["olean_gb_est_per_tower"],
                            pilot["projection"]["olean_gb_est"]],
        "rows": rows,
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("cmd", choices=["site", "faults", "imports", "census", "names",
                                    "names-summary", "summarize"])
    ap.add_argument("--work", default=str(DEFAULT_WORK))
    ap.add_argument("--part", type=int, default=0, help="census: this worker's share")
    ap.add_argument("--parts", type=int, default=1)
    args = ap.parse_args()
    work = Path(args.work)
    work.mkdir(parents=True, exist_ok=True)
    if args.cmd == "site":
        cmd_site(work)
    elif args.cmd == "faults":
        cmd_faults(work)
    elif args.cmd == "imports":
        cmd_imports(work)
    elif args.cmd == "census":
        cmd_census(work, args.part, args.parts)
    elif args.cmd == "names":
        cmd_names(work, args.part, args.parts)
    elif args.cmd == "names-summary":
        pj = HERE / "pilot.json"
        pilot = json.loads(pj.read_text())
        pilot["namespace_census"] = namespace_census(work)
        pj.write_text(json.dumps(pilot, indent=1) + "\n")
        print(json.dumps(pilot["namespace_census"], indent=1))
    else:
        pj = HERE / "pilot.json"
        pilot = json.loads(pj.read_text())
        pilot["whole_site"] = summarize(work, pilot)
        census = _census(work)
        if len(census) == 215:
            pilot["whole_projection"] = reproject(pilot["whole_site"], pilot, census)
        pj.write_text(json.dumps(pilot, indent=1) + "\n")
        print(json.dumps({k: v for k, v in pilot.get("whole_projection", {}).items()
                          if k != "rows"}, indent=1))


if __name__ == "__main__":
    main()

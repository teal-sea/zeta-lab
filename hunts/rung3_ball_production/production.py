#!/usr/bin/env python3
"""Hunt #145: the steps `.github/workflows/rung3-production.yml` runs, one subcommand each.

The workflow is triggered only by a push of `RUN_REQUEST.json` (this directory) to
`hunt/rung3-ball-production`. The request names the mode:

* `calibrate`: one job compiling `request["sites"]` (the centre, K = 361, the largest,
  and one small site) under `--tower whole`, one Lean process at a time;
* `full`: all 215 sites under `--tower whole`, assigned to `request["jobs"]` jobs by
  projected CPU (`whole_projection.rows` in pilot.json, longest first onto the lightest
  job), plus one planted-fault job that must be refused;
* `fault`: the planted-fault job alone (a re-run of the full run's fault job, which
  compiles no production site); the request names the full run it completes
  (`"completes_run"`), and `verdict --runs` pairs the two.

Subcommands (every one fails closed with a non-zero exit):

    plan       print the GitHub outputs `mode=` and `jobs=` for the request
    preflight  pinned toolchain, Mathlib revision, request shape, and the staged
               default's byte identity against the 2026-10-21 hashes
    toplevels  every Lake package under lean/.lake/packages is its own git toplevel
    sites      the site ids of one job, one per line
    generate   scripts/60 --arith ball --shard --tower whole --only <id> per site
    axioms     `#print axioms` of every site theorem; anything but the three standard
               axioms fails the job
    record     per-site CPU, wall, peak RSS and olean bytes from scripts/72's records
    fault      plant a one-unit radius fault in the fault site's Prime_2 tower
    refused    the fault compile must have failed, at that tower's `ev_whole`
    verdict    across all jobs' records: 215 sites ok, every audit clean, fault refused
    collect    (assembly machine) download each job's latest oleans artifact of a run,
               check its SHA-256 against GitHub's digest, unzip, delete the zip, and
               check that every site the job owns has a checkpointed root olean
    assemble   (assembly machine) emit and compile Support, Assembly, Separation, Strip and
               Final, one Lean process at a time under the MemAvailable guard, then print
               the axioms of every final declaration verbatim
    strip-faults  (assembly machine, after assemble) compile scratch copies of Strip.lean:
               the unchanged copy must compile and each planted fault in the strip
               condition must be refused at davenport_heilbronn_strip

`collect` and `assemble` take `--dest`, which may be any directory with room for about
16 GB of oleans: on-disk under ~/.cache on 2026-10-26 for the strip re-assembly, /dev/shm
for the first assembly the same day.
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
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
LEAN = ROOT / "lean"
REQUEST = HERE / "RUN_REQUEST.json"
TOOLCHAIN = "leanprover/lean4:v4.35.0-rc2"
MATHLIB = "065356127b1dc0016f66b7283ce0ce2c4055aa55"
STANDARD_AXIOMS = ["propext", "Classical.choice", "Quot.sound"]
PER_JOB_CPU_S_MAX = 4 * 3600          # projected (this box's rates) per job, at most 4 h
MAX_JOBS = 30
JOB_WALL_S_MAX = 4 * 3600             # a full-mode job, setup included, sized from the runner
WALL_MARGIN = 1.5                     # on the runner's CPU, bounding wall by CPU at one core
RUNNER_RSS_GB = 14.0                  # what a 16 GB runner leaves for concurrent Lean processes


def _load(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    assert spec is not None and spec.loader is not None
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def pilot() -> dict:
    return json.loads((HERE / "pilot.json").read_text())


def plan_sites() -> dict[str, str]:
    """id -> kind for every site of plan v2."""
    plan = json.loads((LEAN / "cert" / "rung3_plan2.json").read_text())
    out = {"centre": "centre"}
    out.update({g["id"]: "grid" for g in plan["grid"]})
    out.update({b["id"]: "big" for b in plan["big"]["boxes"]})
    return out


def theorem(sid: str, kind: str) -> str:
    return {"big": f"upper_{sid}", "grid": f"beta_{sid}", "centre": f"centre_lt_{sid}"}[kind]


def validate(req: dict) -> None:
    assert req.get("tower") == "whole", req
    assert req.get("toolchain") == TOOLCHAIN and req.get("mathlib") == MATHLIB, req
    assert req.get("plan") == "lean/cert/rung3_plan2.json", req
    known = plan_sites()
    if req["mode"] == "calibrate":
        assert req["jobs"] == 1 and req["lean_jobs"] == 1, req
        assert "centre" in req["sites"] and 2 <= len(req["sites"]) <= 3, req
        assert all(s in known for s in req["sites"]), req
    elif req["mode"] == "full":
        assert 2 <= req["jobs"] <= MAX_JOBS and 1 <= req["lean_jobs"] <= 2, req
        assert req["fault_site"] in known, req
        check_calibration(req)
    elif req["mode"] == "fault":
        assert req["fault_site"] in known and req["lean_jobs"] == 1, req
        assert isinstance(req.get("completes_run"), int) and isinstance(req.get("attempt"), int), req
    else:
        raise AssertionError(f"unknown mode {req['mode']!r}")


def calibration() -> dict:
    """The full run's sizing inputs, read off the recorded calibration run."""
    c = pilot()["calibration_runner"]
    assert c["conclusion"] == "success" and all(c["axioms_ok"].values()), c
    return {"run": c["run"], "cpu_scale": max(c["cpu_scale"].values()),
            "setup_s": c["setup_s"],
            "peak_rss_gb": round(max(v["peak_rss_bytes"] for v in c["sites"].values()) / 1e9, 2)}


def job_wall_bound_s(req: dict, ids: list[str]) -> float:
    cal = req["calibration"]
    return cal["setup_s"] + WALL_MARGIN * cal["cpu_scale"] * projected_cpu(ids)


def check_calibration(req: dict) -> None:
    """Fail closed unless the request carries the recorded calibration and every job
    fits: setup plus 1.5 x runner CPU under 4 h, and the concurrent peak RSS in 16 GB."""
    assert req.get("calibration") == calibration(), (req.get("calibration"), calibration())
    assert req["lean_jobs"] * req["calibration"]["peak_rss_gb"] <= RUNNER_RSS_GB, req
    for ids in assign(req["jobs"]):
        assert job_wall_bound_s(req, ids) <= JOB_WALL_S_MAX, ids


def assign(jobs: int) -> list[list[str]]:
    """Longest projected site first onto the lightest job; deterministic."""
    rows = sorted(pilot()["whole_projection"]["rows"], key=lambda r: (-r["cpu_s"], r["id"]))
    bins: list[tuple[float, int, list[str]]] = [(0.0, j, []) for j in range(jobs)]
    for r in rows:
        load, j, ids = min(bins)
        ids.append(r["id"])
        bins[bins.index((load, j, ids))] = (load + r["cpu_s"], j, ids)
    out = [ids for _, _, ids in sorted(bins, key=lambda b: b[1])]
    for ids in out:
        assert projected_cpu(ids) <= PER_JOB_CPU_S_MAX, ids
    return out


def projected_cpu(ids: list[str]) -> float:
    by = {r["id"]: r["cpu_s"] for r in pilot()["whole_projection"]["rows"]}
    return sum(by[i] for i in ids)


def job_sites(req: dict, job: int) -> list[str]:
    return list(req["sites"]) if req["mode"] == "calibrate" else assign(req["jobs"])[job]


# --------------------------------------------------------------------------- subcommands

def cmd_plan(req: dict) -> None:
    validate(req)
    if req["mode"] == "full":
        jobs = [str(j) for j in range(req["jobs"])] + ["fault"]
    else:
        jobs = {"calibrate": ["0"], "fault": ["fault"]}[req["mode"]]
    print("mode=" + req["mode"])
    print("jobs=" + json.dumps(jobs))
    print("lean_jobs=" + str(req["lean_jobs"]))


def cmd_preflight(req: dict) -> None:
    validate(req)
    assert (LEAN / "lean-toolchain").read_text().strip() == TOOLCHAIN
    manifest = json.loads((LEAN / "lake-manifest.json").read_text())
    rev = next(p["rev"] for p in manifest["packages"] if p["name"] == "mathlib")
    assert rev == MATHLIB, rev
    v = subprocess.run(["lean", "--version"], cwd=LEAN, capture_output=True, text=True)
    assert v.returncode == 0 and "version 4.35.0-rc2" in v.stdout, v.stdout + v.stderr
    gen60 = _load("rung3_generate_preflight", ROOT / "scripts" / "60_rung3_generate.py")
    plan = json.loads((LEAN / "cert" / "rung3_plan2.json").read_text())
    site = dict(next(b for b in plan["big"]["boxes"] if b["id"] == "B_right_06"), M=plan["M"])
    files, _ = gen60.emit_site_modules(site, "big")
    got = {rel: hashlib.sha256(t.encode()).hexdigest() for rel, t in files}
    assert got == pilot()["generator_replay"]["this_run"], "staged default is not byte-identical"
    print(f"preflight ok: {TOOLCHAIN}, mathlib {MATHLIB[:12]}, staged default byte-identical")


def cmd_toplevels() -> None:
    pkgs = sorted((LEAN / ".lake" / "packages").iterdir())
    assert pkgs, "no Lake packages"
    for p in pkgs:
        top = subprocess.run(["git", "-C", str(p), "rev-parse", "--show-toplevel"],
                             capture_output=True, text=True).stdout.strip()
        assert Path(top).resolve() == p.resolve(), f"{p.name}: git toplevel is {top}"
    print(f"{len(pkgs)} packages, each its own git toplevel")


def cmd_generate(req: dict, job: int, gen: Path) -> None:
    gen.mkdir(parents=True, exist_ok=True)
    for sid in job_sites(req, job):
        subprocess.run([sys.executable, "scripts/60_rung3_generate.py", req["plan"], str(gen),
                        "--arith", "ball", "--shard", "--tower", "whole", "--only", sid],
                       cwd=ROOT, check=True, stdout=subprocess.DEVNULL)
        print("generated", sid, flush=True)


def parse_axioms(text: str) -> dict[str, list[str]]:
    out = {}
    # a Lean name may end in primes (dh_zero_located'), so the quoted name runs to the
    # last quote before " depends"
    for name, body in re.findall(r"^'(.+?)' depends on axioms: \[(.*?)\]", text, re.S | re.M):
        out[name] = sorted(a.strip() for a in body.split(",") if a.strip())
    for name in re.findall(r"^'(.+?)' does not depend on any axioms", text, re.M):
        out[name] = []
    return out


def axioms_ok(ax: list[str] | None) -> bool:
    """Exactly the three standard axioms: no stub, no `sorryAx`, nothing missing."""
    return ax is not None and sorted(ax) == sorted(STANDARD_AXIOMS)


def cmd_axioms(req: dict, job: int, gen: Path, out: Path) -> None:
    kinds = plan_sites()
    d = out / "axioms"
    d.mkdir(parents=True, exist_ok=True)
    results, bad = {}, []
    for sid in job_sites(req, job):
        thm = f"ZetaLean.DH.Cert.{theorem(sid, kinds[sid])}"
        src = d / f"Axioms_{sid}.lean"
        src.write_text(f"import C{sid}\n#print axioms {thm}\n")
        p = subprocess.run(["lake", "env", "sh", "-c",
                            f'LEAN_PATH="{gen}:{out}:$LEAN_PATH" exec lean "{src}"'],
                           cwd=LEAN, capture_output=True, text=True)
        ax = parse_axioms(p.stdout).get(thm)
        ok = p.returncode == 0 and axioms_ok(ax)
        results[sid] = {"theorem": thm, "returncode": p.returncode, "axioms": ax, "ok": ok}
        if not ok:
            bad.append(sid)
            print(p.stdout[-2000:], p.stderr[-2000:])
        print(sid, "ok" if ok else "FAILED", ax, flush=True)
    (out / "axioms.json").write_text(json.dumps(results, indent=1) + "\n")
    if bad or not results:
        sys.exit(f"axiom audit failed for {bad or 'every site (none audited)'}")


def cmd_record(req: dict, job: int, out: Path) -> None:
    rec = {}
    for sid in job_sites(req, job):
        path = out / "results" / f"C{sid}.json"
        if not path.is_file():
            rec[sid] = {"status": "missing"}
            continue
        site = json.loads(path.read_text())
        oleans = sum(p.stat().st_size for p in (out / f"C{sid}").rglob("*.olean*")
                     if p.is_file()) if (out / f"C{sid}").is_dir() else 0
        root = out / f"C{sid}.olean"
        oleans += root.stat().st_size if root.is_file() else 0
        mods = site.get("modules", [])
        rec[sid] = {"status": site.get("status"), "modules": len(mods),
                    "cpu_s": round(sum((m.get("user") or 0) + (m.get("system") or 0)
                                       for m in mods), 1),
                    "wall_s": round(sum(m.get("elapsed") or 0 for m in mods), 1),
                    "peak_rss_bytes": max((m.get("peak_rss_bytes") or 0 for m in mods),
                                          default=0),
                    "olean_bytes": oleans,
                    "projected_cpu_s": projected_cpu([sid])}
    (out / "sites.json").write_text(json.dumps(rec, indent=1) + "\n")
    print(json.dumps(rec, indent=1))


def cmd_fault(req: dict, gen: Path) -> None:
    sid = req["fault_site"]
    cmd_generate({**req, "mode": "calibrate", "sites": [sid]}, 0, gen)
    path = gen / f"C{sid}" / "Primes.lean"
    text = path.read_text()
    ns = f"Prime_{sid}_2"                       # scripts/69 tower_namespace, whole mode
    start = text.index(f"namespace {ns}\n")
    pat = re.compile(r"def Sq_10 : ComplexBall := \(⟨(\([^⟩]*?\)), (\([^⟩]*?\)), "
                     r"\((-?\d+)(?:/(\d+))? : ℚ\)⟩ : ComplexBall\)")
    m = pat.search(text, start)
    assert m and m.start() < text.index(f"end {ns}", start), f"no {ns}.Sq_10"
    rad = F(int(m.group(3)), int(m.group(4) or 1)) - F(1, 2**64)
    new = (f"def Sq_10 : ComplexBall := (⟨{m.group(1)}, {m.group(2)}, "
           f"({rad.numerator}/{rad.denominator} : ℚ)⟩ : ComplexBall)")
    path.write_text(text[:m.start()] + new + text[m.end():])
    # scripts/72 checks each source's byte count against the manifest before compiling;
    # record the planted file's size so the kernel, not that check, meets the fault
    man_path = gen / f"C{sid}.manifest.json"
    man = json.loads(man_path.read_text())
    rel = f"C{sid}/Primes.lean"
    hits = [m for m in man["modules"] if m["path"] == rel]
    assert len(hits) == 1, rel
    hits[0]["bytes"] = len(path.read_bytes())
    man_path.write_text(json.dumps(man, indent=2) + "\n")
    print(f"planted: C{sid}/Primes.lean {ns}.Sq_10 radius one unit of 2^-64 low")


def error_decls(log: str, source: str, name: str) -> list[str]:
    """`Namespace.decl` enclosing each `error` Lean reported in the file `name`."""
    lines = source.split("\n")
    out = []
    for m in re.finditer(rf"{re.escape(name)}:(\d+):\d+: error", log):
        ln = int(m.group(1))
        decl, stack = None, []
        for i, line in enumerate(lines[:ln]):
            if line.startswith("namespace "):
                stack.append(line.split()[1])
            elif line.startswith("end ") and stack and line.split()[1] == stack[-1]:
                stack.pop()
            d = re.match(r"(?:private )?(?:lemma|theorem|def) ([\w.]+)", line)
            if d:
                decl = d.group(1)
        out.append(".".join(stack[-1:] + [decl or "?"]))
    return out


def cmd_refused(req: dict, gen: Path, out: Path, rc: int) -> None:
    sid = req["fault_site"]
    res = json.loads((out / "results" / f"C{sid}.json").read_text())
    failed = [m for m in res["modules"] if m.get("status") == "failed"]
    logs = "".join(Path(m["log"]).read_text(errors="ignore") for m in failed
                   if m.get("log") and Path(m["log"]).is_file())
    src = gen / f"C{sid}" / "Primes.lean"
    decls = error_decls(logs, src.read_text(), src.name)
    verdict = {"compile_returncode": rc, "site_status": res.get("status"),
               "failed_modules": [m["path"] for m in failed], "error_decls": decls,
               "refused_at_ev_whole": bool(decls) and decls[0] == f"Prime_{sid}_2.ev_whole"}
    (out / "fault.json").write_text(json.dumps(verdict, indent=1) + "\n")
    print(json.dumps(verdict, indent=1))
    ok = (rc != 0 and res.get("status") != "ok"
          and verdict["failed_modules"] == [f"C{sid}/Primes.lean"]
          and verdict["refused_at_ev_whole"])
    if not ok:
        sys.exit("the planted fault was NOT refused as expected: this run does not count")


def download_records(runs: list[int], records: Path, repo: str) -> None:
    """Each run's record artifacts into records/<run>/; later runs come later in rglob."""
    for run in runs:
        d = records / f"{run:012d}"
        d.mkdir(parents=True, exist_ok=True)
        subprocess.run(["gh", "run", "download", str(run), "--repo", repo,
                        "-p", "rung3-production-record-*", "-D", str(d)], check=True)


def cmd_verdict(req: dict, records: Path) -> None:
    sites, axioms, fault = {}, {}, None
    for p in sorted(records.rglob("sites.json")):
        sites.update(json.loads(p.read_text()))
    for p in sorted(records.rglob("axioms.json")):
        axioms.update(json.loads(p.read_text()))
    # sorted, so the latest run's record wins, as download_records lays them out
    # (review, 2026-10-30: an unsorted rglob picked whichever came last on disk)
    for p in sorted(records.rglob("fault.json")):
        fault = json.loads(p.read_text())
    want = {"full": set(plan_sites()), "fault": set()}.get(req["mode"]) \
        if req["mode"] in ("full", "fault") else set(req["sites"])
    ok_sites = {s for s, r in sites.items() if r.get("status") == "ok"}
    clean = {s for s, r in axioms.items() if r.get("ok")}
    summary = {"mode": req["mode"], "sites_wanted": len(want), "sites_ok": len(ok_sites & want),
               "axioms_clean": len(clean & want),
               "missing": sorted(want - ok_sites), "unclean": sorted(want - clean),
               "fault": fault,
               "cpu_core_hours": round(sum(r.get("cpu_s", 0) for r in sites.values()) / 3600, 2),
               "olean_gb": round(sum(r.get("olean_bytes", 0) for r in sites.values()) / 1e9, 3)}
    print(json.dumps(summary, indent=1))
    if os.environ.get("GITHUB_STEP_SUMMARY"):
        with open(os.environ["GITHUB_STEP_SUMMARY"], "a") as f:
            f.write("```json\n" + json.dumps(summary, indent=1) + "\n```\n")
    good = not summary["missing"] and not summary["unclean"]
    if req["mode"] in ("full", "fault"):
        good = good and bool(fault) and fault.get("refused_at_ev_whole") is True
    if not good:
        sys.exit("verdict: the run does not count")


def pick_artifacts(artifacts: list[dict], jobs: int) -> dict[int, dict]:
    """The latest attempt of each job's oleans artifact; every job must have one."""
    best: dict[int, dict] = {}
    for a in artifacts:
        m = re.fullmatch(r"rung3-production-job(\d+)-attempt(\d+)", a["name"])
        if not m or a.get("expired"):
            continue
        job, attempt = int(m.group(1)), int(m.group(2))
        key = (a.get("run_order", 0), attempt)
        if job not in best or key > (best[job].get("run_order", 0), best[job]["attempt"]):
            best[job] = {**a, "attempt": attempt}
    missing = sorted(set(range(jobs)) - set(best))
    assert not missing, f"no oleans artifact for jobs {missing}"
    return best


def cmd_collect(req: dict, runs: list[int], dest: Path, repo: str) -> None:
    """Oleans of one or more runs: for each job the latest attempt among the runs given
    (a later run's artifact of the same job wins, so pass the runs in order)."""
    import zipfile
    arts = []
    for order, run in enumerate(runs):
        listing = subprocess.run(
            ["gh", "api", "--paginate", f"repos/{repo}/actions/runs/{run}/artifacts",
             "--jq", ".artifacts[] | tojson"], check=True, capture_output=True, text=True)
        arts += [{**json.loads(line), "run_order": order}
                 for line in listing.stdout.splitlines() if line]
    jobs = req["jobs"] if req["mode"] == "full" else 1
    dest.mkdir(parents=True, exist_ok=True)
    log = []
    for job, a in sorted(pick_artifacts(arts, jobs).items()):
        zpath = dest / f"{a['name']}.zip"
        with zpath.open("wb") as f:
            subprocess.run(["gh", "api", f"repos/{repo}/actions/artifacts/{a['id']}/zip"],
                           check=True, stdout=f)
        digest = hashlib.sha256()
        with zpath.open("rb") as f:
            for chunk in iter(lambda: f.read(1 << 24), b""):
                digest.update(chunk)
        h = digest.hexdigest()
        assert a["digest"] == f"sha256:{h}", (a["name"], a["digest"], h)
        with zipfile.ZipFile(zpath) as z:
            z.extractall(dest)
        zpath.unlink()
        for sid in job_sites(req, job):
            assert (dest / "out" / f"C{sid}.olean").is_file(), f"C{sid}.olean missing"
            assert (dest / "out" / "checkpoints" / f"C{sid}" / f"C{sid}.lean.ok.json").is_file(), sid
        log.append({"job": job, "artifact": a["name"], "sha256": h, "bytes": a["size_in_bytes"]})
        print(log[-1], flush=True)
    (dest / "collected.json").write_text(json.dumps({"runs": runs, "artifacts": log}, indent=1) + "\n")


FINAL = ["big_bottom", "big_top", "big_left", "big_right", "big_frontier", "deriv_bound_small",
         "small_bottom", "small_top", "small_left", "small_right", "small_frontier",
         "centre_small", "dh_zero_located", "dh_zero_located'", "davenport_heilbronn",
         "dh_separation_of", "dh_separation_hundred"]
STRIP = ["davenport_heilbronn_strip"]      # Strip.lean, added after the first assembly
START_GIB, STOP_GIB = 45.0, 20.0


def mem_available_gib() -> float:
    for line in Path("/proc/meminfo").read_text().splitlines():
        if line.startswith("MemAvailable:"):
            return int(line.split()[1]) / 2**20
    raise RuntimeError("no MemAvailable")


def run_guarded(tag: str, lean_args: list[str], lean_path: list[Path], logdir: Path) -> dict:
    """One `lean` under nice, with LEAN_PATH; refuse to start below START_GIB or above
    load 64, and kill it if MemAvailable falls below STOP_GIB."""
    import time
    load = float(Path("/proc/loadavg").read_text().split()[0])
    mem = mem_available_gib()
    if mem < START_GIB or load > 64:
        sys.exit(f"{tag}: not starting (MemAvailable {mem:.1f} GiB, load {load})")
    lp = ":".join(str(x) for x in lean_path)
    tfile = logdir / f"{tag}.time"
    cmd = ["lake", "env", "sh", "-c",
           f'LEAN_PATH="{lp}:$LEAN_PATH" exec nice -n 10 /usr/bin/time -v -o "{tfile}" lean '
           + " ".join(f'"{a}"' for a in lean_args)]
    t0, low = time.time(), mem
    with (logdir / f"{tag}.log").open("w") as log:
        proc = subprocess.Popen(cmd, cwd=LEAN, stdout=log, stderr=subprocess.STDOUT)
        killed = False
        while proc.poll() is None:
            time.sleep(10)
            m = mem_available_gib()
            low = min(low, m)
            if m < STOP_GIB:
                proc.kill()
                killed = True
        rc = proc.wait()
    txt = tfile.read_text() if tfile.exists() else ""
    rss = re.search(r"Maximum resident set size \(kbytes\): (\d+)", txt)
    cpu = sum(float(x) for x in re.findall(r"(?:User|System) time \(seconds\): ([\d.]+)", txt))
    rec = {"tag": tag, "returncode": rc, "killed_by_guard": killed, "wall_s": round(time.time() - t0, 1),
           "cpu_s": round(cpu, 1), "peak_rss_bytes": int(rss.group(1)) * 1024 if rss else None,
           "mem_available_gib_start": round(mem, 1), "mem_available_gib_low": round(low, 1),
           "load_start": load}
    print(json.dumps(rec), flush=True)
    if killed:
        sys.exit(f"{tag}: stopped by the MemAvailable guard ({low:.1f} GiB)")
    return rec


def cmd_assemble(dest: Path, overlay: Path, rh100: Path) -> None:
    asm, out, logdir = dest / "asm", dest / "out", dest / "logs"
    logdir.mkdir(parents=True, exist_ok=True)
    subprocess.run([sys.executable, str(HERE / "assembly.py"), "--out", str(asm), "--check"],
                   check=True)
    hl = HERE / "lean"
    recs = [run_guarded("support", [f"--root={hl}", "-o", str(asm / "Rung3Assembly" / "Support.olean"),
                                    str(hl / "Rung3Assembly" / "Support.lean")], [asm], logdir)]
    if recs[-1]["returncode"]:          # review, 2026-10-30: a stale Support.olean went through
        sys.exit(f"Support.lean failed: see {logdir / 'support.log'}")
    lp = [overlay, asm, out, rh100]
    for name in ("Assembly", "Separation", "Strip", "Final"):
        recs.append(run_guarded(name.lower(), [f"--root={asm}", "-o",
                                               str(asm / "Rung3Assembly" / f"{name}.olean"),
                                               str(asm / "Rung3Assembly" / f"{name}.lean")],
                                lp, logdir))
        if recs[-1]["returncode"]:
            sys.exit(f"{name}.lean failed: see {logdir / (name.lower() + '.log')}")
    probe = asm / "PrintAxioms.lean"
    probe.write_text("import Rung3Assembly.Final\n" + "".join(
        f"#print axioms ZetaLean.DH.Rung3Assembly.Plan2.{n}\n" for n in FINAL + STRIP))
    recs.append(run_guarded("axioms", [str(probe)], lp, logdir))
    printed = (logdir / "axioms.log").read_text()
    found = parse_axioms(printed)
    verdict = {n: found.get(f"ZetaLean.DH.Rung3Assembly.Plan2.{n}") for n in FINAL + STRIP}
    (dest / "assemble.json").write_text(json.dumps({"runs": recs, "axioms": verdict,
                                                    "printed": printed}, indent=1) + "\n")
    bad = [n for n, ax in verdict.items() if not axioms_ok(ax)]
    print(printed)
    if bad:
        sys.exit(f"axioms other than the standard three, or missing, for {bad}")


def cmd_strip_faults(dest: Path, overlay: Path) -> None:
    """Scratch copies of the emitted Strip.lean (`assembly.strip_variants`), compiled
    against the assembled environment, never written over the real one: the control must
    compile, and each fault must be refused at `davenport_heilbronn_strip`."""
    asm, out, logdir, work = dest / "asm", dest / "out", dest / "logs", dest / "strip-faults"
    assert (asm / "Rung3Assembly" / "Strip.olean").is_file(), "run assemble first"
    work.mkdir(parents=True, exist_ok=True)
    emitter = _load("rung3_assembly_for_strip_faults", HERE / "assembly.py")
    plan = json.loads((LEAN / "cert" / "rung3_plan2.json").read_text())
    want = f"ZetaLean.DH.Rung3Assembly.Plan2.{STRIP[0]}"
    results, bad = {}, []
    for tag, text in emitter.strip_variants(plan).items():
        src = work / f"Strip_{tag.replace('-', '_')}.lean"
        src.write_text(text)
        rec = run_guarded(f"strip-{tag}", [str(src)], [overlay, asm, out], logdir)
        log = (logdir / f"strip-{tag}.log").read_text(errors="ignore")
        rec["refused_at"] = sorted(set(error_decls(log, text, src.name)))
        rec["sha256"] = hashlib.sha256(text.encode()).hexdigest()
        results[tag] = rec
        ok = (rec["returncode"] == 0 and not rec["refused_at"]) if tag == "control" else \
            (rec["returncode"] != 0 and rec["refused_at"] == [want])
        if not ok:
            bad.append(tag)
    (dest / "strip_faults.json").write_text(json.dumps(results, indent=1) + "\n")
    print(json.dumps({t: (r["returncode"], r["refused_at"]) for t, r in results.items()}))
    if bad:
        sys.exit(f"strip faults not as expected: {bad}")


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("cmd", choices=["plan", "preflight", "toplevels", "sites", "generate",
                                    "axioms", "record", "fault", "refused", "verdict",
                                    "collect", "assemble", "strip-faults"])
    ap.add_argument("--request", type=Path, default=REQUEST)
    ap.add_argument("--job", type=int, default=0)
    ap.add_argument("--gen", type=Path, default=Path("gen"))
    ap.add_argument("--out", type=Path, default=Path("out"))
    ap.add_argument("--rc", type=int, default=0, help="refused: the fault compile's exit")
    ap.add_argument("--records", type=Path, default=Path("records"))
    ap.add_argument("--run", type=int, nargs="+", help="collect: the workflow run id(s)")
    ap.add_argument("--runs", type=int, nargs="+",
                    help="verdict: download these runs' records first (sites from one, fault from another)")
    ap.add_argument("--dest", type=Path, help="collect: where the oleans land")
    ap.add_argument("--repo", default="teal-sea/zeta-lab")
    ap.add_argument("--overlay", type=Path, help="assemble: one ZetaLean/ for both trees")
    ap.add_argument("--rh100", type=Path, help="assemble: hunt #137's olean directory")
    args = ap.parse_args()
    if args.cmd == "toplevels":
        return cmd_toplevels()
    req = json.loads(args.request.read_text())
    gen, out = args.gen.resolve(), args.out.resolve()
    if args.cmd == "plan":
        cmd_plan(req)
    elif args.cmd == "preflight":
        cmd_preflight(req)
    elif args.cmd == "sites":
        print("\n".join(job_sites(req, args.job)))
    elif args.cmd == "generate":
        cmd_generate(req, args.job, gen)
    elif args.cmd == "axioms":
        cmd_axioms(req, args.job, gen, out)
    elif args.cmd == "record":
        cmd_record(req, args.job, out)
    elif args.cmd == "fault":
        cmd_fault(req, gen)
    elif args.cmd == "refused":
        cmd_refused(req, gen, out, args.rc)
    elif args.cmd == "collect":
        cmd_collect(req, args.run, args.dest.resolve(), args.repo)
    elif args.cmd == "assemble":
        cmd_assemble(args.dest.resolve(), args.overlay.resolve(), args.rh100.resolve())
    elif args.cmd == "strip-faults":
        cmd_strip_faults(args.dest.resolve(), args.overlay.resolve())
    else:
        if args.runs:
            download_records(args.runs, args.records.resolve(), args.repo)
        cmd_verdict(req, args.records.resolve())


if __name__ == "__main__":
    main()

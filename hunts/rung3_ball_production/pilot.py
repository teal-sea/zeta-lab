#!/usr/bin/env python3
"""Pilot harness for hunt #145: time the rung-3 ball units under Lean v4.35.0-rc2.

Every Lean process is launched through `run_timed`, which waits for the box to be quiet
(1-minute load average at most --max-load, MemAvailable at least --min-mem-gib), then
records argv, cwd, LEAN_PATH, wall, user and system CPU and peak RSS from `os.wait4`, and
the load average before and after.  One JSON object per run is appended to
WORK/runs.jsonl; `report` turns that log into the hunt's `pilot.json`.

Subcommands (run from anywhere; paths derive from this file):

  tower      emit one staged prime tower with scripts/68 and an import-only baseline,
             compile each --repeat times with `lake env lean FILE` from lean/
  composite  emit --atoms composite atoms with scripts/66 and compile them likewise
  site       generate one sharded site (scripts/60 --arith ball --shard --only SITE)
             and compile it with scripts/72 --jobs 1 --module-jobs 1
  shard      recompile one module of that site with `lean -jN` into a scratch olean
  imports    time an import-only probe carrying each site module's own imports
  axioms     print the axioms of the site theorem and its enclosure theorem
  fault      copy the compiled site, plant one named fault, recompile with scripts/72
  centre-eps generate the centre's sources (Python only), and compile probes of the
             centre theorem's final step with its emitted literals, at eps' and below it
  mirror     re-run the site through scripts/65's mirror route and compare
  report     write pilot.json from the run log

No subcommand compiles any site other than --site, and none compiles the centre.
"""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import os
import re
import shutil
import subprocess
import sys
import threading
import time
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
LEAN = ROOT / "lean"
PLAN_PATH = ROOT / "lean" / "cert" / "rung3_plan2.json"
# The second attempt's work directory; the first, interrupted at 18:08 UTC mid-site,
# is kept unchanged at rung3-ball-production-pilot (see RUNS.md).
DEFAULT_WORK = Path(os.environ.get("RUNG3_PILOT_WORK", os.path.expanduser("~/.cache/zeta-lab/rung3-ball-production-pilot-2")))
ELAN_BIN = Path.home() / ".elan" / "bin"
TOWER_MULS = 30


# --------------------------------------------------------------------------- box state

def loadavg() -> list[float]:
    return [round(x, 2) for x in os.getloadavg()]


def memavail_gib() -> float:
    with open("/proc/meminfo") as fh:
        for line in fh:
            if line.startswith("MemAvailable:"):
                return round(int(line.split()[1]) / 2**20, 2)
    raise RuntimeError("no MemAvailable in /proc/meminfo")


def wait_quiet(max_load: float, min_mem_gib: float, label: str) -> dict:
    """Block until the box is quiet enough; return what was waited for."""
    t0 = time.time()
    waited = 0
    while True:
        la, mem = loadavg(), memavail_gib()
        if la[0] <= max_load and mem >= min_mem_gib:
            return {"waited_s": round(time.time() - t0, 1), "load_at_start": la,
                    "memavail_gib_at_start": mem}
        if waited % 10 == 0:
            print(f"[wait {label}] load1={la[0]} memavail={mem} GiB", flush=True)
        waited += 1
        time.sleep(30)


def lean_env(extra_lean_path: list[str] | None = None) -> dict[str, str]:
    env = os.environ.copy()
    env["PATH"] = f"{ELAN_BIN}{os.pathsep}{env.get('PATH', '')}"
    if extra_lean_path:
        parts = list(extra_lean_path)
        if env.get("LEAN_PATH"):
            parts.append(env["LEAN_PATH"])
        env["LEAN_PATH"] = os.pathsep.join(parts)
    else:
        env.pop("LEAN_PATH", None)
    return env


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def _descendants(root_pid: int) -> list[int]:
    """Every live descendant of `root_pid`, from /proc."""
    children: dict[int, list[int]] = {}
    for d in os.listdir("/proc"):
        if not d.isdigit():
            continue
        try:
            with open(f"/proc/{d}/stat") as fh:
                rest = fh.read().rsplit(")", 1)[1].split()
            children.setdefault(int(rest[1]), []).append(int(d))
        except (OSError, IndexError, ValueError):
            continue
    out, todo = [], [root_pid]
    while todo:
        pid = todo.pop()
        for c in children.get(pid, []):
            out.append(c)
            todo.append(c)
    return out


def _lean_memory(root_pid: int) -> dict[int, tuple[int, int]]:
    """(RssAnon, RssFile) in bytes for each `lean` process under `root_pid`."""
    out = {}
    for pid in _descendants(root_pid):
        try:
            with open(f"/proc/{pid}/comm") as fh:
                if fh.read().strip() != "lean":
                    continue
            vals = {}
            with open(f"/proc/{pid}/status") as fh:
                for line in fh:
                    if line.startswith(("RssAnon:", "RssFile:")):
                        k, v = line.split(":", 1)
                        vals[k] = int(v.split()[0]) * 1024
            out[pid] = (vals.get("RssAnon", 0), vals.get("RssFile", 0))
        except OSError:
            continue
    return out


def _lean_source(pid: int) -> str | None:
    """The `.lean` argument of a lean process's command line, if any."""
    try:
        with open(f"/proc/{pid}/cmdline", "rb") as fh:
            argv = fh.read().decode(errors="replace").split("\0")
    except OSError:
        return None
    return next((a for a in argv if a.endswith(".lean")), None)


class Sampler:
    """Sample load, MemAvailable and the lean descendants' memory.

    The lean processes are read ten times per `period`; per process the largest
    anonymous and file-backed resident sizes seen are kept with its source file, so
    a site compile reports the anonymous memory of each module, not only of the run.
    """

    def __init__(self, period: float = 10.0):
        self.period, self.samples = period, []
        self.root_pid: int | None = None
        self.max_anon = self.max_file = self.max_total_anon = 0
        self.max_lean_procs = 0
        self.per_process: dict[int, dict] = {}
        self._stop = threading.Event()
        self._t = threading.Thread(target=self._run, daemon=True)

    def _run(self):
        t0 = time.time()
        n = 0
        while not self._stop.is_set():
            if self.root_pid is not None:
                mem = _lean_memory(self.root_pid)
                if mem:
                    self.max_anon = max(self.max_anon, max(a for a, _ in mem.values()))
                    self.max_file = max(self.max_file, max(f for _, f in mem.values()))
                    self.max_total_anon = max(self.max_total_anon,
                                              sum(a for a, _ in mem.values()))
                    self.max_lean_procs = max(self.max_lean_procs, len(mem))
                    for pid, (anon, fil) in mem.items():
                        rec = self.per_process.get(pid)
                        if rec is None:
                            rec = self.per_process[pid] = {
                                "source": _lean_source(pid), "max_rss_anon_bytes": 0,
                                "max_rss_file_bytes": 0}
                        rec["max_rss_anon_bytes"] = max(rec["max_rss_anon_bytes"], anon)
                        rec["max_rss_file_bytes"] = max(rec["max_rss_file_bytes"], fil)
            if n % 10 == 0:
                self.samples.append({"t": round(time.time() - t0, 1), "load": loadavg(),
                                     "memavail_gib": memavail_gib()})
            n += 1
            self._stop.wait(self.period / 10)

    def __enter__(self):
        self._t.start()
        return self

    def __exit__(self, *exc):
        self._stop.set()
        self._t.join()

    def summary(self) -> dict:
        if not self.samples:
            return {}
        l1 = [s["load"][0] for s in self.samples]
        mem = [s["memavail_gib"] for s in self.samples]
        return {"n": len(self.samples), "load1_min": min(l1), "load1_max": max(l1),
                "load1_mean": round(sum(l1) / len(l1), 2),
                "memavail_gib_min": min(mem),
                "lean_max_rss_anon_bytes": self.max_anon,
                "lean_max_rss_file_bytes": self.max_file,
                "lean_max_sum_rss_anon_bytes": self.max_total_anon,
                "lean_max_concurrent": self.max_lean_procs,
                "lean_processes": list(self.per_process.values())}

    def series(self) -> list[dict]:
        return list(self.samples)


def run_timed(args, argv, *, cwd: Path, env: dict, log: Path, tag: str,
              extra: dict | None = None, gate: bool = True) -> dict:
    gate_rec = (wait_quiet(args.max_load, args.min_mem_gib, tag) if gate
                else {"waited_s": 0.0, "load_at_start": loadavg(),
                      "memavail_gib_at_start": memavail_gib()})
    log.parent.mkdir(parents=True, exist_ok=True)
    started = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    t0 = time.perf_counter()
    with Sampler(10.0) as sampler, open(log, "wb") as fh:
        proc = subprocess.Popen(argv, cwd=str(cwd), env=env, stdout=fh,
                                stderr=subprocess.STDOUT)
        sampler.root_pid = proc.pid
        _, status, ru = os.wait4(proc.pid, 0)
    wall = time.perf_counter() - t0
    try:
        log_errors = [ln for ln in log.read_text(errors="replace").splitlines()
                      if ": error" in ln][:20]
    except OSError:
        log_errors = None
    rec = {
        "tag": tag, "started": started, "argv": [str(a) for a in argv],
        "cwd": str(cwd), "LEAN_PATH": env.get("LEAN_PATH"),
        "returncode": os.waitstatus_to_exitcode(status),
        "wall": round(wall, 3), "user": round(ru.ru_utime, 3),
        "system": round(ru.ru_stime, 3), "peak_rss_bytes": int(ru.ru_maxrss) * 1024,
        "load_after": loadavg(), "log": str(log), "log_errors": log_errors,
        "box": sampler.summary(), "box_samples": sampler.series(), **gate_rec,
        "gate": {"applied": gate, "max_load": args.max_load, "min_mem_gib": args.min_mem_gib},
    }
    if extra:
        rec.update(extra)
    work = Path(args.work)
    work.mkdir(parents=True, exist_ok=True)
    with open(work / "runs.jsonl", "a") as fh:
        fh.write(json.dumps(rec) + "\n")
    print(f"{tag}: rc={rec['returncode']} wall={rec['wall']} user={rec['user']} "
          f"sys={rec['system']} rss={rec['peak_rss_bytes'] / 2**30:.2f}GiB "
          f"load={gate_rec['load_at_start']}", flush=True)
    return rec


def _load_script(name: str, filename: str):
    spec = importlib.util.spec_from_file_location(name, ROOT / "scripts" / filename)
    assert spec is not None and spec.loader is not None
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


# --------------------------------------------------------------------------- units

def cmd_tower(args) -> None:
    out = Path(args.work) / "tower"
    out.mkdir(parents=True, exist_ok=True)
    tower = out / f"Rung3TowerPilot_p{args.prime}.lean"
    base = out / "ImportBallTerm.lean"
    subprocess.run([sys.executable, str(ROOT / "scripts" / "68_rung3_ball_tower_pilot.py"),
                    "--prime", str(args.prime), "--out", str(tower)], cwd=ROOT, check=True)
    base.write_text("import ZetaLean.BallTerm\n")
    env = lean_env()
    flags = [f"-j{args.lean_threads}"] if args.lean_threads else []
    flags += [f"-D{o}" for o in (args.lean_opt or [])]
    suffix = "".join(f"-{f.lstrip('-')}" for f in flags)
    # Every Lean run waits for the box (load and memory gate), not only a batch's first:
    # on this shared box the 1-minute load swung from 30 to 160 within ten minutes.
    for r in range(args.repeat):
        for tag, path in (("tower-baseline", base), ("tower", tower)):
            run_timed(args, ["lake", "env", "lean", *flags, str(path)], cwd=LEAN, env=env,
                      log=out / f"{tag}{suffix}-p{args.prime}-{r}.log", tag=tag + suffix,
                      gate=True,
                      extra={"repeat": r, "file": str(path), "sha256": sha256(path),
                             "bytes": path.stat().st_size, "prime": args.prime,
                             "lean_threads": args.lean_threads,
                             "lean_opts": args.lean_opt or []})


def cmd_composite(args) -> None:
    out = Path(args.work) / "composite"
    out.mkdir(parents=True, exist_ok=True)
    comp = out / f"CompositeAtoms_{args.atoms}.lean"
    base = out / "ImportBallTerm.lean"
    subprocess.run([sys.executable, str(ROOT / "scripts" / "66_rung3_ball_atom_cost.py"),
                    "--atoms", str(args.atoms), "--out", str(comp)], cwd=ROOT, check=True)
    base.write_text("import ZetaLean.BallTerm\n")
    env = lean_env()
    for r in range(args.repeat):
        for tag, path in (("composite-baseline", base), ("composite", comp)):
            run_timed(args, ["lake", "env", "lean", str(path)], cwd=LEAN, env=env,
                      log=out / f"{tag}-{r}.log", tag=tag, gate=True,
                      extra={"repeat": r, "file": str(path), "sha256": sha256(path),
                             "bytes": path.stat().st_size, "atoms": args.atoms})


def site_dirs(args, site: str) -> tuple[Path, Path]:
    base = Path(args.work) / "site" / site
    return base / "gen", base / "out"


def cmd_site(args) -> None:
    gen, out = site_dirs(args, args.site)
    gen.mkdir(parents=True, exist_ok=True)
    out.mkdir(parents=True, exist_ok=True)
    genlog = gen.parent / "generate.log"
    run_timed(args, [sys.executable, str(ROOT / "scripts" / "60_rung3_generate.py"),
                     str(PLAN_PATH), str(gen), "--arith", "ball", "--shard",
                     "--only", args.site],
              cwd=ROOT, env=os.environ.copy(), log=genlog, tag="site-generate",
              gate=False, extra={"site": args.site})
    manifest = gen / f"C{args.site}.manifest.json"
    rec = run_timed(
        args, [sys.executable, str(ROOT / "scripts" / "72_rung3_ball_compile.py"),
               "--lean-project", str(LEAN), "--output-root", str(out),
               "--jobs", "1", "--module-jobs", "1", str(manifest)],
        cwd=ROOT, env=lean_env(), log=gen.parent / "compile.log", tag="site-compile",
        extra={"site": args.site, "manifest": str(manifest),
               "manifest_sha256": sha256(manifest)})
    print(json.dumps({k: rec[k] for k in ("returncode", "wall", "user", "system")}))


def cmd_shard(args) -> None:
    """Recompile one module of the compiled site with `lean -jN`, into a scratch olean.

    The site's own oleans are read, never written: the output goes under WORK/shard.
    The command line is the one scripts/72 runs, plus the thread flag.
    """
    gen, out = site_dirs(args, args.site)
    src = gen / args.module
    if not src.is_file():
        raise SystemExit(f"no such module source {src}")
    sdir = Path(args.work) / "shard" / f"j{args.lean_threads}"
    sdir.mkdir(parents=True, exist_ok=True)
    olean = sdir / Path(args.module).with_suffix(".olean").name
    env = lean_env([str(gen), str(out)])
    for r in range(args.repeat):
        run_timed(args, ["lake", "env", "lean", f"-j{args.lean_threads}", "--root", str(gen),
                         str(src), "-o", str(olean)],
                  cwd=LEAN, env=env,
                  log=sdir / f"{Path(args.module).stem}-{r}.log",
                  tag=f"shard-j{args.lean_threads}",
                  extra={"site": args.site, "module": args.module, "repeat": r,
                         "lean_threads": args.lean_threads, "sha256": sha256(src),
                         "bytes": src.stat().st_size})


def _module_imports(text: str) -> list[str]:
    return re.findall(r"^import\s+\S+", text, re.MULTILINE)


def cmd_imports(args) -> None:
    gen, out = site_dirs(args, args.site)
    man = json.loads((gen / f"C{args.site}.manifest.json").read_text())
    probes = Path(args.work) / "imports" / args.site
    probes.mkdir(parents=True, exist_ok=True)
    env = lean_env([str(gen), str(out)])
    for r in range(args.repeat):
        for i, mod in enumerate(man["modules"]):
            text = (gen / mod["path"]).read_text()
            probe = probes / f"probe_{i:02d}.lean"
            probe.write_text("\n".join(_module_imports(text)) + "\n")
            run_timed(args, ["lake", "env", "lean", str(probe)], cwd=LEAN, env=env,
                      log=probes / f"probe_{i:02d}-{r}.log", tag="import-probe",
                      gate=True,
                      extra={"site": args.site, "module": mod["path"], "repeat": r,
                             "imports": _module_imports(text)})


def cmd_axioms(args) -> None:
    gen, out = site_dirs(args, args.site)
    probe = Path(args.work) / "axioms" / f"Axioms_{args.site}.lean"
    probe.parent.mkdir(parents=True, exist_ok=True)
    probe.write_text(
        f"import C{args.site}\n"
        f"#print axioms ZetaLean.DH.Cert.upper_{args.site}\n"
        f"#print axioms ZetaLean.DH.Cert.enc_{args.site}\n")
    log = probe.with_suffix(".log")
    rec = run_timed(args, ["lake", "env", "lean", str(probe)], cwd=LEAN,
                    env=lean_env([str(gen), str(out)]), log=log, tag="axioms-run",
                    gate=False, extra={"site": args.site})
    text = log.read_text()
    print(text)
    summary = {"tag": "axioms", "site": args.site, "returncode": rec["returncode"],
               "probe": probe.read_text(), "output": text,
               "axioms": sorted(set(re.findall(r"\b(propext|Classical\.choice|Quot\.sound|"
                                               r"sorryAx|[A-Za-z_.]+\.axiom\w*)\b", text)))}
    with open(Path(args.work) / "runs.jsonl", "a") as fh:
        fh.write(json.dumps(summary) + "\n")
    if rec["returncode"] != 0:
        raise SystemExit(1)


# --------------------------------------------------------------------------- faults

def _replace_once(text: str, old: str, new: str) -> str:
    if text.count(old) != 1:
        raise SystemExit(f"expected exactly one occurrence of {old[:80]!r}, "
                         f"found {text.count(old)}")
    return text.replace(old, new)


def _qlit(x: F) -> str:
    return (f"({x.numerator} : ℚ)" if x.denominator == 1
            else f"({x.numerator}/{x.denominator} : ℚ)")


_QRE = r"\((-?\d+)(?:/(\d+))? : ℚ\)"


def _parse_q(s: str) -> F:
    m = re.fullmatch(_QRE, s.strip())
    if not m:
        raise SystemExit(f"not a rational literal: {s!r}")
    return F(int(m.group(1)), int(m.group(2) or 1))


def _ball_def(text: str, name: str) -> tuple[str, F, F, F]:
    pat = (rf"^def {re.escape(name)} : ComplexBall := \(⟨({_QRE}), ({_QRE}), ({_QRE})⟩ "
           r": ComplexBall\)$")
    m = re.search(pat, text, re.MULTILINE)
    if not m:
        raise SystemExit(f"no ball literal for {name}")
    line = m.group(0)
    return line, _parse_q(m.group(1)), _parse_q(m.group(4)), _parse_q(m.group(7))


def plant(kind: str, gen: Path, site: str) -> dict:
    """Apply one named fault to the sources under `gen`; return what changed."""
    root_rel = f"C{site}.lean"
    if kind == "tower-rad":
        # The largest prime's last squaring: claim a radius one unit smaller.
        files = sorted((gen / f"C{site}").glob("Primes*.lean"))
        best = None
        for path in files:
            for m in re.finditer(r"^namespace Prime_(\d+)$", path.read_text(), re.MULTILINE):
                p = int(m.group(1))
                if best is None or p > best[0]:
                    best = (p, path)
        assert best is not None
        prime, path = best
        text = path.read_text()
        start = text.index(f"namespace Prime_{prime}\n")
        stop = text.index(f"end Prime_{prime}\n", start)
        block = text[start:stop]
        line, cre, cim, rad = _ball_def(block, "Sq_10")
        new_rad = rad - F(1, rad.denominator)
        new_line = (f"def Sq_10 : ComplexBall := (⟨{_qlit(cre)}, {_qlit(cim)}, "
                    f"{_qlit(new_rad)}⟩ : ComplexBall)")
        block2 = _replace_once(block, line, new_line)
        path.write_text(text[:start] + block2 + text[stop:])
        return {"file": str(path.relative_to(gen)), "declaration": f"Prime_{prime}.Sq_10",
                "old_rad": str(rad), "new_rad": str(new_rad),
                "expected_failure": f"Prime_{prime}.ev_mul_29"}
    path = gen / root_rel
    text = path.read_text()
    if kind == "tail-rad":
        # Claim the tail radius just below the tail bound the hypothesis must clear.
        plan = json.loads(PLAN_PATH.read_text())
        s = next(b for b in plan["big"]["boxes"] if b["id"] == site)
        r = F(s["r"])
        bound = (F(5, 8) * ((3 + F(2840794, 10**7)) * F(s["NS"]) * F(s["NS1"])
                 * F(s["NS2"])) * F(s["P"]) / (F(s["sigma_lo"]) + 2))
        assert bound <= r, (bound, r)
        new_r = F(int(bound * 2**40) - 1, 2**40)
        assert new_r < bound
        n = text.count(_qlit(r))
        text = text.replace(_qlit(r), _qlit(new_r))
        path.write_text(text)
        return {"file": root_rel, "declaration": f"enc_{site} (r := ...)",
                "old_r": str(r), "tail_bound": str(bound), "new_r": str(new_r),
                "occurrences_replaced": n, "expected_failure": f"enc_{site}"}
    if kind == "M":
        # Claim the big-box bound just below what the enclosure delivers.
        line, cre, cim, rad = _ball_def(text, f"B_{site}")
        plan = json.loads(PLAN_PATH.read_text())
        s = next(b for b in plan["big"]["boxes"] if b["id"] == site)
        r = F(s["r"])
        m = re.search(rf"\(ComplexBall\.norm_centre_le \(x := \(B_{site}\.inflate "
                      rf"{re.escape(_qlit(r))}\)\) \(u := ({_QRE})\)", text)
        assert m, "no norm_centre_le for the inflated ball"
        u = _parse_q(m.group(1))
        upper = u + rad + r
        new_M = upper - F(1, 2**40)
        old_M = F(plan["M"])
        text = _replace_once(text, f"‖DH s‖ ≤ (({_qlit(old_M)}) : ℝ)",
                             f"‖DH s‖ ≤ (({_qlit(new_M)}) : ℝ)")
        path.write_text(text)
        return {"file": root_rel, "declaration": f"upper_{site}", "old_M": str(old_M),
                "u_plus_rad": str(upper), "new_M": str(new_M),
                "expected_failure": f"upper_{site}"}
    raise SystemExit(f"unknown fault kind {kind}")


_DECL = re.compile(r"^(?:private\s+)?(?:noncomputable\s+)?(?:theorem|lemma|def)\s+(\S+)")


def enclosing_declaration(path: Path, line_no: int) -> str | None:
    """Namespace-qualified name of the declaration whose text holds line `line_no`."""
    lines = path.read_text().splitlines()[:line_no]
    name, ns = None, []
    for ln in lines:
        m = _DECL.match(ln)
        if m:
            name = ".".join(ns + [m.group(1)])
        if ln.startswith("namespace "):
            ns.append(ln.split()[1])
        elif ln.startswith("end ") and ns and ln.split()[1] == ns[-1]:
            ns.pop()
    return name


def cmd_fault(args) -> None:
    gen, out = site_dirs(args, args.site)
    fdir = Path(args.work) / "faults" / args.kind
    if fdir.exists():
        shutil.rmtree(fdir)
    fgen, fout = fdir / "gen", fdir / "out"
    # The oleans linked beside the sources are left behind: on resume the driver
    # relinks every checkpointed olean from the copied output root.
    shutil.copytree(gen, fgen, symlinks=True, ignore=shutil.ignore_patterns("*.olean"))
    shutil.copytree(out, fout, symlinks=True)
    change = plant(args.kind, fgen, args.site)
    manifest = fgen / f"C{args.site}.manifest.json"
    man = json.loads(manifest.read_text())
    for mod in man["modules"]:
        mod["bytes"] = (fgen / mod["path"]).stat().st_size
    manifest.write_text(json.dumps(man, indent=2) + "\n")
    rec = run_timed(
        args, [sys.executable, str(ROOT / "scripts" / "72_rung3_ball_compile.py"),
               "--lean-project", str(LEAN), "--output-root", str(fout),
               "--jobs", "1", "--module-jobs", "1", str(manifest)],
        cwd=ROOT, env=lean_env(), log=fdir / "compile.log", tag=f"fault-{args.kind}",
        extra={"site": args.site, "fault": change})
    result = json.loads((fout / "results" / f"C{args.site}.json").read_text())
    failed = [m for m in result["modules"] if m.get("status") == "failed"]
    errors, decls = [], []
    for m in failed:
        for ln in Path(m["log"]).read_text().splitlines():
            hit = re.match(r"^(.*\.lean):(\d+):(\d+): error", ln)
            if hit:
                errors.append(ln[len(hit.group(1)) - len(Path(hit.group(1)).name):])
                d = enclosing_declaration(Path(hit.group(1)), int(hit.group(2)))
                if d and d not in decls:
                    decls.append(d)
    summary = {"tag": f"fault-{args.kind}-outcome", "site_status": result["status"],
               "driver_returncode": rec["returncode"],
               "recompiled": [m["path"] for m in result["modules"] if m["status"] != "skipped"],
               "failed_modules": [m["path"] for m in failed], "errors": errors[:12],
               "error_declarations": decls, "fault": change}
    with open(Path(args.work) / "runs.jsonl", "a") as fh:
        fh.write(json.dumps(summary) + "\n")
    print(json.dumps(summary, indent=2))


def cmd_centre_eps(args) -> None:
    cdir = Path(args.work) / "centre-eps"
    gen = cdir / "gen"
    root = gen / "Ccentre.lean"
    if not root.is_file():
        gen.mkdir(parents=True, exist_ok=True)
        run_timed(args, [sys.executable, str(ROOT / "scripts" / "60_rung3_generate.py"),
                         str(PLAN_PATH), str(gen), "--arith", "ball", "--shard",
                         "--only", "centre"],
                  cwd=ROOT, env=os.environ.copy(), log=cdir / "generate.log",
                  tag="centre-generate", gate=False)
    if args.generate_only:
        return
    text = root.read_text()
    bline, cre, cim, rad = _ball_def(text, "B_centre")
    zline = re.search(r"^noncomputable def z_centre : ℂ := .*$", text, re.MULTILINE).group(0)
    start = text.index("theorem centre_lt_centre")
    block = text[start:text.index("\nend ZetaLean.DH.Cert", start)].rstrip()
    lines = block.splitlines()
    have = [i for i, ln in enumerate(lines) if ln.startswith("  have henc := enc_centre")]
    assert have == [1], lines[:3]
    m = re.search(r"\(x := \(B_centre\.inflate (" + _QRE + r")\)\) \(u := (" + _QRE + r")\)",
                  block)
    r, u = _parse_q(m.group(1)), _parse_q(m.group(4))
    eps = F(json.loads(PLAN_PATH.read_text())["small"]["eps"])
    upper = u + rad + r
    # A bracket around the bound the enclosure delivers: just above it must compile,
    # at it (the claim is strict) and at half the plan's eps' must not.
    above = F(int(upper * 2**64) + 1, 2**64)
    assert upper < above < eps
    variants = {"control": eps, "eps-above-bound": above, "eps-at-bound": upper,
                "eps-half": eps / 2}
    for name, e in variants.items():
        head = (f"theorem centre_lt_centre (henc : (B_centre.inflate {_qlit(r)}).contains "
                f"(DH z_centre)) :\n    ‖DH z_centre‖ < (({_qlit(e)}) : ℝ) := by")
        body = "\n".join(lines[2:])
        probe = cdir / f"CentreEps_{name}.lean"
        probe.write_text("\n".join([
            "/- Hunt #145 probe: the last step of the generated centre theorem, verbatim,",
            "   with the enclosure taken as a hypothesis.  Generated by pilot.py. -/",
            "import ZetaLean.BallCertSupport", "",
            "open Complex Finset ZetaLean ZetaLean.ComplexBall ZetaLean.DH", "",
            "set_option maxRecDepth 8000000", "set_option maxHeartbeats 40000000", "",
            "namespace ZetaLean.DH.CentreProbe", "", bline, "", zline, "", head, body, "",
            "end ZetaLean.DH.CentreProbe", ""]))
        run_timed(args, ["lake", "env", "lean", str(probe)], cwd=LEAN, env=lean_env(),
                  log=probe.with_suffix(".log"), tag=f"centre-eps-{name}",
                  gate=True,
                  extra={"eps": str(e), "u_plus_rad": str(upper), "file": str(probe),
                         "sha256": sha256(probe)})


def _assemble_seeded(ball, site: dict, seed_one: bool):
    """scripts/65's `_assemble_ball`, copied, with `m = 1` optionally seeded as the
    exact ball (1, 0, 0), which is what scripts/69 emits for `1^(-s)`."""
    S = ball.from_box(F(site["re_lo"]), F(site["re_hi"]), F(site["im_lo"]),
                      F(site["im_hi"]))
    K = int(site["K"])
    N = 5 * K
    cache = {1: ball.cexact(1, 0)} if seed_one else {}
    args = (S, 32, 20, 64, 10, cache)
    acc = ball.cexact(0, 0)
    for m in range(N):
        acc = ball.cadd(acc, ball.term_chain(m, *args))
    bt = {m: ball.cpowBox(m, *args) for m in (N + 1, N + 2, N + 3, N + 4)}
    m1, m2, m3, m4 = N + 1, N + 2, N + 3, N + 4
    blk = ball.cadd(ball.cadd(bt[m1], ball.cneg(bt[m4])),
                    ball.cmul(ball.KAPPA_C, ball.cadd(bt[m2], ball.cneg(bt[m3]))))
    anti = ball.cadd(
        ball.cadd(ball.cmul(ball.cexact(m1, 0), bt[m1]),
                  ball.cneg(ball.cmul(ball.cexact(m4, 0), bt[m4]))),
        ball.cmul(ball.KAPPA_C, ball.cadd(ball.cmul(ball.cexact(m2, 0), bt[m2]),
                                          ball.cneg(ball.cmul(ball.cexact(m3, 0), bt[m3])))))
    anti_b = ball.cmul(anti, ball.invC(ball.inv5sBox(S)))
    return ball.cadd(ball.cadd(acc, ball.cmul(blk, ball.cexact(F(1, 2), 0))),
                     ball.cneg(anti_b))


def cmd_mirror(args) -> None:
    v = _load_script("rung3_full_validation", "65_rung3_full_validation.py")
    plan = json.loads(PLAN_PATH.read_text())
    site = next(b for b in plan["big"]["boxes"] if b["id"] == args.site)
    t0 = time.time()
    ball, B = v._assemble_ball(site["re_lo"], site["re_hi"], site["im_lo"], site["im_hi"],
                               site["K"], site["r"])
    nb = ball.normBound(B)
    r = F(site["r"])
    seeded = _assemble_seeded(ball, site, seed_one=True)
    unseeded = _assemble_seeded(ball, site, seed_one=False)
    gen, _ = site_dirs(args, args.site)
    man = json.loads((gen / f"C{args.site}.manifest.json").read_text())
    text = (gen / f"C{args.site}.lean").read_text()
    _, cre, cim, rad = _ball_def(text, f"B_{args.site}")
    one = ball.cpowBox(1, ball.from_box(F(site["re_lo"]), F(site["re_hi"]),
                                        F(site["im_lo"]), F(site["im_hi"])))
    rec = {"tag": "mirror", "site": args.site, "secs": round(time.time() - t0, 1),
           "scripts65_normBound": str(nb), "manifest_normBound": man["normBound"],
           "scripts65_normBound_float": float(nb),
           "manifest_normBound_float": float(F(man["normBound"])),
           "M": plan["M"],
           "emitted_B": [str(cre), str(cim), str(rad)],
           "scripts65_B": [str(B.cre), str(B.cim), str(B.rad - r)],
           "centre_agrees": B.cre == cre and B.cim == cim,
           "scripts65_extra_radius": str(B.rad - r - rad),
           "scripts65_extra_radius_float": float(B.rad - r - rad),
           "copy_of_scripts65_reproduces_it": unseeded.cre == B.cre and unseeded.cim == B.cim
           and unseeded.rad + r == B.rad,
           "scripts63_cpowBox_1": [str(one.cre), str(one.cim), str(one.rad)],
           "seeded_one_agrees_bit_for_bit": (seeded.cre == cre and seeded.cim == cim
                                             and seeded.rad == rad),
           "agree": (str(nb) == man["normBound"] and B.cre == cre and B.cim == cim
                     and B.rad - r == rad)}
    with open(Path(args.work) / "runs.jsonl", "a") as fh:
        fh.write(json.dumps(rec) + "\n")
    print(json.dumps(rec, indent=2))


def main(argv: list[str] | None = None) -> None:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--work", default=str(DEFAULT_WORK))
    ap.add_argument("--max-load", type=float, default=64.0)
    ap.add_argument("--min-mem-gib", type=float, default=30.0)
    sub = ap.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("tower")
    p.add_argument("--prime", type=int, default=2)
    p.add_argument("--repeat", type=int, default=3)
    p.add_argument("--lean-threads", type=int, default=None)
    p.add_argument("--lean-opt", action="append", default=None,
                   help="a Lean option passed as -D<opt>, e.g. linter.all=false")
    p = sub.add_parser("composite")
    p.add_argument("--atoms", type=int, default=10)
    p.add_argument("--repeat", type=int, default=3)
    for name in ("site", "imports", "axioms", "mirror"):
        p = sub.add_parser(name)
        p.add_argument("--site", default="B_right_06")
        if name == "imports":
            p.add_argument("--repeat", type=int, default=2)
    p = sub.add_parser("shard")
    p.add_argument("--site", default="B_right_06")
    p.add_argument("--module", default="CB_right_06/Primes02.lean")
    p.add_argument("--lean-threads", type=int, default=1)
    p.add_argument("--repeat", type=int, default=1)
    p = sub.add_parser("fault")
    p.add_argument("--site", default="B_right_06")
    p.add_argument("--kind", choices=("tower-rad", "tail-rad", "M"), required=True)
    p = sub.add_parser("centre-eps")
    p.add_argument("--generate-only", action="store_true",
                   help="write the centre's sources and stop; compiles nothing")
    args = ap.parse_args(argv)
    {"tower": cmd_tower, "composite": cmd_composite, "site": cmd_site,
     "imports": cmd_imports, "axioms": cmd_axioms, "fault": cmd_fault,
     "centre-eps": cmd_centre_eps, "mirror": cmd_mirror, "shard": cmd_shard}[args.cmd](args)


if __name__ == "__main__":
    main()

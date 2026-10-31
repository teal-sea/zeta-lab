#!/usr/bin/env python3
"""Hunt #145, resumed 2026-10-26: price the staged prime tower with `decide +kernel`.

`scripts/68` closes each staged ball equality of a prime tower by `norm_num`, which the
2026-10-21 pilot measured at about 2.1 CPU-s per atom.  This instrument emits the same
tower with every staged equality closed by `decide +kernel` instead (the containment
theorem is untouched), and times it beside an import-only baseline, a `norm_num` control,
one planted fault, one composite product, one kappa product and one whole-tower decision
(`dirichletTermBallB ... = lit`, which makes the kernel evaluate `Nat.sqrt` and the
recursive tower) under a ten-minute timeout.

Every literal comes from the bit-exact mirror `scripts/63` through `scripts/68`'s own
renderer, so the files are deterministic and replayable from the repository alone.

    .venv/bin/python hunts/rung3_ball_production/decide_pilot.py emit
    .venv/bin/python hunts/rung3_ball_production/decide_pilot.py run      # gated, one process
    .venv/bin/python hunts/rung3_ball_production/decide_pilot.py summarize

`run` appends one JSON line per Lean process to WORK/runs.jsonl; `summarize` writes the
`decide_kernel` section of pilot.json from that log alone.
"""
from __future__ import annotations

import argparse
import hashlib
import importlib
import json
import math
import os
import re
import statistics as st
import subprocess
import sys
import time
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
LEAN = ROOT / "lean"
sys.path.insert(0, str(ROOT / "scripts"))
ball = importlib.import_module("63_rung3_ball_mirror")
tower68 = importlib.import_module("68_rung3_ball_tower_pilot")

DEFAULT_WORK = Path(os.environ.get(
    "RUNG3_DECIDE_WORK",
    os.path.expanduser("~/.cache/zeta-lab/rung3-ball-production-decide")))
NLOG, NEXP, P, KE = tower68.NLOG, tower68.NEXP, tower68.P, tower68.KE
PRIME = 2
THRESHOLD_CPU_S = 10.0          # recorded in RUNS.md before any run
WHOLE_TIMEOUT_S = 600
LOAD_MAX, MEM_MIN_GIB = 64.0, 30.0
HEADER = ["import ZetaLean.BallCertSupport", "",
          "open Complex Finset ZetaLean ZetaLean.ComplexBall", "",
          "set_option maxRecDepth 8000000", "set_option maxHeartbeats 40000000", ""]
q, lit = tower68.q, tower68.lit


# --------------------------------------------------------------------------- emission

def _decide(text: str) -> str:
    """Close every `private lemma ev_* ... := by` block by `decide +kernel`."""
    out, skip = [], False
    for line in text.split("\n"):
        if skip:
            if line.strip() == "":
                skip = False
                out.append(line)
            continue
        out.append(line)
        if line.startswith("private lemma ev_") and line.endswith(":= by"):
            out.append("  decide +kernel")
            skip = True
    return "\n".join(out)


def _eq_only(text: str) -> str:
    """The definitions and staged equalities, without the containment theorem."""
    head = text.split("theorem pilot_contains_cpow")[0]
    return head + "end ZetaLean.Rung3TowerPilot\n"


def _imports(text: str) -> str:
    return text.replace("import ZetaLean.BallTerm", "import ZetaLean.BallCertSupport", 1)


def _tower():
    text, stats = tower68.render_prime_tower(PRIME)
    return _imports(text), stats


def _fault(eq_decide: str, final) -> tuple[str, str]:
    """Sq_10's radius one unit of 2^-64 low: only `ev_mul_29` should be refused."""
    bad = ball.C(final.cre, final.cim, final.rad - F(1, 2**P))
    old = f"def Sq_{KE} : ComplexBall := {lit(final)}"
    assert eq_decide.count(old) == 1
    return eq_decide.replace(old, f"def Sq_{KE} : ComplexBall := {lit(bad)}"), "ev_mul_29"


def _atoms() -> dict[str, str]:
    S = ball.C(*tower68.ORACLE, 0)
    A = ball.dirichletTermBox2(NLOG, NEXP, P, 2, KE, 2, S)
    B = ball.dirichletTermBox2(NLOG, NEXP, P, 2, KE, 3, S)
    prod = ball.ccoarsen(P, ball.cmul(A, B))
    uA, uB = ball._absc_upper(A), ball._absc_upper(B)
    kap = ball.cmul(ball.KAPPA_C, A)
    uK = ball._absc_upper(ball.KAPPA_C)
    files = {}
    for how, proof in (("decide", "  decide +kernel"),
                       ("normnum", None)):
        comp = HEADER + [f"def A : ComplexBall := {lit(A)}", f"def B : ComplexBall := {lit(B)}",
                         f"theorem comp_6 : coarsenB {P} (ComplexBall.mul A B {q(uA)} {q(uB)})",
                         f"    = {lit(prod)} := by",
                         proof or ("  norm_num [A, B, coarsenB, recentre, widenRad, ceilP,\n"
                                   "    ComplexBall.mul]"), ""]
        kappa = HEADER + [f"def A : ComplexBall := {lit(A)}",
                          f"theorem kappa_2 : ComplexBall.mul (coeffBall 2) A {q(uK)} {q(uA)}",
                          f"    = {lit(kap)} := by",
                          proof or ("  norm_num [A, coeffBall, kappaBall, ofRealInterval, DH.kappaI,\n"
                                    "    ComplexBall.exact, ComplexBall.neg, ComplexBall.mul]"), ""]
        files[f"Composite_{how}.lean"] = "\n".join(comp)
        files[f"Kappa_{how}.lean"] = "\n".join(kappa)
    S_lit = lit(S)
    whole_val = ball.dirichletTermBox2(NLOG, NEXP, P, PRIME.bit_length(), KE, PRIME, S)
    stmt = (f"dirichletTermBallB {NLOG} {NEXP} {P} {PRIME.bit_length()} {KE} {PRIME} {S_lit}\n"
            f"    = {lit(whole_val)}")
    files["WholeEval.lean"] = "\n".join(HEADER + [f"#eval decide ({stmt})", ""])
    files["WholeDecide.lean"] = "\n".join(
        HEADER + [f"theorem whole_tower : {stmt} := by", "  decide +kernel", ""])
    files.update(_whole_files())
    return files


def _whole_containment(prime: int, S, tag: str, fault: bool = False) -> str:
    """A full tower through the whole decision: `contains_dirichletTermBallB`, its
    norm side condition by `decide +kernel`, and the value by one `decide +kernel`."""
    kL = prime.bit_length()
    val = ball.dirichletTermBox2(NLOG, NEXP, P, kL, KE, prime, S)
    if fault:
        val = ball.C(val.cre, val.cim, val.rad - F(1, 2**P))
    args = f"{NLOG} {NEXP} {P} {kL} {KE} {prime} S_{tag}"
    return "\n".join(HEADER + [
        f"def S_{tag} : ComplexBall := {lit(S)}",
        f"def V_{tag} : ComplexBall := {lit(val)}",
        f"theorem ev_{tag} : dirichletTermBallB {args} = V_{tag} := by",
        "  decide +kernel",
        f"theorem tower_{tag} {{s : ℂ}} (hS : S_{tag}.contains s) :",
        f"    V_{tag}.contains ((({prime} : ℕ) : ℂ) ^ (-s)) := by",
        f"  have h := contains_dirichletTermBallB (nLog := {NLOG}) (nExp := {NEXP}) (p := {P})",
        f"    (kL := {kL}) (kE := {KE}) (by norm_num) (m := {prime}) (by norm_num) hS",
        "    (by norm_num) (by norm_num) (by decide +kernel)",
        f"  rwa [ev_{tag}] at h",
        f"#print axioms tower_{tag}", ""])


def _whole_files() -> dict[str, str]:
    oracle = ball.C(*tower68.ORACLE, 0)
    plan = json.loads((LEAN / "cert" / "rung3_plan2.json").read_text())
    b = next(x for x in plan["big"]["boxes"] if x["id"] == "B_right_06")
    site = ball.from_box(F(b["re_lo"]), F(b["re_hi"]), F(b["im_lo"]), F(b["im_hi"]))
    return {"TowerWhole_p2.lean": _whole_containment(2, oracle, "p2"),
            "TowerWhole_p1801_box.lean": _whole_containment(1801, site, "p1801"),
            "TowerWholeFault_p2.lean": _whole_containment(2, oracle, "p2", fault=True)}


def emit_all() -> dict[str, str]:
    text, stats = _tower()
    eq_nn = _eq_only(text)
    full_d = _decide(text)
    eq_d = _eq_only(full_d)
    fault, _ = _fault(eq_d, stats["final"])
    files = {"Baseline.lean": "\n".join(HEADER),
             "TowerNormNumEq.lean": eq_nn,
             "TowerNormNum.lean": text,
             "TowerDecideEq.lean": eq_d,
             "TowerDecide.lean": full_d,
             "TowerDecideFault.lean": fault}
    files.update(_atoms())
    return files


# --------------------------------------------------------------------------- running

PLAN = [  # (file, repeats, timeout seconds)
    ("Baseline.lean", 2, 600), ("TowerDecideEq.lean", 2, 600), ("TowerDecide.lean", 2, 600),
    ("TowerNormNumEq.lean", 1, 900), ("TowerDecideFault.lean", 1, 600),
    ("TowerNormNum.lean", 1, 900),
    ("Composite_decide.lean", 2, 600), ("Composite_normnum.lean", 1, 600),
    ("Kappa_decide.lean", 2, 600), ("Kappa_normnum.lean", 1, 600),
    ("WholeEval.lean", 1, 600), ("WholeDecide.lean", 1, WHOLE_TIMEOUT_S),
    ("TowerWhole_p2.lean", 2, WHOLE_TIMEOUT_S), ("TowerWhole_p1801_box.lean", 2, WHOLE_TIMEOUT_S),
    ("TowerWholeFault_p2.lean", 1, WHOLE_TIMEOUT_S),
]


def _load1() -> float:
    return float(Path("/proc/loadavg").read_text().split()[0])


def _memavail_gib() -> float:
    for line in Path("/proc/meminfo").read_text().splitlines():
        if line.startswith("MemAvailable:"):
            return int(line.split()[1]) / 2**20
    raise RuntimeError("no MemAvailable")


def _gate() -> tuple[float, float, float]:
    t0 = time.time()
    while _load1() > LOAD_MAX or _memavail_gib() < MEM_MIN_GIB:
        time.sleep(15)
    return _load1(), _memavail_gib(), time.time() - t0


_TIME = {"user": r"User time \(seconds\): ([\d.]+)", "sys": r"System time \(seconds\): ([\d.]+)",
         "maxrss_kb": r"Maximum resident set size \(kbytes\): (\d+)",
         "wall": r"Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([\d:.]+)"}


def _wall(s: str) -> float:
    parts = [float(x) for x in s.split(":")]
    return sum(v * 60 ** i for i, v in enumerate(reversed(parts)))


def _errors(log: str, src: str) -> list[dict]:
    """Each `error` line with the declaration it falls in."""
    lines = src.split("\n")
    out = []
    for m in re.finditer(r":(\d+):(\d+): error: ?(.*)", log):
        ln = int(m.group(1))
        decl = None
        for i in range(ln - 1, -1, -1):
            d = re.match(r"(?:private )?(?:lemma|theorem|def|example) ?([\w.]*)", lines[i])
            if d:
                decl = d.group(1) or "example"
                break
        out.append({"line": ln, "decl": decl, "msg": m.group(3)[:200]})
    return out


def run_one(work: Path, name: str, timeout: int) -> dict:
    src = (work / "src" / name).read_text()
    load, mem, waited = _gate()
    env = dict(os.environ, PATH=f"{os.path.expanduser('~/.elan/bin')}:{os.environ['PATH']}")
    cmd = ["nice", "-n", "10", "/usr/bin/time", "-v", "timeout", str(timeout),
           "lake", "env", "lean", str(work / "src" / name)]
    t0 = time.time()
    p = subprocess.run(cmd, cwd=LEAN, env=env, capture_output=True, text=True)
    rec = {"file": name, "sha256": hashlib.sha256(src.encode()).hexdigest(),
           "returncode": p.returncode, "timed_out": p.returncode == 124,
           "load1_before": load, "memavail_gib_before": round(mem, 1),
           "gate_wait_s": round(waited, 1), "started_unix": round(t0, 1)}
    for k, pat in _TIME.items():
        m = re.search(pat, p.stderr)
        rec[k] = (_wall(m.group(1)) if k == "wall" else float(m.group(1))) if m else None
    rec["cpu_s"] = round(rec["user"] + rec["sys"], 2) if rec["user"] is not None else None
    rec["load1_after"] = _load1()
    rec["errors"] = _errors(p.stdout + p.stderr, src)
    rec["stdout_tail"] = p.stdout[-400:]
    return rec


def run(work: Path, only: list[str] | None) -> None:
    log = work / "runs.jsonl"
    for name, reps, timeout in PLAN:
        if only and name not in only:
            continue
        for _ in range(reps):
            rec = run_one(work, name, timeout)
            with log.open("a") as f:
                f.write(json.dumps(rec) + "\n")
            print(f"{name}: rc={rec['returncode']} cpu={rec['cpu_s']} wall={rec['wall']} "
                  f"rss={rec['maxrss_kb']} load={rec['load1_before']} "
                  f"errors={[e['decl'] for e in rec['errors']]}", flush=True)


# --------------------------------------------------------------------------- summary

def summarize(records: list[dict]) -> dict:
    by: dict[str, list[dict]] = {}
    for r in records:
        by.setdefault(r["file"], []).append(r)
    base = st.median(r["cpu_s"] for r in by["Baseline.lean"])

    def net(name):
        rs = by.get(name, [])
        cpus = [r["cpu_s"] for r in rs if r["returncode"] == 0]
        return {"runs": len(rs), "returncodes": [r["returncode"] for r in rs],
                "cpu_s": [r["cpu_s"] for r in rs], "wall_s": [r["wall"] for r in rs],
                "maxrss_kb": [r["maxrss_kb"] for r in rs],
                "load1_before": [r["load1_before"] for r in rs],
                "net_cpu_s_median": round(st.median(cpus) - base, 2) if cpus else None}

    out = {"date": "2026-10-26", "prime": PRIME, "staged_atoms": 30,
           "threshold_full_tower_cpu_s": THRESHOLD_CPU_S,
           "baseline_cpu_s": [r["cpu_s"] for r in by["Baseline.lean"]],
           "baseline_cpu_s_median": base}
    for name in [n for n, _, _ in PLAN if n != "Baseline.lean"]:
        out[name.removesuffix(".lean")] = net(name)
    fault = by.get("TowerDecideFault.lean", [{}])[0]
    out["fault"] = {"expected_refused": "ev_mul_29", "returncode": fault.get("returncode"),
                    "refused_decls": sorted({e["decl"] for e in fault.get("errors", [])})}
    whole = by.get("WholeDecide.lean", [{}])[0]
    out["whole"] = {"timeout_s": WHOLE_TIMEOUT_S, "timed_out": whole.get("timed_out"),
                    "returncode": whole.get("returncode"),
                    "errors": [e["msg"] for e in whole.get("errors", [])][:3],
                    "eval_stdout": by.get("WholeEval.lean", [{}])[0].get("stdout_tail", "").strip()}
    whole_fault = by.get("TowerWholeFault_p2.lean", [{}])[0]
    out["whole_fault"] = {"expected_refused": "ev_p2", "returncode": whole_fault.get("returncode"),
                          "refused_decls": sorted({e["decl"] for e in whole_fault.get("errors", [])})}
    out["axioms_printed"] = sorted({r["stdout_tail"].strip() for n in
                                    ("TowerWhole_p2.lean", "TowerWhole_p1801_box.lean")
                                    for r in by.get(n, [])})
    staged = out["TowerDecide"]["net_cpu_s_median"]
    whole = [out["TowerWhole_p2"]["net_cpu_s_median"],
             out["TowerWhole_p1801_box"]["net_cpu_s_median"]]
    out["verdict"] = {
        "staged_decide_full_tower_net_cpu_s": staged,
        "staged_meets_threshold": staged is not None and staged <= THRESHOLD_CPU_S,
        "whole_decision_full_tower_net_cpu_s": whole,
        "whole_meets_threshold": all(w is not None and w <= THRESHOLD_CPU_S for w in whole)}
    return out


def reprice(dk: dict, pilot: dict) -> dict:
    """Production with every prime tower proved through the whole decision, every other
    component at the 2026-10-21 projection's own price.  An extrapolation from two towers
    in standalone files, not a measurement of production."""
    towers = sum(site["primes"] for site in pilot["projection"]["sites"])
    lo, hi = sorted(dk["verdict"]["whole_decision_full_tower_net_cpu_s"])
    ch = pilot["projection"]["core_hours"]
    rest = round(sum(v for k, v in ch.items() if k != "tower"), 2)
    return {"towers": towers, "tower_core_hours": [round(towers * lo / 3600, 1),
                                                   round(towers * hi / 3600, 1)],
            "other_core_hours_unchanged": rest,
            "total_core_hours": [round(towers * lo / 3600 + rest, 1),
                                 round(towers * hi / 3600 + rest, 1)],
            "norm_num_total_core_hours": pilot["projection"]["total_core_hours"]}
    return out


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("cmd", choices=["emit", "run", "summarize"])
    ap.add_argument("--work", default=str(DEFAULT_WORK))
    ap.add_argument("--only", nargs="*")
    args = ap.parse_args()
    work = Path(args.work)
    if args.cmd == "emit":
        (work / "src").mkdir(parents=True, exist_ok=True)
        for name, text in emit_all().items():
            (work / "src" / name).write_text(text)
            print(f"wrote {name} ({len(text)} bytes)")
    elif args.cmd == "run":
        run(work, args.only)
    else:
        recs = [json.loads(l) for l in (work / "runs.jsonl").read_text().splitlines() if l]
        summary = summarize(recs)
        pj = HERE / "pilot.json"
        pilot = json.loads(pj.read_text())
        summary["reprice"] = reprice(summary, pilot)
        pilot["decide_kernel"] = summary
        pj.write_text(json.dumps(pilot, indent=1) + "\n")
        print(json.dumps(summary, indent=1))


if __name__ == "__main__":
    main()

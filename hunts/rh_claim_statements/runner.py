"""Run every test of claims.json, and every mutant, and write results.json.

    .venv/bin/python -m hunts.rh_claim_statements.runner                 # the recorded run
    .venv/bin/python -m hunts.rh_claim_statements.runner --level fast --out /tmp/fast.json
    .venv/bin/python -m hunts.rh_claim_statements.runner --prec-scale 2 --out hunts/rh_claim_statements/results_prec2.json
    .venv/bin/python -m hunts.rh_claim_statements.runner --only C01,C21

A claim's record carries `holds` (True: no violation in the grade's sense;
False: a rigorous counterexample; None: undecided somewhere), the grade, the
margin, the tightest point, the smallest constant the test would still accept
(`sharp_constant`) and the slack. A mutant's record carries `rejected`, which
is True only when the same test returns a rigorous counterexample for it.

The archive is not needed and not touched: everything comes from claims.json.
"""
from __future__ import annotations

import argparse
import json
import platform
import sys
import time
from pathlib import Path

from . import checks_analytic, checks_exact, checks_ff, common

HERE = Path(__file__).resolve().parent
MODULES = {"analytic": checks_analytic, "exact": checks_exact, "ff": checks_ff}
GRADES = ("complete_cover", "exact_finite", "measured_range")


def load_claims():
    return json.loads((HERE / "claims.json").read_text(encoding="utf-8"))


def run_check(fn, params):
    module, name = fn.split(".")
    t0 = time.perf_counter()
    r = getattr(MODULES[module], name)(params)
    r["seconds"] = round(time.perf_counter() - t0, 3)
    return r


def base_params(claim, level):
    if level == "fast":
        return claim["test"]["fast"]          # None: the claim is outside the fast tier
    return claim["test"]["params"]


def mutant_params(claim, mutant, level):
    p = dict(base_params(claim, level) or claim["test"]["params"])
    p.update(mutant["params"])
    if level == "fast" and mutant.get("fast"):
        p.update(mutant["fast"])
    return p


def run_mutant(claim, mutant, level="full"):
    r = run_check(claim["test"]["fn"], mutant_params(claim, mutant, level))
    return dict(id=mutant["id"], tag=mutant["tag"], kind=mutant["kind"], rejected=r["holds"] is False,
                holds=r["holds"], witness=r.get("witness"), seconds=r["seconds"])


def run_claim(claim, level="full", with_mutants=True):
    params = base_params(claim, level)
    if params is None:
        rec = dict(id=claim["id"], name=claim["name"], skipped="outside the fast tier")
    else:
        r = run_check(claim["test"]["fn"], params)
        grade = claim["grade_if_it_holds"] if r["holds"] is True else None
        if grade == "complete_cover" and r.get("tail_covered") is False:
            grade = "measured_range"
        rec = dict(id=claim["id"], name=claim["name"], topic=claim["topic"], grade=grade, **r)
    if with_mutants:
        rec["mutants"] = [run_mutant(claim, m, level) for m in claim["mutants"]]
    return rec


def environment():
    import flint
    import numpy
    env = dict(python=platform.python_version(), python_flint=flint.__version__, numpy=numpy.__version__,
               platform=platform.platform())
    try:
        import cypari2
        env["pari"] = str(cypari2.Pari().version())
    except Exception as exc:                                  # pragma: no cover
        env["pari"] = f"unavailable: {exc}"
    try:
        from zeta import rigor
        env["zeta_rigor_backend"] = rigor.BACKEND
    except Exception as exc:                                  # pragma: no cover
        env["zeta_rigor_backend"] = f"unavailable: {exc}"
    return env


def summarise(records):
    done = [r for r in records if "holds" in r]
    by_grade = {g: sum(1 for r in done if r.get("grade") == g) for g in GRADES}
    muts = [m for r in records for m in r.get("mutants", [])]
    return dict(claims=len(records), tested=len(done),
                hold=sum(1 for r in done if r["holds"] is True),
                fail=[r["id"] for r in done if r["holds"] is False],
                undecided=[r["id"] for r in done if r["holds"] is None],
                by_grade=by_grade, mutants=len(muts), mutants_rejected=sum(1 for m in muts if m["rejected"]),
                mutants_not_rejected=[m["id"] for m in muts if not m["rejected"]],
                seconds=round(sum(r.get("seconds", 0) for r in done) + sum(m["seconds"] for m in muts), 1))


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--level", choices=("full", "fast"), default="full")
    ap.add_argument("--only", default="")
    ap.add_argument("--prec-scale", type=int, default=1)
    ap.add_argument("--no-mutants", action="store_true")
    ap.add_argument("--decoys", action="store_true")
    ap.add_argument("--out", default=None)
    a = ap.parse_args(argv)
    common.PREC_SCALE = a.prec_scale
    data = load_claims()
    only = {x for x in a.only.split(",") if x}
    started = time.strftime("%Y-%m-%dT%H:%M:%S%z")
    records = []
    for c in data["claims"]:
        if only and c["id"] not in only:
            continue
        rec = run_claim(c, a.level, with_mutants=not a.no_mutants)
        records.append(rec)
        muts = rec.get("mutants", [])
        print(f"{rec['id']} {rec['name'][:44]:44s} holds={rec.get('holds')!s:5} grade={rec.get('grade')!s:15} "
              f"{rec.get('seconds', 0):7.2f}s  mutants {sum(m['rejected'] for m in muts)}/{len(muts)}", flush=True)
    out = dict(meta=dict(level=a.level, prec_scale=a.prec_scale, started=started,
                         finished=time.strftime("%Y-%m-%dT%H:%M:%S%z"), environment=environment(),
                         archive_tarball_sha256=data["meta"]["tarball_sha256"]),
               summary=summarise(records), claims=records)
    if a.decoys:
        from . import decoys
        out["decoys"] = decoys.run_all()
    print(json.dumps(out["summary"]))
    if a.out is None and a.level == "full" and a.prec_scale == 1 and not only:
        a.out = str(HERE / "results.json")
    if a.out:
        Path(a.out).write_text(json.dumps(out, ensure_ascii=False, indent=1, default=str) + "\n", encoding="utf-8")
        print("wrote", a.out)
    return 0 if not out["summary"]["fail"] else 2


if __name__ == "__main__":
    sys.exit(main())

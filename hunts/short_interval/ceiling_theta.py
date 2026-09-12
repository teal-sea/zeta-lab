"""The configuration LP of ``hunts/frontier_math/configuration_lp.py`` with the
band ``[-1, 1]`` replaced by ``[-theta, theta]``: MISSION.md section 7.

Nothing here is a result. This file builds the instrument, runs its controls,
checkpoints one JSON per bandwidth, and collects a table. Nothing here bears
on RH (``docs/08``).

WHAT THE INSTRUMENT IS.  The LP minimises the density of simple on-line
points over multiplicity types ``p_m``, an off-line pair density ``q`` and an
off-diagonal pair measure ``rho = 1 + tau >= 0``, subject to the band data

    R2hat(alpha) = delta(alpha) + |alpha|     on  [-theta, theta],

which in the LP is ``D + tauhat(alpha) = alpha`` on ``[0, theta]`` with
``D = sum m^2 p_m + 4 q``.  At ``theta = 1`` this is exactly the bandwidth-one
LP, and ``test_reduces_to_bandwidth_one`` below checks that the two solvers
agree to solver precision at the same rung.

WHAT CHANGED AGAINST ``configuration_lp.solve``, and why it is copied rather
than imported.  The band edge is a literal ``1`` in two places of the original:
the alpha grid ``a = arange(J+1)/J`` and the out-of-band start ``aout = 1.0 +
...``.  Both become ``theta``.  The data row itself, ``rhs = a +- eps``, does
not change in form, because ``|alpha|`` is what it is on any band.  No window
enters this LP at all (the window is the LP's dual, see below), so there is no
Fourier-support cap to move.  Adding a ``theta=`` parameter to the original
would have been a two-line edit; it is copied because ``configuration_lp.py``
is another hunt's instrument, its bandwidth-one ladder is cited by three
hunts, and a hunt may not edit files outside its own directory.  The copy
also returns the LP's dual, which the original discards.

WHAT THE INSTRUMENT MEASURES, stated before it is run.  ``frontier_math/
RESULTS-frontier-math.md`` section 1 records that at bandwidth one this LP's
ladder descends ``0.6794 -> 0.6750823`` toward the Montgomery-Taylor record
``0.6725007036794116`` and *not* toward the configuration ceiling
``0.6818286874638``: the type structure eliminates exactly, so the LP value is
``2 - sup D``, the Montgomery-Taylor dual, and "the ceiling gap (0.6725007,
0.68185) is not about the pair measure at all, it measures what configuration
realizability adds beyond measure positivity".  ``outband_intake/
inband_control.py`` uses that known limit as its calibration.  The ceiling
``0.6818286874638`` comes from an extremal law on marked periodic
configurations (``Zeta23/PairCeiling/LawN256.lean``), whose exact-rational
certificate file is not public and which nothing in this tree recomputes
(``wide_search/RESULTS-pair-ceiling.md``).

So the mandatory control that this file must reproduce ``0.6818286874638`` at
``theta = 1`` is expected to FAIL, and the file says so rather than fudging
it.  What the theta ladder does test is whether Wang's landscape
``c(theta) = 2 - theta/2 - (1/sqrt 2) cot(theta/sqrt 2)`` is the limit of this
LP at every bandwidth, which by Wang's Proposition 4.1 (valid at every interval
length) it should be.  A ceiling below the landscape at any rung is a bug in
this file, and the run exits non-zero on it.

THE DUAL.  scipy's HiGHS interface returns the marginals on every row.  The
marginals on the two data bands (``D + tauhat(a) <= a + eps`` and
``-(D + tauhat(a)) <= -(a - eps)``) are the certificate's weight function on
the alpha grid, the object a bandwidth-theta certificate ``c0 + integral r(x)
x dx`` would read; they are saved raw, in scipy's sign convention (marginals
of a minimisation against ``<=`` rows are nonpositive), with their grid.

Run from the repo root with the repository virtualenv:

    .venv/bin/python hunts/short_interval/ceiling_theta.py --control
    .venv/bin/python hunts/short_interval/ceiling_theta.py --theta 0.9
    .venv/bin/python hunts/short_interval/ceiling_theta.py --collect

``--theta`` checkpoints ``artifacts/ceiling-theta-<theta>.json`` after every
rung, per ``CLAUDE.md`` compute discipline rule 4.
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path

import numpy as np
from scipy.optimize import curve_fit, linprog

HERE = Path(__file__).resolve().parent
ARTIFACTS = HERE / "artifacts"
sys.path.insert(0, str(HERE))
from verify import c_simple  # noqa: E402  Wang's c(theta), stdlib, this hunt

# Reference constants, each with its source in this tree.
H_MT = 0.6725007036794116        # Montgomery-Taylor record; c_simple(1.0)
CEILING_ONE = 0.6818286874638     # hunts/wide_search/RESULTS-pair-ceiling.md
HEADROOM_ONE = CEILING_ONE - H_MT  # 0.00932798, MISSION.md section 7
METHOD_ERROR = 0.0018             # hunts/outband_intake/RESULTS.md section 1
INBAND_CONTROL = HERE.parent / "outband_intake" / "artifacts" / "lane-a-control-inband.json"
INBAND_CONTROL_LONG = HERE.parent / "outband_intake" / "artifacts" / "lane-a-control-inband-long.json"

# The (X, J) ladder of outband_intake/inband_control.py and inband_long.py, with
# eps = 0.4/X tracking the truncation floor ~1/(pi^2 X).
DEFAULT_RUNGS = [(40.0, 200), (80.0, 320), (120.0, 480), (160.0, 640),
                 (240.0, 960), (320.0, 1280)]
DEFAULT_THETAS = [1.0, 0.95, 0.9, 0.85, 0.8, 0.75, 0.7, 0.65, 0.6, 0.55]


def alpha_grid(theta, J):
    """The data grid on ``[0, theta]`` with spacing ``theta / round(theta J)``.

    When ``theta J`` is an integer, which it is for every default theta and
    rung, this is the bandwidth-one grid ``arange(J+1)/J`` cut at ``theta``,
    so the discretisation does not change with the band and the endpoint is
    exactly ``theta``.  The band is open, ``(-theta, theta)``, in Wang's
    Theorem 2.2; the closed endpoint is one row of measure zero and is kept
    so that ``theta = 1`` reduces to the original grid row for row.
    """
    n_alpha = int(round(theta * J))
    if abs(n_alpha - theta * J) > 1e-9:
        print(f"note: theta*J = {theta * J} is not an integer; grid spacing is "
              f"{theta / n_alpha:.6g} rather than {1 / J:.6g}", file=sys.stderr)
    return theta * np.arange(n_alpha + 1) / n_alpha


def solve(theta=1.0, J=640, X=160.0, h=1 / 16, eps=2.5e-3, M=6, A_out=None,
          objective="simple"):
    """One LP solve on the band ``[-theta, theta]``; None if infeasible.

    Identical to ``configuration_lp.solve`` except: the alpha grid runs to
    ``theta`` (``alpha_grid``), the optional out-of-band block starts at
    ``theta`` rather than ``1.0``, and the result carries the dual marginals.
    """
    n = int(round(X / h))
    x = h * (np.arange(1, n + 1) - 0.5)
    a = alpha_grid(theta, J)                       # CHANGED: was arange(J+1)/J
    nv = n + M + 1
    row_m = np.array([m * m for m in range(1, M + 1)], float)
    Cin = 2.0 * h * np.cos(2.0 * np.pi * np.outer(a, x))
    rows = [Cin, -Cin]
    rhs = [a + eps, -(a - eps)]
    if A_out is not None:
        # CHANGED: the out-of-band block starts at the band edge theta, not 1.
        aout = theta + np.arange(1, int((A_out - theta) * J) + 1) / J
        Cout = 2.0 * h * np.cos(2.0 * np.pi * np.outer(aout, x))
        rows.append(-Cout)
        rhs.append(np.zeros(len(aout)))
    nrows = sum(r.shape[0] for r in rows)
    Aub = np.zeros((nrows, nv))
    bub = np.concatenate(rhs)
    at = 0
    for blk, sgn in zip(rows, (1.0, -1.0, -1.0)):
        m_ = blk.shape[0]
        Aub[at:at + m_, :n] = blk
        Aub[at:at + m_, n:n + M] = sgn * row_m
        Aub[at:at + m_, n + M] = sgn * 4.0
        at += m_
    Aeq = np.zeros((1, nv))
    beq = np.array([1.0])
    Aeq[0, n:n + M] = np.arange(1, M + 1)
    Aeq[0, n + M] = 2.0
    c = np.zeros(nv)
    if objective == "simple":
        c[n] = 1.0
    elif objective == "distinct":
        c[n:n + M] = 1.0
        c[n + M] = 2.0
    bounds = [(-1.0, None)] * n + [(0.0, None)] * (M + 1)
    res = linprog(c, A_ub=Aub, b_ub=bub, A_eq=Aeq, b_eq=beq, bounds=bounds,
                  method="highs")
    if not res.success:
        return None
    na = len(a)
    marg = res.ineqlin.marginals
    return {"value": float(res.fun),
            "D": float(row_m @ res.x[n:n + M] + 4 * res.x[n + M]),
            "p": res.x[n:n + M].tolist(), "q": float(res.x[n + M]),
            "tau": res.x[:n].tolist(), "x_grid": x.tolist(),
            "dual": {"alpha_grid": a.tolist(),
                     "data_upper_marginals": marg[:na].tolist(),
                     "data_lower_marginals": marg[na:2 * na].tolist(),
                     "outband_marginals": marg[2 * na:].tolist(),
                     "density_marginal": float(res.eqlin.marginals[0]),
                     "type_lower_bound_marginals": res.lower.marginals[n:].tolist(),
                     "convention": "scipy HiGHS: nonpositive on <= rows of a minimisation"}}


def power(x, a, b, p):
    return a + b * x ** (-p)


def fit_free(xs, ys):
    """``refit.py``'s free-exponent fit ``a + b X^(-p)``; None below 4 rungs."""
    xs, ys = np.asarray(xs, float), np.asarray(ys, float)
    if len(xs) < 4:
        return None
    try:
        (a, b, p), _ = curve_fit(power, xs, ys, p0=[ys[-1] * 0.5, 1.0, 1.0],
                                 maxfev=20000)
    except RuntimeError:
        return None
    return {"a": float(a), "b": float(b), "p": float(p)}


def run_theta(theta, rungs, out_path, quiet=False):
    """The ladder at one bandwidth, checkpointed after every rung."""
    ARTIFACTS.mkdir(exist_ok=True)
    landscape = c_simple(theta)
    rec = {"theta": theta, "landscape_c_theta": landscape,
           "ceiling_one": CEILING_ONE, "record_H": H_MT,
           "headroom_one": HEADROOM_ONE, "rungs": [], "landscape_violations": []}
    if not quiet:
        print(f"theta = {theta}   c(theta) = {landscape:+.10f}", flush=True)
        print(f"{'X':>6} {'J':>5} {'eps':>9} {'value':>12} {'D':>10} "
              f"{'value-c':>11} {'ratio':>8} {'s':>7}", flush=True)
    for X, J in rungs:
        eps = 0.4 / X
        t0 = time.time()
        r = solve(theta=theta, J=J, X=X, eps=eps)
        dt = time.time() - t0
        if r is None:
            row = {"X": X, "J": J, "eps": eps, "value": None, "wall_seconds": round(dt, 1)}
            rec["rungs"].append(row)
            out_path.write_text(json.dumps(rec, indent=1) + "\n")
            print(f"{X:6.0f} {J:5d} {eps:9.2e}   infeasible", flush=True)
            continue
        excess = r["value"] - landscape
        row = {"X": X, "J": J, "eps": eps, "value": r["value"], "D": r["D"],
               "p": r["p"], "q": r["q"], "excess_over_landscape": excess,
               "ratio_to_headroom_one": excess / HEADROOM_ONE,
               "wall_seconds": round(dt, 1), "tau": r["tau"], "x_grid": r["x_grid"],
               "dual": r["dual"]}
        # The primal tau (X/h floats) is kept for the largest completed rung
        # only; the dual is kept at every rung. This holds a checkpoint near
        # 100 KB instead of 600 KB.
        for earlier in rec["rungs"]:
            earlier.pop("tau", None)
            earlier.pop("x_grid", None)
        rec["rungs"].append(row)
        if r["value"] < landscape - 1e-9:
            rec["landscape_violations"].append({"X": X, "J": J, "value": r["value"]})
        good = [(q["X"], q["value"]) for q in rec["rungs"] if q.get("value") is not None]
        fit = fit_free([g[0] for g in good], [g[1] for g in good])
        rec["fit"] = fit
        if fit is not None:
            rec["extrapolated_value"] = fit["a"]
            rec["extrapolated_excess_over_landscape"] = fit["a"] - landscape
            rec["extrapolated_ratio_to_headroom_one"] = (fit["a"] - landscape) / HEADROOM_ONE
        out_path.write_text(json.dumps(rec, indent=1) + "\n")
        if not quiet:
            print(f"{X:6.0f} {J:5d} {eps:9.2e} {r['value']:12.7f} {r['D']:10.6f} "
                  f"{excess:+11.7f} {excess / HEADROOM_ONE:8.4f} {dt:7.1f}", flush=True)
    if rec.get("fit"):
        f = rec["fit"]
        if not quiet:
            print(f"fit a + b X^(-p): a = {f['a']:.7f}  p = {f['p']:.3f}   "
                  f"a - c(theta) = {f['a'] - landscape:+.7f}   "
                  f"ratio = {(f['a'] - landscape) / HEADROOM_ONE:+.4f}", flush=True)
    if rec["landscape_violations"]:
        print(f"BUG: LP value below the landscape at theta = {theta}: "
              f"{rec['landscape_violations']}", file=sys.stderr)
    return rec


# ---------------------------------------------------------------------------
# Controls
# ---------------------------------------------------------------------------


def test_reduces_to_bandwidth_one(X=40.0, J=200):
    """At theta = 1 this solver and ``configuration_lp.solve`` are one LP."""
    sys.path.insert(0, str(HERE.parent / "frontier_math"))
    from configuration_lp import solve as solve_one
    a_here = alpha_grid(1.0, J)
    assert np.array_equal(a_here, np.arange(J + 1) / J), "grid differs at theta = 1"
    v0 = solve_one(J=J, X=X, eps=0.4 / X)["value"]
    v1 = solve(theta=1.0, J=J, X=X, eps=0.4 / X)["value"]
    return v0, v1, abs(v0 - v1)


def recorded_inband_ladder():
    """The bandwidth-one in-band ladder as ``outband_intake`` checkpointed it."""
    rows = {}
    for path in (INBAND_CONTROL, INBAND_CONTROL_LONG):
        if path.is_file():
            for row in json.loads(path.read_text()):
                rows[float(row["X"])] = row["value"]
    return rows


def control(rungs, write=True):
    """The theta = 1 control, printed in full and exit-coded.

    Three checks, in the order they can fail:
      1. the solver reduces to ``configuration_lp.solve`` at theta = 1;
      2. every rung reproduces the value ``outband_intake`` recorded for it;
      3. the extrapolated value is compared with BOTH the configuration
         ceiling 0.6818286874638 (the control the mission asks for) and the
         Montgomery-Taylor record 0.6725007036794116 (the limit
         ``frontier_math`` section 1 measured for this LP).  Which of the two
         it lands on, within the ladder's method error 0.0018, is the finding.
    """
    v0, v1, d = test_reduces_to_bandwidth_one()
    print(f"control 1, theta = 1 reduces to configuration_lp.solve at X=40, J=200: "
          f"{v0:.10f} vs {v1:.10f}, |diff| = {d:.2e}  "
          f"{'PASS' if d < 1e-9 else 'FAIL'}")
    ok = d < 1e-9
    out = ARTIFACTS / "ceiling-theta-1.00.json" if write else Path("/dev/null")
    rec = run_theta(1.0, rungs, out)
    recorded = recorded_inband_ladder()
    worst = 0.0
    for row in rec["rungs"]:
        if row.get("value") is None or row["X"] not in recorded:
            continue
        dd = abs(row["value"] - recorded[row["X"]])
        worst = max(worst, dd)
        print(f"control 2, X = {row['X']:.0f}: here {row['value']:.10f}, "
              f"outband_intake recorded {recorded[row['X']]:.10f}, |diff| = {dd:.2e}")
    print(f"control 2, worst |diff| against the recorded in-band ladder: {worst:.2e}  "
          f"{'PASS' if worst < 1e-6 else 'FAIL'}")
    ok = ok and worst < 1e-6
    fit = rec.get("fit")
    if fit is None:
        print("control 3: fewer than four rungs, no extrapolation")
        return ok
    a = fit["a"]
    gap_ceiling = a - CEILING_ONE
    gap_record = a - H_MT
    print(f"control 3, extrapolated theta = 1 value {a:.7f} (p = {fit['p']:.3f}):")
    print(f"   against the configuration ceiling {CEILING_ONE}: {gap_ceiling:+.7f}, "
          f"method error {METHOD_ERROR}: "
          f"{'PASS' if abs(gap_ceiling) <= METHOD_ERROR else 'FAIL, not reproduced'}")
    print(f"   against the Montgomery-Taylor record {H_MT}: {gap_record:+.7f}, "
          f"method error {METHOD_ERROR}: "
          f"{'PASS' if abs(gap_record) <= METHOD_ERROR else 'FAIL'}")
    if abs(gap_ceiling) > METHOD_ERROR and abs(gap_record) <= METHOD_ERROR:
        print("   reading: this LP is the Montgomery-Taylor dual at bandwidth one, as\n"
              "   frontier_math/RESULTS-frontier-math.md section 1 measured; it does not\n"
              "   reach the configuration ceiling, whose extra 0.0093 is configuration\n"
              "   realizability, which this LP does not encode.")
    rec["control"] = {"reduces_to_configuration_lp": d, "worst_diff_vs_recorded": worst,
                      "extrapolated": a, "gap_to_ceiling_one": gap_ceiling,
                      "gap_to_record": gap_record, "method_error": METHOD_ERROR,
                      "ceiling_reproduced": bool(abs(gap_ceiling) <= METHOD_ERROR),
                      "record_reproduced": bool(abs(gap_record) <= METHOD_ERROR)}
    if write:
        out.write_text(json.dumps(rec, indent=1) + "\n")
    return ok and not rec["landscape_violations"]


# ---------------------------------------------------------------------------
# Collect
# ---------------------------------------------------------------------------


def collect(paths):
    """One table over every per-theta JSON: the ceiling as a function of theta."""
    recs = []
    for p in paths:
        try:
            recs.append(json.loads(Path(p).read_text()))
        except (OSError, ValueError) as exc:
            print(f"skipping {p}: {exc}", file=sys.stderr)
    recs.sort(key=lambda r: -r["theta"])
    print(f"{'theta':>6} {'c(theta)':>11} {'last X':>7} {'last value':>11} "
          f"{'extrap a':>10} {'p':>6} {'a-c':>10} {'ratio':>8} {'theta^3':>8} {'viol':>5}")
    table = []
    for r in recs:
        good = [q for q in r["rungs"] if q.get("value") is not None]
        if not good:
            continue
        last = good[-1]
        fit = r.get("fit") or {}
        a = fit.get("a")
        c = r["landscape_c_theta"]
        exc = (a - c) if a is not None else None
        ratio = exc / HEADROOM_ONE if exc is not None else None
        row = {"theta": r["theta"], "c_theta": c, "last_X": last["X"],
               "last_value": last["value"], "extrapolated": a, "p": fit.get("p"),
               "extrapolated_excess": exc, "ratio_to_headroom_one": ratio,
               "theta_cubed": r["theta"] ** 3,
               "landscape_violations": len(r.get("landscape_violations", []))}
        table.append(row)
        print(f"{r['theta']:6.2f} {c:+11.7f} {last['X']:7.0f} {last['value']:11.7f} "
              f"{(a if a is not None else float('nan')):10.7f} "
              f"{(fit.get('p') if fit.get('p') is not None else float('nan')):6.2f} "
              f"{(exc if exc is not None else float('nan')):+10.6f} "
              f"{(ratio if ratio is not None else float('nan')):8.4f} "
              f"{r['theta'] ** 3:8.4f} {row['landscape_violations']:5d}")
    print("\nratio = (extrapolated value - c(theta)) / (0.6818286874638 - 0.6725007036794116);\n"
          "MISSION.md section 7 predicts headroom ~ theta^3 for the configuration ceiling.\n"
          "For this LP the theta = 1 control says what the column measures; read that first.")
    return table


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--theta", type=float, help="run the ladder at one bandwidth")
    ap.add_argument("--rungs", default=",".join(f"{int(X)}" for X, _ in DEFAULT_RUNGS),
                    help="comma-separated X values; J = 4X (matches the recorded ladder)")
    ap.add_argument("--control", action="store_true", help="the theta = 1 control")
    ap.add_argument("--collect", nargs="*", metavar="JSON",
                    help="print the table over per-theta JSON files (default: artifacts/)")
    ap.add_argument("--out", type=Path, help="checkpoint path for --theta")
    args = ap.parse_args(argv)

    # J follows the recorded ladder: 5X at X = 40, 4X from X = 80 on.
    known_J = {X: J for X, J in DEFAULT_RUNGS}
    rungs = [(float(X), known_J.get(float(X), 4 * int(X)))
             for X in args.rungs.split(",") if X.strip()]
    if args.control:
        ok = control(rungs)
        return 0 if ok else 1
    if args.theta is not None:
        out = args.out or (ARTIFACTS / f"ceiling-theta-{args.theta:.2f}.json")
        rec = run_theta(args.theta, rungs, out)
        return 1 if rec["landscape_violations"] else 0
    if args.collect is not None:
        paths = args.collect or sorted(ARTIFACTS.glob("ceiling-theta-*.json"))
        table = collect(paths)
        (ARTIFACTS / "ceiling-theta-table.json").write_text(json.dumps(table, indent=1) + "\n")
        return 0
    ap.print_help()
    return 2


if __name__ == "__main__":
    sys.exit(main())

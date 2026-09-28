"""The closest call: Lehmer's pair at t ~ 7005 under ball arithmetic.

Run from the repo root:

    .venv/bin/python hunts/lehmer_pair/probe.py

Writes ``results.json`` and ``lehmer_zoom.png`` next to this file.  See
``MISSION.md`` for what each experiment is for.

Vocabulary note (the probe discipline, ``tests/test_hunt_probe_discipline.py``):
the strongest word this hunt is allowed is *decided*, meaning an enclosure
``[lo, hi]`` of Z(t) from ``zeta.rigor`` came back with ``lo > 0`` or
``hi < 0``, an exact comparison on exact endpoints.  The reserved word for
that regime belongs to ``zeta/rigor.py`` and is deliberately absent from this
directory; the case log in ``hunts/README.md`` names it.  The instruments
used here are ``rigor.proven_sign`` and ``rigor.enclose_Z`` only, so the
grid scans below carry their own undecided-point accounting.  The
Davenport-Heilbronn rival scan and the figure samples are floats, the
accurate regime, a weaker claim.
"""

from __future__ import annotations

import json
import os
import sys
import time
from fractions import Fraction

import matplotlib

matplotlib.use("Agg")  # before pyplot, per repo rule
import matplotlib.pyplot as plt

from mpmath import mp, mpf, siegelz

from zeta import epstein, rigor

HERE = os.path.dirname(os.path.abspath(__file__))

# The pair, to 30 digits (mpmath.zetazero, cross-checked against docs/05).
GAMMA_6709 = "7005.06286617492058138034378359"
GAMMA_6710 = "7005.10056467264672156872043198"
# Interior extremum of Z between them (float scout, dps=30); the probe point
# below is the exact decimal rational named here, not "the extremum".
T_BUMP = Fraction("7005.0819")
T_LEFT = Fraction("7005.02")   # between gamma_6708 = 7004.04 and gamma_6709
T_RIGHT = Fraction("7005.15")  # between gamma_6710 and gamma_6711 = 7006.74

WINDOW = (Fraction("7004.9"), Fraction("7005.3"))  # contains the pair, nothing else

# The packaged grid scanner in zeta.rigor defaults to mean_spacing/20; at
# t ~ 7005 that is 0.0448, wider than the 0.0377 Lehmer gap.  Same policy,
# reimplemented over proven_sign so this probe owns its grid and its
# undecided-point accounting.
DEFAULT_STEP_AT_7005 = 0.8954856592858557 / 20.0

BACKENDS = rigor.available_backends()


def scan_signs(t0: Fraction, t1: Fraction, n: int, prec_bits: int, backend: str) -> dict:
    """Sign changes of Z on [t0, t1]: decided signs only, on n exact rationals.

    Consecutive decided signs that differ bracket a zero of Z, a zero of
    zeta on the critical line.  Undecided samples break the chain but are
    compared across, so the count is a lower bound either way.
    """
    changes, undecided, last = 0, [], 0
    started = time.time()
    for k in range(n):
        t = t0 + (t1 - t0) * Fraction(k, n - 1)
        s = rigor.proven_sign(t, prec_bits=prec_bits, backend=backend)
        if s == 0:
            undecided.append(float(t))
            continue
        if last != 0 and s != last:
            changes += 1
        last = s
    return {
        "changes": changes,
        "undecided_points": undecided,
        "every_sample_decided": not undecided,
        "n_samples": n,
        "wall_seconds": round(time.time() - started, 3),
    }


def experiment_three_point() -> dict:
    """Sign of Z at left flank / bump / right flank, every backend."""
    out = {"points": {"left": str(T_LEFT), "bump": str(T_BUMP), "right": str(T_RIGHT)}}
    for backend in BACKENDS:
        t0 = time.time()
        signs = [
            rigor.proven_sign(t, prec_bits=64, backend=backend)
            for t in (T_LEFT, T_BUMP, T_RIGHT)
        ]
        out[backend] = {
            "signs": signs,
            "pattern_is_minus_plus_minus": signs == [-1, 1, -1],
            "wall_seconds": round(time.time() - t0, 3),
        }
    return out


def experiment_window_scan() -> dict:
    """Dense sign-change count over the isolating window, every backend.

    Step 0.4/80 = 0.005, ~7x finer than the Lehmer gap.
    """
    out = {"t0": float(WINDOW[0]), "t1": float(WINDOW[1])}
    for backend in BACKENDS:
        out[backend] = scan_signs(WINDOW[0], WINDOW[1], 81, 64, backend)
    return out


def experiment_default_grid_lesion() -> dict:
    """Does the default-policy grid see the pair at all?

    The default step at this height (mean_spacing/20 ~ 0.045) is wider than
    the 0.0377 gap.  The grid is anchored to the window endpoints, so sliding
    the window changes the sample phase; sweep five phases spanning one
    default step.  Every window contains both pair zeros and no others, so
    the true count is 2 and the only possible grid answers are 2 (a sample
    landed inside the bump) or 0 (all samples missed it).  Flint only, this
    is a resolution measurement, not a backend cross-check.
    """
    n = int(0.4 / DEFAULT_STEP_AT_7005) + 2  # the packaged scanner's formula
    rows = []
    for k in range(5):
        d = Fraction(9 * k, 1000)  # 0, 0.009, ..., 0.036
        r = scan_signs(WINDOW[0] + d, WINDOW[1] + d, n, 64, "python-flint")
        rows.append({"shift": float(d), **{k: r[k] for k in ("n_samples", "changes", "every_sample_decided")}})
    return {
        "default_step_at_7005": round(DEFAULT_STEP_AT_7005, 5),
        "lehmer_gap": 0.0376985,
        "phases": rows,
        "hits": sum(1 for row in rows if row["changes"] == 2),
        "misses": sum(1 for row in rows if row["changes"] == 0),
    }


def _decision_cost(t: Fraction, backend: str) -> dict:
    """Smallest prec_bits in {32, 64, ..., 4096} that decides sign(Z(t))."""
    for prec in (32, 64, 128, 256, 512, 1024, 2048, 4096):
        lo, hi = rigor.enclose_Z(t, prec_bits=prec, backend=backend)
        if lo > 0 or hi < 0:
            return {
                "prec_bits": prec,
                "sign": 1 if lo > 0 else -1,
                "width": float(hi - lo),
            }
    return {"prec_bits": None, "sign": 0, "width": float(hi - lo)}


def experiment_precision_response() -> dict:
    """(a) enclosure width at the bump vs prec_bits, both backends;
    (b) decision cost as the probe point slides toward gamma_6709.

    A real quantity responds to precision (ROADMAP standing rule): widths
    must shrink roughly like 2^-prec while the enclosed value stays put, and
    the bits needed to decide a sign must grow as the point approaches the
    zero (|Z| ~ |Z'| * distance there, so each 1000x step toward the zero
    costs ~10 more bits of enclosure).
    """
    widths = {}
    for backend in BACKENDS:
        rows = []
        for prec in (32, 64, 128, 256):
            lo, hi = rigor.enclose_Z(T_BUMP, prec_bits=prec, backend=backend)
            rows.append(
                {
                    "prec_bits": prec,
                    "width": float(hi - lo),
                    "midpoint": float((lo + hi) / 2),
                    "sign_decided_at_this_prec": bool(lo > 0 or hi < 0),
                }
            )
        widths[backend] = rows

    gamma = Fraction(GAMMA_6709)
    approach = []
    for exp10 in (3, 6, 9, 12):
        t = gamma + Fraction(1, 10**exp10)
        row = {"distance": f"1e-{exp10}"}
        for backend in BACKENDS:
            row[backend] = _decision_cost(t, backend)
        approach.append(row)
    return {"bump_widths": widths, "approach_gamma_6709": approach}


def experiment_rival_dh() -> dict:
    """The bump that failed: Z_dh near the off-line zero 0.8085 + 85.6993i.

    tests/test_epstein.py pins that [85.2, 86.2] holds 2 strip zeros while
    Z_dh has 0 sign changes there.  Measure the closest approach to zero so
    the two bumps can sit side by side.  Float regime (accurate only),
    zeta.rigor speaks for zeta and nothing else.
    """
    with mp.workdps(25):
        ts = [mpf("85.2") + mpf(k) * mpf("0.01") for k in range(101)]
        zs = [epstein.Z_dh(t, dps=25) for t in ts]
        signs = {int(mp.sign(z)) for z in zs}
        k_min = min(range(101), key=lambda k: abs(zs[k]))
        # ternary refinement of the extremum around the minimal sample
        a, b = ts[max(0, k_min - 1)], ts[min(100, k_min + 1)]
        for _ in range(40):
            m1, m2 = a + (b - a) / 3, b - (b - a) / 3
            if abs(epstein.Z_dh(m1, dps=25)) < abs(epstein.Z_dh(m2, dps=25)):
                b = m2
            else:
                a = m1
        t_star = (a + b) / 2
        z_star = epstein.Z_dh(t_star, dps=25)
    return {
        "window": [85.2, 86.2],
        "grid_signs_seen": sorted(signs),
        "sign_changes_on_grid": sum(
            1 for u, v in zip(zs, zs[1:]) if mp.sign(u) != mp.sign(v)
        ),
        "closest_approach_t": float(t_star),
        "closest_approach_Z": float(z_star),
        "offline_zero": "0.80851718245663738555 + 85.699348485377592171929i",
        "note": "float regime; the pinned strip-vs-line count is in tests/test_epstein.py",
    }


def make_figure(results: dict) -> None:
    """Two bumps, one figure: the one that crossed and the one that did not."""
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(11, 4.2))

    with mp.workdps(20):
        ts = [7004.7 + k * 0.002 for k in range(401)]
        zs = [float(siegelz(t)) for t in ts]
    ax1.plot(ts, zs, lw=1.0, color="tab:blue")
    ax1.axhline(0.0, color="k", lw=0.6)
    ax1.set_title("Hardy Z near the Lehmer pair, the bump crosses", fontsize=10)
    ax1.set_xlabel("t")
    ax1.set_ylabel("Z(t)")
    ax1.annotate(
        "peak +0.00397\nenclosure lo > 0 at 64 bits\n(both backends)",
        xy=(7005.082, 0.01),
        xytext=(7005.16, -0.55),
        fontsize=8,
        arrowprops={"arrowstyle": "->", "lw": 0.8},
    )
    axins = ax1.inset_axes([0.5, 0.06, 0.46, 0.42])
    with mp.workdps(20):
        tz = [7005.04 + k * 0.0005 for k in range(161)]
        zz = [float(siegelz(t)) for t in tz]
    axins.plot(tz, zz, lw=1.0, color="tab:blue")
    axins.axhline(0.0, color="k", lw=0.6)
    axins.set_xlim(7005.04, 7005.12)
    axins.set_ylim(-0.012, 0.007)
    axins.set_title("gap 0.0377 (mean spacing 0.895)", fontsize=7)
    axins.tick_params(labelsize=6)

    with mp.workdps(20):
        td = [85.2 + k * 0.01 for k in range(101)]
        zd = [float(epstein.Z_dh(t, dps=20)) for t in td]
    ax2.plot(td, zd, lw=1.0, color="tab:red")
    ax2.axhline(0.0, color="k", lw=0.6)
    ax2.set_title("Davenport–Heilbronn Z near 85.70, the bump fails", fontsize=10)
    ax2.set_xlabel("t")
    r = results["rival_dh"]
    ax2.annotate(
        f"closest approach {r['closest_approach_Z']:+.4f}\n2 strip zeros, 0 crossings",
        xy=(r["closest_approach_t"], r["closest_approach_Z"]),
        xytext=(85.62, -0.85),
        fontsize=8,
        arrowprops={"arrowstyle": "->", "lw": 0.8},
    )

    fig.suptitle("The closest call and the counterexample: crossing is the whole game", y=1.02)
    fig.tight_layout()
    fig.savefig(os.path.join(HERE, "lehmer_zoom.png"), dpi=150, bbox_inches="tight")
    plt.close(fig)


def main() -> int:
    results = {
        "backends": BACKENDS,
        "pair": {"gamma_6709": GAMMA_6709, "gamma_6710": GAMMA_6710,
                 "gap": 0.0376984977261402, "local_mean_spacing": 0.8954856592858557},
    }
    for name, fn in (
        ("three_point", experiment_three_point),
        ("window_scan", experiment_window_scan),
        ("default_grid_lesion", experiment_default_grid_lesion),
        ("precision_response", experiment_precision_response),
        ("rival_dh", experiment_rival_dh),
    ):
        t0 = time.time()
        results[name] = fn()
        print(f"[{name}] done in {time.time() - t0:.1f}s", flush=True)

    make_figure(results)
    with open(os.path.join(HERE, "results.json"), "w") as fh:
        json.dump(results, fh, indent=2)
    print("wrote results.json and lehmer_zoom.png")
    return 0


if __name__ == "__main__":
    sys.exit(main())

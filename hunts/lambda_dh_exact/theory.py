"""Theory-phase checks for hunt #52 (lambda_dh_exact).

Everything here is float grade: numpy exact-polynomial heat flow, scipy
quadrature, mpmath nowhere. No enclosure claims are made and none of the
strong words are used. Run from the repo root:

    .venv/bin/python hunts/lambda_dh_exact/theory.py           # ~3 min
    .venv/bin/python hunts/lambda_dh_exact/theory.py --full    # adds the grids

Stages, matching MISSION.md:
  1  isolated-pair law t* = y0^2/2                      (section 3)
  2  crowding law (*) against exact flow, with a t=0 gate (section 4.7)
  3  no-creation sweep                                   (section 2)
  4  density formula h(T) = 2 pi / log(5T/(2 pi))        (section 4.5)
  5  one-parameter calibration on nine landings, holdout (section 4.6)
  6  the collapse criterion: crossovers, ceiling, sup    (section 5)
  7  the delay mechanism: crowding that runs the other way (section 5.3)
"""
from __future__ import annotations

import json
import sys
from math import cos, cosh, factorial, log, pi, sinh
from pathlib import Path

import numpy as np
from scipy.integrate import quad
from scipy.optimize import brentq

_ROOT = Path(__file__).resolve().parents[2]
if str(_ROOT) not in sys.path:
    sys.path.insert(0, str(_ROOT))

FULL = "--full" in sys.argv

# inherited from hunts/lambda_dh_bounds/STRIP2.md, decided there
DELTA = 0.62036249819
UPPER = DELTA ** 2 / 2                      # 0.19242481458...
FLOOR = 0.0576518                           # best measured landing, flow_repair pair 5
DBAR = 1.4284                               # local-gap parameter, fitted in stage 5

# flow_repair NOTES.md section 1: gamma, y0, measured t*
NINE = [
    (85.6993, 0.3085172, 0.04412634450), (114.1633, 0.1508270, 0.01112958794),
    (166.4793, 0.0743505, 0.00274784849), (176.7025, 0.2242763, 0.02366473172),
    (240.4046, 0.3695261, 0.05765184035), (320.8765, 0.3195496, 0.04468146893),
    (331.0503, 0.2682231, 0.03217819397), (366.6409, 0.1285081, 0.00803041920),
    (411.7967, 0.3158737, 0.04265328332),
]
# lambda_dh_bounds/census_results.json, ode_landing_pair_531: the holdout
HOLDOUT = (531.27972689652, 0.34695380309204904, 0.05033975468118168)

RESULTS: dict = {}


# --------------------------------------------------------------------------
# exact polynomial heat flow: p_t = exp(-t d^2/dz^2) p_0 = sum_k (-t)^k/k! p^{(2k)}
# --------------------------------------------------------------------------
def heat_evolve(p, t):
    p = np.asarray(p, dtype=float)
    out = np.zeros_like(p)
    term = p.copy()
    k = 0
    while term.size and np.any(term != 0) and k <= p.size:
        out = out + np.concatenate([np.zeros(p.size - term.size), term]) * ((-t) ** k / factorial(k))
        term = np.polyder(term, 2)
        k += 1
    return out


def admissible(base, roots, tol=1e-6):
    """The gate. float64 root-finding fails silently above degree ~30 with
    closely spaced roots; it once reported 14 nonreal roots where there are 2.
    """
    r = np.roots(base)
    want = np.asarray(roots, dtype=complex)
    n_nonreal = int(np.sum(np.abs(want.imag) > 1e-12))
    return (abs(np.max(np.abs(r.imag)) - np.max(np.abs(want.imag))) < tol
            and int(np.sum(np.abs(r.imag) > 1e-8)) == n_nonreal)


def max_imag(base, t, half=None):
    r = np.roots(heat_evolve(base, t))
    if half is not None:
        r = r[np.abs(r.real) < half]
        if r.size == 0:
            return 0.0
    return float(np.max(np.abs(r.imag)))


def landing(base, t_hi, half=None, tol=1e-12):
    lo, hi = 0.0, t_hi
    if max_imag(base, hi, half) > 1e-9:
        return None
    while hi - lo > tol:
        m = 0.5 * (lo + hi)
        if max_imag(base, m, half) > 1e-9:
            lo = m
        else:
            hi = m
    return 0.5 * (lo + hi)


def n_real(base, t, tol=1e-8):
    return int(np.sum(np.abs(np.roots(heat_evolve(base, t)).imag) < tol))


# --------------------------------------------------------------------------
# the landing integral (*) and its two closed forms
# --------------------------------------------------------------------------
def t_star_sum(y0, neighbours, x=0.0):
    """(*) with an explicit neighbour list."""
    S = lambda y: sum(1.0 / ((x - a) ** 2 + y * y) for a in neighbours)
    return quad(lambda y: y / (1.0 + 2.0 * y * y * S(y)), 0.0, y0, limit=300)[0]


def t_star_lattice(y0, h, theta=0.5):
    """Infinite lattice, spacing h, pair at phase theta. Uses
    sum_k 1/((k+theta)^2 + c^2) = (pi/c) sinh(2 pi c)/(cosh(2 pi c) - cos(2 pi theta)).
    """
    def f(y):
        al = 2 * pi * y / h
        return y / (1.0 + al * sinh(al) / (cosh(al) - cos(2 * pi * theta)))
    return quad(f, 0.0, y0, limit=300)[0]


def t_star_continuum(y0, rho):
    """The deep regime: dy/dt = -1/y - 2 pi rho."""
    V = 2 * pi * rho * y0
    return (V - np.log1p(V)) / (2 * pi * rho) ** 2


def L(gamma):
    return log(5 * gamma / (2 * pi))


def h_dh(gamma):
    """Mean gap of the strip zeros of F near height gamma, derived in
    MISSION.md section 4.5 from the gamma factor.
    """
    return 2 * pi / L(gamma)


def t_star_gap(y0, gamma, dfac=DBAR, K=6000):
    """The calibrated model: a local gap of half-width dfac*h, lattice beyond."""
    h = h_dh(gamma)
    a = dfac * h + np.arange(K) * h
    S = lambda y: float(np.sum(2.0 / (a * a + y * y)))
    return quad(lambda y: y / (1.0 + 2.0 * y * y * S(y)), 0.0, y0, limit=300)[0]


# --------------------------------------------------------------------------
def stage1():
    print("=== 1. isolated conjugate pair: t* = y0^2/2 (MISSION section 3) ===")
    rows = []
    for y0 in (0.2, 0.5, 0.9, 0.620362):
        base = np.poly([1j * y0, -1j * y0]).real
        t = landing(base, y0 * y0 / 2 + 1e-9)
        rows.append(dict(y0=y0, naive=y0 * y0 / 2, landing=t, diff=t - y0 * y0 / 2))
        print(f"   y0={y0:<9} y0^2/2={y0*y0/2:.12f}  landing={t:.12f}  diff={t-y0*y0/2:+.2e}")
    RESULTS["isolated_pair"] = rows


def stage2():
    print("\n=== 2. crowding: exact flow vs the frozen-neighbour integral (section 4.7) ===")
    print(f"{'h':>5} {'y0':>5} {'deg':>4} | {'naive':>11} {'exact':>12} {'frozen (*)':>12} {'exact/(*)':>9}")
    rows = []
    cases = [(1.0, 12, 0.15), (1.0, 12, 0.3), (1.0, 12, 0.6), (1.0, 12, 0.9),
             (0.7, 14, 0.6), (0.5, 14, 0.6), (0.35, 14, 0.6)]
    if FULL:
        cases += [(2.0, 8, 0.6), (0.5, 14, 0.3), (1.5, 10, 0.9)]
    for h, N, y0 in cases:
        nb = [(k + 0.5) * h for k in range(-N, N)]
        roots = [1j * y0, -1j * y0] + nb
        base = np.poly(np.array(roots, dtype=complex)).real
        if not admissible(base, roots):
            print(f"{h:>5} {y0:>5} {base.size-1:>4} | INADMISSIBLE at t=0 (float64 root noise)")
            continue
        te = landing(base, y0 * y0 / 2 + 1e-9, half=h)
        tm = t_star_sum(y0, nb)
        rows.append(dict(h=h, N=N, y0=y0, naive=y0 * y0 / 2, exact=te, frozen=tm, ratio=te / tm))
        print(f"{h:>5} {y0:>5} {base.size-1:>4} | {y0*y0/2:>11.8f} {te:>12.8f} {tm:>12.8f} {te/tm:>9.4f}")
    RESULTS["crowding"] = rows
    # the lesion, kept because it fired silently
    y0, h, N = 0.6, 0.5, 25
    nb = [(k + 0.5) * h for k in range(-N, N)]
    roots = [1j * y0, -1j * y0] + nb
    base = np.poly(np.array(roots, dtype=complex)).real
    r = np.roots(base)
    print(f"   lesion, degree {base.size-1}: gate says admissible={admissible(base, roots)}; "
          f"max|Im| at t=0 is {np.max(np.abs(r.imag)):.4f} where it should be {y0}, and "
          f"{int(np.sum(np.abs(r.imag)>1e-8))} roots read nonreal where 2 are")
    RESULTS["lesion_degree52"] = dict(degree=int(base.size - 1),
                                      max_imag_at_zero=float(np.max(np.abs(r.imag))),
                                      expected=y0,
                                      n_nonreal_read=int(np.sum(np.abs(r.imag) > 1e-8)))


def stage3():
    print("\n=== 3. no creation: can forward flow drive two real zeros off the axis? (section 2) ===")
    rng = np.random.default_rng(7)
    admitted = fails = 0
    n_trials = 400 if not FULL else 1200
    for _ in range(n_trials):
        n = int(rng.integers(2, 7))
        reals = np.sort(rng.uniform(-3, 3, size=n))
        if n > 1 and np.min(np.diff(reals)) < 1e-3:
            continue
        u, v = rng.uniform(-1, 1), rng.uniform(0.5, 3.0)
        roots = list(reals.astype(complex)) + [u + 1j * v, u - 1j * v]
        base = np.poly(np.array(roots, dtype=complex)).real
        if not admissible(base, roots):
            continue
        admitted += 1
        n0 = n_real(base, 0.0)
        if min(n_real(base, t) for t in np.linspace(0, 3.0, 121)) < n0:
            fails += 1
    print(f"   admissible configurations: {admitted}/{n_trials};  real-zero-count decreases: {fails}")
    RESULTS["no_creation"] = dict(trials=n_trials, admitted=admitted, decreases=fails)
    # the exactly solvable control
    print("   control, (z^2-a^2)(z^2+Y^2): landing is the positive root of "
          "12t^2 - 2(Y^2-a^2)t - a^2 Y^2 = 0")
    ctl = []
    for a, Y in ((0.1, 1.0), (0.05, 1.2), (0.3, 0.8)):
        closed = ((Y * Y - a * a) + np.sqrt((Y * Y - a * a) ** 2 + 12 * a * a * Y * Y)) / 12.0
        base = np.poly([a, -a, 1j * Y, -1j * Y]).real
        te = landing(base, Y * Y / 2 + 1e-9)
        ctl.append(dict(a=a, Y=Y, closed_form=closed, measured=te, n_real_after=n_real(base, te * 1.01)))
        print(f"     a={a} Y={Y}: closed form {closed:.9f}  measured {te:.9f}  "
              f"#real just after = {n_real(base, te*1.01)}")
    RESULTS["quartic_control"] = ctl


def stage4():
    print("\n=== 4. the density, derived then checked (section 4.5) ===")
    checks = [("flow_repair pair 1, +-40 at gamma 85.7, 53 strip zeros", 80 / 53, h_dh(85.6993)),
              ("lambda_dh_bounds census (412,600), 179 strip zeros", 188 / 179, h_dh(506.0))]
    for name, measured, model in checks:
        print(f"   {name}: gap {measured:.5f} vs h {model:.5f}  ({abs(measured/model-1):.2%})")
    RESULTS["density"] = [dict(what=n, measured=m, formula=f, rel=abs(m / f - 1)) for n, m, f in checks]


def stage5():
    print("\n=== 5. calibration on the nine, holdout on the tenth (section 4.6) ===")
    ds = []
    for g, y0, tm in NINE:
        h = h_dh(g)
        d = brentq(lambda dd: t_star_sum(y0, [dd + k * h for k in range(4000)] +
                                         [-(dd + k * h) for k in range(4000)]) - tm,
                   0.05 * h, 20 * h, xtol=1e-10)
        ds.append(d / h)
        print(f"   gamma={g:>9.4f} y0={y0:.7f} h={h:.4f}  d/h fitted = {d/h:.4f}")
    ds = np.array(ds)
    dbar = float(ds.mean())
    print(f"   d/h: mean {dbar:.4f}  sd {ds.std():.4f}  range [{ds.min():.4f}, {ds.max():.4f}]"
          f"   (MISSION.md uses {DBAR})")
    res = np.array([t_star_gap(y0, g) / tm for g, y0, tm in NINE])
    print(f"   held at {DBAR}: pred/meas in [{res.min():.4f}, {res.max():.4f}], "
          f"rms deviation {np.sqrt(np.mean((res-1)**2)):.4f}")
    g, y0, tm = HOLDOUT
    tp = t_star_gap(y0, g)
    print(f"   HOLDOUT gamma={g:.5f} y0={y0:.8f}: measured {tm:.9f}  model {tp:.9f}  "
          f"pred/meas {tp/tm:.4f}")
    RESULTS["calibration"] = dict(d_over_h=list(map(float, ds)), mean=dbar, sd=float(ds.std()),
                                  training_ratio=list(map(float, res)),
                                  holdout=dict(gamma=g, y0=y0, measured=tm, model=tp, ratio=tp / tm))


def stage6():
    print("\n=== 6. the collapse criterion (section 5) ===")
    print(f"   Delta = {DELTA}, Delta^2/2 = {UPPER:.14f}")
    print("   C1 crossovers: above this height no pair at any depth up to Delta beats the floor")
    cross = {}
    for floor in (FLOOR, 0.08, 0.10, 0.12):
        gc = brentq(lambda lg: t_star_gap(DELTA, 10 ** lg) - floor, 1.0, 40.0, xtol=1e-6)
        cross[floor] = 10 ** gc
        print(f"     floor {floor:<10.7f}: gamma = {10**gc:.4g}")
    gmin = 85.6993
    ceil = t_star_gap(DELTA, gmin)
    print(f"   C2 ceiling: t*(Delta, gamma={gmin}) = {ceil:.8f} = {ceil/UPPER:.2%} of Delta^2/2")
    print("   C3 sup, under y_max(gamma) = Delta (1 - c_p / L(gamma)^p) anchored at y_max(600)=0.3695261")
    sup = {}
    grid = (600, 3e3, 1e4, 1e5, 1e6, 1e8, 1e12, 1e20)
    for p in (0.5, 1.0, 1.5, 2.0):
        cp = (1 - 0.3695261 / DELTA) * L(600) ** p
        rows = [(g, DELTA * (1 - cp / L(g) ** p)) for g in grid]
        rows = [(g, y, t_star_gap(y, g)) for g, y in rows if y > 0]
        best = max(rows, key=lambda r: r[2])
        sup[p] = dict(y_max_1e4=DELTA * (1 - cp / L(1e4) ** p), sup=best[2],
                      at_gamma=best[0], at_y0=best[1], consistent=best[2] >= 36 / 625)
        print(f"     p={p}: y_max(1e4)={sup[p]['y_max_1e4']:.4f}  sup t*={best[2]:.6f} "
              f"at gamma={best[0]:.3g}, y0={best[1]:.4f}  wide {4*best[2]:.6f}"
              f"  consistent with 36/625: {best[2] >= 36/625}")
    RESULTS["criterion"] = dict(crossovers=cross, ceiling=ceil, ceiling_fraction=ceil / UPPER, sup=sup)


def stage7():
    print("\n=== 7. the delay mechanism: crowding that runs the other way (section 5.3) ===")
    rng = np.random.default_rng(11)
    over = tot = 0
    n = 300 if not FULL else 900
    for _ in range(n):
        x, v, y = rng.uniform(0, 1.5), rng.uniform(0.1, DELTA), rng.uniform(0.1, DELTA)
        roots = [x + 1j * v, x - 1j * v, -x + 1j * y, -x - 1j * y]
        base = np.poly(np.array(roots, dtype=complex)).real
        if not admissible(base, roots):
            continue
        ts = landing(base, UPPER + 1e-6, half=None if x == 0 else 10.0)
        # track only the pair near -x
        def pim(t):
            r = np.roots(heat_evolve(base, t))
            loc = r[r.real < 0]
            return float(np.max(np.abs(loc.imag))) if loc.size else 0.0
        lo, hi = 0.0, UPPER + 1e-6
        if pim(hi) > 1e-9:
            continue
        tot += 1
        while hi - lo > 1e-10:
            m = 0.5 * (lo + hi)
            if pim(m) > 1e-9:
                lo = m
            else:
                hi = m
        if 0.5 * (lo + hi) > y * y / 2 + 1e-9:
            over += 1
    print(f"   of {tot} admissible two-pair configurations, the tracked pair landed LATER "
          f"than its own y0^2/2 in {over}")
    # two deep pairs, separated: how close to Delta^2/2 can the last landing get
    best = (0.0, None)
    for xx in np.linspace(0.0, 1.5, 16 if not FULL else 31):
        roots = [xx + 1j * DELTA, xx - 1j * DELTA, -xx + 1j * DELTA, -xx - 1j * DELTA]
        base = np.poly(np.array(roots, dtype=complex)).real
        t = landing(base, UPPER + 1e-6)
        if t is not None and t > best[0]:
            best = (t, xx)
    print(f"   two pairs both at depth Delta, separation 2x={2*best[1]:.4f}: last landing "
          f"{best[0]:.8f} = {best[0]/UPPER:.2%} of Delta^2/2")
    RESULTS["delay"] = dict(sampled=tot, later_than_naive=over,
                            two_deep_last_landing=best[0], separation=2 * best[1],
                            fraction_of_upper=best[0] / UPPER)


if __name__ == "__main__":
    stage1(); stage2(); stage3(); stage4(); stage5(); stage6(); stage7()
    out = Path(__file__).with_name("theory_results.json")
    out.write_text(json.dumps(RESULTS, indent=1))
    print(f"\nwrote {out}")

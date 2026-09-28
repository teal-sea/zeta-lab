"""An adversarial search against the MT-window retention trade.

WHAT IS UNDER ATTACK.  For one off-line pair at depth ``y``, sitting at
grid position ``t = 0``, an on-line configuration ``X = {x_1, ..., x_n}``
(multiplicity allowed) extracts

    D(X)  = sum_i (-2 W(x_i, y))                       [damage]
    R(X)  = sum_{i != j} omega2(x_i - x_j)             [internal mass]

and the pair's own retained slack is ``8 sigma^2 + 8 sigma^4``.  The trade
asserted by `mt_chain.py` (from a crude greedy) is

    sup_X [ D(X) - (1 - theta) R(X) ]  <=  slack(y),

reported "inside by 4.7x even at theta = 1" at ``y = 0.49``.  This module
searches much harder than that greedy did, and reports what it finds.

WHAT WAS TRIED
--------------
1. **Exhaustive small n** (`exhaustive_small_n`, `grid_search_small_n`):
   multi-start L-BFGS-B on the exact objective with analytic gradients for
   n = 1..6, plus a brute grid for n <= 3 with local polish.
2. **Band-lattice families** (`band_lattice_family`): the damage bands of
   ``-2W(., y)`` on both sides, k = 1..K, with sub-band phase offsets, plus
   every-other-band, top-K and pseudo-random irregular subsets.
3. **Multiplicity and near-coincidence** (`multiplicity_probe`): m zeros
   stacked on one band, and m zeros spread by s across a band, s swept.
4. **Free greedy on a fine grid** (`fine_greedy`): marginal-gain greedy over
   a 0.05-grid out to |g| = 200, which subsumes the `mt_chain` greedy.
5. **Minimum-separation harvest** (`spacing_harvest`, `critical_spacing`):
   the theta = 1 reading in which the internal charge is switched off but
   on-line zeros are required to be at least ``d`` apart.
6. **Depth sweep** over 12 depths and **theta sweep** by bisection on the
   charge coefficient ``c = 1 - theta`` (`depth_sweep`, `theta_star`).
7. **Controls** (`lesion_no_repulsion`, `naive_relaxation_is_vacuous`,
   `precision_ladder`): a planted fault the search must detect, the natural
   concave relaxation shown to be worthless, and a discretization ladder on
   the worst case found.

WHAT WAS FOUND
--------------
**One break, and it is a break of the literal wording, not of the
mechanism.**  At ``theta = 1`` the internal charge is multiplied by zero, so
nothing bounds ``D``: m zeros stacked on the top damage band give
``D = m * f_max -> infinity`` at no cost.  The statement "inside by 4.7x
even at theta = 1" is therefore about the configuration selected while
charging ``R`` at full weight (c = 1) and then reporting ``D`` on it, the
`mt_chain` convention, and the number reproduces (D = 0.02976 vs slack
0.14234 at y = 0.49, i.e. 0.2091 slack = 4.78x inside).  Read literally,
with the charge switched off, ``sup_X D`` is unbounded.  The honest repair
is a minimum-separation hypothesis: with on-line zeros at least ``d`` apart
the sup is finite, measured at 0.317 * slack for every ``d >= 1`` grid unit
(one zero per band is then forced; 0.328 at d = 0.5), and crossing the
slack only below ``d* = 0.200`` grid units = 0.0318 mean gaps at y = 0.49
(``d* = 0.120`` = 0.0191 mean gaps at y = 0.3).

**The mechanism survives everything else tried.**  With the charge on:

* at c = 1 the best configuration found at every depth is the two-zero
  band pair ``x = +-6.8558`` (y = 0.49), value 0.026759 = 0.1880 * slack.
  No coordinated placement with n = 3..6, no band lattice, no subset and no
  multiplicity beat it; the n = 3..6 optima keep the same pair and park the
  extra zeros on far bands (+-31.7, +-38.1) at a net loss, so they decay
  back to n = 2 (0.1863, 0.1851, 0.1764, 0.1627 slack for n = 3, 4, 5, 6).
* the free one-zero-per-band harvest, the whole damage envelope, taken at
  zero charge, is 0.325 to 0.335 of the slack across 0.02 <= y <= 0.49,
  worst (0.3348) at y = 0.49.  So even a charge-free adversary restricted
  to simple, band-separated zeros stays 2.99x inside at every depth probed.
* the largest theta for which the searched sup stays under the slack is
  ``theta* = 0.99900`` (c* = 1.00e-3) at y = 0.49 and rises towards 1 as
  y -> 0 (c* = 8.6e-9 at y = 0.02).

**The shallow end is safer, not tighter.**  sigma^2 -> 0 there and the
slack vanishes like sigma^2, but the damage vanishes at the *same* rate
(both are O(sinh(y/2)^2) to leading order), so ``D_bands / slack`` is
nearly depth-free (0.3252 at y = 0.02 vs 0.3348 at y = 0.49), while the
multiplicity term, being quadratic in the damage, vanishes *faster*, hence
theta* -> 1 as y -> 0.

WHY THE ADVERSARY FAILS (three measured reasons)
------------------------------------------------
1. **Near-miss, not coincidence.**  The damage bands sit almost exactly on
   the zeros of ``omega2`` (band peaks 6.907 / 12.895 / 19.070 at y = 0.49
   against omega2 zeros 7.0422 / 12.9509 / 19.1060), which is why band
   riding is cheap at all, but the miss is real and grows with depth
   (0.135 at y = 0.49 vs 0.052 at y = 0.3), leaving a small residual charge
   at every band pair (omega2 = 0.0019 at the +-band separation 13.81,
   0.011 to 0.023 at adjacent-band separations).
2. **The repulsion is far wider than the damage.**  omega2 is flat near the
   origin (omega2(1) = 0.930, omega2(2) = 0.744, omega2(4) = 0.273) while a
   damage band is only ~1 grid unit wide.  A second zero placed inside a
   band therefore pays essentially the full 2c and collects at most
   f_max = 0.0151, self-defeating by a factor ~130 at c = 1.  Splitting the
   stack does not help: moving apart by 1 unit saves 7% of the charge and
   loses most of the damage.
3. **The harvest is bounded and the charge is not.**  Band damage decays
   like 1/g^2, so the whole two-sided harvest converges to 0.335 * slack,
   while the pairwise charge over K bands grows superlinearly in K
   (adjacent-band omega2 tends to ~0.0113, not to 0).  Beyond n = 2 the
   marginal band is already unprofitable at c = 1.

STATUS.  Every number here is a **measured lower bound on the adversary's
power** obtained by search over the families listed above, not a proof of
safety: no configuration-free bound is established by this module, and the
named T1 gap (a band-lattice counting dual with point-separation charges)
is untouched.  The natural concave relaxation that would give an upper
bound is measured vacuous (`naive_relaxation_is_vacuous`): fractional
multiplicities make the self-charge negative and the relaxed optimum
overshoots the slack by 66x at c = 1 on a unit grid (and grows with the
grid refinement, so it is not a discretization artefact to be tuned away).
Nothing here is evidence for or against the Riemann Hypothesis.

Run ``.venv/bin/python hunts/frontier_math/mt_adversary.py`` (~8 min).
"""

from __future__ import annotations

import math
import sys
from pathlib import Path

import numpy as np
from scipy.optimize import minimize
from scipy.signal import find_peaks

sys.path.insert(0, str(Path(__file__).resolve().parent))
from mt_chain import MEAN_GAP, MTChain, A, S2, phi2mt  # noqa: E402

MT = MTChain()

#: the twelve probe depths
DEPTHS = (0.02, 0.05, 0.08, 0.12, 0.16, 0.20, 0.25, 0.30, 0.35, 0.40, 0.45, 0.49)


# ---------------------------------------------------------------------------
# exact objective and its gradient
# ---------------------------------------------------------------------------


def _scp(z):
    """d/dz of sc(z) = 2 sin(z/2)/z."""
    z = np.asarray(z, complex)
    small = np.abs(z) < 1e-9
    zs = np.where(small, 1.0, z)
    out = np.cos(zs / 2) / zs - 2 * np.sin(zs / 2) / zs**2
    return np.where(small, 0.0, out)


def dphi2mt(z):
    """d/dz Phi2 at the MT window."""
    z = np.asarray(z, complex)
    return 0.5 * _scp(z) + 0.25 * (_scp(z + 2 * S2) + _scp(z - 2 * S2))


def damage(x, y: float):
    """f(x) = -2 W(x, y): what one on-line zero at x extracts from the pair."""
    return -2 * MT.W(np.asarray(x, float), y)


def d_damage(x, y: float):
    x = np.asarray(x, float)
    v = phi2mt(x + 1j * y)
    dv = dphi2mt(x + 1j * y)
    dW = 4 * (v.real * dv.real - v.imag * dv.imag) / A**2
    return -2 * dW


def omega2(r):
    return MT.omega2(np.asarray(r, float).astype(complex)).real


def d_omega2(r):
    r = np.asarray(r, float)
    P = phi2mt(r.astype(complex)).real
    dP = dphi2mt(r.astype(complex)).real
    return 2 * P * dP / A**2


def objective(xs, y: float, c: float):
    """(value, D, R) for the configuration xs at depth y and charge c = 1-theta."""
    xs = np.asarray(xs, float)
    if xs.size == 0:
        return 0.0, 0.0, 0.0
    D = float(np.sum(damage(xs, y)))
    O = omega2(xs[:, None] - xs[None, :])
    R = float(O.sum() - xs.size)  # omega2(0) = 1 on the diagonal
    return D - c * R, D, R


def _neg_objective_grad(xs, y: float, c: float):
    xs = np.asarray(xs, float)
    val = objective(xs, y, c)[0]
    d = xs[:, None] - xs[None, :]
    Od = d_omega2(d)
    np.fill_diagonal(Od, 0.0)
    grad = d_damage(xs, y) - 2 * c * Od.sum(axis=1)
    return -val, -grad


def slack(y: float) -> float:
    return MT.slack(y)


# ---------------------------------------------------------------------------
# the damage bands
# ---------------------------------------------------------------------------


def band_table(y: float, G: float = 400.0, step: float = 0.002):
    """Positions and heights of the positive-damage bands on g > 0."""
    gs = np.arange(step, G, step)
    f = damage(gs, y)
    pk, _ = find_peaks(f)
    pk = pk[f[pk] > 0]
    return gs[pk], f[pk]


def omega2_zeros(n: int = 8):
    """The real zeros of Phi2 (equivalently of omega2), for the near-miss table."""
    from scipy.optimize import brentq

    p = lambda r: float(phi2mt(np.array([r], complex))[0].real)  # noqa: E731
    rs = np.arange(0.01, 60.0, 0.001)
    v = phi2mt(rs.astype(complex)).real
    sg = np.where(np.sign(v[:-1]) != np.sign(v[1:]))[0]
    return np.array([brentq(p, rs[i], rs[i + 1]) for i in sg[:n]])


def near_miss_table(y: float, n: int = 5):
    """How far each damage band sits from the omega2 zero it rides."""
    b, _ = band_table(y)
    z = omega2_zeros(n)
    return [(float(b[k]), float(z[k]), float(z[k] - b[k]),
             float(omega2(np.array([b[k]]))[0])) for k in range(min(n, len(b)))]


# ---------------------------------------------------------------------------
# 1. exhaustive small n
# ---------------------------------------------------------------------------


def exhaustive_small_n(y: float, c: float, nmax: int = 6, restarts: int = 120,
                       spread: float = 40.0, seed: int = 20260812):
    """Multi-start L-BFGS-B on the exact objective, n = 1..nmax.

    Seeds: random uniform draws plus band-peak seeds (with and without sign
    mirroring), so a coordinated placement is not missed for want of a start.
    """
    rng = np.random.default_rng(seed)
    bands, _ = band_table(y)
    bands = bands[bands < spread]
    pool = np.concatenate([-bands[::-1], bands]) if bands.size else np.array([0.0])
    out = {}
    for n in range(1, nmax + 1):
        best, bx = -math.inf, None
        starts = [rng.uniform(-spread, spread, n) for _ in range(restarts)]
        for _ in range(restarts // 2):
            pick = rng.choice(pool, size=n, replace=True)
            starts.append(pick + rng.normal(0.0, 0.3, n))
        for x0 in starts:
            r = minimize(_neg_objective_grad, x0, args=(y, c), jac=True,
                         method="L-BFGS-B",
                         options=dict(maxiter=800, ftol=1e-16, gtol=1e-12))
            if -r.fun > best:
                best, bx = float(-r.fun), np.sort(r.x)
        out[n] = (best, bx)
    return out


def grid_search_small_n(y: float, c: float, span: float = 30.0):
    """Brute grid for n <= 3 (independent of the local optimiser), then polish."""
    out = {}
    g1 = np.arange(-span, span, 0.01)
    v1 = damage(g1, y)
    i = int(np.argmax(v1))
    out[1] = (float(v1[i]), np.array([g1[i]]))

    g2 = np.arange(-span, span, 0.05)
    v2 = damage(g2, y)
    D = v2[:, None] + v2[None, :]
    Rm = 2 * omega2(g2[:, None] - g2[None, :])
    M = D - c * Rm
    np.fill_diagonal(M, -math.inf)
    k = int(np.argmax(M))
    i2, j2 = divmod(k, len(g2))
    out[2] = (float(M[i2, j2]), np.array([g2[i2], g2[j2]]))

    g3 = np.arange(-span, span, 0.5)
    v3 = damage(g3, y)
    O3 = omega2(g3[:, None] - g3[None, :])
    best, bx = -math.inf, None
    nn = len(g3)
    for i in range(nn):
        for j in range(i + 1, nn):
            base = v3[i] + v3[j] - 2 * c * O3[i, j]
            cand = base + v3[j + 1:] - 2 * c * (O3[i, j + 1:] + O3[j, j + 1:])
            if cand.size:
                m = int(np.argmax(cand))
                if cand[m] > best:
                    best, bx = float(cand[m]), np.array([g3[i], g3[j], g3[j + 1 + m]])
    out[3] = (best, bx)

    polished = {}
    for n, (val, xs) in out.items():
        r = minimize(_neg_objective_grad, xs, args=(y, c), jac=True,
                     method="L-BFGS-B", options=dict(maxiter=800, ftol=1e-16))
        polished[n] = (max(val, float(-r.fun)),
                       np.sort(r.x) if -r.fun >= val else np.sort(xs))
    return polished


# ---------------------------------------------------------------------------
# 2. band-lattice families
# ---------------------------------------------------------------------------


def band_lattice_family(y: float, c: float, Kmax: int = 40,
                        offsets=(-0.6, -0.3, -0.15, 0.0, 0.15, 0.3, 0.6),
                        seed: int = 5):
    """Two-sided band ladders: top-K, every-other, every-third, irregular.

    Each family is also swept over a rigid sub-band phase offset, since the
    band maxima and the omega2 zeros are near-arithmetic but not equal, a
    small rigid shift can trade damage against internal charge.
    """
    bands, _ = band_table(y)
    bands = bands[:Kmax]
    rng = np.random.default_rng(seed)
    fams = {}
    for K in (1, 2, 3, 5, 8, 12, 20, min(Kmax, len(bands))):
        fams[f"top-{K}"] = bands[:K]
    fams["every-other"] = bands[::2][:20]
    fams["every-third"] = bands[::3][:14]
    fams["odd-shifted"] = bands[1::2][:20]
    for r in range(6):
        m = rng.random(len(bands)) < 0.45
        if m.any():
            fams[f"irregular-{r}"] = bands[m]
    best = (-math.inf, None, None, None)
    rows = []
    for name, b in fams.items():
        for off in offsets:
            bb = b + off
            xs = np.concatenate([-bb[::-1], bb])
            val, D, R = objective(xs, y, c)
            rows.append((name, off, val, D, R, len(xs)))
            if val > best[0]:
                best = (val, name, off, xs)
            # one-sided variant: no mirror partner, halves the cheap +- pair
            val1, _, _ = objective(bb, y, c)
            rows.append((name + " (one-sided)", off, val1, 0.0, 0.0, len(bb)))
            if val1 > best[0]:
                best = (val1, name + " (one-sided)", off, bb)
    return best, rows


# ---------------------------------------------------------------------------
# 3. multiplicity and near-coincidence
# ---------------------------------------------------------------------------


def multiplicity_probe(y: float, c: float, mmax: int = 12,
                       spreads=(0.0, 0.05, 0.1, 0.2, 0.4, 0.6, 1.0, 1.5)):
    """m zeros on the top band, stacked or spread by s; both sides mirrored."""
    bands, vals = band_table(y)
    b0 = float(bands[0])
    rows = []
    for m in range(1, mmax + 1):
        for s in spreads:
            xs = b0 + s * (np.arange(m) - (m - 1) / 2)
            xs = np.concatenate([-xs[::-1], xs])
            val, D, R = objective(xs, y, c)
            rows.append((m, s, val, D, R))
    best = max(rows, key=lambda r: r[2])
    return best, rows


def coincidence_arithmetic(y: float, c: float):
    """The closed form for m stacked zeros on one band: m f - c m(m-1)."""
    _, vals = band_table(y)
    f = float(vals[0])
    ms = np.arange(1, 200)
    # two mirrored stacks of m each: D = 2 m f; R = 2 m(m-1) + 2 m^2 omega2(2 b0)
    b0 = float(band_table(y)[0][0])
    o = float(omega2(np.array([2 * b0]))[0])
    vals_m = 2 * ms * f - c * (2 * ms * (ms - 1) + 2 * ms**2 * o)
    k = int(np.argmax(vals_m))
    return {"f_max": f, "omega2_across": o, "m_star": int(ms[k]),
            "value": float(vals_m[k]), "slack": slack(y)}


# ---------------------------------------------------------------------------
# 4. free greedy on a fine grid
# ---------------------------------------------------------------------------


def fine_greedy(y: float, c: float, G: float = 200.0, step: float = 0.05,
                nmax: int = 6000):
    """Marginal-gain greedy over a fine grid; multiplicity allowed.

    Maintains the potential P(x) = sum_j omega2(x - x_j) so each addition is
    O(|grid|).  Stops when no site has positive marginal gain.
    """
    gs = np.arange(-G, G + step / 2, step)
    v = damage(gs, y)
    P = np.zeros_like(gs)
    chosen = []
    for _ in range(nmax):
        g = v - 2 * c * P
        k = int(np.argmax(g))
        if g[k] <= 1e-15:
            break
        chosen.append(float(gs[k]))
        P += omega2(gs - gs[k])
    return np.array(chosen)


def polished_greedy(y: float, c: float, **kw):
    """Greedy, then a continuous L-BFGS-B polish of the positions."""
    xs = fine_greedy(y, c, **kw)
    if xs.size == 0:
        return 0.0, xs
    r = minimize(_neg_objective_grad, xs, args=(y, c), jac=True,
                 method="L-BFGS-B", options=dict(maxiter=2000, ftol=1e-16))
    val0 = objective(xs, y, c)[0]
    if -r.fun > val0:
        return float(-r.fun), np.sort(r.x)
    return float(val0), np.sort(xs)


def best_known(y: float, c: float):
    """The strongest configuration this module can find at (y, c)."""
    cands = []
    val, xs = polished_greedy(y, c)
    cands.append((val, xs))
    for n, (v, x) in exhaustive_small_n(y, c, nmax=4, restarts=40).items():
        cands.append((v, x))
    (bval, bname, boff, bxs), _ = band_lattice_family(y, c, Kmax=24, offsets=(0.0, -0.15, 0.15))
    cands.append((bval, bxs))
    (m, s, mv, _, _), _ = multiplicity_probe(y, c, mmax=8)
    b0 = float(band_table(y)[0][0])
    mx = b0 + s * (np.arange(m) - (m - 1) / 2)
    cands.append((mv, np.concatenate([-mx[::-1], mx])))
    return max(cands, key=lambda t: t[0])


# ---------------------------------------------------------------------------
# 5. the theta = 1 reading: harvest under a minimum separation
# ---------------------------------------------------------------------------


def spacing_harvest(y: float, d: float, G: float = 400.0, step: float = 0.02):
    """Max damage with the charge switched off but on-line zeros >= d apart.

    Greedy by descending damage subject to the separation constraint; this is
    the natural relaxation of the theta = 1 objective and is what makes it
    finite at all.
    """
    gs = np.arange(-G, G, step)
    f = damage(gs, y)
    order = np.argsort(-f)
    chosen = np.empty(0)
    total = 0.0
    for i in order:
        if f[i] <= 0:
            break
        x = gs[i]
        if chosen.size and float(np.min(np.abs(chosen - x))) < d:
            continue
        chosen = np.append(chosen, x)
        total += float(f[i])
    return total, chosen.size


def critical_spacing(y: float, lo: float = 0.02, hi: float = 1.0):
    """Smallest separation d at which the charge-free harvest still fits."""
    for _ in range(24):
        mid = math.sqrt(lo * hi)
        if spacing_harvest(y, mid)[0] > slack(y):
            lo = mid
        else:
            hi = mid
    return hi


def band_envelope(y: float, G: float = 2000.0, step: float = 0.002):
    """One zero per band, both sides, plus a 1/g^2 tail majorant beyond G."""
    b, v = band_table(y, G=G, step=step)
    total = 2 * float(v.sum())
    tail = 2 * (1 / math.pi) * 4 * MT.C_im(y) ** 2 / (A**2 * G)
    return total, tail


# ---------------------------------------------------------------------------
# 6. depth and theta sweeps
# ---------------------------------------------------------------------------


def depth_sweep(ys=DEPTHS, c: float = 1.0):
    rows = []
    for y in ys:
        val, xs = polished_greedy(y, c)
        _, D, R = objective(xs, y, c)
        env, tail = band_envelope(y)
        rows.append(dict(y=y, slack=slack(y), sigma2=MT.sigma2(y), value=val,
                         D=D, R=R, n=len(xs), ratio=D / slack(y),
                         net_ratio=val / slack(y),
                         env_ratio=(env + tail) / slack(y),
                         xs=xs))
    return rows


def theta_star(y: float, lo: float = 1e-10, hi: float = 3.0, iters: int = 28):
    """Largest theta for which the searched sup stays under the slack.

    Bisects the charge c = 1 - theta: the searched sup is decreasing in c, so
    the crossing c* gives theta* = 1 - c*.  Because the sup is a search
    result, theta* is an *upper* estimate of the true threshold.
    """
    s = slack(y)
    for _ in range(iters):
        mid = math.sqrt(lo * hi)
        # the raw greedy, not the polish: bisection needs hundreds of calls and
        # the polish moves the value by < 1% (see the c = 1 row of section 5)
        val = objective(fine_greedy(y, mid, G=150.0, step=0.1), y, mid)[0]
        if val > s:
            lo = mid
        else:
            hi = mid
    return 1.0 - hi, hi


# ---------------------------------------------------------------------------
# 7. controls
# ---------------------------------------------------------------------------


def lesion_no_repulsion(y: float = 0.49, m: int = 40):
    """Planted fault: with omega2 deleted, the search must break the trade.

    m zeros stacked on the top band, charged at zero, the detector-power
    control for everything above.  If this does not exceed the slack the
    search is blind and no other row in the audit means anything.
    """
    b0 = float(band_table(y)[0][0])
    xs = np.full(m, b0)
    D = float(np.sum(damage(xs, y)))
    return {"D": D, "slack": slack(y), "breaks": D > slack(y), "m": m}


def naive_relaxation_is_vacuous(y: float = 0.49, c: float = 1.0,
                                G: float = 120.0, step: float = 1.0):
    """The concave QP that would bound the sup from above is worthless.

    With multiplicities m_x >= 0 on a grid, R = m^T O m - |m|_1 agrees with
    the true R at integer m and is convex, so the relaxed max is a genuine
    upper bound, but fractional m makes the self-charge negative and the
    bound overshoots by two orders of magnitude.  Recorded so that no later
    session spends a day on this dual.
    """
    xs = np.arange(-G, G + step / 2, step)
    v = damage(xs, y)
    O = omega2(xs[:, None] - xs[None, :])
    b = v + c

    def nf(m):
        Om = O @ m
        return -(b @ m - c * (m @ Om)), -(b - 2 * c * Om)

    m0 = np.maximum(b, 0.0) / (2 * c)
    r = minimize(nf, m0, jac=True, method="L-BFGS-B",
                 bounds=[(0.0, None)] * len(xs),
                 options=dict(maxiter=3000, ftol=1e-18))
    return {"relaxed": float(-r.fun), "slack": slack(y),
            "overshoot": float(-r.fun) / slack(y), "mass": float(r.x.sum())}


def precision_ladder(y: float = 0.49, c: float = 1.0):
    """Discretization response of the worst case: grid step and range."""
    rows = []
    for step in (0.2, 0.1, 0.05, 0.02):
        val, xs = polished_greedy(y, c, G=200.0, step=step)
        rows.append(("step", step, val, len(xs)))
    for G in (50.0, 100.0, 200.0, 400.0):
        val, xs = polished_greedy(y, c, G=G, step=0.05)
        rows.append(("G", G, val, len(xs)))
    for G in (500.0, 1000.0, 2000.0):
        env, tail = band_envelope(y, G=G)
        rows.append(("envelope G", G, (env + tail) / slack(y), 0))
    return rows


# ---------------------------------------------------------------------------
# audit
# ---------------------------------------------------------------------------


def audit():
    print("=" * 74)
    print("MT-window retention trade: adversarial search (single off-line pair)")
    print("=" * 74)

    print("\n-- 0. detector power: the planted fault must break the trade --")
    les = lesion_no_repulsion()
    print(f"   omega2 deleted, {les['m']} zeros stacked on the top band: "
          f"D = {les['D']:.4f} vs slack {les['slack']:.4f} -> "
          f"{'BREAKS (search has power)' if les['breaks'] else 'BLIND - audit is void'}")

    print("\n-- 1. the near miss: damage bands ride the omega2 zeros --")
    for y in (0.30, 0.49):
        print(f"   y = {y}:")
        for b, z, gap, o in near_miss_table(y, 4):
            print(f"     band {b:8.4f}   omega2 zero {z:8.4f}   miss {gap:+.4f}"
                  f"   omega2(band) = {o:.5f}")
    print(f"   omega2 profile: omega2(1) = {float(omega2(np.array([1.0]))[0]):.4f}, "
          f"omega2(2) = {float(omega2(np.array([2.0]))[0]):.4f}, "
          f"omega2(4) = {float(omega2(np.array([4.0]))[0]):.4f}  "
          "(a band is ~1 unit wide: the charge is far wider than the damage)")

    print("\n-- 2. exhaustive small n at c = 1 (theta = 0 charging), y = 0.49 --")
    y = 0.49
    ex = exhaustive_small_n(y, 1.0, nmax=6, restarts=60)
    gr = grid_search_small_n(y, 1.0)
    for n in sorted(ex):
        val, xs = ex[n]
        extra = ""
        if n in gr:
            extra = f"   grid {gr[n][0]:+.6e}"
        print(f"   n={n}: best {val:+.6e} = {val / slack(y):.4f} slack{extra}"
              f"   x = {np.round(xs, 3)[:6]}")
    print("   -> n = 2 is the optimum; larger n parks the extra zeros where f = 0")

    print("\n-- 3. band-lattice families (two-sided, phase-swept, subsets) --")
    for c in (1.0, 0.1, 0.01):
        (bv, bname, boff, bxs), _ = band_lattice_family(y, c)
        print(f"   c={c:<5g} best family {bname:22s} offset {boff:+.2f}  "
              f"value {bv:+.6e} = {bv / slack(y):.4f} slack  (n={len(bxs)})")

    print("\n-- 4. multiplicity and near-coincidence --")
    for c in (1.0, 0.1, 0.01, 0.001):
        (m, s, mv, mD, mR), _ = multiplicity_probe(y, c)
        ar = coincidence_arithmetic(y, c)
        print(f"   c={c:<6g} best stack m={m} spread={s:.2f}  value {mv:+.6e} "
              f"= {mv / slack(y):.4f} slack   |  closed form m* = {ar['m_star']}, "
              f"value {ar['value']:+.4e}")

    print("\n-- 5. free greedy on a 0.05 grid, and the best known configuration --")
    for c in (1.0, 0.1, 0.01, 0.003, 0.001):
        val, xs = best_known(y, c)
        _, D, R = objective(xs, y, c)
        print(f"   c={c:<6g} value {val:+.6e} = {val / slack(y):6.3f} slack   "
              f"D {D:.5f}  R {R:.5f}  n={len(xs)}")

    print("\n-- 6. the theta = 1 reading: charge off, minimum separation d --")
    print("   (with d -> 0 the sup is unbounded: this is the literal break)")
    for y2 in (0.30, 0.49):
        print(f"   y = {y2}, slack {slack(y2):.5f}:")
        for d in (0.1, 0.15, 0.2, 0.25, 0.5, 1.0, math.pi, MEAN_GAP):
            tot, n = spacing_harvest(y2, d)
            print(f"     d={d:5.3f}: D = {tot:.5f} = {tot / slack(y2):6.3f} slack "
                  f"(n={n}) {'EXCEEDS' if tot > slack(y2) else 'inside'}")
        print(f"     critical separation d* = {critical_spacing(y2):.4f} grid units "
              f"= {critical_spacing(y2) / MEAN_GAP:.4f} mean gaps")

    print("\n-- 7. depth sweep (12 depths), c = 1 --")
    print("     y    sigma^2     slack      D        D/slack  net/slack  env/slack  n")
    rows = depth_sweep()
    for r in rows:
        print(f"   {r['y']:.2f}  {r['sigma2']:.3e}  {r['slack']:.3e}  "
              f"{r['D']:.5f}  {r['ratio']:7.4f}  {r['net_ratio']:8.4f}  "
              f"{r['env_ratio']:8.4f}  {r['n']:2d}")
    worst = max(rows, key=lambda r: r["ratio"])
    worst_env = max(rows, key=lambda r: r["env_ratio"])
    print(f"   worst D/slack        {worst['ratio']:.4f} at y = {worst['y']} "
          f"({1 / worst['ratio']:.2f}x inside), configuration "
          f"x = {np.round(worst['xs'], 4)}")
    print(f"   worst envelope ratio {worst_env['env_ratio']:.4f} at y = "
          f"{worst_env['y']} ({1 / worst_env['env_ratio']:.2f}x inside) "
          "-- one zero per band, charge off")

    print("\n-- 8. theta sweep: largest theta with the searched sup <= slack --")
    print("     y      c* = 1-theta*     theta*")
    for y2 in DEPTHS:
        th, cs = theta_star(y2)
        print(f"   {y2:.2f}   {cs:.4e}      {th:.7f}")

    print("\n-- 9. controls: the natural upper-bound dual is vacuous --")
    rel = naive_relaxation_is_vacuous()
    print(f"   concave QP relaxation at c=1, y=0.49: {rel['relaxed']:.4e} = "
          f"{rel['overshoot']:.1f} x slack (fractional multiplicities make the "
          "self-charge negative)")

    print("\n-- 10. precision response of the worst case --")
    for kind, param, val, n in precision_ladder():
        print(f"   {kind:11s} {param:8.3f} -> {val:.6e}  (n={n})")
    print("   (the c=1 optimum is grid- and range-stable to 6 figures; the")
    print("    envelope rows fall with G because the crude 1/g^2 tail majorant")
    print("    is O(1/G) while the band sum itself has already converged)")

    print("\n" + "=" * 74)
    print("SUMMARY (measured lower bounds on the adversary, not a safety proof)")
    print("=" * 74)
    print(f"  worst D/slack found with the charge on (c=1): {worst['ratio']:.4f} "
          f"at y = {worst['y']}, configuration x = {np.round(worst['xs'], 3)}")
    print(f"  charge-free one-per-band envelope:            "
          f"{worst_env['env_ratio']:.4f} at y = {worst_env['y']}")
    print("  the trade survives every family searched with the charge on;")
    print("  read literally at theta = 1 the sup is unbounded (stacking), so the")
    print("  statement needs either the full charge or a minimum-separation")
    print(f"  hypothesis d >= {critical_spacing(0.49):.3f} grid units at y = 0.49.")
    print("  no configuration-free bound is established here; the named T1 gap")
    print("  (band-lattice dual with point-separation charges) is untouched.")


if __name__ == "__main__":
    audit()

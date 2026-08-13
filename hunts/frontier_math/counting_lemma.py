"""ROAD B, step 3: the counting lemma, and a uniform floor for the budget.

`gram_form.py` reduced `k >= 2` to one inequality,

    B(T, y) + R(X)/400  >=  sum_{a,p} D(y, x_a - t_p),

with `B >= 0` free from `energy_F_ge` and `R >= 0` a sum of squares.  What
was missing was a *count*: how many pair centres can simultaneously collect
large damage.  Two measurements supply it.

## 1. The counting lemma: at most ONE pair per damage window

Within one damage window (width `<= w_max = 0.9860008`) put `m` atoms and
`j` pair centres.  Then

    damage        <=  m j D_1,          D_1        = 4.396424e-03
    atom relief   >=  m(m-1) g^2/800,   g^2/800    = 9.779689e-04
    pair relief   >=  j(j-1) kappa(W),  kappa(W)   = 1.620239e+00

with `kappa(tau) = K_0(tau) + K_{2y}(tau)` the pair-pair term of the
`k`-pair identity.  A two-species square completion closes iff

    D_1^2  <=  4 (g^2/800) kappa(W),

and it does, at **1.932855e-05 vs 6.338174e-03 — a margin of 327.9x**
(:func:`am_gm_margin`).  The consequence is sharper than the AM-GM
statement itself: maximising `f(m,j) = m j D_1 - m(m-1) g^2/800 -
j(j-1) kappa(W)` over integers gives

    j = 1:  +7.321459e-03  (at m = 3 — exactly the k=1 optimum)
    j = 2:  -3.216073e+00
    j = 3:  -9.670185e+00

so **a second pair in the same window is never profitable**
(:func:`window_occupancy`).  `kappa(W) = 1.62` is 1657x the per-pair atom
relief, which is why the pair species is the one that cannot crowd.

## 2. The budget floor: `B/k` does not decay

`B` is not additive, so "budget per pair" is not `Shq(y)/2` and could in
principle vanish as `k` grows.  It does not.  Minimising over lattice
spacings at `k = 64` puts the worst case at `L = 6.30` (just past `2 pi`,
the window period), and along that worst family

    k    = 2, 4, 8, 16, 32, 64, 128, 256
    B/k  = 2.459e-2, 1.749e-2, 1.260e-2, 9.492e-3, 7.653e-3,
           6.680e-3, 6.325e-3, 6.392e-3

which bottoms out near **6.3e-03 and turns back up**
(:func:`budget_floor_ladder`).  So every pair brings a guaranteed budget
bounded away from zero, uniformly in `k` — measured, not proved.

## What this does and does not settle

Together: each pair carries budget `>= ~6.3e-03` and can be crowded by at
most one pair per window.  That is exactly the count `gram_form` said was
missing, and it kills the configuration the `k = 1` analysis feared — many
pairs sharing one atom cluster's windows.

It does **not** close `k >= 2`.  A single pair facing atoms at every one of
its window peaks already collects `1.372e-02 > 6.3e-03`, so the atom
repulsion `R/400` is still load-bearing and the shared-`R`-across-pairs
question is untouched.  What is gone is the *unbounded* version of the
worry.  `k >= 2` remains open and nothing here is evidence about RH.
"""

from __future__ import annotations

import cmath
import math

__all__ = [
    "A_CONST", "W_MAX", "D_ONE", "ATOM_RELIEF", "KAPPA_W", "kappa",
    "kernel", "damage", "budget", "am_gm_margin", "window_occupancy",
    "budget_floor_ladder", "worst_spacing", "BUDGET_FLOOR", "NAMED_GAPS",
    "report",
]

SQ2 = math.sqrt(2.0)
A_CONST = SQ2 * math.sin(1 / SQ2)
_A2 = A_CONST ** 2

#: max damage-window width at `y = 1/2` (`window_table`).
W_MAX = 0.9860008
#: top window peak `D(1/2, 6.516999776)`.
D_ONE = 4.396424118e-03
#: measured floor of `B/k`, uniform in `k`, at the worst lattice spacing.
BUDGET_FLOOR = 6.3e-03


def _gh(a: float, b: float) -> complex:
    z = complex(a, b)
    zp, zm = z + 1j * SQ2, z - 1j * SQ2
    return cmath.sinh(zp / 2) / zp + cmath.sinh(zm / 2) / zm


def damage(y: float, s: float) -> float:
    g = _gh(y, s)
    return -(g * g).real


def kernel(kap: float, s: float) -> float:
    """`K_kappa(s) = -D(kappa, s)`."""
    return (_gh(kap, s) ** 2).real


def kappa(tau: float, y: float = 0.5) -> float:
    """`kappa(tau) = K_0(tau) + K_{2y}(tau)`, the pair-pair term."""
    return kernel(0.0, tau) + kernel(2 * y, tau)


def phi_r(v: float) -> float:
    return _gh(0.0, v).real


#: atom-atom relief per within-window pair, `gamma^2/800`.
ATOM_RELIEF = phi_r(W_MAX) ** 2 / 800
#: pair-pair relief per within-window pair, `kappa(w_max)`.
KAPPA_W = kappa(W_MAX)


def budget(ts, y: float = 0.5) -> float:
    """`B = (1/2)[G_T(2y) + G_T(0)] - k A^2`."""
    k = len(ts)
    tot = 0.0
    for a in ts:
        for b in ts:
            tot += kernel(2 * y, a - b) + kernel(0.0, a - b)
    return tot / 2 - k * _A2


# --- 1. the counting lemma -------------------------------------------------

def am_gm_margin() -> dict:
    """`D_1^2 <= 4 (gamma^2/800) kappa(w_max)` — the closure condition."""
    lhs = D_ONE ** 2
    rhs = 4 * ATOM_RELIEF * KAPPA_W
    return {"lhs": lhs, "rhs": rhs, "holds": lhs <= rhs, "margin": rhs / lhs,
            "D_one": D_ONE, "atom_relief": ATOM_RELIEF, "kappa_w": KAPPA_W,
            "kappa_over_atom_relief": KAPPA_W / ATOM_RELIEF}


def site_value(m: int, j: int) -> float:
    """`m j D_1 - m(m-1) gamma^2/800 - j(j-1) kappa(w_max)`."""
    return m * j * D_ONE - m * (m - 1) * ATOM_RELIEF - j * (j - 1) * KAPPA_W


def window_occupancy(js=(1, 2, 3), m_max: int = 40) -> list:
    """Best `m` for each pair-occupancy `j`.  `j >= 2` must be negative."""
    out = []
    for j in js:
        best, arg = max((site_value(m, j), m) for m in range(m_max + 1))
        out.append({"j": j, "best": best, "m": arg, "profitable": best > 0})
    return out


# --- 2. the budget floor ---------------------------------------------------

def budget_per_pair(L: float, k: int, y: float = 0.5) -> float:
    return budget([L * i for i in range(k)], y) / k


def worst_spacing(k: int = 64, lo: float = 2.0, hi: float = 14.0,
                  n: int = 120) -> dict:
    """The lattice spacing that minimises `B/k`."""
    best = None
    for i in range(n):
        L = lo + i * (hi - lo) / n
        v = budget_per_pair(L, k)
        if best is None or v < best[0]:
            best = (v, L)
    return {"min_budget_per_pair": best[0], "spacing": best[1], "k": k}


def budget_floor_ladder(L: float | None = None,
                        ks=(2, 4, 8, 16, 32, 64, 128, 256)) -> list:
    """`B/k` along the worst family — must not decay to zero."""
    if L is None:
        L = worst_spacing()["spacing"]
    return [{"k": k, "budget_per_pair": budget_per_pair(L, k)} for k in ks]


NAMED_GAPS = (
    "C1 `k >= 2` is NOT closed. A single pair facing atoms at every one of "
    "its window peaks collects 1.372e-02 > the 6.3e-03 budget floor, so "
    "R/400 is still load-bearing and the shared-R-across-pairs question "
    "is untouched.",
    "C2 the budget floor is MEASURED along lattice families to k = 256 and "
    "minimised over spacing at k = 64; it is not proved, and no search "
    "over non-lattice pair sets at large k was run.",
    "C3 the counting lemma uses the single-window constants (w_max, D_1, "
    "gamma, kappa(w_max)); it is a statement about one window, and the "
    "assembly over windows is not carried out here.",
    "C4 kappa(tau) is NOT a pure repulsion -- it is positive at short "
    "range but reaches about -1.82e-02 near tau = 2 pi, which is why the "
    "worst spacing sits just past the window period.",
    "C5 nothing here is evidence about RH.",
)


def report() -> dict:
    print("= 1. the counting lemma: at most one pair per window =")
    a = am_gm_margin()
    print(f"  D_1 = {a['D_one']:.6e}   gamma^2/800 = {a['atom_relief']:.6e}"
          f"   kappa(w_max) = {a['kappa_w']:.6e}")
    print(f"  AM-GM: {a['lhs']:.6e} <= {a['rhs']:.6e}  -> {a['holds']}, "
          f"margin {a['margin']:.1f}x")
    print(f"  kappa(w_max) is {a['kappa_over_atom_relief']:.0f}x the per-pair "
          f"atom relief")
    for r in window_occupancy():
        print(f"  j = {r['j']}: max over m = {r['best']:+.6e} at m = {r['m']}"
              f"   profitable: {r['profitable']}")
    print("= 2. the budget floor: B/k does not decay =")
    ws = worst_spacing()
    print(f"  worst lattice spacing at k=64: L = {ws['spacing']:.2f} "
          f"(window period is 2 pi = {2*math.pi:.4f})")
    for r in budget_floor_ladder():
        print(f"  k = {r['k']:4d}: B/k = {r['budget_per_pair']:.6e}")
    print(f"  floor taken as {BUDGET_FLOOR:.1e}; Shq/2 = "
          f"{(_gh(1.0, 0.0).real ** 2 - _A2) / 2:.6e}")
    print("= named gaps =")
    for g in NAMED_GAPS:
        print(f"  * {g}")
    return {"am_gm": a, "floor": BUDGET_FLOOR}


if __name__ == "__main__":
    report()

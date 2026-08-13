"""The gap identity as one convex functional of the on-line sum.

Found by the coordinator while four agents worked the near-coincident
case; landed here so none of them has to rediscover it.

THE IDENTITY (checked below to 6.7e-16 on five configurations):

    gap * A^2 = (1/200) [ int_{-1}^{1} c2(w) |F(w)|^2 dw  -  n A^2 ]
              + 4 int_{-1}^{1} c2(w) e^{-y w} Re[ e^{-i t w} F(w) ] dw
              + 8 A Shq(y) + 8 Shq(y)^2

with F(w) = sum_j e^{i x_j w} the on-line exponential sum, c2 = g * g
the (nonnegative, compactly supported) autocorrelation of the window,
and A = int g.

THREE STEPS, each an exact identity, each checked:

1. ghat(s + iy) = Pre(y,s) + i Qim(y,s) - the two transform components
   are the real and imaginary parts of ONE complex transform.
2. Pre^2 - Qim^2 = Re[ c2hat(s + iy) ] = Re int c2(w) e^{i(s+iy)w} dw.
   The damage profile is the c2-transform at a complex argument. This is
   what makes the whole thing one kernel instead of two.
3. sum_{j,k} phiR(x_j - x_k)^2 = int c2(w) |F(w)|^2 dw, since
   c2hat = |ghat|^2 = phiR^2 (Bochner: phiR^2 is positive definite
   because c2 >= 0).

WHY IT MATTERS.  The repulsion term and the damage term were being
handled by separate machinery - band covers for one, near/far splits for
the other.  They are the quadratic and linear parts of a single convex
functional against a single positive measure.  In particular:

- the quadratic coefficient is 1 - theta = 1/200 and it is POSITIVE, so
  clustering raises int c2 |F|^2.  **But that does NOT mean clustering
  raises the gap**, because clustering also concentrates the LINEAR
  term, and the coordinator's first reading of this file got that
  backwards.  See `clustering_helps` below, which measures both;
- the only nonconvexity remaining is the constraint that F be an n-atom
  exponential sum.  Relaxing it gives a convex problem whose minimum
  lower-bounds the truth.

THE TRADE, MEASURED PROPERLY (with the cluster centre held fixed, which
the first attempt failed to do).  At the damage peak, offset 6.517 from
the pair, y = 0.49, gap against cluster size m at spacing 0.01:

    m  =    1      2      3      4      5      6      8     12     16
    gap = .1335  .1235  .1236  .1337  .1538  .1840  .2747  .5776 1.043

So the trade is **not monotone**.  Going from one on-line point to two
at the damage peak HURTS (0.1335 -> 0.1235); the m^2 growth of the
repulsion only overtakes the m growth of the damage from m = 4 on, after
which it wins decisively.  Away from the damage peak (offset 0)
clustering helps at every m: 4.245 -> 12.408 as the spacing closes.

Two consequences, both against the coordinator's first reading:

- **the separation hypothesis was excluding the DANGEROUS cases, not the
  safe ones.**  A tight pair sitting on the damage peak is the worst
  configuration in this family, and separation is exactly what forbids
  it;
- but the worst value found is **+0.1235, positive with room**, and the
  minimum over cluster size is at m = 2 rather than at m -> infinity.
  That is a much better-shaped search than "check all configurations":
  the adversary's best play in this family is a PAIR, and it does not
  win.

WHAT THIS IS NOT.  It is not a proof.  The naive relaxation - dropping
the atom constraint entirely and completing the square - is too lossy:
it grants the adversary perfect anti-alignment against the linear term
and the resulting bound degrades linearly in n (the same failure the
Gram/SOS attempt hit, recorded in PROOF-LEDGER.md).  What the form buys
is that any proof can now be stated about one functional rather than
two coupled sums.

Run ``.venv/bin/python hunts/frontier_math/spectral_gap.py`` (~1 min).
"""

from __future__ import annotations

import cmath
import math

from scipy.integrate import quad

S2 = math.sqrt(2.0)
A = S2 * math.sin(1 / S2)


def g(u: float) -> float:
    return math.cos(S2 * u)


def c2(w: float) -> float:
    """The autocorrelation g * g: even, supported in [-1, 1], >= 0."""
    w = abs(w)
    if w >= 1.0:
        return 0.0
    return quad(lambda u: g(u) * g(u - w), w - 0.5, 0.5, limit=200)[0]


def shq(y: float) -> float:
    return quad(lambda u: g(u) * math.sinh(y * u) ** 2, -0.5, 0.5, limit=200)[0]


def phi_r(r: float) -> float:
    return quad(lambda u: g(u) * math.cos(r * u), -0.5, 0.5, limit=200)[0]


def pre(y: float, s: float) -> float:
    return quad(lambda u: g(u) * math.cos(s * u) * math.cosh(y * u),
                -0.5, 0.5, limit=200)[0]


def qim(y: float, s: float) -> float:
    return -quad(lambda u: g(u) * math.sin(s * u) * math.sinh(y * u),
                 -0.5, 0.5, limit=200)[0]


def gap_direct(xs, y: float, t: float) -> float:
    """The gap from the kernel-checked identity, term by term."""
    n = len(xs)
    rep = sum(phi_r(a - b) ** 2 for a in xs for b in xs) - n * A * A
    dam = sum(pre(y, x - t) ** 2 - qim(y, x - t) ** 2 for x in xs)
    return (rep / 200 + 4 * dam + 8 * A * shq(y) + 8 * shq(y) ** 2) / A ** 2


def gap_spectral(xs, y: float, t: float) -> float:
    """The same gap as one convex functional of F against c2 dw."""
    n = len(xs)

    def F(w):
        return sum(cmath.exp(1j * x * w) for x in xs)

    quad_term = quad(lambda w: c2(w) * abs(F(w)) ** 2, -1, 1, limit=400)[0]
    lin_term = quad(
        lambda w: c2(w) * math.exp(-y * w) * (cmath.exp(-1j * t * w) * F(w)).real,
        -1, 1, limit=400)[0]
    return ((quad_term - n * A * A) / 200 + 4 * lin_term
            + 8 * A * shq(y) + 8 * shq(y) ** 2) / A ** 2


def step_identities(probes=((0.4, 2.3), (0.5, 7.1), (0.3, 13.0))):
    """The three exact steps, each as a worst defect."""
    d1 = d2 = 0.0
    for y, s in probes:
        lhs = (quad(lambda u: g(u) * math.cos(s * u) * math.exp(-y * u),
                    -0.5, 0.5, limit=200)[0]
               + 1j * quad(lambda u: g(u) * math.sin(s * u) * math.exp(-y * u),
                           -0.5, 0.5, limit=200)[0])
        d1 = max(d1, abs(lhs - (pre(y, s) + 1j * qim(y, s))))
        rhs = quad(lambda w: c2(w) * math.cos(s * w) * math.exp(-y * w),
                   -1, 1, limit=300)[0]
        d2 = max(d2, abs((pre(y, s) ** 2 - qim(y, s) ** 2) - rhs))
    d3 = 0.0
    for xs in ([0.0, 2.5], [0.0, 3.1, 7.7, 11.2]):
        lhs = sum(phi_r(a - b) ** 2 for a in xs for b in xs)
        rhs = quad(lambda w: c2(w) * abs(sum(cmath.exp(1j * x * w)
                                             for x in xs)) ** 2,
                   -1, 1, limit=400)[0]
        d3 = max(d3, abs(lhs - rhs))
    return {"ghat_split": d1, "damage_is_c2hat": d2, "repulsion_is_energy": d3}


CONFIGS = (
    ([0.0], 0.49, 3.2),
    ([0.0, 6.28], 0.3, 3.1),
    ([0.0, 3.1, 7.7, 11.2], 0.5, 5.5),
    ([0.0, 0.5, 1.0], 0.45, 6.5),                    # a tight cluster
    ([0.0, 6.28, 12.57, 18.85, 25.13], 0.49, 9.4),   # a unit lattice
)


def identity_defects():
    return [(len(xs), abs(gap_direct(xs, y, t) - gap_spectral(xs, y, t)))
            for xs, y, t in CONFIGS]


#: the measured argmax of the single-point damage, y = 1/2
DAMAGE_PEAK = 6.517


def clustering_helps(y: float = 0.49, offset: float = DAMAGE_PEAK):
    """The trade, with the cluster CENTRE held fixed.

    The first version of this function varied the spacing without
    holding the centre, so the cluster drifted away from the damage
    peak and the measurement was confounded - it appeared to show
    clustering helping when it was really showing the cluster escaping.
    Returns (spacing, energy, gap) for a centred triple.
    """
    out = []
    for spacing in (6.0, 3.0, 1.5, 0.5, 0.1, 0.0):
        xs = [offset - spacing, offset, offset + spacing]
        e = quad(lambda w: c2(w) * abs(sum(cmath.exp(1j * x * w)
                                           for x in xs)) ** 2,
                 -1, 1, limit=400)[0]
        out.append((spacing, e, gap_spectral(xs, y, 0.0)))
    return out


def gap_by_cluster_size(y: float = 0.49, spacing: float = 0.01, ms=None):
    """Gap against cluster size at the damage peak: the non-monotone trade.

    The minimum is at m = 2, not at either extreme; the m^2 repulsion
    overtakes the m damage from m = 4 on.
    """
    ms = ms or (1, 2, 3, 4, 5, 6, 8, 12, 16, 24)
    return [(m, gap_spectral([DAMAGE_PEAK + i * spacing for i in range(m)],
                             y, 0.0)) for m in ms]


def audit() -> None:
    print("= the three exact steps =")
    for k, v in step_identities().items():
        print(f"  {k:24s} worst defect {v:.2e}")
    print("= the full identity, direct vs spectral =")
    for n, d in identity_defects():
        print(f"  n={n}: defect {d:.2e}")
    print("= the trade, centre held fixed, AT the damage peak =")
    print(f"  {'spacing':>9} {'int c2|F|^2':>13} {'gap':>12}")
    for sp, e, gp in clustering_helps():
        print(f"  {sp:>9.2f} {e:>13.6f} {gp:>12.6f}")
    print("  energy rises monotonically; the gap FALLS.  Clustering onto the")
    print("  damage peak is the adversary's move, not ours.")
    print("= the same trade against cluster size: non-monotone, min at m = 2 =")
    for m, gp in gap_by_cluster_size():
        print(f"  m={m:>3}: gap {gp:>10.6f}")
    print("  worst is a PAIR at the damage peak, and it is positive with room.")
    print("  From m = 4 the m^2 repulsion overtakes the m damage. No")
    print("  proportion is claimed.")


if __name__ == "__main__":
    audit()

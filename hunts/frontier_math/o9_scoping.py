"""O9 scoping: what the nine-window damage table costs as an interval object.

`RETENTION-PROBLEM.md` §4 lists eleven obligations for the k=1 retention
inequality.  Six are already in `zeta23ext` with zero `sorry`s; O3, O4, O10 and
O11 are small; **O9 is named there as "the only real work"** — a two-variable
statement on `[28/5, 60] x [0, 1/2]`, the analogue of the `BandCert` leaf
tables already in the package.

This module measures what that object actually costs, so the build is scoped
before it is started rather than after.  Four questions, in order:

1. **Do the recorded caps hold?**  Recompute `sup Dam(y,s)/y^2` over each
   window box and compare with the `c_k` of §4.
2. **How much headroom does §7 leave?**  The caps enter the final arithmetic
   through the integer trade `P(c,q)`; inflating them raises the deficit
   against a fixed budget.  The largest admissible inflation sets how loose the
   enclosure is allowed to be, and therefore how deep the subdivision must go.
3. **What does the subdivision cost?**  Adaptive bisection of each window box
   under Arb ball arithmetic, counting leaves.
4. **The complement.**  O9 also asserts no damage outside the windows, which is
   tangent at each window edge; measure the widening that buys a margin there.

Closed forms.  `Qre_closed` / `Qim_closed` are kernel-checked in
`Zeta23Ext/EForm3/ClosedForm.lean`, so the enclosure never has to carry a
quadrature: with `kp = s + sqrt2`, `km = s - sqrt2`,

    Qre(y,s) = C(y,kp) + C(y,km),
        C(a,k) = [a sinh(a/2) cos(k/2) + k cosh(a/2) sin(k/2)] / (a^2 + k^2)
    Qim(y,s) = S(y,kp) + S(y,km),
        S(a,k) = [a cosh(a/2) sin(k/2) - k sinh(a/2) cos(k/2)] / (a^2 + k^2)

Run:

    .venv/bin/python hunts/frontier_math/o9_scoping.py
"""

from __future__ import annotations

import time
from fractions import Fraction

from flint import arb, ctx

ctx.prec = 160

# --------------------------------------------------------------------------
# The field, from the kernel-checked closed forms
# --------------------------------------------------------------------------

SQRT2 = arb(2).sqrt()
ACONST = SQRT2 * (1 / SQRT2).sin()


def _C(a: arb, k: arb) -> arb:
    return (a * (a / 2).sinh() * (k / 2).cos() + k * (a / 2).cosh() * (k / 2).sin()) / (
        a * a + k * k
    )


def _S(a: arb, k: arb) -> arb:
    return (a * (a / 2).cosh() * (k / 2).sin() - k * (a / 2).sinh() * (k / 2).cos()) / (
        a * a + k * k
    )


def Qre(y: arb, s: arb) -> arb:
    return _C(y, s + SQRT2) + _C(y, s - SQRT2)


def Qim(y: arb, s: arb) -> arb:
    return _S(y, s + SQRT2) + _S(y, s - SQRT2)


def _sinhc(x: arb, *, terms: int = 14) -> arb:
    """`sinh(x)/x`, through its series, so `x = 0` is not special.

    On `|x| <= 1/4` — the only range this module needs, since `y <= 1/2` — the
    tail after 14 terms is below `2^-160`, so the truncation is absorbed by the
    working precision.  `Leaves.lean` already carries the same device for
    `sin(u/2)/u` (its `sfnL`), which is why this branch costs no new machinery.
    """
    total = arb(0)
    fact = 1
    for n in range(terms):
        if n:
            fact *= (2 * n) * (2 * n + 1)
        total += x ** (2 * n) / fact
    tail = arb(0, arb(2) ** -160)
    return total + tail


def _Sdiv(a: arb, k: arb) -> arb:
    """`S(a,k)/a`, with the removable singularity at `a = 0` taken out."""
    return (
        (a / 2).cosh() * (k / 2).sin() - k * _sinhc(a / 2) / 2 * (k / 2).cos()
    ) / (a * a + k * k)


def Qim_over_y(y: arb, s: arb) -> arb:
    """`Qim(y,s)/y`, analytic across `y = 0` (`Qim(0,s) = 0`)."""
    return _Sdiv(y, s + SQRT2) + _Sdiv(y, s - SQRT2)


def damage_raw(y: arb, s: arb) -> arb:
    """`Qim^2 - Qre^2`; the damage is its positive part."""
    return Qim(y, s) ** 2 - Qre(y, s) ** 2


def Shq(y: arb) -> arb:
    return Qre(2 * y, arb(0)) ** 2 - ACONST**2


def Wt(w: arb) -> arb:
    """The far-field majorant of `Qim^2/y^2` (`FarField.lean`, O7)."""
    return (
        arb(5) / 8 / w
        + arb(611) / 50 / w**2
        + arb(6711) / 100 / w**3
        + arb(2583) / 25 / w**4
    )


# --------------------------------------------------------------------------
# The recorded table (RETENTION-PROBLEM.md §4, O9)
# --------------------------------------------------------------------------

WINDOWS: list[tuple[Fraction, Fraction, Fraction]] = [
    (Fraction(60653, 10000), Fraction(35257, 5000), Fraction(439643, 25000000)),
    (Fraction(61171, 5000), Fraction(131999, 10000), Fraction(390023, 100000000)),
    (Fraction(11544, 625), Fraction(48583, 2500), Fraction(169313, 100000000)),
    (Fraction(247289, 10000), Fraction(256909, 10000), Fraction(18889, 20000000)),
    (Fraction(309971, 10000), Fraction(159793, 5000), Fraction(6021, 10000000)),
    (Fraction(372701, 10000), Fraction(76463, 2000), Fraction(10431, 25000000)),
    (Fraction(21773, 500), Fraction(27817, 625), Fraction(6123, 20000000)),
    (Fraction(498237, 10000), Fraction(507849, 10000), Fraction(1171, 5000000)),
    (Fraction(280513, 5000), Fraction(570637, 10000), Fraction(9247, 50000000)),
]

#: How far each recorded window is widened before the enclosure runs.  The
#: added strips carry no damage, so the caps are unmoved (checked in [3]); what
#: they buy is a strict margin on the complement, where the bare window edge is
#: a tangency by construction.
#:
#: **Bounded above by O3, not by taste.**  §5 step 3 groups the offsets inside
#: one window and charges every pair `Kpair >= 39/50`, which O3 supplies only on
#: `|u| <= 1`.  A widened window wider than `1` puts two of its own points
#: further apart than that, and the charge is no longer available: `Kpair` is
#: decreasing there, and `Kpair(1.01) = 0.77943 < 39/50` already.  The widest
#: recorded window is `0.9861`, so the widening may not exceed `0.00695`.
WIDEN = Fraction(1, 200)

#: The radius on which O3 supplies `Kpair >= 39/50`.
O3_RADIUS = Fraction(1)

Q_NEAR = Fraction(39, 10000)  # (39/50)/200
Q_FAR = Fraction(1, 25000)  # (1/125)/200
BUDGET_COEFF = Fraction(51944, 100000)  # 2*Shq(y) >= BUDGET_COEFF * y^2  (O8)
S_FAR_START = 60
S_TAIL_START = 400


def _f(x: Fraction) -> arb:
    return arb(x.numerator) / arb(x.denominator)


# --------------------------------------------------------------------------
# 1. Do the recorded caps hold?
# --------------------------------------------------------------------------


def window_sup(lo: Fraction, hi: Fraction, *, ns: int = 900, ny: int = 60) -> tuple[float, float, float]:
    """Grid maximum of `Dam(y,s)/y^2` over `[lo,hi] x (0,1/2]`.

    Returns `(sup, s_argmax, y_argmax)`.  A grid maximum is a lower bound on the
    true supremum; it is used here only to check the recorded cap for gross
    error, never as the cap itself.
    """
    best = (-1.0, 0.0, 0.0)
    for j in range(ny):
        y = Fraction(1, 2) * Fraction(j + 1, ny)
        ya = _f(y)
        y2 = float(y) ** 2
        for i in range(ns + 1):
            s = lo + (hi - lo) * Fraction(i, ns)
            d = float(damage_raw(ya, _f(s)))
            if d > 0:
                r = d / y2
                if r > best[0]:
                    best = (r, float(s), float(y))
    return best


# --------------------------------------------------------------------------
# 2. How much headroom does the final arithmetic leave?
# --------------------------------------------------------------------------


def integer_trade(c: Fraction, q: Fraction) -> Fraction:
    """`P(c,q) = max_m (4 c m - q m (m-1))` over `m` a nonnegative integer.

    The real maximiser is `1/2 + 2c/q`; the integer one is a neighbour of it
    (Lemma 5.1).  `m = 0` is always available, so `P >= 0`.
    """
    star = Fraction(1, 2) + 2 * c / q
    lo = max(0, int(star))
    best = Fraction(0)
    for m in {0, lo, lo + 1}:
        val = 4 * c * m - q * m * (m - 1)
        if val > best:
            best = val
    return best


def total_deficit(inflation: Fraction, *, y: Fraction = Fraction(1, 2)) -> dict:
    """The §7 accounting at depth `y`, with every window cap scaled by `inflation`.

    Returns the window part, the far part, the tail part and the budget.  The
    far and tail parts use the O7 majorant and are not inflated: they are
    already upper bounds carrying their own proof.
    """
    v = y * y

    windows = Fraction(0)
    for _lo, _hi, cap in WINDOWS:
        windows += integer_trade(cap * inflation * v, Q_NEAR)
    windows *= 2  # both signs of s

    far = Fraction(0)
    j = 0
    while True:
        left = S_FAR_START + 6 * j
        if left >= S_TAIL_START:
            break
        w = Fraction(left) ** 2 - 2
        cap = Fraction(float(Wt(_f(w)))).limit_denominator(10**12)
        far += integer_trade(cap * v, Q_FAR)
        j += 1
    far *= 2

    # Beyond s = 400 single points are optimal (4c <= q_far), so the trade is
    # not needed and the tail is 4 * sum of caps.
    tail_sum = Fraction(1, Fraction(S_TAIL_START) ** 2 - 2) + Fraction(1, 6) / (
        S_TAIL_START - 2
    )
    tail_cap = Fraction(637, 1000) * tail_sum
    tail = 2 * 4 * tail_cap * v

    budget = BUDGET_COEFF * v
    return {
        "windows": windows,
        "far": far,
        "tail": tail,
        "deficit": windows + far + tail,
        "budget": budget,
        "surplus": budget - (windows + far + tail),
    }


def max_inflation(*, lo: Fraction = Fraction(1), hi: Fraction = Fraction(4), steps: int = 60) -> Fraction:
    """Largest cap inflation for which the §7 arithmetic still closes."""
    if total_deficit(hi)["surplus"] > 0:
        return hi
    for _ in range(steps):
        mid = (lo + hi) / 2
        if total_deficit(mid)["surplus"] > 0:
            lo = mid
        else:
            hi = mid
    return lo


# --------------------------------------------------------------------------
# 3. What does the subdivision cost?
# --------------------------------------------------------------------------


def _box(lo: Fraction, hi: Fraction) -> arb:
    """The ball enclosing `[lo, hi]`."""
    mid = (lo + hi) / 2
    rad = (hi - lo) / 2
    return arb(_f(mid), _f(rad))


def leaf_count(
    s_lo: Fraction,
    s_hi: Fraction,
    cap: Fraction,
    *,
    y_lo: Fraction = Fraction(0),
    y_hi: Fraction = Fraction(1, 2),
    max_depth: int = 40,
) -> tuple[int, int, bool]:
    """Adaptive bisection holding `Qim^2 - Qre^2 <= cap * y^2` on the box.

    Written through `R = Qim/y` so that `y = 0` is an ordinary point:

        Qim^2 - Qre^2 <= cap y^2   <=>   y^2 (R^2 - cap) <= Qre^2.

    If `sup R^2 <= cap` the box passes whatever `Qre` does; otherwise the worst
    case is the box's largest `y` against its smallest `Qre^2`.  Testing the
    literal difference instead would force every box touching `y = 0` to prove
    `Qim^2 <= Qre^2`, which is false at the zeros of `Qre(0, .)` and would make
    the bisection run forever there.

    Bisects the longer side.  Returns `(leaves, depth_reached, ok)`.
    """
    stack = [(s_lo, s_hi, y_lo, y_hi, 0)]
    leaves = 0
    deepest = 0
    while stack:
        a, b, c, d, depth = stack.pop()
        deepest = max(deepest, depth)
        S = _box(a, b)
        Y = _box(c, d)
        excess = Qim_over_y(Y, S) ** 2 - _f(cap)
        excess_up = arb(excess.mid()) + arb(excess.rad())
        if excess_up <= 0:
            leaves += 1
            continue
        qre2 = Qre(Y, S) ** 2
        qre2_lo = arb(qre2.mid()) - arb(qre2.rad())
        if _f(d) ** 2 * excess_up <= qre2_lo:
            leaves += 1
            continue
        if depth >= max_depth:
            return leaves, deepest, False
        if (b - a) >= (d - c):
            m = (a + b) / 2
            stack.append((a, m, c, d, depth + 1))
            stack.append((m, b, c, d, depth + 1))
        else:
            m = (c + d) / 2
            stack.append((a, b, c, m, depth + 1))
            stack.append((a, b, m, d, depth + 1))
    return leaves, deepest, True


# --------------------------------------------------------------------------
# 4. The complement: no damage between the windows
# --------------------------------------------------------------------------


def complement_leaf_count(
    widen: Fraction, *, max_depth: int = 40
) -> tuple[int, int, bool, list[tuple[float, float]]]:
    """Hold `Qim^2 - Qre^2 <= 0` on `[28/5, 60]` minus the widened windows."""
    gaps: list[tuple[Fraction, Fraction]] = []
    cursor = Fraction(28, 5)
    for lo, hi, _cap in WINDOWS:
        left = lo - widen
        if left > cursor:
            gaps.append((cursor, left))
        cursor = hi + widen
    if cursor < 60:
        gaps.append((cursor, Fraction(60)))

    total = 0
    deepest = 0
    ok = True
    for a, b in gaps:
        n, d, good = leaf_count(a, b, Fraction(0), max_depth=max_depth)
        total += n
        deepest = max(deepest, d)
        ok = ok and good
    return total, deepest, ok, [(float(a), float(b)) for a, b in gaps]


# --------------------------------------------------------------------------
# Report
# --------------------------------------------------------------------------


def main() -> None:
    print("=" * 74)
    print("O9 scoping — the nine-window damage table as an interval object")
    print("=" * 74)

    print("\n[0] The closed forms against the values pinned in RETENTION-PROBLEM.md")
    checks = [
        ("A", ACONST, "0.91872537"),
        ("Kpair(1) = Qre(0,1)^2", Qre(arb(0), arb(1)) ** 2, "0.78066657"),
        ("Kpair(6) = Qre(0,6)^2", Qre(arb(0), arb(6)) ** 2, "0.00834800"),
        ("Shq(1/2)/2", Shq(arb(1) / 2) / 2, "0.03375420"),
        ("Dam(1/2, 6.517)", damage_raw(arb(1) / 2, arb("6.517")), "0.00439642"),
    ]
    for name, got, want in checks:
        print(f"    {name:28s} {float(got):.8f}   pinned {want}")

    print("\n[1] Recorded caps against a grid maximum of Dam/y^2 on each window")
    print("    k   window                       c_k          grid sup     ratio   argmax")
    for k, (lo, hi, cap) in enumerate(WINDOWS):
        sup, s_at, y_at = window_sup(lo, hi)
        ratio = sup / float(cap)
        print(
            f"    {k}   [{float(lo):8.4f},{float(hi):8.4f}]  {float(cap):.6e}  "
            f"{sup:.6e}  {ratio:6.4f}  s={s_at:8.4f} y={y_at:.3f}"
        )

    print("\n[2] Headroom in the §7 arithmetic (depth y = 1/2)")
    base = total_deficit(Fraction(1))
    print(f"    windows, both sides   {float(base['windows']):.7e}   (§7: 7.5279200e-02)")
    print(f"    far intervals         {float(base['far']):.7e}   (§7: 3.6305145e-03)")
    print(f"    tail beyond s=400     {float(base['tail']):.7e}   (§7: 5.4146340e-04)")
    print(f"    total deficit         {float(base['deficit']):.7e}   (§7: 7.9451178e-02)")
    print(f"    budget                {float(base['budget']):.7e}   (§7: 1.2986000e-01)")
    print(f"    surplus               {float(base['surplus']):.7e}   (§7: 5.0408822e-02)")

    infl = max_inflation()
    at = total_deficit(infl)
    print(f"\n    largest admissible cap inflation: {float(infl):.4f}x")
    print(f"    at that inflation: deficit {float(at['deficit']):.7e}, surplus {float(at['surplus']):.3e}")

    print("\n[3] The widening is bounded by O3, not by taste")
    widest = max(hi - lo for lo, hi, _c in WINDOWS)
    ceiling = (O3_RADIUS - widest) / 2
    print(f"    widest recorded window          {float(widest):.4f}")
    print(f"    O3 radius (Kpair >= 39/50)      {float(O3_RADIUS):.4f}")
    print(f"    => widening may not exceed      {float(ceiling):.5f}")
    print(f"    chosen WIDEN                    {float(WIDEN):.5f}")
    for r in ("1.0", "1.01", "1.05"):
        print(f"      Kpair({r:>5s}) = {float(Qre(arb(0), arb(r)) ** 2):.8f}")
    assert WIDEN <= ceiling, "widening breaks the O3 hypothesis in §5 step 3"

    print("\n[3b] Does widening a window move its cap?  (grid sup on the widened box)")
    widen = WIDEN
    for k, (lo, hi, cap) in enumerate(WINDOWS):
        sup, _s, _y = window_sup(lo - widen, hi + widen, ns=400, ny=30)
        verdict = "unchanged" if sup <= float(cap) else "RAISED"
        print(
            f"    k={k}  widened by {float(widen):.3f}: sup {sup:.6e} vs c_k "
            f"{float(cap):.6e}  -> {verdict}"
        )

    print(f"\n[4] Subdivision cost per window (windows widened by {float(widen):.3f})")
    print("    inflation   §7 surplus     leaves   depth    time   status")
    for infl_try in [
        Fraction(1),
        Fraction(21, 20),
        Fraction(11, 10),
        Fraction(23, 20),
        Fraction(6, 5),
        Fraction(5, 4),
        Fraction(13, 10),
        Fraction(27, 20),
    ]:
        surplus = total_deficit(infl_try)["surplus"]
        if surplus <= 0:
            print(f"    {float(infl_try):.2f}x       {float(surplus):+.3e}   — §7 does not close")
            continue
        t0 = time.time()
        total = 0
        deepest = 0
        ok = True
        per = []
        for lo, hi, cap in WINDOWS:
            n, d, good = leaf_count(lo - widen, hi + widen, cap * infl_try, max_depth=30)
            per.append(n)
            total += n
            deepest = max(deepest, d)
            ok = ok and good
        dt = time.time() - t0
        status = "holds" if ok else "depth cap hit"
        print(
            f"    {float(infl_try):.2f}x       {float(surplus):.3e}    {total:6d}   "
            f"{deepest:5d}  {dt:6.1f}s   {status}"
        )
        if ok:
            print(f"                  per window: {per}")

    print("\n[5] The complement, and the widening it needs")
    print(f"    (only widenings <= {float(ceiling):.5f} are admissible; the rest are shown")
    print("     to show the trend, and are not usable without weakening O3)")
    for w in [
        Fraction(0),
        Fraction(1, 400),
        Fraction(1, 200),
        Fraction(139, 20000),
        Fraction(1, 50),
    ]:
        t0 = time.time()
        n, d, ok, gaps = complement_leaf_count(w, max_depth=30)
        dt = time.time() - t0
        status = "holds" if ok else "depth cap hit"
        print(
            f"    widen {float(w):.3f} -> {len(gaps)} gaps, {n:6d} leaves, "
            f"max depth {d:2d}, {dt:6.1f}s, {status}"
        )


if __name__ == "__main__":
    main()

"""ROAD B, step 1: the damage functional has negative total integral.

The `k >= 2` case needed a quantitative form of "only two positions carry
the top damage peak" — a bound on how many pair centres can each collect
near-maximal damage from one on-line configuration.  There is a sharper
and much more elementary statement available, and it is exact.

## The identity

`-D(y,s) = int c2(w) cosh(y w) cos(s w) dw` is the Fourier cosine
transform of `w -> c2(w) cosh(y w)`, which is continuous and supported on
`[-1,1]`.  Fourier inversion **at the single point `w = 0`** gives

    int_{-inf}^{inf} D(y, s) ds  =  -2 pi c2(0),      c2(0) = int g^2,

**independent of `y`**, with the closed form

    c2(0) = int_{-1/2}^{1/2} cos^2(sqrt2 u) du = 1/2 + sin(sqrt2)/(2 sqrt2)
          = 0.84922799931830418...,
    int D ds = -2 pi c2(0) = -5.3358568877622847...

Measured against quadrature at five depths: the truncation to `|s| <= S`
agrees with `-2 pi c2(0)` to `O(1/S)` and the `y`-dependence of the
truncated integral is `1.2e-05` across `y in [0.05, 0.5]` — flat, as the
identity says (:func:`integral_ladder`).

## What it buys

For a fixed on-line multiset `X`, the damage a pair centred at `t`
collects is `C(t) = sum_a D(y, x_a - t)`, and

    int C(t) dt = n * int D ds = -2 pi c2(0) * n  <  0.

**A pair placed at random collects negative damage.**  Positive collection
is not the generic case; it requires the centre to land in one of the
narrow windows, and the mean over placements is negative at a rate that
does not weaken with depth.  Measured against the prediction
`n * int D / (2L)` on a window of length `2L = 1200`: agreement to four
digits for coincident and for spread atom sets alike
(:func:`mean_collection`).

This is the shape the `k >= 2` argument wants: the damage side is not
merely bounded per pair, it is *negative on average per pair*, so the
adversary pays for every centre it places off a window — and the windows
are what the `k = 1` accounting already controls.

## What it does NOT do

It is a statement about the *mean*, and the adversary chooses placements,
not a random draw.  Converting it into a bound on `sum_p C(t_p)` needs a
count of how many `t` can have `C(t)` large, which is **not** supplied
here.  So this is step 1 of Road B, not Road B.  `k >= 2` remains open;
nothing here is evidence about RH.
"""

from __future__ import annotations

import mpmath as mp

__all__ = [
    "SQ2", "A_CONST", "ghat", "damage", "c2", "c2_zero", "MEAN_DAMAGE",
    "C2_ZERO", "integral_of_damage", "integral_ladder", "mean_collection",
    "NAMED_GAPS", "report",
]

with mp.workdps(30):
    SQ2 = mp.sqrt(2)
    A_CONST = float(SQ2 * mp.sin(1 / SQ2))

#: `c2(0) = int_{-1/2}^{1/2} cos^2(sqrt2 u) du = 1/2 + sin(sqrt2)/(2 sqrt2)`.
C2_ZERO = 0.84922799931830418
#: `int D(y,s) ds = -2 pi c2(0)`, independent of `y`.
MEAN_DAMAGE = -5.3358568877622847


def _sq2():
    return mp.sqrt(2)


def ghat(z):
    """`int_{-1/2}^{1/2} cos(sqrt2 u) cosh(z u) du`."""
    s2 = _sq2()
    z = mp.mpmathify(z)
    zp, zm = z + 1j * s2, z - 1j * s2
    return mp.sinh(zp / 2) / zp + mp.sinh(zm / 2) / zm


def damage(y, s):
    """`D(y,s) = Qim^2 - Qre^2 = -Re ghat(y + i s)^2`."""
    return -mp.re(ghat(mp.mpc(y, s)) ** 2)


def c2(w):
    """`c2(w) = int g(u) g(u+w) du`, supported on `|w| <= 1`."""
    s2 = _sq2()
    w = mp.mpf(w)
    lo = max(-mp.mpf(1) / 2, -mp.mpf(1) / 2 - w)
    hi = min(mp.mpf(1) / 2, mp.mpf(1) / 2 - w)
    if hi <= lo:
        return mp.mpf(0)
    return mp.quad(lambda u: mp.cos(s2 * u) * mp.cos(s2 * (u + w)), [lo, hi])


def c2_zero():
    """The closed form `1/2 + sin(sqrt2)/(2 sqrt2)`."""
    s2 = _sq2()
    return mp.mpf(1) / 2 + mp.sin(s2) / (2 * s2)


def integral_of_damage(y, S: float = 2000.0):
    """`int_{-S}^{S} D(y,s) ds`.  The tail is `O(1/S)` since `D ~ C/s^2`."""
    y = mp.mpf(y)
    pts = [-S, -100, -30, -12, -6, 0, 6, 12, 30, 100, S]
    return mp.quad(lambda s: damage(y, s), pts)


def integral_ladder(ys=(0.05, 0.1, 0.25, 0.4, 0.5), S: float = 2000.0):
    """The truncated integral by depth — must be flat in `y`."""
    target = -2 * mp.pi * c2_zero()
    rows = []
    for y in ys:
        v = integral_of_damage(y, S)
        rows.append({"y": float(y), "integral": float(v),
                     "diff_from_closed_form": float(abs(v - target))})
    spread = max(r["integral"] for r in rows) - min(r["integral"] for r in rows)
    return {"rows": rows, "target": float(target), "y_spread": spread}


def mean_collection(xs, y=0.5, L: float = 600.0):
    """Mean of `C(t) = sum_a D(y, x_a - t)` over `t in [-L, L]`.

    Prediction: `n * int D ds / (2L)`, i.e. `n * MEAN_DAMAGE / (2L)`.
    """
    y = mp.mpf(y)
    xs = [mp.mpf(x) for x in xs]

    def C(t):
        return mp.fsum([damage(y, x - t) for x in xs])

    got = mp.quad(C, [-L, -100, -30, 0, 30, 100, L]) / (2 * L)
    pred = len(xs) * mp.mpf(MEAN_DAMAGE) / (2 * L)
    return {"measured": float(got), "predicted": float(pred),
            "rel_error": float(abs(got - pred) / abs(pred))}


NAMED_GAPS = (
    "M1 the identity is Fourier inversion at a point for a continuous "
    "compactly supported function; it is derived on paper and checked "
    "numerically here, and is NOT written in Lean.",
    "M2 it bounds the MEAN over placements. The adversary chooses "
    "placements, so this alone bounds nothing about sum_p C(t_p).",
    "M3 the missing count -- how many t can have C(t) large -- is NOT "
    "supplied here. This is step 1 of Road B, not Road B.",
    "M4 the quadrature truncates at |s| <= S with an O(1/S) tail; the "
    "flatness in y is measured, not enclosed.",
    "M5 k >= 2 remains open and nothing here is evidence about RH.",
)


def report() -> dict:
    print("= the closed form =")
    q, cf = c2(0), c2_zero()
    print(f"  c2(0) by quadrature   = {mp.nstr(q, 18)}")
    print(f"  1/2 + sin(v2)/(2 v2)  = {mp.nstr(cf, 18)}   |diff| "
          f"{mp.nstr(abs(q - cf), 3)}")
    print(f"  int D ds = -2 pi c2(0) = {mp.nstr(-2 * mp.pi * cf, 18)}")
    print("= flatness in depth (the identity says: no y-dependence) =")
    lad = integral_ladder()
    for r in lad["rows"]:
        print(f"  y = {r['y']:.2f}: int = {r['integral']:.10f}   "
              f"diff from closed form {r['diff_from_closed_form']:.2e}")
    print(f"  spread across depths = {lad['y_spread']:.3e}")
    print("= mean collectable damage is negative =")
    for xs, label in (([0.0], "n=1"), ([0.0] * 3, "n=3 coincident"),
                      ([0.0] * 8, "n=8 coincident"),
                      ([-70.0, -50, -30, -10, 10, 30, 50, 70],
                       "n=8 spread over 140")):
        m = mean_collection(xs)
        print(f"  {label:<22}: mean C = {m['measured']:+.9f}  "
              f"predicted {m['predicted']:+.9f}  rel err {m['rel_error']:.2e}")
    print("= named gaps =")
    for g in NAMED_GAPS:
        print(f"  * {g}")
    return lad


if __name__ == "__main__":
    report()

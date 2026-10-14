"""Measured constants for extending hunt #132's kernel-checked zero to ten intervals below 50.

Run from the repository root:

    .venv/bin/python hunts/hardy_ten_zeros/sizing.py            # print, write artifacts/sizing.json
    .venv/bin/python hunts/hardy_ten_zeros/sizing.py --no-write # print only

Hunt #132 (`hunts/hardy_first_zero/`) proved one zero with `14.13 < t < 14.14`. This file
sizes the three obstacles to doing the same at nine more two-decimal brackets, before any
heavy Lean work:

1. **The phase lemma.** Hunt #132's window has lower end `delta (log pi - 1 - 2K) - 66 delta^3`
   with `K = ab/4`; at `delta = 1/200` it leaves the quarter turn once `K > 157`.
   `lean/HardyTenZeros/PhaseShort.lean` drops the first `m` arctangents and gets
   `delta (log pi - 1 - log m - K/(m^2 - 1/16)) - delta^3/(m^2 - 1/16)`; both windows are
   computed here, with the crude constants the Lean instantiation uses.
2. **The remainder.** The order-4 Euler-Maclaurin remainder grows like `|s|^4 / N^3.5`.
   For every bracket the truncations `(N_a, N_b)` are chosen per endpoint, minimizing
   `N_a + N_b`, with the rational radii the Lean side conditions use and a margin of
   1.5 on them; orders 6 and 8 are sized the same way for the comparison.
3. **The kernel cost.** Only primes need an exp tower; a composite term box is the
   coarsened product of two earlier boxes. The cost is projected from the measured
   seconds per tower of one whole generated file (`RUNS.md`).

Grades (`CLAUDE.md`, the certainty ladder): the endpoint values of `Z` are Arb enclosures
cross-checked against `mpmath.iv`, so *hardened*; the remainder bounds are formulas checked
against Arb enclosures of zeta at every endpoint, *hardened* at those points; the truncation
choices and the order comparison are floating-point models, *measured*; the boxes that the
proof uses are computed by the bit-exact mirror and decided again by the Lean kernel.
Nothing here is a theorem, and nothing bears on RH (`docs/08`).
"""
from __future__ import annotations

import argparse
import json
import math
import sys
from fractions import Fraction
from pathlib import Path

import mpmath
from mpmath import mp

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
if str(ROOT) not in sys.path:  # pragma: no cover - import bootstrap
    sys.path.insert(0, str(ROOT))

from hunts.hardy_first_zero import sizing as S1  # noqa: E402

#: The ordinates as the owner stated them, six decimals.
STATED = (14.134725, 21.022040, 25.010858, 30.424876, 32.935062,
          37.586178, 40.918719, 43.327073, 48.005151, 49.773832)
#: Box parameters for the term boxes (`dirichletTermBox2 nLog nExp p kL kE`); see RUNS.md
#: (`term-cost`) for the measurement that chose them over hunt #132's (40, 24, 96, 8).
NLOG, NEXP, P, KE = 36, 16, 80, 8
#: The margin the truncation choice keeps on the Lean radii.
MARGIN = Fraction(3, 2)
#: Measured wall seconds of kernel work per exp tower, whole generated file included: the
#: (21.02, 21.03) file, 17 towers and 28 composite products, compiled in 52 s (RUNS.md,
#: `first-bracket`). Composite products and the assembly are folded into this rate.
SECONDS_PER_TOWER = 52 / 17
#: `m` and `L` of `gammaR_re_pos_short`.
PHASE_M, PHASE_L = 8, Fraction(1, 5)

#: Bernoulli numbers B_2 .. B_8, exactly.
BERN = {2: Fraction(1, 6), 4: Fraction(-1, 30), 6: Fraction(1, 42), 8: Fraction(-1, 30)}


# ---------------------------------------------------------------------------
# The ordinates and the brackets
# ---------------------------------------------------------------------------


def ordinates(dps: int = 30) -> list:
    """The ordinates `mpmath.zetazero(k)` returns for k = 1..10, at `dps` digits (numerics, not a theorem)."""
    with mp.workdps(dps):
        return [mpmath.zetazero(k).imag for k in range(1, 11)]


def bracket(g) -> tuple[Fraction, Fraction]:
    """The two-decimal interval holding `g`: (floor(100 g)/100, that plus 1/100)."""
    lo = Fraction(int(mpmath.floor(g * 100)), 100)
    return lo, lo + Fraction(1, 100)


def brackets() -> list[tuple[Fraction, Fraction]]:
    return [bracket(g) for g in ordinates()]


def tag(a: Fraction) -> str:
    """`Fraction(2102, 100)` -> `"2102"`, the Lean name suffix of a bracket."""
    return str(int(a * 100))


# ---------------------------------------------------------------------------
# 1. The phase windows
# ---------------------------------------------------------------------------


def _dK(a: Fraction, b: Fraction):
    return (mpmath.mpf(b.numerator) / b.denominator - mpmath.mpf(a.numerator) / a.denominator) / 2, \
        (mpmath.mpf(a.numerator) / a.denominator) * (mpmath.mpf(b.numerator) / b.denominator) / 4


def window_132(a: Fraction, b: Fraction) -> dict:
    """Hunt #132's window: [d (log pi - 1 - 2K) - 66 d^3, d (log pi + 5)]."""
    with mp.workdps(30):
        d, K = _dK(a, b)
        lp = mpmath.log(mpmath.pi)
        lo = d * (lp - 1 - 2 * K) - 66 * d**3
        up = d * (lp + 5)
        return {"lower": float(lo), "upper": float(up),
                "inside_quarter_turn": bool(max(-lo, up) < mpmath.pi / 2)}


def window_tail(a: Fraction, b: Fraction, m: int = PHASE_M) -> dict:
    """`le_phi_tail`: [d (log pi - 1 - log m - K/D) - d^3/D, d (log pi + 5)], D = m^2 - 1/16.

    `lower_lean` is the end the Lean instantiation `gammaR_re_pos_short` actually uses:
    `log pi >= 0`, `log m <= m - 1`, `K <= 625`, `d <= 1/200`, the same for every bracket.
    """
    with mp.workdps(30):
        d, K = _dK(a, b)
        lp = mpmath.log(mpmath.pi)
        D = mpmath.mpf(m) ** 2 - mpmath.mpf(1) / 16
        lo = d * (lp - 1 - mpmath.log(m) - K / D) - d**3 / D
        up = d * (lp + 5)
        dl, Kl = mpmath.mpf(1) / 200, mpmath.mpf(625)
        lo_lean = dl * (0 - 1 - (m - 1) - Kl / D) - dl**3 / D
        up_lean = dl * (mpmath.pi - 1 + 5)
        return {"lower": float(lo), "upper": float(up),
                "lower_lean": float(lo_lean), "upper_lean": float(up_lean),
                "inside_quarter_turn": bool(max(-lo, up) < mpmath.pi / 2)}


def theta_increment(a: Fraction, b: Fraction) -> float:
    return S1.theta_increment(a, b)


# ---------------------------------------------------------------------------
# 2. Euler-Maclaurin: main terms, bounds, the truncation choice
# ---------------------------------------------------------------------------


def s_of(t: Fraction):
    return S1.s_of(t)


def main_terms(t: Fraction, n_max: int, order: int = 4) -> dict:
    """The order-`order` main term at every N in [3, n_max], from running partial sums."""
    with mp.workdps(30):
        s = s_of(t)
        out = {}
        acc = mpmath.mpf(0)
        for N in range(1, n_max + 1):
            if N >= 3:
                M = acc + mpmath.power(N, 1 - s) / (s - 1) + mpmath.power(N, -s) / 2
                for j in range(1, order // 2):
                    poch = mpmath.mpf(1)
                    for i in range(2 * j - 1):
                        poch *= s + i
                    c = BERN[2 * j]
                    M += mpmath.mpf(c.numerator) / c.denominator / math.factorial(2 * j) * poch \
                        * mpmath.power(N, -s - 2 * j + 1)
                out[N] = M
            acc += mpmath.power(N, -s)
        return out


def em_bound(t: Fraction, N: int, order: int = 4):
    """|s(s+1)...(s+order-1)| |B_order|/order! (N-1)^(-sigma-order+1)/(sigma+order-1)."""
    with mp.workdps(30):
        s = s_of(t)
        sig = mpmath.re(s)
        p = mpmath.mpf(1)
        for i in range(order):
            p *= abs(s + i)
        c = abs(BERN[order])
        return p * (mpmath.mpf(c.numerator) / c.denominator) / math.factorial(order) \
            * mpmath.power(N - 1, -sig - order + 1) / (sig + order - 1)


def q4(t: Fraction) -> Fraction:
    """`q4Q t` of the Lean side: the squared norm of s(s+1)(s+2)(s+3) at s = 1/2 + it."""
    t = Fraction(t)
    out = Fraction(1)
    for j in range(4):
        out *= (Fraction(2 * j + 1, 2)) ** 2 + t * t
    return out


def lean_radius(t: Fraction, N: int) -> dict:
    """The rationals `r`, `R`, `e` of the Lean side conditions of `zeta_mem_mainBox`.

    r^2 <= N - 1, q4(t) <= R^2, e >= R / ((N-1)^3 r (7/2) 720), each rounded the safe way.
    """
    r = Fraction(math.isqrt((N - 1) * 10**12), 10**6)
    R = Fraction(math.isqrt(math.ceil(q4(t) * 10**6)) + 1, 10**3)
    exact = R / (Fraction(N - 1) ** 3 * r * Fraction(7, 2) * 720)
    e = Fraction(math.ceil(exact * 10**12), 10**12)
    assert r > 0 and r * r <= N - 1 and q4(t) <= R * R and exact <= e
    return {"r": r, "R": R, "e": e}


def rect_product_hi(Ma, Mb, ea, eb) -> float:
    """Upper end of [Re Ma +- ea][Re Mb +- eb] + [Im Ma +- ea][Im Mb +- eb]."""
    def hi(x, e, y, f):
        cs = [(x + u) * (y + v) for u in (-e, e) for v in (-f, f)]
        return max(cs)
    return hi(float(mpmath.re(Ma)), ea, float(mpmath.re(Mb)), eb) + \
        hi(float(mpmath.im(Ma)), ea, float(mpmath.im(Mb)), eb)


def choose_truncations(a: Fraction, b: Fraction, order: int = 4, lean_radii: bool = True,
                       margin: Fraction = MARGIN, n_max: int = 160) -> dict:
    """Minimize N_a + N_b subject to the rectangle sign test passing with radii x margin.

    `lean_radii` uses the rational radii the Lean side conditions use (order 4 only);
    otherwise the sharp bound `em_bound`. Ties go to the smaller max(N_a, N_b).
    """
    Ma_all = main_terms(a, n_max, order)
    Mb_all = main_terms(b, n_max, order)
    rad = (lambda t, N: float(lean_radius(t, N)["e"])) if lean_radii else \
        (lambda t, N: float(em_bound(t, N, order)))
    ea = {N: rad(a, N) * float(margin) for N in Ma_all}
    eb = {N: rad(b, N) * float(margin) for N in Mb_all}
    best = None
    for Na in sorted(Ma_all):
        for Nb in sorted(Mb_all):
            if best is not None and Na + Nb > best[0]:
                break
            if rect_product_hi(Ma_all[Na], Mb_all[Nb], ea[Na], eb[Nb]) < 0:
                key = (Na + Nb, max(Na, Nb))
                if best is None or key < best:
                    best = (key[0], key[1], Na, Nb)
                break
    if best is None:
        raise ValueError(f"no truncation up to {n_max} decides ({a}, {b}) at order {order}")
    return {"N_a": best[2], "N_b": best[3], "terms": best[2] + best[3]}


def is_prime(m: int) -> bool:
    return m >= 2 and all(m % f for f in range(2, math.isqrt(m) + 1))


def towers(*Ns: int) -> int:
    """Exp towers for term tables 1..N, one table per N: one per prime."""
    return sum(1 for N in Ns for m in range(2, N + 1) if is_prime(m))


def order_comparison(brs=None) -> dict:
    """Terms and towers per bracket at orders 4, 6, 8 (sharp bounds) and at order 4 with
    the Lean radii, and the kernel minutes each would cost at `SECONDS_PER_TOWER`.

    Brackets 2 to 10 only: the first is hunt #132's theorem, reused as it stands.
    """
    brs = brs or brackets()
    out = {}
    for a, b in brs[1:]:
        row = {}
        for key, order, lean in (("order4_lean", 4, True), ("order4_sharp", 4, False),
                                 ("order6_sharp", 6, False), ("order8_sharp", 8, False)):
            c = choose_truncations(a, b, order, lean)
            row[key] = c["terms"]
            row[key + "_towers"] = towers(c["N_a"], c["N_b"])
        out[tag(a)] = row
    totals = {k: sum(v[k] for v in out.values()) for k in next(iter(out.values()))}
    minutes = {k: totals[k + "_towers"] * SECONDS_PER_TOWER / 60
               for k in ("order4_lean", "order4_sharp", "order6_sharp", "order8_sharp")}
    return {"per_bracket": out, "totals": totals, "projected_kernel_minutes": minutes}


def plan(brs=None) -> list[dict]:
    """The planned truncations and radii for brackets 2 to 10 (order 4, Lean radii)."""
    brs = brs or brackets()
    rows = []
    for a, b in brs[1:]:
        c = choose_truncations(a, b, 4, True)
        rows.append({"a": a, "b": b, "tag": tag(a), "N_a": c["N_a"], "N_b": c["N_b"],
                     "rad_a": lean_radius(a, c["N_a"]), "rad_b": lean_radius(b, c["N_b"])})
    return rows


def defect_vs_radius(rows=None) -> dict:
    """Arb's defect |zeta - main term| against the Lean radius, at every planned endpoint."""
    rows = rows or plan()
    out = {}
    for r in rows:
        for side, t, N in (("a", r["a"], r["N_a"]), ("b", r["b"], r["N_b"])):
            d = float(S1.em_error_upper(t, N))
            e = float(r["rad_" + side]["e"])
            out[f"{t}"] = {"N": N, "defect": d, "radius": e, "ratio": e / d}
    return out


def margin_cost(brs=None) -> dict:
    """Order-4 term boxes over brackets 2 to 10 at margin 1 and at the planned margin."""
    brs = brs or brackets()
    return {str(float(m)): sum(choose_truncations(a, b, 4, True, margin=m)["terms"]
                               for a, b in brs[1:])
            for m in (Fraction(1), MARGIN)}


def exp_range_limit(t: Fraction = Fraction(4978, 100), kE: int = KE) -> dict:
    """normBound of -s log m against 2^kE for the primes around the limit of kE at height t."""
    M = S1.load_mirror()
    S = M.cexact(Fraction(1, 2), t)
    out = {}
    for m in (151, 157, 163, 167):
        arg = M.cmul(M.cneg(S), M.C(M.logQ(NLOG, m.bit_length(), Fraction(m)), M.iexact(0)))
        out[m] = float(M.normBound(arg))
    return {"t": str(t), "two_to_kE": 2**kE, "normBound": out}


def old_window_alternative() -> dict:
    """What keeping hunt #132's window would have cost at the last ordinate.

    That window needs b - a < 0.00254 at t near 49.77; the bracket here is the width-0.002
    interval (49.7728, 49.7748) around 49.773832. Priced with the same truncation rule.
    """
    a, b = Fraction(497728, 10000), Fraction(497748, 10000)
    c = choose_truncations(a, b, 4, True)
    return {"a": str(a), "b": str(b), "window_132": window_132(a, b),
            "Z_a": S1.z_enclosure(a, "python-flint"), "Z_b": S1.z_enclosure(b, "python-flint"),
            "N_a": c["N_a"], "N_b": c["N_b"], "terms": c["terms"],
            "towers": towers(c["N_a"], c["N_b"])}


# ---------------------------------------------------------------------------
# 3. Endpoint values of Z
# ---------------------------------------------------------------------------


def endpoint_signs(brs=None) -> dict:
    brs = brs or brackets()
    out = {}
    for a, b in brs:
        za = S1.z_enclosure(a, "python-flint")
        zb = S1.z_enclosure(b, "python-flint")
        za_iv = S1.z_enclosure(a, "mpmath.iv")
        zb_iv = S1.z_enclosure(b, "mpmath.iv")
        out[tag(a)] = {"Z_a": za, "Z_b": zb, "Z_a_iv": za_iv, "Z_b_iv": zb_iv,
                       "theta_increment": theta_increment(a, b)}
    return out


# ---------------------------------------------------------------------------


def collect() -> dict:
    brs = brackets()
    rows = plan(brs)
    comp = order_comparison(brs)
    terms = sum(r["N_a"] + r["N_b"] for r in rows)
    tw = sum(towers(r["N_a"], r["N_b"]) for r in rows)
    return {
        "ordinates": [float(g) for g in ordinates()],
        "brackets": [[str(a), str(b)] for a, b in brs],
        "box_params": {"nLog": NLOG, "nExp": NEXP, "p": P, "kE": KE},
        "margin": float(MARGIN),
        "phase_132": {tag(a): window_132(a, b) for a, b in brs},
        "phase_tail": {tag(a): window_tail(a, b) for a, b in brs},
        "endpoints": endpoint_signs(brs),
        "plan": [{"a": str(r["a"]), "b": str(r["b"]), "N_a": r["N_a"], "N_b": r["N_b"],
                  "e_a": str(r["rad_a"]["e"]), "e_b": str(r["rad_b"]["e"])} for r in rows],
        "planned_terms": terms,
        "planned_towers": tw,
        "projected_kernel_minutes": tw * SECONDS_PER_TOWER / 60,
        "order_comparison": comp,
        "old_window_alternative": old_window_alternative(),
        "margin_cost": margin_cost(brs),
        "exp_range_limit": exp_range_limit(),
        "defect_vs_radius": defect_vs_radius(rows),
    }


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--no-write", action="store_true")
    args = ap.parse_args(argv)
    out = collect()
    print(json.dumps(out, indent=2))
    if not args.no_write:
        (HERE / "artifacts").mkdir(exist_ok=True)
        (HERE / "artifacts" / "sizing.json").write_text(json.dumps(out, indent=2) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

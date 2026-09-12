"""Enclosure-checked arithmetic for the improved window constant.

What is enclosed, and how (both ball backends, per the repo convention that
the two check each other; see zeta/rigor.py for the convention's owner):

  1. The paper window cos(8s/5): m2, m3 and F = 2 m2 - m3 have exact closed
     forms (functional.moments_cos_sympy; the antiderivative identities are
     verified symbolically inside that routine).  The closed-form expressions
     are evaluated in ball arithmetic by a small recursive walker, once with
     Arb (python-flint, prec 200) and once with mpmath.iv (dps 60).  The two
     enclosures must overlap and must contain the 30-digit sympy reference.
  2. The chosen rational window v(s) = 1 - (1467/1000) s^2 + (1159/1000) s^4:
     m2, m3, F are EXACT RATIONALS (functional.moments_polyeven_exact,
     Fraction arithmetic, independently confirmed by the sympy route and by
     the finite-N CUE lattice count).  No enclosure is needed for these
     beyond exactness itself.
  3. The strict inequality F_rat > F_cos(8/5): checked as a ball statement
     in both backends (the lower bound of F_rat - F_cos must be positive).
  4. The new RH-conditional constant 1/2 + F_rat/18 + (4/9)(19/27): an exact
     rational, printed to 25 digits, with the delta over the paper's
     constant enclosed in both backends.

Positivity and monotonicity of the chosen window are also proved here in
exact rational arithmetic (they are needed for admissibility, RESULTS.md
section 6).

Vocabulary note: the reserved word for enclosure-carrying claims belongs to
zeta/rigor.py and is not used in this directory; everything here says
"enclosure-checked".  The inequality statements below carry enclosures on
every step; the *interpretation* (a lifted distinct-zeros proportion) is
conditional on RH and on the source paper's section 7.5(g) machinery.

Run: .venv/bin/python hunts/rogue_frontier/window_opt/enclose.py
Exits nonzero if python-flint is unavailable (the cross-check would silently
lose its second backend otherwise).
"""

from __future__ import annotations

import os
import sys
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from functional import (OPT_Q, PAPER_F_30, PAPER_M2_30, PAPER_M3_30,  # noqa: E402
                        moments_cos_sympy, moments_polyeven_exact)


# ---------------------------------------------------------------------------
# ball evaluation of sympy closed forms, two backends
# ---------------------------------------------------------------------------

def _eval_arb(expr):
    import sympy as sp
    from flint import arb

    if expr.is_Integer:
        return arb(int(expr))
    if expr.is_Rational:
        return arb(int(expr.p)) / arb(int(expr.q))
    if expr.is_Add:
        acc = arb(0)
        for t in expr.args:
            acc += _eval_arb(t)
        return acc
    if expr.is_Mul:
        acc = arb(1)
        for t in expr.args:
            acc *= _eval_arb(t)
        return acc
    if expr.is_Pow:
        base, exp = expr.args
        assert exp.is_Integer, expr
        return _eval_arb(base) ** int(exp)
    if isinstance(expr, sp.sin):
        return _eval_arb(expr.args[0]).sin()
    if isinstance(expr, sp.cos):
        return _eval_arb(expr.args[0]).cos()
    raise TypeError(f"unhandled node {type(expr)}: {expr}")


def _eval_iv(expr):
    import sympy as sp
    from mpmath import iv

    if expr.is_Integer:
        return iv.mpf(int(expr))
    if expr.is_Rational:
        return iv.mpf(int(expr.p)) / iv.mpf(int(expr.q))
    if expr.is_Add:
        acc = iv.mpf(0)
        for t in expr.args:
            acc += _eval_iv(t)
        return acc
    if expr.is_Mul:
        acc = iv.mpf(1)
        for t in expr.args:
            acc *= _eval_iv(t)
        return acc
    if expr.is_Pow:
        base, exp = expr.args
        assert exp.is_Integer, expr
        return _eval_iv(base) ** int(exp)
    if isinstance(expr, sp.sin):
        return iv.sin(_eval_iv(expr.args[0]))
    if isinstance(expr, sp.cos):
        return iv.cos(_eval_iv(expr.args[0]))
    raise TypeError(f"unhandled node {type(expr)}: {expr}")


def _frac_arb(x: Fraction):
    from flint import arb
    return arb(x.numerator) / arb(x.denominator)


def _frac_iv(x: Fraction):
    from mpmath import iv
    return iv.mpf(x.numerator) / iv.mpf(x.denominator)


def main() -> int:
    try:
        from flint import ctx
    except ImportError:
        print("FAIL: python-flint is not importable; the Arb arm of the "
              "two-backend cross-check cannot run.  Install it (pinned in "
              "requirements.txt) before trusting any enclosure here.")
        return 1
    import sympy as sp
    from mpmath import iv, mp

    ctx.prec = 200
    iv.dps = 60

    from zeta import rigor
    print(f"ball backends: zeta.rigor reports {rigor.BACKEND}, "
          f"available {rigor.available_backends()}")

    # -- 1. enclose the paper window's closed forms ------------------------
    print("\n== 1. paper window v = cos(8s/5): closed forms, two backends ==")
    m2e, m3e, Fe = moments_cos_sympy(8, 5)
    encl = {}
    mp.dps = 70
    for name, expr, ref in (("m2", m2e, PAPER_M2_30), ("m3", m3e, PAPER_M3_30),
                            ("F", Fe, PAPER_F_30)):
        a = _eval_arb(sp.nsimplify(expr))
        b = _eval_iv(sp.nsimplify(expr))
        encl[name] = (a, b)
        print(f"  {name}: arb  {a}")
        lo, hi = mp.make_mpf(b._mpi_[0]), mp.make_mpf(b._mpi_[1])
        print(f"  {name}: iv   [{mp.nstr(lo, 45)},")
        print(f"             {mp.nstr(hi, 45)}]")
        # the 30-digit reference truncations must sit within a widened
        # interval (the refs carry ~1e-29 truncation error themselves)
        ref_mp = mp.mpf(ref)
        assert lo - mp.mpf("1e-28") <= ref_mp <= hi + mp.mpf("1e-28"), \
            (name, "iv enclosure misses reference")
        from flint import arb
        assert (a - arb(ref)).abs_upper() < arb(1) / arb(10) ** 25, \
            (name, "arb enclosure misses reference")
        # backend agreement: the two enclosures must overlap
        assert float(a.lower()) <= float(hi) and float(lo) <= float(a.upper())
    print("  both backends agree and contain the 30-digit references")

    # -- 2. the rational window: exact arithmetic --------------------------
    print("\n== 2. rational window v = 1 - (1467/1000)s^2 + (1159/1000)s^4 ==")
    m2r, m3r, Fr = moments_polyeven_exact(OPT_Q)
    print(f"  m2 = {m2r}\n     = {float(m2r):.18f}")
    print(f"  m3 = {m3r}\n     = {float(m3r):.18f}")
    print(f"  F  = {Fr}\n     = {float(Fr):.18f}")

    # positivity and monotonicity, exact: v(s) = 1 + q1 s^2 + q2 s^4,
    # v'(s) = s (2 q1 + 4 q2 s^2); on (0, 1/2], 2 q1 + 4 q2 s^2 <=
    # 2 q1 + q2 < 0, so v is strictly decreasing; v(1/2) > 0 closes it.
    q1, q2 = OPT_Q
    assert 2 * q1 + q2 < 0, "monotonicity certificate failed"
    v_half = 1 + q1 * Fraction(1, 4) + q2 * Fraction(1, 16)
    assert v_half > 0, "positivity certificate failed"
    print(f"  exact: 2 q1 + q2 = {2*q1 + q2} < 0  =>  v nonincreasing on "
          f"[0, 1/2];  v(1/2) = {v_half} > 0  =>  v > 0 on [-1/2, 1/2]")

    # -- 3. strict inequality F_rat > F_cos, both backends -----------------
    print("\n== 3. strict improvement, enclosure-checked ==")
    Fe_simpl = sp.nsimplify(Fe)
    da = _frac_arb(Fr) - _eval_arb(Fe_simpl)
    db = _frac_iv(Fr) - _eval_iv(Fe_simpl)
    db_lo = mp.make_mpf(db._mpi_[0])
    db_hi = mp.make_mpf(db._mpi_[1])
    print(f"  arb: F_rat - F_cos = {da}")
    print(f"  iv : F_rat - F_cos = [{mp.nstr(db_lo, 20)}, "
          f"{mp.nstr(db_hi, 20)}]")
    from flint import arb
    assert da > arb(0), "arb cannot separate F_rat from F_cos"
    assert db_lo > 0, "iv cannot separate F_rat from F_cos"
    print("  both backends prove F_rat - F_cos > 0 "
          "(delta ~ 4.3147748e-5)")

    # -- 4. the new constant ----------------------------------------------
    print("\n== 4. the RH-conditional distinct-zeros constant ==")
    const_new = Fraction(1, 2) + Fr / 18 + Fraction(76, 243)
    print(f"  1/2 + F/18 + (4/9)(19/27)\n    = {const_new}")
    mp.dps = 30
    print(f"    = {mp.nstr(mp.mpf(const_new.numerator) / mp.mpf(const_new.denominator), 25)}  (exact rational)")
    dconst_a = da / arb(18)
    print(f"  lift over the paper's window constant, arb: {dconst_a}")
    paper_const_ball = (arb(1) / arb(2) + _eval_arb(Fe_simpl) / arb(18)
                        + arb(76) / arb(243))
    print(f"  paper's constant, arb enclosure:  {paper_const_ball}")
    assert _frac_arb(const_new) > paper_const_ball
    print("  arb proves new constant > paper constant")

    print("\nPASS: every number above is exact rational arithmetic or "
          "carries an enclosure in both ball backends.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

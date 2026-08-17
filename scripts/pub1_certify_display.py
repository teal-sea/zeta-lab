#!/usr/bin/env python3
"""Publication-safe display values for the Pub 1 xi' ceiling certificate.

Why this file exists
--------------------
The exact certificate lives in Lean (``ZetaLean.Pub1.zpp_arith_final`` and
``concavity_closes_final``).  The manuscript, however, prints *decimal* upper
bounds for the individual terms, and a referee reasonably adds them up.  The
first published draft rounded each term outward to ten decimal places; the
resulting printed addends summed to 0.0060608998731, which *exceeds* the
printed total bound 0.006060899845.  The exact certificate was never wrong --
its margin is only 3.63e-13, and rounding ||r0''||_inf up at 1e-10 alone
spends 76x that margin.

This script therefore derives every displayed decimal *from the Lean constants
themselves*, rounds each one outward at a precision chosen so that the printed
addends still sum to no more than the printed total, and refuses to emit
anything that violates that property.  Nothing here is part of the proof; it
exists so the paper's arithmetic is reproducible by inspection.

Stdlib only (fractions/decimal): the repo's fast CI tier installs bare pytest.

Usage:
    python3 scripts/pub1_certify_display.py            # human-readable
    python3 scripts/pub1_certify_display.py --latex    # LaTeX fragments
    python3 scripts/pub1_certify_display.py --manifest # name=value pairs
"""

from __future__ import annotations

import argparse
import re
import sys
from decimal import Decimal, localcontext
from fractions import Fraction
from pathlib import Path

# NB: never mutate the *global* decimal context here.  This module is imported
# by the test-suite, and a module-level getcontext().prec assignment leaks into
# every other test in the session (it broke
# tests/test_discovery_knownness.py::TestBasis in CI).
_PREC = 80

REPO = Path(__file__).resolve().parents[1]
CERT_ARITH = REPO / "lean" / "ZetaLean" / "Pub1" / "CertArith.lean"
NUMERIC = REPO / "lean" / "ZetaLean" / "Pub1" / "Numeric.lean"

# --------------------------------------------------------------------------
# 1.  Parse the exact rational constants out of the Lean sources.
#     Parsing (rather than copying) is deliberate: the script cannot drift
#     away from the formalisation without failing loudly.
# --------------------------------------------------------------------------

_DEF = re.compile(r"^def\s+([A-Za-z0-9_]+)\s*:\s*ℚ\s*:=\s*(.+?)\s*$", re.M)


def _eval_rat(expr: str, env: dict[str, Fraction]) -> Fraction:
    """Evaluate a Lean rational literal such as ``(a/b)``, ``2 * c1`` or
    ``-59326318 / 10 ^ 8`` in exact arithmetic."""
    e = expr.strip().rstrip(".")
    e = e.replace("^", "**")
    # integer literals must become Fractions so that / stays exact
    e = re.sub(r"(?<![\w.])(\d+)(?![\w.])", r"Fraction(\1)", e)
    return eval(e, {"__builtins__": {}}, {"Fraction": Fraction, **env})  # noqa: S307


def load_constants() -> dict[str, Fraction]:
    env: dict[str, Fraction] = {}
    for path in (NUMERIC, CERT_ARITH):
        if not path.exists():
            raise SystemExit(f"missing Lean source: {path}")
        for name, expr in _DEF.findall(path.read_text(encoding="utf-8")):
            try:
                env[name] = _eval_rat(expr, env)
            except Exception as exc:  # pragma: no cover - defensive
                raise SystemExit(f"cannot parse `def {name} : ℚ := {expr}`: {exc}")
    required = [
        "r2C", "stC", "usupC", "zinfC", "qabsC", "zl2C", "rhoC",
        "uSecondDerivBound", "residualC2", "concavityBound",
    ]
    missing = [k for k in required if k not in env]
    if missing:
        raise SystemExit(f"constants not found in Lean sources: {missing}")
    return env


# --------------------------------------------------------------------------
# 2.  Outward rounding helpers.  Every displayed number must be a *valid
#     bound in the direction the manuscript uses it*.
# --------------------------------------------------------------------------

def round_up(x: Fraction, places: int) -> Fraction:
    """Smallest multiple of 10^-places that is >= x."""
    scale = 10 ** places
    return Fraction(-((-x * scale).__floor__()), scale)


def round_down(x: Fraction, places: int) -> Fraction:
    """Largest multiple of 10^-places that is <= x."""
    scale = 10 ** places
    return Fraction((x * scale).__floor__(), scale)


def dec(x: Fraction, places: int) -> str:
    """Exact fixed-point rendering of a rational that is a multiple of
    10^-places (no float ever touches a displayed digit)."""
    scale = 10 ** places
    n = x * scale
    if n.denominator != 1:
        raise ValueError(f"{x} is not a multiple of 10^-{places}")
    n = int(n)
    sign = "-" if n < 0 else ""
    n = abs(n)
    s = str(n).rjust(places + 1, "0")
    return f"{sign}{s[:-places]}.{s[-places:]}" if places else f"{sign}{s}"


def agreeing_decimals(lo: Fraction, hi: Fraction, cap: int = 40) -> int:
    """Number of decimal places to which lo and hi agree after truncation."""
    for p in range(cap, -1, -1):
        if round_down(lo, p) == round_down(hi, p):
            return p
    return 0


# --------------------------------------------------------------------------
# 3.  The z'' certificate display.
# --------------------------------------------------------------------------

ZPP_TERMS = ("r0pp", "tail", "twoZinf", "qz")

ZPP_LABELS = {
    "r0pp": r"\|r_0''\|_\infty",
    "tail": r"\sigma_M\|u\|_\infty",
    "twoZinf": r"2\|z\|_\infty",
    "qz": r"q_{\mathrm{abs}}\|z\|_2",
}


def zpp_terms(k: dict[str, Fraction]) -> dict[str, Fraction]:
    return {
        "r0pp": k["r2C"],
        "tail": k["stC"] * k["usupC"],
        "twoZinf": 2 * k["zinfC"],
        "qz": k["qabsC"] * k["zl2C"],
    }


def safe_display_precision(k: dict[str, Fraction], max_places: int = 30) -> int:
    """Smallest number of decimal places at which every term can be rounded
    *up* independently and the printed addends still sum to no more than the
    certified bound.  This is the whole point of the file."""
    terms = zpp_terms(k)
    bound = k["residualC2"]
    # Strict: the printed addends must sum to something visibly *below* the
    # printed bound.  At 13 places the sum lands exactly on it, which reads as
    # if the bound were not strict.
    for places in range(1, max_places + 1):
        if sum(round_up(v, places) for v in terms.values()) < bound:
            return places
    raise SystemExit("no display precision satisfies the summation property")


def zpp_display(k: dict[str, Fraction]) -> dict[str, object]:
    places = safe_display_precision(k)
    terms = zpp_terms(k)
    shown = {name: round_up(v, places) for name, v in terms.items()}
    shown_total = sum(shown.values())
    bound = k["residualC2"]

    # --- the properties this file exists to guarantee -----------------------
    for name, v in terms.items():
        assert shown[name] >= v, f"{name}: displayed value is not an upper bound"
    assert shown_total < bound, "printed addends do not sum strictly below the printed bound"
    concl = k["uSecondDerivBound"] + shown_total
    assert concl < k["concavityBound"], "concavity conclusion fails at display precision"

    return {
        "places": places,
        "exact": terms,
        "shown": shown,
        "shown_total": shown_total,
        "bound": bound,
        "exact_total": sum(terms.values()),
        "concavity_lhs": concl,
        "concavity_bound": k["concavityBound"],
        "uSecondDerivBound": k["uSecondDerivBound"],
    }


# --------------------------------------------------------------------------
# 4.  The c* / H* / D* enclosure, re-derived here so the manuscript's
#     displayed digit count is not asserted by hand.
# --------------------------------------------------------------------------

C_LOWER = Fraction(3535572501442319, 4000000000000000)
C_UPPER = Fraction(110486640670072469, 125000000000000000)


def enclosures() -> dict[str, object]:
    h_lo = 2 - 1 / C_LOWER
    h_hi = 2 - 1 / C_UPPER
    d_lo = (1 + h_lo) / 2
    d_hi = (1 + h_hi) / 2
    return {
        "c_lower": C_LOWER, "c_upper": C_UPPER,
        "H_lower": h_lo, "H_upper": h_hi,
        "D_lower": d_lo, "D_upper": d_hi,
        "H_digits": agreeing_decimals(h_lo, h_hi),
        "D_digits": agreeing_decimals(d_lo, d_hi),
        "c_digits": agreeing_decimals(C_LOWER, C_UPPER),
        "target": Fraction(86957, 100000),
    }


# --------------------------------------------------------------------------
# 5.  The F_1 window functional, used only to validate the comparison
#     numbers the manuscript quotes against the source's Remark 7.1.
# --------------------------------------------------------------------------

def _a(k: int) -> Fraction:
    """a_k = 2^(2k+1) (k-1)! / (2k)!  for k >= 1."""
    num = 2 ** (2 * k + 1)
    fnum = 1
    for i in range(1, k):
        fnum *= i
    fden = 1
    for i in range(1, 2 * k + 1):
        fden *= i
    return Fraction(num * fnum, fden)


def _poly_mul(p, q):
    out = [Fraction(0)] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        if a:
            for j, b in enumerate(q):
                out[i + j] += a * b
    return out


def _poly_int(p, lo, hi):
    tot = Fraction(0)
    for i, a in enumerate(p):
        if a:
            tot += a * (hi ** (i + 1) - lo ** (i + 1)) / (i + 1)
    return tot


def R_F1(v_coeffs, K: int = 80):
    """R_{F_1}(psi) for an even polynomial psi(s) = sum v_coeffs[j] s^j on
    [-1/2, 1/2].  Returns (value, rigorous tail bound on the truncation)."""
    half = Fraction(1, 2)
    I1 = _poly_int(v_coeffs, -half, half)
    I2 = _poly_int(_poly_mul(v_coeffs, v_coeffs), -half, half)

    # g(r) = int v(s) v(s-r) ds over the overlap, as a polynomial in r.
    # Expand v(s-r) symbolically in s with coefficients polynomial in r.
    # Simpler: integrate numerically-exactly by expanding the product in s
    # for each power of r via binomial expansion.
    # v(s-r) = sum_j v_j (s-r)^j
    from math import comb
    # build the double polynomial P[i][m] = coefficient of s^i r^m in v(s)v(s-r)
    deg = len(v_coeffs) - 1
    P = [[Fraction(0)] * (2 * deg + 1) for _ in range(2 * deg + 1)]
    for a_i, va in enumerate(v_coeffs):
        if not va:
            continue
        for b_j, vb in enumerate(v_coeffs):
            if not vb:
                continue
            for m in range(b_j + 1):  # (s-r)^b = sum_m C(b,m) s^(b-m) (-r)^m
                c = Fraction(comb(b_j, m) * (-1) ** m) * va * vb
                P[a_i + b_j - m][m] += c
    # g(r) = int_{r-1/2}^{1/2} (that polynomial in s) ds
    g = [Fraction(0)] * (2 * deg + 2)
    for i in range(2 * deg + 1):
        for m in range(2 * deg + 1):
            c = P[i][m]
            if not c:
                continue
            # int s^i ds from r-1/2 to 1/2  =  ((1/2)^{i+1} - (r-1/2)^{i+1})/(i+1)
            g[m] += c * (half ** (i + 1)) / (i + 1)
            for t in range(i + 2):
                coef = Fraction(comb(i + 1, t)) * (-half) ** (i + 1 - t)
                if m + t < len(g):
                    g[m + t] -= c * coef / (i + 1)
                elif coef != 0:
                    g.extend([Fraction(0)] * (m + t - len(g) + 1))
                    g[m + t] -= c * coef / (i + 1)

    def Ig(power: int) -> Fraction:
        return sum(c / (power + j + 1) for j, c in enumerate(g) if c)

    pair = Ig(1) - 4 * Ig(2)
    for k in range(1, K + 1):
        pair += _a(k) * Ig(2 * k + 1)
    pair *= 2

    gmax = sum(abs(c) for c in g)
    tail = sum(_a(k) for k in range(K + 1, K + 12)) * gmax * 2
    return (I2 + pair) / (I1 * I1), tail


FLAT = [Fraction(1)]
QUARTIC = [Fraction(1), Fraction(0), Fraction(-7, 25), Fraction(0), Fraction(-102, 25)]


# --------------------------------------------------------------------------
# 6.  Reporting.
# --------------------------------------------------------------------------

def build() -> dict[str, object]:
    k = load_constants()
    z = zpp_display(k)
    e = enclosures()
    r_flat, t_flat = R_F1(FLAT)
    r_quart, t_quart = R_F1(QUARTIC)
    h_flat, h_quart = 2 - r_flat, 2 - r_quart
    d_flat, d_quart = (1 + h_flat) / 2, (1 + h_quart) / 2
    return {
        "k": k, "z": z, "e": e,
        "flat": {"R": r_flat, "H": h_flat, "D": d_flat, "tail": t_flat},
        "quart": {"R": r_quart, "H": h_quart, "D": d_quart, "tail": t_quart},
        "gap_simple": e["H_lower"] - h_quart,
        "gap_distinct": e["D_lower"] - d_quart,
    }


def _f(x: Fraction, p: int = 18) -> str:
    with localcontext() as ctx:
        ctx.prec = _PREC
        return f"{Decimal(x.numerator) / Decimal(x.denominator):.{p}f}"


def report(b) -> None:
    z, e, k = b["z"], b["e"], b["k"]
    p = z["places"]
    print("=" * 74)
    print("PUB 1 -- PUBLICATION-SAFE DISPLAY VALUES")
    print(f"constants parsed from {CERT_ARITH.name} and {NUMERIC.name}")
    print("=" * 74)
    print(f"\n[1] z'' CERTIFICATE   (display precision: {p} decimal places)\n")
    print(f"    {'term':22s} {'exact':<26s} displayed upper bound")
    for name in ZPP_TERMS:
        print(f"    {ZPP_LABELS[name]:22s} {_f(z['exact'][name], 24):<26s} {dec(z['shown'][name], p)}")
    print(f"    {'-' * 68}")
    print(f"    {'sum of displayed':22s} {'':<26s} {dec(z['shown_total'], p)}")
    print(f"    {'printed bound':22s} {'':<26s} {_f(z['bound'], p)}")
    print(f"\n    sum(displayed) <= printed bound : {z['shown_total'] <= z['bound']}"
          f"   (slack {float(z['bound'] - z['shown_total']):.4e})")
    print(f"    exact total                     : {_f(z['exact_total'], 24)}")
    print(f"\n[2] DOWNSTREAM CONCAVITY (uses the DISPLAYED total, not the exact one)\n")
    print(f"    u''            <= {_f(z['uSecondDerivBound'], 18)}   = {z['uSecondDerivBound']}")
    print(f"    + ||z''||_inf   < {dec(z['shown_total'], p)}")
    print(f"    => w''          < {_f(z['concavity_lhs'], 18)}")
    print(f"    concavity bound   {_f(z['concavity_bound'], 18)}   = {z['concavity_bound']}")
    print(f"    strict           : {z['concavity_lhs'] < z['concavity_bound']}"
          f"   (margin {float(z['concavity_bound'] - z['concavity_lhs']):.4e})")
    print(f"\n[3] ENCLOSURES\n")
    print(f"    c* in [{_f(e['c_lower'], 20)}, {_f(e['c_upper'], 20)}]  -> {e['c_digits']} decimals certified")
    print(f"    H* in [{_f(e['H_lower'], 20)}, {_f(e['H_upper'], 20)}]  -> {e['H_digits']} decimals certified")
    print(f"    D* in [{_f(e['D_lower'], 20)}, {_f(e['D_upper'], 20)}]  -> {e['D_digits']} decimals certified")
    print(f"    H* display (truncated to certified length): {dec(round_down(e['H_lower'], e['H_digits']), e['H_digits'])}")
    print(f"    D* display (truncated to certified length): {dec(round_down(e['D_lower'], e['D_digits']), e['D_digits'])}")
    print(f"    D* enclosure: {e['D_lower']} <= D* <= {e['D_upper']}")
    print(f"    H*_upper < 0.86957 : {e['H_upper'] < e['target']}")
    print(f"\n[4] SOURCE COMPARISON VALUES (validate against [7, Remark 7.1])\n")
    for nm, key, exp_h, exp_d in (("flat", "flat", "0.85838", "0.92919"),
                                  ("quartic", "quart", "0.86864", "0.93432")):
        d = b[key]
        print(f"    {nm:8s} R={_f(d['R'], 12)}  H={_f(d['H'], 12)} (src {exp_h})"
              f"  D={_f(d['D'], 12)} (src {exp_d})   series tail < {float(d['tail']):.1e}")
    print(f"\n    gap H* - H(quartic) = {float(b['gap_simple']):.6e}   (< 1.0e-6 : {b['gap_simple'] < Fraction(1, 10**6)})")
    print(f"    gap D* - D(quartic) = {float(b['gap_distinct']):.6e}   (< 5.0e-7 : {b['gap_distinct'] < Fraction(5, 10**7)})")
    print(f"\n[5] rho = {k['rhoC']}  (~{float(k['rhoC']):.3e}, < 1.6e-20 : {k['rhoC'] < Fraction(16, 10**21)})")
    print("\n" + "=" * 74)
    print("ALL DISPLAY INVARIANTS HOLD")
    print("=" * 74)


def latex(b) -> None:
    z = b["z"]; p = z["places"]
    print("% --- emitted by scripts/pub1_certify_display.py; do not hand-edit ---")
    print(r"\[ \|r_0''\|_\infty < " + dec(z["shown"]["r0pp"], p) + r", \qquad"
          r" \sigma_M\|u\|_\infty < " + dec(z["shown"]["tail"], p) + r", \]")
    print(r"\[ 2\|z\|_\infty < " + dec(z["shown"]["twoZinf"], p) + r", \qquad"
          r" q_{\mathrm{abs}}\|z\|_2 < " + dec(z["shown"]["qz"], p) + r", \]")
    print(r"\[ \text{sum} \le " + dec(z["shown_total"], p) + r" < " + _f(z["bound"], p) + r" \]")


def manifest(b) -> None:
    z, e = b["z"], b["e"]
    p = z["places"]
    for name in ZPP_TERMS:
        print(f"zpp.{name}={dec(z['shown'][name], p)}")
    print(f"zpp.total={dec(z['shown_total'], p)}")
    print(f"zpp.bound={_f(z['bound'], p)}")
    print(f"H.digits={e['H_digits']}")
    print(f"D.digits={e['D_digits']}")
    print(f"H.display={dec(round_down(e['H_lower'], e['H_digits']), e['H_digits'])}")
    print(f"D.display={dec(round_down(e['D_lower'], e['D_digits']), e['D_digits'])}")
    print(f"D.lower={e['D_lower']}")
    print(f"D.upper={e['D_upper']}")


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--latex", action="store_true")
    ap.add_argument("--manifest", action="store_true")
    args = ap.parse_args()
    b = build()
    if args.latex:
        latex(b)
    elif args.manifest:
        manifest(b)
    else:
        report(b)
    return 0


if __name__ == "__main__":
    sys.exit(main())

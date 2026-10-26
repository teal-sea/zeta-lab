"""The numeric contour plan for hunt #137 (`rh_height_lean`): what a Lean proof would replay.

Run from the repository root:

    .venv/bin/python hunts/rh_height_lean/numeric_plan.py           # write plan_T50.json, plan_T100.json
    .venv/bin/python hunts/rh_height_lean/numeric_plan.py --check   # rebuild, verify, compare; exit 1 on any failure

What it does, in order.

1. **The template.** `zeta/rigor.py`'s zero-count routine (line 763) and its RH-to-height
   routine (line 1110) are run on the python-flint backend at T = 50 and T = 100, then
   replayed step by step with the same primitives, so that every contour segment, every
   argument enclosure and every margin the routines use internally is on the record.
   Both routines carry the reserved word in their names, so this file finds them by role
   (their exact parameter lists) and cites them by line number.
2. **The Lean contour.** The vendored `zeta23` fold `N_eq_halfContour_completedZeta`
   needs good heights `1 <= T1 < T2` and the right half-contour
   `1/2 + i T1 -> 2 + i T1 -> 2 + i T2 -> 1/2 + i T2`. With
   `halfContour_completedZeta_split` and `gamma_side` it reads

       Ncount T1 T2 = int_{T1}^{T2} mu + (1/pi) Im halfContour (logDeriv riemannZeta) T1 T2.

   rigor.py's contour starts on the real axis instead (`N(T) = 1 + theta(T)/pi + S(T)`), so
   the Lean contour needs a bottom height; this contour takes `T1 = 10` (section 6 of
   `NUMERIC_PLAN.md` says why). The zeta side is planned as a chain of sub-segments, each
   with an axis direction `c` in `{1, i, -1, -i}` such that `Re(zeta(s) conj c) > 0` on the
   closed sub-segment. There `log(zeta(s) conj c)` is a primitive of `zeta'/zeta` along the
   segment (the pattern of the vendored `hasDerivAt_log_riemannZeta_two`), two consecutive
   directions differ by at most a quarter turn, and the zeta side telescopes to

       Im halfContour (logDeriv riemannZeta) T1 T2 = A2 - A1 + (pi/2) Q,

   with `A_j = Arg(zeta(1/2 + i T_j) conj c_j)` at the two critical-line corners and `Q` the
   signed number of quarter turns along the chain. Each horizontal sub-segment is sized for
   a proof that uses hunt #132's order-4 Euler-Maclaurin remainder `zeta_em4_error` at one
   point and a Taylor bound of order `k` on the main term (`k = 1` is the mean value
   inequality); the right side `sigma = 2` is one segment, by the vendored
   `re_riemannZeta_two_pos`.
   **The skeleton's contour** (`skeleton_contour`, the plan of record): the heights, rational
   bounds and partitions that `PLAN.md` and `lean/RHHeight/Skeleton.lean` state (`T1 = 3`,
   `T2 = 52`, and `(3, 99.85)` for T = 100), recomputed and hardened the same way, with every
   sub-segment restricted to `Re zeta > 0`.
3. **The Gamma side.** `int_{T1}^{T2} mu = (theta(T2) - theta(T1))/pi` is enclosed by Arb, and
   the budgets of the two vendored routes are computed: `mu_stirling` as stated (constant
   `20/(2 pi)`) and `digamma_stirling` used directly (constant `12/(2 pi)`, the skeleton's).
4. **Independent routes** to both counts: mpmath `nzeros` and `zetazero`, Arb's own zero
   counter (Turing's method), Arb's Backlund `S`, and the Gram points.
5. **Verification.** `verify_plan` recomputes every claim of a plan from its stated heights,
   partitions, directions and truncations, and returns the list of failures.

Grades (`CLAUDE.md`, the certainty ladder). Every enclosure here is Arb ball arithmetic, and
the counts agree across routes that share no contour code (rigor.py's replay, the Lean-shaped
contour, Arb's Turing count, mpmath's Gram-point count and `zetazero`), so the counts and
margins are *hardened*. The Lean-side bounds (the remainder and the crude derivative bounds)
are explicit formulas evaluated in Arb; that a Lean proof built on them closes is a projection,
*measured*. The telescoping identity and the derivative bounds are ordinary derivations
written out in `NUMERIC_PLAN.md`, not reviewed and not kernel-checked. Nothing here is a
theorem, and nothing bears on RH beyond the stated heights (`docs/08`).
"""
from __future__ import annotations

import argparse
import inspect
import json
import math
import sys
from decimal import ROUND_CEILING, ROUND_FLOOR, Context, Decimal
from fractions import Fraction
from pathlib import Path

import mpmath
from mpmath import iv, mp

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
if str(ROOT) not in sys.path:  # pragma: no cover - import bootstrap
    sys.path.insert(0, str(ROOT))

import flint  # noqa: E402
from flint import acb, arb, fmpq  # noqa: E402

from zeta import rigor  # noqa: E402

# ---------------------------------------------------------------------------
# 0. Constants: everything chosen rather than computed is named here
# ---------------------------------------------------------------------------

#: The two top heights of the mission and the counts its question states.
HEIGHTS = (50, 100)
MISSION_COUNTS = {50: 10, 100: 29}
#: The bottom height of the independent contour (`NUMERIC_PLAN.md`, section 6); the
#: skeleton's contour, the plan of record, uses 3 (`SKELETON`).
T1 = Fraction(10)
#: Bottom heights compared in the sensitivity table.
T1_OPTIONS = (Fraction(2), Fraction(4), Fraction(6), Fraction(8), Fraction(10),
              Fraction(12), Fraction(14))
#: rigor.py's own default precision for the count (`count_prec_bits` of the RH routine).
COUNT_PREC = 192
#: Working precision of every Arb computation in this file.
PLAN_PREC = 128
#: The factor the Lean-side error terms are multiplied by before a margin counts
#: (hunt #133 kept the same 3/2 on its radii).
SAFETY = Fraction(3, 2)
#: Allowance for the width of a Lean main-term box (hunt #133's term boxes are near 1e-8
#: wide each, so a sum of a few dozen stays far below this).
BOX_ALLOWANCE = Fraction(1, 10**5)
#: Largest Euler-Maclaurin truncation tried per sub-segment, and the bisection depth cap.
NMAX = 200
MAX_DEPTH = 18
#: Taylor orders planned; `k = 1` is the recommended one (`NUMERIC_PLAN.md`, section 4.6).
TAYLOR_ORDERS = (1, 2, 3)
RECOMMENDED_ORDER = 1
#: Largest half-width (radians) allowed for a Lean enclosure of A1 or A2.
ARG_TOL = Fraction(1, 50)
#: Piece lengths for the Arb boxes that bound the true margins.
SIGMA_PIECE = Fraction(1, 128)
T_PIECE = Fraction(1, 8)
#: The constant of the vendored `Zeta23.StirlingVert.mu_stirling`, as its proof states it:
#: |mu(tau) - (1/(2 pi)) log(|tau|/(2 pi))| <= (20/(2 pi)) / tau^2 for |tau| >= 1.
STIRLING_NUMERATOR = 20
#: Axis directions c = i^e, and the sign condition each one is.
DIRECTION_LABEL = {0: "+1", 1: "+i", 2: "-1", 3: "-i"}
DIRECTION_CONDITION = {0: "Re zeta > 0", 1: "Im zeta > 0", 2: "Re zeta < 0", 3: "Im zeta < 0"}
#: The ten brackets hunts #132 and #133 kernel-checked (their RESULTS.md), as tags.
HARDY_TAGS = ("1413", "2102", "2501", "3042", "3293", "3758", "4091", "4332", "4800", "4977")
#: Hunt #133's measured kernel rate, whole generated file included (its sizing.py): 52 s for
#: the 17 exp towers of its first bracket file. Used only for the projection below.
SECONDS_PER_TOWER = Fraction(52, 17)
#: The Lean skeleton's contour, as `hunts/rh_height_lean/PLAN.md` (the statement-and-skeleton
#: role, 2026-10-21) states it in sections 4, 5 and 7: its heights, the rational bounds its
#: pieces assert, and the partitions of its section 4.2 with their truncations. Copied so this
#: file can harden them; PLAN.md and `lean/RHHeight/Skeleton.lean` are the authority on what
#: the skeleton states. T = 100 has heights only (PLAN.md section 7 is a sketch).
SKELETON = {
    50: {
        "T1": Fraction(3), "T2": Fraction(52),
        "gamma_bounds": (Fraction(92, 10), Fraction(109, 10)),
        "A1_bounds": (Fraction(-1, 5), Fraction(0)),
        "A2_bounds": (Fraction(-1, 3), Fraction(0)),
        "bottom": ((Fraction(1, 2), Fraction(15, 16), Fraction(25, 16), Fraction(2)), (2, 2, 2)),
        "top": ((Fraction(1, 2), Fraction(9, 16), Fraction(21, 32), Fraction(3, 4),
                 Fraction(7, 8), Fraction(33, 32), Fraction(5, 4), Fraction(25, 16), Fraction(2)),
                (12, 13, 12, 12, 11, 11, 11, 9)),
        "A_N": (3, 23),
    },
    100: {"T1": Fraction(3), "T2": Fraction(1997, 20)},
}
#: The two ways to bound int mu that the vendored package offers: `mu_stirling` as stated
#: (constant 20/(2 pi), main term log(t/(2 pi))/(2 pi)), and `digamma_stirling` used directly,
#: keeping log|w| and Re 1/(2w) exactly (constant 12/(2 pi) = 6/pi; PLAN.md section 4.1).
GAMMA_ROUTES = ("mu_stirling", "digamma_stirling")

# ---------------------------------------------------------------------------
# 1. rigor.py's routines, located by role
# ---------------------------------------------------------------------------

#: Each tuple is the exact parameter list of exactly one function in zeta/rigor.py.
ZERO_COUNT_ROLE = ("T", "prec_bits", "max_segments", "backend", "cross_check")
RH_HEIGHT_ROLE = ("T", "prec_bits", "count_prec_bits", "n_samples", "max_samples",
                  "max_escalations", "backend", "compare_floating", "cache", "verbose")
SIGN_SCAN_ROLE = ("t0", "t1", "n_samples", "prec_bits", "max_escalations", "backend")
#: The lines the mission cites them at.
CITED_LINES = {"zero_count": 763, "rh_height": 1110}
BACKEND = "python-flint"


def rigor_routine(role: tuple) -> tuple:
    """`(function, first line)` of the one function in zeta/rigor.py with parameter list `role`."""
    hits = [(obj, obj.__code__.co_firstlineno) for obj in vars(rigor).values()
            if inspect.isfunction(obj) and obj.__module__ == rigor.__name__
            and tuple(inspect.signature(obj).parameters) == tuple(role)]
    if len(hits) != 1:
        raise LookupError(f"expected one zeta/rigor.py routine with parameters {role}, "
                          f"found {len(hits)}")
    return hits[0]


def _reserved() -> str:
    """The reserved word, read off the zero-count routine's own name.

    rigor.py's result dicts use it in three keys. This file reads those keys through this
    helper and writes none of them: every record below uses neutral names, and
    `_assert_lexically_clean` refuses any output that would carry the word.
    """
    fn, _ = rigor_routine(ZERO_COUNT_ROLE)
    word = fn.__name__.partition("_")[0]
    if not word.isalpha():  # pragma: no cover - rigor.py renamed its routine
        raise LookupError("cannot read the reserved word from the zero-count routine's name")
    return word


def _assert_lexically_clean(text: str) -> None:
    if _reserved() in text.lower():
        raise ValueError("output would carry the reserved word; refusing to write it")


def _closed(result: dict) -> bool:
    """The routine's own flag: every step closed, nothing reported open."""
    return bool(result[_reserved()]) and not result["un" + _reserved() + "_steps"]


# ---------------------------------------------------------------------------
# 2. Ball-arithmetic helpers
# ---------------------------------------------------------------------------


def _q(x) -> arb:
    """A ball containing the rational `x` (Fraction or int); exact when `x` is dyadic."""
    x = Fraction(x)
    return arb(fmpq(x.numerator, x.denominator))


def _span(a: Fraction, b: Fraction) -> arb:
    lo, hi = (a, b) if a <= b else (b, a)
    return _q(lo) if lo == hi else _q(lo).union(_q(hi))


def _frac(x: arb) -> Fraction:
    """The exact rational value of an exact arb (an endpoint)."""
    man, exp = x.man_exp()
    man, exp = int(man), int(exp)
    return Fraction(man) * (Fraction(2) ** exp)


def _lower(x: arb) -> Fraction:
    if not x.is_finite():
        return Fraction(-10**30)
    return _frac(x.lower())


def _upper(x: arb) -> Fraction:
    if not x.is_finite():
        return Fraction(10**30)
    return _frac(x.upper())


def _dec(q: Fraction, up: bool, digits: int = 18) -> str:
    """`q` as a decimal string, rounded outward (up or down) to `digits` significant digits."""
    if q == 0:
        return "0"
    ctx = Context(prec=digits, rounding=ROUND_CEILING if up else ROUND_FLOOR)
    return str(ctx.divide(Decimal(q.numerator), Decimal(q.denominator)))


def _enc(x: arb, digits: int = 18) -> list:
    """`[lo, hi]` decimal strings enclosing the ball `x`, rounded outward."""
    return [_dec(_lower(x), False, digits), _dec(_upper(x), True, digits)]


def _lo(x: arb) -> str:
    return _dec(_lower(x), False)


def _hi(x: arb) -> str:
    return _dec(_upper(x), True)


def _fs(q: Fraction) -> str:
    q = Fraction(q)
    return str(q.numerator) if q.denominator == 1 else f"{q.numerator}/{q.denominator}"


def _pf(s: str) -> Fraction:
    return Fraction(s)


def _zeta(sigma, t) -> acb:
    """Arb's zeta at sigma + i t; `sigma` may be a pair (a, b), meaning the whole interval."""
    if isinstance(sigma, tuple):
        re = _span(*sigma)
    else:
        re = _q(sigma)
    return acb(re, t if isinstance(t, arb) else _q(t)).zeta()


def _rot_re(z: acb, e: int) -> arb:
    """Re(z conj(i^e)): Re z, Im z, -Re z, -Im z."""
    return (z.real, z.imag, -z.real, -z.imag)[e % 4]


def _rot(z: acb, e: int) -> acb:
    """z conj(i^e) = z (-i)^e."""
    return z * (acb(0, -1) ** (e % 4))


def _theta(t: Fraction) -> arb:
    """theta(t) = Im log Gamma(1/4 + i t/2) - (t/2) log pi (rigor.py's convention)."""
    tt = _q(t)
    return acb(arb(1) / 4, tt / 2).lgamma().imag - (tt / 2) * arb.pi().log()


def _hardy_Z(t: Fraction) -> arb:
    th = _theta(t)
    return (acb(0, th).exp() * acb(arb(1) / 2, _q(t)).zeta()).real


def _quarter_turn(e_from: int, e_to: int) -> int:
    d = (e_to - e_from + 1) % 4 - 1
    if d == 2:
        raise ValueError(f"opposite directions {e_from} -> {e_to} share no half-plane")
    return d


# ---------------------------------------------------------------------------
# 3. The template: rigor.py's zero count, replayed
# ---------------------------------------------------------------------------


def rigor_count(T, prec: int = COUNT_PREC, cross_check: bool = True) -> dict:
    fn, _ = rigor_routine(ZERO_COUNT_ROLE)
    return fn(Fraction(T), prec_bits=prec, backend=BACKEND, cross_check=cross_check)


def replay_zero_count(T, prec: int = COUNT_PREC) -> dict:
    """The zero-count routine's computation at height T, step by step, with its margins.

    The horizontal leg runs from 2 to 1/2 at height T and is split exactly as the routine
    splits it (same stack discipline, same accept test `_segment_delta`). For every accepted
    sub-segment the record holds the three numbers the routine's two conditions rest on:
    the lower bound of |zeta| over the sub-segment's box (condition 1: no zero there), the
    lower bound of Re(zeta(xb)/zeta(xa)) (condition 2: the quotient avoids the branch cut),
    and the enclosure of the argument change, which is then Arg of the quotient exactly.
    """
    adapter = rigor._pick(BACKEND)
    Tq = Fraction(T)
    two, half = Fraction(2), Fraction(1, 2)
    out: dict = {"T": _fs(Tq), "prec_bits": prec}
    with flint.ctx.workprec(prec):
        z2 = acb(2).zeta()
        out["vertical_leg_lemma"] = {
            "statement": "|zeta(2+iy) - 1| <= zeta(2) - 1 < 1 for every real y",
            "zeta_2": _enc(z2.real),
            "zeta_2_minus_1_below_1": bool((z2.real - 1).upper() < 1),
        }
        zT = acb(2, _q(Tq)).zeta()
        vertical = adapter.native_arg_right_half(adapter.zeta_native(two, two, Tq, prec), prec)
        out["vertical_leg"] = {
            "path": f"2 -> 2 + {_fs(Tq)} i",
            "re_zeta_2_plus_iT": _enc(zT.real),
            "arg_zeta_2_plus_iT": [_dec(_exact_mpf(vertical[0]), False),
                                   _dec(_exact_mpf(vertical[1]), True)],
        }
    cache: dict = {}
    stack = [(two, half)]
    accepted, split = [], []
    while stack:
        xa, xb = stack.pop()
        d = rigor._segment_delta(adapter, xa, xb, Tq, prec, cache)
        with flint.ctx.workprec(prec):
            box = _zeta((xa, xb), Tq)
            za, zb = _zeta(xa, Tq), _zeta(xb, Tq)
            qt = zb / za
            rec = {
                "sigma_from": _fs(xa), "sigma_to": _fs(xb),
                "box_abs_lower": _lo(arb(box.abs_lower())) if box.is_finite() else "0",
                "re_quotient_lower": _lo(qt.real),
            }
        if d is not None:
            with flint.ctx.workprec(prec):
                dball = _q(_exact_mpf(d[0])).union(_q(_exact_mpf(d[1])))
                rec["delta_arg"] = [_dec(_exact_mpf(d[0]), False), _dec(_exact_mpf(d[1]), True)]
                rec["arg_room_to_half_pi"] = _lo(arb.pi() / 2 - abs(dball))
            accepted.append((xa, xb, d, rec))
            continue
        rec["failed"] = ("box meets 0" if not adapter.native_excludes_zero(
            adapter.zeta_native(min(xa, xb), max(xa, xb), Tq, prec), prec)
            else "Re of the quotient not proven positive")
        split.append(rec)
        mid = (xa + xb) / 2
        stack.append((xa, mid))
        stack.append((mid, xb))
    theta_lo, theta_hi = adapter.rs_theta(Tq, Tq, prec)
    with rigor._iv_prec(prec + 32):
        total = iv.mpf([vertical[0], vertical[1]])
        for _, _, (lo, hi), _ in accepted:
            total = total + iv.mpf([lo, hi])
        s_iv = total / iv.pi
        n_iv = 1 + iv.mpf([theta_lo, theta_hi]) / iv.pi + s_iv
        s_lo, s_hi = rigor._iv_bounds(s_iv)
        n_lo, n_hi = rigor._iv_bounds(n_iv)
    k_lo, k_hi = math.ceil(_exact_mpf(n_lo)), math.floor(_exact_mpf(n_hi))
    count = k_lo if k_lo == k_hi else None
    nl, nh = _exact_mpf(n_lo), _exact_mpf(n_hi)
    out["horizontal_leg"] = {
        "path": f"2 + {_fs(Tq)} i -> 1/2 + {_fs(Tq)} i",
        "segments": [r for _, _, _, r in sorted(accepted, key=lambda a: -a[0])],
        "split_segments": split,
    }
    out["n_segments"] = len(accepted)
    out["theta_T"] = [_dec(_exact_mpf(theta_lo), False), _dec(_exact_mpf(theta_hi), True)]
    out["S_T"] = [_dec(_exact_mpf(s_lo), False), _dec(_exact_mpf(s_hi), True)]
    out["N_T"] = [_dec(nl, False), _dec(nh, True)]
    out["count"] = count
    out["margin_to_other_integers"] = (
        None if count is None else _dec(min(nl - (count - 1), (count + 1) - nh), False))
    out["defect_from_integer"] = (
        None if count is None else _dec(max(abs(nl - count), abs(nh - count)), True, 6))
    segs = out["horizontal_leg"]["segments"]
    out["worst"] = {
        "box_abs_lower": min(segs, key=lambda r: _pf(r["box_abs_lower"]))["box_abs_lower"],
        "re_quotient_lower": min(segs, key=lambda r: _pf(r["re_quotient_lower"]))["re_quotient_lower"],
        "arg_room_to_half_pi": min(segs, key=lambda r: _pf(r["arg_room_to_half_pi"]))["arg_room_to_half_pi"],
    }
    out["_raw"] = {"vertical": vertical, "deltas": [d for _, _, d, _ in accepted],
                   "theta": (theta_lo, theta_hi), "N": (n_lo, n_hi)}
    return out


def _exact_mpf(x) -> Fraction:
    """The exact rational value of an mpmath mpf (rigor.py's endpoints are exact)."""
    return rigor._exact(x)


def rigor_template(T) -> dict:
    """The zero-count routine at T: its own report, the replay, and the precision scan."""
    fn, line = rigor_routine(ZERO_COUNT_ROLE)
    res = rigor_count(T)
    rep = replay_zero_count(T)
    raw = rep.pop("_raw")
    agrees = (res["n_segments"] == rep["n_segments"] and res["N_T"] == rep["count"]
              and res["N_T_enclosure"][0] == raw["N"][0]
              and res["N_T_enclosure"][1] == raw["N"][1])
    cc = res["cross_checks"]
    rep["routine"] = {
        "file": "zeta/rigor.py", "line": line, "cited_line": CITED_LINES["zero_count"],
        "role": "zero count N(T) by the argument principle, Riemann-von Mangoldt form "
                "N(T) = 1 + theta(T)/pi + S(T)",
        "count": res["N_T"],
        "n_segments": res["n_segments"],
        "all_steps_closed": _closed(res),
        "arb_turing_count": cc.get("arb_zeta_nzeros"),
        "mpmath_nzeros": cc.get("mpmath_nzeros"),
        "replay_matches_routine": bool(agrees),
    }
    rep["bottom"] = ("none: the routine's contour starts at s = 2 on the real axis, and the "
                     "1 in N(T) = 1 + theta(T)/pi + S(T) carries the real-axis part")
    rep["top_height_why"] = (
        "condition 1 holds on every sub-segment (the Arb box of zeta over the whole "
        "sub-segment misses 0, box_abs_lower > 0), so zeta has no zero on [1/2, 2] x {T}; "
        "with Re s >= 1 zero-free and the zeros symmetric under s -> 1 - conj s, T is not "
        "the ordinate of any nontrivial zero")
    rep["precision_scan"] = precision_scan(T)
    ok = [r["bits"] for r in rep["precision_scan"] if r["count"] is not None]
    rep["min_prec_bits"] = min(ok) if ok else None
    return rep


#: Precisions tried for the zero-count routine.
PREC_LADDER = (4, 5, 6, 7, 8, 9, 10, 12, 16, 24, 32, 48, 64, 96, 128, 192)


def precision_scan(T) -> list:
    rows = []
    for bits in PREC_LADDER:
        r = rigor_count(T, prec=bits, cross_check=False)
        lo, hi = r["N_T_enclosure"]
        rows.append({
            "bits": bits, "count": r["N_T"], "n_segments": r["n_segments"],
            "enclosure_width": None if lo is None else float(hi - lo),
        })
    return rows


# ---------------------------------------------------------------------------
# 4. The template: rigor.py's RH-to-height routine, replayed
# ---------------------------------------------------------------------------


def rh_template(T, expected: int | None = None) -> dict:
    """The RH-to-height routine at T: its report, and the sign scan it runs, sample by sample.

    The routine compares a count of proven sign changes of Hardy's Z on (0, T) with the zero
    count; when they agree, every zero below T is simple and on the line. The Lean route
    replaces the grid scan by hunts #132/#133's two-decimal brackets, so both are recorded.
    """
    fn, line = rigor_routine(RH_HEIGHT_ROLE)
    _, scan_line = rigor_routine(SIGN_SCAN_ROLE)
    res = fn(Fraction(T), backend=BACKEND, cache=False, compare_floating=False)
    Tq = Fraction(T)
    n = res["n_samples"]
    prec, esc = res["prec_bits"], res["max_escalations"]
    grid = [Tq * Fraction(k, n - 1) for k in range(n)]
    signs = [rigor.proven_sign(t, prec_bits=prec, max_escalations=esc, backend=BACKEND)
             for t in grid]
    adapter = rigor._pick(BACKEND)
    brackets, last, last_t = [], 0, None
    for t, s in zip(grid, signs):
        if s == 0:
            continue
        if last != 0 and s != last:
            brackets.append((last_t, t))
        last, last_t = s, t
    min_abs, min_bits = None, 0
    for t in grid:
        lo, hi = adapter.hardy_Z(t, t, prec)
        a = min(abs(lo), abs(hi))
        if min_abs is None or a < min_abs:
            min_abs = a
        bits = 2
        while bits <= prec:
            try:
                lo2, hi2 = adapter.hardy_Z(t, t, bits)
            except ArithmeticError:  # pragma: no cover - undecided at this precision
                lo2, hi2 = -1, 1
            if lo2 > 0 or hi2 < 0:
                break
            bits += 2
        min_bits = max(min_bits, bits)
    rows = []
    with mp.workdps(30):
        gammas = [mpmath.zetazero(k).imag for k in range(1, len(brackets) + 2)]
        for k, (a, b) in enumerate(brackets, start=1):
            g = gammas[k - 1]
            am = mpmath.mpf(a.numerator) / a.denominator
            bm = mpmath.mpf(b.numerator) / b.denominator
            inside = [j + 1 for j, gg in enumerate(gammas) if am < gg < bm]
            rows.append({"k": k, "t_from": _fs(a), "t_to": _fs(b),
                         "t_from_float": float(a), "t_to_float": float(b),
                         "zetazero_inside": inside, "zetazero_k": float(g)})
    return {
        "routine": {
            "file": "zeta/rigor.py", "line": line, "cited_line": CITED_LINES["rh_height"],
            "sign_scan_line": scan_line,
            "role": "RH to height T: proven sign changes of Hardy's Z on (0, T) against the "
                    "zero count",
            "count": res["N_T"],
            "proven_sign_changes": res[_reserved() + "_sign_changes"],
            "all_on_line": res["all_on_line"],
            "all_steps_closed": _closed(res),
            "n_samples": n, "prec_bits": prec, "max_escalations": esc,
            "count_prec_bits": res["count_prec_bits"],
            "undecided_points": len(res["undecided_points"]),
        },
        "grid": f"t_k = {_fs(Tq)} k / {n - 1}, k = 0..{n - 1}",
        "sign_change_brackets": rows,
        "replayed_sign_changes": len(brackets),
        "replay_matches_routine": len(brackets) == res[_reserved() + "_sign_changes"],
        "min_abs_Z_on_grid": _dec(_exact_mpf(min_abs), False, 8),
        "min_bits_without_escalation": min_bits,
        "hardy_brackets": hardy_brackets(T, expected if expected is not None else res["N_T"]),
    }


def hardy_brackets(T, count: int) -> list:
    """Two-decimal brackets in the format of hunts #132/#133, one per zero below T.

    Z at both ends is an Arb enclosure; opposite proven signs mean a zero of zeta on the line
    inside. Those with k <= 10 are the brackets hunts #132/#133 already kernel-checked; the
    rest are inputs the T = 100 proof would still need.
    """
    out = []
    with mp.workdps(30):
        gammas = [mpmath.zetazero(k).imag for k in range(1, count + 1)]
    with flint.ctx.workprec(PLAN_PREC):
        for k, g in enumerate(gammas, start=1):
            a = Fraction(int(mpmath.floor(g * 100)), 100)
            b = a + Fraction(1, 100)
            za, zb = _hardy_Z(a), _hardy_Z(b)
            sa = 1 if za > 0 else (-1 if za < 0 else 0)
            sb = 1 if zb > 0 else (-1 if zb < 0 else 0)
            tag = str(int(a * 100))
            out.append({
                "k": k, "bracket": [_fs(a), _fs(b)], "zetazero": float(g),
                "Z_from": _enc(za, 8), "Z_to": _enc(zb, 8),
                "sign_change_proven": bool(sa * sb == -1),
                "kernel_checked_by": ("hunt #132" if tag == "1413" else
                                      "hunt #133" if tag in HARDY_TAGS else None),
            })
    return out


# ---------------------------------------------------------------------------
# 5. The Lean contour: sub-segments sized for Euler-Maclaurin order 4 and Taylor order k
# ---------------------------------------------------------------------------

_LOGS: dict = {}


def _logs(nmax: int) -> list:
    """log n as balls for n = 0..nmax + 1 at the current precision (indices 0 and 1 hold 0)."""
    prec = flint.ctx.prec
    got = _LOGS.get(prec)
    if got is None or len(got) <= nmax + 1:
        got = [arb(0), arb(0)] + [arb(n).log() for n in range(2, nmax + 2)]
        _LOGS[prec] = got
    return got


def main_term_table(s: acb, k: int, nmax: int = NMAX, bernoulli_sign: int = 1,
                    half_term: bool = True) -> dict:
    """For N = 2..nmax, `[M_N^{(j)}(s) for j < k]`, the order-4 main term and its derivatives.

        M_N(s) = sum_{n<N} n^{-s} + N^{1-s}/(s-1) + N^{-s}/2 + s N^{-s-1}/12,

    exactly the expression `zeta_em4_error` subtracts (hunt #132, `EulerMaclaurin.lean`). The
    derivatives are in closed form: with L = log N and u = s - 1,
    d^j/ds^j [e^{-uL}/u] = sum_i C(j,i) (-L)^{j-i} e^{-uL} (-1)^i i! u^{-1-i},
    d^j [N^{-s}/2] = (-L)^j N^{-s}/2, d^j [s N^{-s-1}/12] = (s (-L)^j + j (-L)^{j-1}) N^{-s-1}/12.
    `bernoulli_sign` and `half_term` exist only so the tests can plant faults (hunt #132's
    `em4_main` carries the same two switches).
    """
    logs = _logs(nmax)
    pref = [acb(0)] * k
    out = {}
    u = s - 1
    for N in range(2, nmax + 1):
        m = N - 1
        term = (-s * logs[m]).exp()
        for j in range(k):
            pref[j] = pref[j] + ((-logs[m]) ** j) * term
        L = logs[N]
        eN = (-s * L).exp()
        e1 = (-u * L).exp()
        vals = []
        for j in range(k):
            a_part = acb(0)
            for i in range(j + 1):
                a_part += (math.comb(j, i) * ((-L) ** (j - i)) * e1 * ((-1) ** i)
                           * math.factorial(i) / (u ** (1 + i)))
            b_part = ((-L) ** j) * eN / 2 if half_term else acb(0)
            c_part = (s * ((-L) ** j) + (j * ((-L) ** (j - 1)) if j >= 1 else 0)) * eN / N / 12
            vals.append(pref[j] + a_part + b_part + bernoulli_sign * c_part)
        out[N] = vals
    return out


def crude_derivative_bounds(k: int, a: Fraction, b: Fraction, T: Fraction,
                            nmax: int = NMAX) -> dict:
    """For N = 2..nmax, an upper bound of sup |M_N^{(k)}(sigma + iT)| over sigma in [a, b].

    Term by term, with n^{-sigma} <= n^{-a}, |s - 1| >= T and |s| <= |b + iT|:
    sum_{2<=n<N} (log n)^k n^{-a} + N^{1-a} sum_i C(k,i) L^{k-i} i!/T^{1+i}
    + L^k N^{-a}/2 + (|b + iT| L^k + k L^{k-1}) N^{-a-1}/12. These are the bounds a Lean proof
    gets from the triangle inequality on the closed form above, nothing sharper.
    """
    logs = _logs(nmax)
    A, B, Tb = _q(a), _q(b), _q(T)
    smax = (B ** 2 + Tb ** 2).sqrt()
    out = {}
    acc = arb(0)
    for N in range(2, nmax + 1):
        m = N - 1
        if m >= 2:
            acc += (logs[m] ** k) * (-A * logs[m]).exp()
        L = logs[N]
        Na = (-A * L).exp()
        N1a = ((1 - A) * L).exp()
        a_part = arb(0)
        for i in range(k + 1):
            a_part += math.comb(k, i) * (L ** (k - i)) * N1a * math.factorial(i) / (Tb ** (1 + i))
        b_part = (L ** k) * Na / 2
        c_part = (smax * (L ** k) + (k * (L ** (k - 1)) if k >= 1 else 0)) * Na / N / 12
        out[N] = arb((acc + a_part + b_part + c_part).upper())
    return out


def em4_remainder_bounds(a: Fraction, b: Fraction, T: Fraction, nmax: int = NMAX) -> dict:
    """For N = 2..nmax, an upper bound of hunt #132's `zeta_em4_error` radius on [a, b] x {T}.

    The radius at s = sigma + iT is |s(s+1)(s+2)(s+3)| (N-1)^{-sigma-3} / (720 (sigma+3)); the
    product grows with sigma and the rest shrinks, so |P4(b + iT)| (N-1)^{-a-3}/(720 (a+3))
    bounds it on the whole sub-segment.
    """
    A, B, Tb = _q(a), _q(b), _q(T)
    p4 = arb(1)
    for j in range(4):
        p4 *= ((B + j) ** 2 + Tb ** 2).sqrt()
    out = {}
    for N in range(2, nmax + 1):
        out[N] = arb((p4 * ((-A - 3) * arb(N - 1).log()).exp() / (720 * (A + 3))).upper())
    return out


def lean_judgement(T: Fraction, a: Fraction, b: Fraction, k: int, nmax: int = NMAX,
                   N_only: int | None = None, e_only: int | None = None,
                   e_set: tuple = (0, 1, 2, 3)) -> dict | None:
    """The smallest truncation N, and the best axis direction at it, that close [a, b] at T.

    With p the midpoint, rho = (b - a)/2 and c = i^e, a Lean proof would show, for every
    sigma in [a, b],

        Re(zeta(sigma + iT) conj c) >= m - sum_{1<=j<k} rho^j |d_j|/j! - rho^k L_k/k! - R > 0,

    where m and d_j are the Lean box values of Re(M_N^{(j)}(p + iT) conj c) at one point, L_k the
    crude derivative bound and R the order-4 remainder bound. The margin recorded is that with
    the last two terms multiplied by SAFETY and the box allowance subtracted.
    """
    p = (a + b) / 2
    rho = _q((b - a) / 2)
    s = acb(_q(p), _q(T))
    hi_n = nmax if N_only is None else N_only
    table = main_term_table(s, k, hi_n)
    Lk = crude_derivative_bounds(k, a, b, T, hi_n)
    R = em4_remainder_bounds(a, b, T, hi_n)
    safety, allowance = _q(SAFETY), _q(BOX_ALLOWANCE)
    Ns = range(2, hi_n + 1) if N_only is None else (N_only,)
    for N in Ns:
        best = None
        for e in (e_set if e_only is None else (e_only,)):
            vals = table[N]
            m = arb(_rot_re(vals[0], e).lower())
            taylor = arb(0)
            for j in range(1, k):
                taylor += (rho ** j) * arb(abs(_rot_re(vals[j], e)).upper()) / math.factorial(j)
            tail = (rho ** k) * Lk[N] / math.factorial(k)
            margin = m - taylor - safety * (tail + R[N]) - allowance
            if best is None or _lower(margin) > _lower(best["_margin"]):
                best = {"_margin": margin, "N": N, "e": e, "m": m, "taylor": taylor,
                        "tail": tail, "R": R[N], "Lk": Lk[N]}
        if best is not None and _lower(best["_margin"]) > 0:
            return best
        if N_only is not None:
            return best
    return None


def true_margin(T: Fraction, a: Fraction, b: Fraction, e: int,
                piece: Fraction = SIGMA_PIECE, depth: int = 10) -> Fraction:
    """A lower bound for min Re(zeta(sigma + iT) conj c) over sigma in [a, b], from Arb boxes.

    Independent of every Lean-side bound: the sub-segment is cut into pieces no longer than
    `piece`, zeta is enclosed over each whole piece, and a piece whose enclosure is not on the
    right side is halved again (up to `depth` times) before the bound is taken.
    """
    n = max(1, math.ceil((b - a) / piece))
    worst = None
    stack = [(a + (b - a) * Fraction(i, n), a + (b - a) * Fraction(i + 1, n), 0)
             for i in range(n)]
    while stack:
        x, y, d = stack.pop()
        lb = _lower(_rot_re(_zeta((x, y), T), e))
        if lb <= 0:
            if d < depth:
                mid = (x + y) / 2
                stack.extend([(x, mid, d + 1), (mid, y, d + 1)])
                continue
            return lb  # not decided at full depth: the condition is not shown, stop here
        worst = lb if worst is None else min(worst, lb)
    return worst


def partition_leg(T: Fraction, k: int, lo: Fraction = Fraction(1, 2),
                  hi: Fraction = Fraction(2), directions: tuple = (0, 1, 2, 3)) -> list:
    """Bisect [lo, hi] at height T until every piece closes; pieces in increasing sigma.

    `directions` restricts the axis directions allowed (`(0,)`: Re zeta > 0 only, the shape
    of the skeleton's `horizontal_legs`)."""
    stack = [(lo, hi, 0)]
    out = []
    while stack:
        a, b, d = stack.pop()
        j = lean_judgement(T, a, b, k, e_set=directions)
        if j is not None:
            out.append((a, b, j))
            continue
        if d >= MAX_DEPTH:
            raise ValueError(f"leg at height {_fs(T)} does not close near sigma = {float(a)} "
                             f"with Taylor order {k} (a zero on or near the leg?)")
        mid = (a + b) / 2
        stack.append((mid, b, d + 1))
        stack.append((a, mid, d + 1))
    out.sort(key=lambda r: r[0])
    return out


def _subsegment_record(T: Fraction, a: Fraction, b: Fraction, k: int, j: dict) -> dict:
    tm = true_margin(T, a, b, j["e"])
    za, zb = _rot(_zeta(a, T), j["e"]), _rot(_zeta(b, T), j["e"])
    room = j["m"] - j["taylor"] - _q(BOX_ALLOWANCE)
    return {
        "sigma_from": _fs(a), "sigma_to": _fs(b), "midpoint": _fs((a + b) / 2),
        "half_length": _fs((b - a) / 2),
        "direction": DIRECTION_LABEL[j["e"]], "e": j["e"],
        "condition": DIRECTION_CONDITION[j["e"]],
        "N": j["N"],
        "main_term_lower": _lo(j["m"]),
        "taylor_terms_upper": _hi(j["taylor"]),
        "taylor_tail_upper": _hi(j["tail"]),
        "crude_derivative_bound": _hi(j["Lk"]),
        "em4_remainder_upper": _hi(j["R"]),
        "lean_margin": _lo(j["_margin"]),
        "safety_achieved": _lo(room / (j["tail"] + j["R"])),
        "true_margin": _dec(tm, False),
        "delta_arg_rightwards": _enc(zb.arg() - za.arg()),
    }


def _primes_below(n: int) -> int:
    return sum(1 for m in range(2, n) if all(m % p for p in range(2, int(m ** 0.5) + 1)))


def leg_plan(T: Fraction, k: int, orientation: str, directions: tuple = (0, 1, 2, 3)) -> dict:
    """A horizontal leg at height T: the partition, each sub-segment's record, the costs."""
    parts = partition_leg(T, k, directions=directions)
    recs = [_subsegment_record(T, a, b, k, j) for a, b, j in parts]
    path = recs if orientation == "rightwards" else list(reversed(recs))
    return {
        "height": _fs(T),
        "path": (f"1/2 + {_fs(T)} i -> 2 + {_fs(T)} i" if orientation == "rightwards"
                 else f"2 + {_fs(T)} i -> 1/2 + {_fs(T)} i"),
        "orientation": orientation,
        "taylor_order": k,
        "em_order": 4,
        "subsegments": recs,
        "arg_change_along_path": _enc(leg_arg_change(T, recs, orientation)),
        "directions_along_path": [r["direction"] for r in path],
        "n_subsegments": len(recs),
        "term_boxes": sum(r["N"] - 1 for r in recs),
        "prime_towers": sum(_primes_below(r["N"]) for r in recs),
        "max_N": max(r["N"] for r in recs),
        "worst_lean_margin": min(recs, key=lambda r: _pf(r["lean_margin"]))["lean_margin"],
        "worst_true_margin": min(recs, key=lambda r: _pf(r["true_margin"]))["true_margin"],
    }


def right_side(T1_: Fraction, T2_: Fraction) -> dict:
    """sigma = 2 from T1 to T2: one segment, direction +1, by `re_riemannZeta_two_pos`."""
    n = max(1, math.ceil((T2_ - T1_) / T_PIECE))
    worst = None
    for i in range(n):
        x = T1_ + (T2_ - T1_) * Fraction(i, n)
        y = T1_ + (T2_ - T1_) * Fraction(i + 1, n)
        lb = _lower(acb(_q(2), _span(x, y)).zeta().real)
        worst = lb if worst is None else min(worst, lb)
    vendored = 2 - arb.pi() ** 2 / 6
    return {
        "path": f"2 + {_fs(T1_)} i -> 2 + {_fs(T2_)} i",
        "direction": "+1", "e": 0, "condition": "Re zeta > 0",
        "lean_lemma": "Zeta23.RvM.re_riemannZeta_two_pos (vendored): Re zeta(2+it) > 0, "
                      "indeed >= 2 - pi^2/6",
        "vendored_lower_bound": _lo(vendored),
        "true_margin": _dec(worst, False),
        "n_subsegments": 1,
    }


def endpoint_arg(T: Fraction, e: int) -> dict:
    """A_j = Arg(zeta(1/2 + iT) conj c), and the Lean box that would enclose it.

    The Lean box is M_N(1/2 + iT) inflated by SAFETY times the order-4 radius plus the box
    allowance; for a disc of radius r around w0 with r < |w0|, the argument moves by at most
    arcsin(r/|w0|). N is the smallest truncation that keeps that below ARG_TOL.
    """
    half = Fraction(1, 2)
    z = _zeta(half, T)
    w = _rot(z, e)
    if not w.real > 0:
        raise ValueError(f"endpoint 1/2 + {_fs(T)} i is not on the side its direction claims")
    A = w.arg()
    s = acb(_q(half), _q(T))
    table = main_term_table(s, 1, NMAX)
    R = em4_remainder_bounds(half, half, T, NMAX)
    tol = _q(ARG_TOL)
    for N in range(2, NMAX + 1):
        w0 = _rot(table[N][0], e)
        r = _q(SAFETY) * R[N] + _q(BOX_ALLOWANCE)
        if not (r < w0.abs_lower() and w0.real - r > 0):
            continue  # the disc must miss 0 and stay in the right half-plane
        h = (r / w0.abs_lower()).asin()
        if h < tol:
            crude = _crude_arctan(w0, r)
            return {"point": f"1/2 + {_fs(T)} i", "direction": DIRECTION_LABEL[e], "e": e,
                    "zeta": [_enc(z.real), _enc(z.imag)], "rotated": [_enc(w.real), _enc(w.imag)],
                    "A": _enc(A), "lean_N": N, "lean_box_arg": _enc(w0.arg()),
                    "lean_half_width": _hi(h),
                    "crude_arctan_interval": [_dec(crude[0], False), _dec(crude[1], True)],
                    "_A": A, "_A_box": w0.arg(), "_h": arb(h.upper()), "_crude": crude}
    raise ValueError(f"no truncation up to {NMAX} encloses A at 1/2 + {_fs(T)} i within ARG_TOL")


def _crude_arctan(w0: acb, r: arb) -> tuple:
    """An enclosure of Arg w for every w in the square w0 +- r, using only arctan's sign and
    |arctan x| <= |x|: with x = Im w / Re w in [x_lo, x_hi], Arg w lies in
    [min(0, x_lo), max(0, x_hi)]. No arctan series is needed for it."""
    ru = _upper(r)
    re_lo, re_hi = _lower(w0.real) - ru, _upper(w0.real) + ru
    im_lo, im_hi = _lower(w0.imag) - ru, _upper(w0.imag) + ru
    if re_lo <= 0:
        raise ValueError("the box reaches the imaginary axis")
    x_lo = im_lo / re_hi if im_lo >= 0 else im_lo / re_lo
    x_hi = im_hi / re_lo if im_hi >= 0 else im_hi / re_hi
    return (min(Fraction(0), x_lo), max(Fraction(0), x_hi))


def gamma_side(T1_: Fraction, T2_: Fraction) -> dict:
    """int_{T1}^{T2} mu = (theta(T2) - theta(T1))/pi, and what each vendored route leaves.

    Route `mu_stirling`: |mu(t) - log(t/(2 pi))/(2 pi)| <= (20/(2 pi))/t^2, main term
    G(T2) - G(T1) with G(t) = (t log(t/(2 pi)) - t)/(2 pi). Route `digamma_stirling` (PLAN.md
    section 4.1): with w = 1/4 + it/2, |mu(t) - m(t)| <= (12/(2 pi))/t^2 for
    m(t) = ((1/2) log((1 + 4t^2)/16) - 2/(1 + 4t^2) - log pi)/(2 pi), whose antiderivative is
    F(t) = ((t/2) log((1 + 4t^2)/16) - t - arctan(2t)/2 - t log pi)/(2 pi).
    """
    th1, th2 = _theta(T1_), _theta(T2_)
    inc = (th2 - th1) / arb.pi()
    twopi = 2 * arb.pi()

    def G(t):
        tt = _q(t)
        return (tt * (tt / twopi).log() - tt) / twopi

    def F(t):
        tt = _q(t)
        return (tt / 2 * ((1 + 4 * tt ** 2) / 16).log() - tt - (2 * tt).atan() / 2
                - tt * arb.pi().log()) / twopi

    span = 1 / _q(T1_) - 1 / _q(T2_)
    main, main_d = G(T2_) - G(T1_), F(T2_) - F(T1_)
    budget = arb(STIRLING_NUMERATOR) / twopi * span
    budget_d = arb(12) / twopi * span
    return {
        "identity": "gamma_side (vendored): (1/pi) Im halfContour (logDeriv Gammaℝ) T1 T2 = "
                    "int_{T1}^{T2} mu, and int mu = (theta(T2) - theta(T1))/pi",
        "theta_T1": _enc(th1), "theta_T2": _enc(th2),
        "increment_over_pi": _enc(inc),
        "stirling_main": _enc(main),
        "stirling_main_formula": "G(T2) - G(T1), G(t) = (t log(t/(2 pi)) - t)/(2 pi)",
        "true_remainder": _enc(inc - main),
        "vendored_constant": "20/(2 pi), from Zeta23.StirlingVert.mu_stirling (its proof)",
        "vendored_budget": _hi(budget),
        "vendored_budget_formula": "(20/(2 pi)) (1/T1 - 1/T2)",
        "digamma_main": _enc(main_d),
        "digamma_main_formula": ("F(T2) - F(T1), F(t) = ((t/2) log((1+4t^2)/16) - t "
                                 "- arctan(2t)/2 - t log pi)/(2 pi)"),
        "digamma_true_remainder": _enc(inc - main_d),
        "digamma_budget": _hi(budget_d),
        "digamma_budget_formula": "(12/(2 pi)) (1/T1 - 1/T2), from digamma_stirling directly",
        "_inc": inc,
        "_route": {"mu_stirling": (main, arb(budget.upper())),
                   "digamma_stirling": (main_d, arb(budget_d.upper()))},
    }


def _junctions(bottom: dict, top: dict) -> tuple:
    """The direction chain along the whole half-contour, its junctions and Q.

    The chain runs 1/2 + i T1 -> 2 + i T1 (bottom, sigma increasing), up sigma = 2 (direction
    +1), then 2 + i T2 -> 1/2 + i T2 (top, sigma decreasing). Each element carries the point
    where it ends; a junction sits at that point.
    """
    h1, h2 = bottom["height"], top["height"]
    chain = ([(f"{r['sigma_to']} + {h1} i", r["e"]) for r in bottom["subsegments"]]
             + [(f"2 + {h2} i", 0)]
             + [(f"{r['sigma_from']} + {h2} i", r["e"]) for r in reversed(top["subsegments"])])
    rows, Q = [], 0
    for (end0, e0), (_, e1) in zip(chain, chain[1:]):
        d = _quarter_turn(e0, e1)
        Q += d
        if d:
            rows.append({"at": end0, "from": DIRECTION_LABEL[e0], "to": DIRECTION_LABEL[e1],
                         "quarter_turns": d})
    return rows, Q


def lean_contour(T1_: Fraction, T2_: Fraction, k: int, top: dict | None = None,
                 directions: tuple = (0, 1, 2, 3), route: str = "mu_stirling") -> dict:
    """The whole Lean-shaped plan for Ncount T1 T2 at Taylor order k.

    `directions` restricts the axis directions of the horizontal sub-segments; `route` picks
    the Gamma-side bound the Lean budget uses (`GAMMA_ROUTES`)."""
    bottom = leg_plan(T1_, k, "rightwards", directions)
    if top is None:
        top = leg_plan(T2_, k, "leftwards", directions)
    right = right_side(T1_, T2_)
    junctions, Q = _junctions(bottom, top)
    e1 = bottom["subsegments"][0]["e"]
    e2 = top["subsegments"][0]["e"]
    A1, A2 = endpoint_arg(T1_, e1), endpoint_arg(T2_, e2)
    gam = gamma_side(T1_, T2_)
    main, budget = gam["_route"][route]
    pi = arb.pi()
    exact = gam["_inc"] + arb(Q) / 2 + (A2["_A"] - A1["_A"]) / pi
    lo, hi = _lower(exact), _upper(exact)
    n_lo, n_hi = math.ceil(lo), math.floor(hi)
    count = n_lo if n_lo == n_hi else None
    h = (A1["_h"] + A2["_h"]) / pi
    centre = main + arb(Q) / 2 + (A2["_A_box"] - A1["_A_box"]) / pi
    lean_lo = _lower(centre - budget - h)
    lean_hi = _upper(centre + budget + h)
    l_lo, l_hi = math.ceil(lean_lo), math.floor(lean_hi)
    lean_count = l_lo if l_lo == l_hi else None
    base = main + arb(Q) / 2
    crude_lo = _lower(base - budget + (_q(A2["_crude"][0]) - _q(A1["_crude"][1])) / pi)
    crude_hi = _upper(base + budget + (_q(A2["_crude"][1]) - _q(A1["_crude"][0])) / pi)
    c_lo, c_hi = math.ceil(crude_lo), math.floor(crude_hi)
    crude_count = c_lo if c_lo == c_hi else None
    two_pi = 2 * pi
    towers = (bottom["prime_towers"] + top["prime_towers"] + _primes_below(A1["lean_N"])
              + _primes_below(A2["lean_N"]))
    out = {
        "T1": _fs(T1_), "T2": _fs(T2_), "taylor_order": k,
        "directions_allowed": [DIRECTION_LABEL[e] for e in directions],
        "gamma_route": route,
        "formula": "Ncount T1 T2 = (theta(T2) - theta(T1))/pi + Q/2 + (A2 - A1)/pi",
        "legs": {"bottom": bottom, "right": right, "top": top},
        "junctions": junctions,
        "quarter_turns_Q": Q,
        "A1": {kk: v for kk, v in A1.items() if not kk.startswith("_")},
        "A2": {kk: v for kk, v in A2.items() if not kk.startswith("_")},
        "gamma_side": {kk: v for kk, v in gam.items() if not kk.startswith("_")},
        "count_exact": [_dec(lo, False), _dec(hi, True)],
        "count": count,
        "exact_margin_to_other_integers": (
            None if count is None else _dec(min(lo - (count - 1), (count + 1) - hi), False)),
        "count_lean_budget": [_dec(lean_lo, False), _dec(lean_hi, True)],
        "lean_count": lean_count,
        "lean_margin_to_other_integers": (
            None if lean_count is None else
            _dec(min(lean_lo - (lean_count - 1), (lean_count + 1) - lean_hi), False)),
        "count_lean_crude_arctan": [_dec(crude_lo, False), _dec(crude_hi, True)],
        "crude_arctan_count": crude_count,
        "crude_arctan_margin_to_other_integers": (
            None if crude_count is None else
            _dec(min(crude_lo - (crude_count - 1), (crude_count + 1) - crude_hi), False)),
        "sensitivity": {
            "d_count_d_log_2pi": _enc(-(_q(T2_) - _q(T1_)) / two_pi, 8),
            "note": ("an error e in a Lean bound for log(2 pi) moves the Stirling main term by "
                     "about (T2 - T1) e/(2 pi); the margin above tolerates it while that stays "
                     "well below the margin"),
        },
        "term_boxes_total": bottom["term_boxes"] + top["term_boxes"] + A1["lean_N"] - 1
        + A2["lean_N"] - 1,
        "prime_towers_total": towers,
        "projected_kernel_seconds": round(float(towers * SECONDS_PER_TOWER)),
        "projection_basis": ("prime exp towers times hunt #133's measured 52 s per 17 towers; "
                             "for Taylor orders above 1 the derivative boxes add products "
                             "this does not count"),
        "worst_lean_margin": min((bottom["worst_lean_margin"], top["worst_lean_margin"]),
                                 key=_pf),
        "worst_true_margin": min((bottom["worst_true_margin"], top["worst_true_margin"],
                                  right["true_margin"]), key=_pf),
    }
    return out


def leg_arg_change(T: Fraction, recs: list, orientation: str) -> arb:
    """The continuous argument change along a planned leg, sub-segment by sub-segment (Arb)."""
    total = arb(0)
    for r in recs:
        a, b, e = _pf(r["sigma_from"]), _pf(r["sigma_to"]), r["e"]
        za, zb = _rot(_zeta(a, T), e), _rot(_zeta(b, T), e)
        total += zb.arg() - za.arg()
    return total if orientation == "rightwards" else -total


def contour_cross_check(T1_: Fraction, T2_: Fraction, plan: dict) -> dict:
    """The Lean chain against rigor.py's own contour at T1 and T2 (they share the top leg)."""
    r1, r2 = replay_zero_count(T1_), replay_zero_count(T2_)
    top = plan["legs"]["top"]
    lean_top = leg_arg_change(T2_, top["subsegments"], "leftwards")
    rig_top = sum((_q(_exact_mpf(lo)).union(_q(_exact_mpf(hi)))
                   for lo, hi in r2["_raw"]["deltas"]), arb(0))
    via_rigor = (r2["count"] - r1["count"]) if None not in (r1["count"], r2["count"]) else None
    return {
        "top_leg_arg_change_lean_chain": _enc(lean_top),
        "top_leg_arg_change_rigor_replay": _enc(rig_top),
        "top_leg_agrees": bool(lean_top.overlaps(rig_top)),
        "rigor_count_at_T1": r1["count"], "rigor_count_at_T2": r2["count"],
        "count_via_rigor_difference": via_rigor,
        "agrees_with_lean_contour": via_rigor == plan["count"],
    }


def bottom_height_options(T2_: Fraction, top: dict) -> list:
    """The planned contour with other bottom heights, Taylor order RECOMMENDED_ORDER."""
    rows = []
    for t1 in T1_OPTIONS:
        try:
            c = lean_contour(t1, T2_, RECOMMENDED_ORDER, top=top)
        except ValueError as exc:  # pragma: no cover - reported, not raised
            rows.append({"T1": _fs(t1), "closes": False, "reason": str(exc)})
            continue
        rows.append({
            "T1": _fs(t1), "closes": c["lean_count"] is not None,
            "count": c["count"], "lean_count": c["lean_count"],
            "vendored_gamma_budget": c["gamma_side"]["vendored_budget"],
            "lean_margin_to_other_integers": c["lean_margin_to_other_integers"],
            "bottom_subsegments": c["legs"]["bottom"]["n_subsegments"],
            "bottom_term_boxes": c["legs"]["bottom"]["term_boxes"],
            "bottom_worst_true_margin": c["legs"]["bottom"]["worst_true_margin"],
        })
    return rows


def left_end_margins(T: Fraction, breaks: tuple, Ns: tuple) -> list:
    """PLAN.md's segment rule, recomputed: expand from each segment's left end.

    For sigma in [a, b], Re zeta(sigma + iT) >= Re M_N(a + iT) - (b - a) L_1 - R with the same
    L_1 and R as `lean_judgement`. Three conventions are reported, because they disagree: the
    bare bounds; the factor SAFETY on the remainder radius only (hunt #133's convention, and
    PLAN.md's wording "the radii multiplied by 1.5"); and SAFETY on the radius and on the
    variation term (`lean_judgement`'s convention). Each also gets its Arb true margin.
    """
    rows = []
    safety, allowance = _q(SAFETY), _q(BOX_ALLOWANCE)
    for (a, b), N in zip(zip(breaks, breaks[1:]), Ns):
        s = acb(_q(a), _q(T))
        m = arb(main_term_table(s, 1, N)[N][0].real.lower())
        var = _q(b - a) * crude_derivative_bounds(1, a, b, T, N)[N]
        R = em4_remainder_bounds(a, b, T, N)[N]
        rows.append({
            "sigma_from": _fs(a), "sigma_to": _fs(b), "N": N,
            "left_end_main_term_lower": _lo(m),
            "variation_upper": _hi(var), "em4_remainder_upper": _hi(R),
            "margin_bare": _lo(m - var - R - allowance),
            "margin_safety_on_radius": _lo(m - var - safety * R - allowance),
            "margin_safety_on_both": _lo(m - safety * (var + R) - allowance),
            "true_margin": _dec(true_margin(T, a, b, 0), False),
        })
    return rows


def stated_arg_check(T: Fraction, bounds: tuple) -> dict:
    """Arg zeta(1/2 + iT) against a stated rational interval, and the truncation each needs.

    The Lean route of PLAN.md section 4.2 step 4: on a box w0 +- r with Re > 0, Arg lies in
    [min(0, x_lo), max(0, x_hi)], x = Im/Re (`_crude_arctan`). The smallest N whose box puts
    that interval inside `bounds` is reported with r the bare order-4 radius plus the box
    allowance, and with r = SAFETY times the radius plus the allowance.
    """
    lo_b, hi_b = bounds
    z = _zeta(Fraction(1, 2), T)
    A = z.arg()
    s = acb(_q(Fraction(1, 2)), _q(T))
    table = main_term_table(s, 1, NMAX)
    R = em4_remainder_bounds(Fraction(1, 2), Fraction(1, 2), T, NMAX)
    found = {}
    for name, factor in (("bare", 1), ("safety", SAFETY)):
        found[name] = None
        for N in range(2, NMAX + 1):
            r = _q(factor) * R[N] + _q(BOX_ALLOWANCE)
            w0 = table[N][0]
            if not (w0.real - r > 0):
                continue
            c_lo, c_hi = _crude_arctan(w0, r)
            if lo_b <= c_lo and c_hi <= hi_b:
                found[name] = {"N": N, "radius": _hi(r),
                               "interval": [_dec(c_lo, False), _dec(c_hi, True)],
                               "room": _dec(min(c_lo - lo_b, hi_b - c_hi), False)}
                break
    return {"point": f"1/2 + {_fs(T)} i", "stated": [_fs(lo_b), _fs(hi_b)], "A": _enc(A),
            "inside": bool(_q(lo_b) <= A.lower() and A.upper() <= _q(hi_b)),
            "smallest_N": found}


def skeleton_contour(T) -> dict:
    """The skeleton's contour (SKELETON), hardened: its heights, bounds and partitions."""
    sk = SKELETON[int(T)]
    t1, t2 = sk["T1"], sk["T2"]
    out: dict = {
        "source": "hunts/rh_height_lean/PLAN.md, sections 4, 5 and 7 (2026-10-21), and "
                  "lean/RHHeight/Skeleton.lean, whose count_eq_ten_of concludes Ncount 3 52 = 10",
        "T1": _fs(t1), "T2": _fs(t2),
        "contour": lean_contour(t1, t2, 1, directions=(0,), route="digamma_stirling"),
    }
    gam = gamma_side(t1, t2)
    main_d, budget_d = gam["_route"]["digamma_stirling"]
    route_lo, route_hi = _lower(main_d - budget_d), _upper(main_d + budget_d)
    out["gamma_route_interval"] = [_dec(route_lo, False), _dec(route_hi, True)]
    if "gamma_bounds" in sk:
        g_lo, g_hi = sk["gamma_bounds"]
        a1_lo, a1_hi = sk["A1_bounds"]
        a2_lo, a2_hi = sk["A2_bounds"]
        out["stated_gamma_bounds"] = [_fs(g_lo), _fs(g_hi)]
        out["gamma_inside_stated"] = bool(_q(g_lo) <= gam["_inc"].lower()
                                          and gam["_inc"].upper() <= _q(g_hi))
        out["gamma_route_inside_stated"] = bool(g_lo <= route_lo and route_hi <= g_hi)
        out["gamma_route_room"] = _dec(min(route_lo - g_lo, g_hi - route_hi), False)
        out["A1_check"] = stated_arg_check(t1, sk["A1_bounds"])
        out["A2_check"] = stated_arg_check(t2, sk["A2_bounds"])
        pi = arb.pi()
        lo = _lower(_q(g_lo) + (_q(a2_lo) - _q(a1_hi)) / pi)
        hi = _upper(_q(g_hi) + (_q(a2_hi) - _q(a1_lo)) / pi)
        k_lo, k_hi = math.ceil(lo), math.floor(hi)
        out["count_from_stated_bounds"] = [_dec(lo, False), _dec(hi, True)]
        out["stated_bounds_count"] = k_lo if k_lo == k_hi else None
        out["stated_bounds_margin"] = (_dec(min(lo - (k_lo - 1), (k_lo + 1) - hi), False)
                                       if k_lo == k_hi else None)
    for leg in ("bottom", "top"):
        if leg in sk:
            breaks, Ns = sk[leg]
            rows = left_end_margins(t1 if leg == "bottom" else t2, breaks, Ns)
            out[f"stated_{leg}_partition"] = rows
            for conv in ("bare", "safety_on_radius", "safety_on_both"):
                out[f"stated_{leg}_closes_{conv}"] = all(
                    _pf(r[f"margin_{conv}"]) > 0 for r in rows)
    return out


# ---------------------------------------------------------------------------
# 6. Independent routes to the count
# ---------------------------------------------------------------------------


def independent_checks(T, count: int | None) -> dict:
    Tq = Fraction(T)
    n = count if count is not None else MISSION_COUNTS[int(T)]
    with mp.workdps(30):
        nz = int(mpmath.nzeros(mpmath.mpf(Tq.numerator) / Tq.denominator))
        gammas = [mpmath.zetazero(k).imag for k in range(1, n + 2)]
        below, above = gammas[n - 1], gammas[n]
        g_list = [float(g) for g in gammas]
    with flint.ctx.workprec(PLAN_PREC):
        turing = _q(Tq).zeta_nzeros().unique_fmpz()
        backlund = _q(Tq).backlund_s()
        gram, m = [], -1
        while True:
            g = arb.gram_point(m)
            z = _hardy_Z(_frac(g.mid()))
            sgn = 1 if z > 0 else (-1 if z < 0 else 0)
            gram.append({"n": m, "g_n": float(g.mid()), "sign_Z": sgn,
                         "gram_law": bool(sgn != 0 and sgn == (1 if m % 2 == 0 else -1))})
            if g > _q(Tq):
                break
            m += 1
    return {
        "mpmath_nzeros": nz,
        "mpmath_nzeros_method": "Gram points and Rosser blocks, floating point (mpmath source)",
        "zetazero_ordinates": g_list,
        "zetazero_last_below": float(below), "zetazero_first_above": float(above),
        "distance_below": float(mpmath.mpf(float(Tq)) - below),
        "distance_above": float(above - mpmath.mpf(float(Tq))),
        "zetazero_count_below_T": sum(1 for g in gammas if g < float(Tq)),
        "arb_turing_count": None if turing is None else int(turing),
        "arb_turing_method": "Arb's zero counter, which uses Turing's method (rigor.py's "
                             "zero-count docstring and Arb's documentation)",
        "arb_backlund_S": _enc(backlund),
        "gram_points": gram,
        "gram_law_holds_throughout": all(r["gram_law"] for r in gram),
    }


# ---------------------------------------------------------------------------
# 7. The plan, its verification, and the files
# ---------------------------------------------------------------------------


def build_plan(T) -> dict:
    T2_ = Fraction(T)
    with flint.ctx.workprec(PLAN_PREC):
        template = rigor_template(T2_)
        rh = rh_template(T2_, template["count"])
        tops = {k: leg_plan(T2_, k, "leftwards") for k in TAYLOR_ORDERS}
        contours = {k: lean_contour(T1, T2_, k, top=tops[k]) for k in TAYLOR_ORDERS}
        rec = contours[RECOMMENDED_ORDER]
        cross = contour_cross_check(T1, T2_, rec)
        options = bottom_height_options(T2_, tops[RECOMMENDED_ORDER])
        indep = independent_checks(T2_, rec["count"])
        low = rigor_template_low(T1)
        skel = skeleton_contour(T2_)
    counts = {
        "rigor_zero_count_routine": template["routine"]["count"],
        "rigor_replay": template["count"],
        "rigor_rh_height_routine": rh["routine"]["count"],
        "proven_sign_changes": rh["routine"]["proven_sign_changes"],
        "lean_contour_exact": rec["count"],
        "lean_contour_budget": rec["lean_count"],
        "skeleton_contour_exact": skel["contour"]["count"],
        "skeleton_contour_budget": skel["contour"]["lean_count"],
        "rigor_difference_T2_minus_T1": cross["count_via_rigor_difference"],
        "mpmath_nzeros": indep["mpmath_nzeros"],
        "zetazero_below_T": indep["zetazero_count_below_T"],
        "arb_turing_count": indep["arb_turing_count"],
    }
    plan = {
        "schema": "rh_height_lean numeric contour plan, version 1",
        "generated_by": "hunts/rh_height_lean/numeric_plan.py",
        "versions": {"python-flint": flint.__version__, "mpmath": mpmath.__version__},
        "T": _fs(T2_),
        "mission_count": MISSION_COUNTS.get(int(T)),
        "counts": counts,
        "counts_agree": len({v for v in counts.values()}) == 1,
        "good_heights": {
            "top": _fs(T2_), "bottom": _fs(T1),
            "top_why": (f"every sub-segment of the top leg has Re(zeta conj c) > 0 for its axis "
                        f"direction c, so zeta has no zero on [1/2, 2] x {{{_fs(T2_)}}}; "
                        "Re s >= 1 is zero-free (Mathlib) and the zeros are symmetric under "
                        "s -> 1 - conj s, so no nontrivial zero has ordinate T"),
            "bottom_why": ("the same, on the bottom leg; and zeta has no zero with "
                           "0 < Im s <= T1 (low_height below)"),
            "top_nearest_ordinates": [indep["zetazero_last_below"], indep["zetazero_first_above"]],
            "top_distance_to_nearest_ordinate": min(indep["distance_below"],
                                                    indep["distance_above"]),
            "skeleton": {"bottom": skel["T1"], "top": skel["T2"],
                         "why": "the same half-plane argument, on the skeleton contour's legs, "
                                "every sub-segment in Re zeta > 0"},
        },
        "plan_of_record": ("skeleton_contour: the heights the skeleton states "
                           "(lean/RHHeight/Skeleton.lean and PLAN.md); lean_contour at T1 = 10 "
                           "is an independent route and the fallback"),
        "skeleton_contour": skel,
        "low_height": low,
        "rigor_template": template,
        "rh_template": rh,
        "lean_contour": {
            "recommended_taylor_order": RECOMMENDED_ORDER,
            "constants": {
                "safety": _fs(SAFETY), "box_allowance": _fs(BOX_ALLOWANCE), "nmax": NMAX,
                "arg_tol": _fs(ARG_TOL), "sigma_piece": _fs(SIGMA_PIECE),
                "t_piece": _fs(T_PIECE), "ball_prec_bits": PLAN_PREC,
            },
            "by_taylor_order": {str(k): contours[k] for k in TAYLOR_ORDERS},
            "cross_check_with_rigor": cross,
            "bottom_height_options": options,
            "min_ball_bits": min_ball_bits(rec),
        },
        "independent_checks": indep,
    }
    return plan


def rigor_template_low(t1: Fraction) -> dict:
    """No zero with 0 < Im s <= T1: what the routes say (the Lean piece is separate)."""
    res = rigor_count(t1)
    with flint.ctx.workprec(PLAN_PREC):
        turing = _q(t1).zeta_nzeros().unique_fmpz()
    with mp.workdps(20):
        nz = int(mpmath.nzeros(mpmath.mpf(t1.numerator) / t1.denominator))
        g1 = float(mpmath.zetazero(1).imag)
    return {
        "T1": _fs(t1),
        "rigor_zero_count_at_T1": res["N_T"],
        "rigor_enclosure_at_T1": [_dec(_exact_mpf(res["N_T_enclosure"][0]), False),
                                  _dec(_exact_mpf(res["N_T_enclosure"][1]), True)],
        "rigor_all_steps_closed": _closed(res),
        "arb_turing_count": None if turing is None else int(turing),
        "mpmath_nzeros": nz,
        "first_ordinate": g1,
        "note": ("the zero-count routine's contour runs along the real axis, so N(T1) = 0 "
                 "there is an enclosure-carrying statement that no zero has 0 < Im s < T1; "
                 "the Lean proof still needs its own low-height exclusion"),
    }


def min_ball_bits(contour: dict) -> int | None:
    """The least Arb precision at which every true margin of the plan stays positive."""
    for bits in (2, 3, 4, 5, 6, 8, 10, 12, 16, 24, 32, 48, 64, 96, 128):
        with flint.ctx.workprec(bits):
            ok = True
            for name in ("bottom", "top"):
                leg = contour["legs"][name]
                T = _pf(leg["height"])
                for r in leg["subsegments"]:
                    if true_margin(T, _pf(r["sigma_from"]), _pf(r["sigma_to"]), r["e"],
                                   depth=4) <= 0:
                        ok = False
                        break
                if not ok:
                    break
        if ok:
            return bits
    return None


def verify_plan(plan: dict, k: int | None = None, deep: bool = True,
                report: dict | None = None) -> list:
    """Recompute a plan's claims from its stated data; return the failures (empty: it holds).

    Checked: each horizontal leg is tiled by its sub-segments with no gap or overlap; each
    sub-segment's Lean margin is positive when recomputed at its stated N and direction; each
    true margin is positive by fresh Arb boxes; consecutive directions share a half-plane and
    Q is what they add up to; the endpoint arguments and the Gamma side are recomputed at the
    stated heights and must agree with the stored enclosures; the count, recomputed, must hold
    exactly one integer, equal to the stated count, under both the exact and the Lean budget.
    When `report` is a dict it receives the recomputed count, Q and worst margins (exact
    rationals), so a test can pin numbers this function derived rather than read.
    """
    fails: list = []
    k = plan["lean_contour"]["recommended_taylor_order"] if k is None else k
    c = plan["lean_contour"]["by_taylor_order"][str(k)]
    T1_, T2_ = _pf(c["T1"]), _pf(c["T2"])
    if _pf(plan["T"]) != T2_ or _pf(plan["good_heights"]["top"]) != T2_:
        fails.append("the plan's top height and its contour's T2 differ")
    if _pf(plan["good_heights"]["bottom"]) != T1_:
        fails.append("the plan's bottom height and its contour's T1 differ")
    return fails + verify_contour(c, deep=deep, report=report,
                                  expected_count=plan["mission_count"])


def verify_contour(c: dict, deep: bool = True, report: dict | None = None,
                   expected_count: int | None = None) -> list:
    """`verify_plan`'s checks for one contour record (the plan's, or the skeleton's)."""
    fails: list = []
    rep = {} if report is None else report
    lean_ms, true_ms = [], []
    k = c["taylor_order"]
    route = c.get("gamma_route", "mu_stirling")
    T1_, T2_ = _pf(c["T1"]), _pf(c["T2"])
    if not (1 <= T1_ < T2_):
        fails.append("the fold needs 1 <= T1 < T2")
    with flint.ctx.workprec(PLAN_PREC):
        for name in ("bottom", "top"):
            leg = c["legs"][name]
            T = _pf(leg["height"])
            if T != (T1_ if name == "bottom" else T2_):
                fails.append(f"{name} leg height {leg['height']} is not the contour's")
            recs = leg["subsegments"]
            edge = Fraction(1, 2)
            for r in recs:
                a, b = _pf(r["sigma_from"]), _pf(r["sigma_to"])
                if a != edge:
                    fails.append(f"{name} leg: gap or overlap at sigma = {_fs(edge)}")
                edge = b
            if edge != 2:
                fails.append(f"{name} leg: does not reach sigma = 2 (ends at {_fs(edge)})")
            for r in recs:
                a, b = _pf(r["sigma_from"]), _pf(r["sigma_to"])
                j = lean_judgement(T, a, b, k, N_only=r["N"], e_only=r["e"])
                if j is not None:
                    lean_ms.append(_lower(j["_margin"]))
                if j is None or _lower(j["_margin"]) <= 0:
                    fails.append(f"{name} leg [{r['sigma_from']}, {r['sigma_to']}]: Lean margin "
                                 f"not positive at N = {r['N']}, direction {r['direction']}")
                if deep:
                    tm = true_margin(T, a, b, r["e"])
                    true_ms.append(tm)
                    if tm <= 0:
                        fails.append(f"{name} leg [{r['sigma_from']}, {r['sigma_to']}]: "
                                     f"{r['condition']} not proven on the sub-segment")
        rep["worst_lean_margin"] = min(lean_ms) if lean_ms else None
        try:
            junctions, Q = _junctions(c["legs"]["bottom"], c["legs"]["top"])
        except ValueError as exc:
            fails.append(str(exc))
            return fails
        rep["Q"] = Q
        if Q != c["quarter_turns_Q"]:
            fails.append(f"quarter turns recomputed {Q}, stated {c['quarter_turns_Q']}")
        if deep:
            rs = right_side(T1_, T2_)
            true_ms.append(_pf(rs["true_margin"]))
            rep["right_side_true_margin"] = _pf(rs["true_margin"])
            if _pf(rs["true_margin"]) <= 0:
                fails.append("right side: Re zeta(2+it) > 0 not proven")
            rep["worst_true_margin"] = min(true_ms)
        try:
            A1 = endpoint_arg(T1_, c["legs"]["bottom"]["subsegments"][0]["e"])
            A2 = endpoint_arg(T2_, c["legs"]["top"]["subsegments"][0]["e"])
        except ValueError as exc:
            fails.append(str(exc))
            return fails
        for tag, got in (("A1", A1), ("A2", A2)):
            lo, hi = (_pf(x) for x in c[tag]["A"])
            if not (_lower(got["_A"]) <= hi and lo <= _upper(got["_A"])):
                fails.append(f"{tag} recomputed at the stated height disagrees with the plan")
        gam = gamma_side(T1_, T2_)
        lo, hi = (_pf(x) for x in c["gamma_side"]["increment_over_pi"])
        if not (_lower(gam["_inc"]) <= hi and lo <= _upper(gam["_inc"])):
            fails.append("Gamma-side increment recomputed at the stated heights disagrees")
        pi = arb.pi()
        exact = gam["_inc"] + arb(Q) / 2 + (A2["_A"] - A1["_A"]) / pi
        n_lo, n_hi = math.ceil(_lower(exact)), math.floor(_upper(exact))
        rep["count"] = n_lo if n_lo == n_hi else None
        if n_lo != n_hi:
            fails.append(f"recomputed count enclosure [{float(_lower(exact))}, "
                         f"{float(_upper(exact))}] holds {max(0, n_hi - n_lo + 1)} integers")
        elif n_lo != c["count"]:
            fails.append(f"recomputed count {n_lo} differs from the stated {c['count']}")
        main, budget = gam["_route"][route]
        h = (A1["_h"] + A2["_h"]) / pi
        centre = main + arb(Q) / 2 + (A2["_A_box"] - A1["_A_box"]) / pi
        lean_lo, lean_hi = _lower(centre - budget - h), _upper(centre + budget + h)
        l_lo, l_hi = math.ceil(lean_lo), math.floor(lean_hi)
        rep["lean_budget_margin"] = (min(lean_lo - (l_lo - 1), (l_lo + 1) - lean_hi)
                                     if l_lo == l_hi else None)
        if l_lo != l_hi or l_lo != c["count"]:
            fails.append("the Lean budget does not pin the count to one integer")
        if c.get("crude_arctan_count") is not None:
            base = main + arb(Q) / 2
            lo_c = _lower(base - budget + (_q(A2["_crude"][0]) - _q(A1["_crude"][1])) / pi)
            hi_c = _upper(base + budget + (_q(A2["_crude"][1]) - _q(A1["_crude"][0])) / pi)
            c_lo = math.ceil(lo_c)
            rep["crude_arctan_margin"] = (min(lo_c - (c_lo - 1), (c_lo + 1) - hi_c)
                                          if c_lo == math.floor(hi_c) else None)
            if c_lo != math.floor(hi_c) or c_lo != c["count"]:
                fails.append("the arctan-free Lean budget does not pin the count")
        if expected_count is not None and c["count"] != expected_count:
            fails.append(f"count {c['count']} is not the mission's {expected_count}")
    return fails


def verify_template(template: dict, drop: int | None = None) -> list:
    """Re-add rigor.py's replayed argument changes; the sum must sit on an integer.

    `drop` leaves one sub-segment out (a planted fault); the enclosure is ~1e-55 wide, so any
    missing piece leaves it holding no integer at all.
    """
    fails = []
    segs = template["horizontal_leg"]["segments"]

    def ball(pair):
        lo, hi = (_pf(x) for x in pair)
        return _q(lo).union(_q(hi))

    with flint.ctx.workprec(COUNT_PREC):
        total = ball(template["vertical_leg"]["arg_zeta_2_plus_iT"])
        for i, r in enumerate(segs):
            if i != drop:
                total += ball(r["delta_arg"])
        n_ball = 1 + ball(template["theta_T"]) / arb.pi() + total / arb.pi()
        lo, hi = _lower(n_ball), _upper(n_ball)
    k_lo, k_hi = math.ceil(lo), math.floor(hi)
    if k_lo != k_hi:
        fails.append(f"template enclosure [{float(lo):.12g}, {float(hi):.12g}] holds "
                     f"{max(0, k_hi - k_lo + 1)} integers")
    elif k_lo != template["count"]:
        fails.append(f"template sum gives {k_lo}, stated {template['count']}")
    return fails


def _strip_private(obj):
    if isinstance(obj, dict):
        return {k: _strip_private(v) for k, v in obj.items() if not str(k).startswith("_")}
    if isinstance(obj, list):
        return [_strip_private(v) for v in obj]
    return obj


def plan_json(plan: dict) -> str:
    text = json.dumps(_strip_private(plan), indent=1, ensure_ascii=False) + "\n"
    _assert_lexically_clean(text)
    return text


def plan_path(T) -> Path:
    return HERE / f"plan_T{int(T)}.json"


def main(argv: list | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--check", action="store_true",
                    help="rebuild, verify and compare with the files on disk; write nothing")
    args = ap.parse_args(argv)
    status = 0
    for T in HEIGHTS:
        plan = build_plan(T)
        text = plan_json(plan)
        sk = plan["skeleton_contour"]
        fails = (verify_plan(plan) + verify_template(plan["rigor_template"])
                 + verify_contour(sk["contour"], expected_count=plan["mission_count"]))
        c = plan["lean_contour"]["by_taylor_order"][str(RECOMMENDED_ORDER)]
        print(f"T = {T}: counts {plan['counts']}")
        skc = sk["contour"]
        print(f"  skeleton contour ({sk['T1']}, {sk['T2']}): count {skc['count']}, Lean budget "
              f"{skc['count_lean_budget']}, margin {skc['lean_margin_to_other_integers']}, "
              f"sub-segments {skc['legs']['bottom']['n_subsegments']} / "
              f"{skc['legs']['top']['n_subsegments']}")
        for leg in ("bottom", "top"):
            if f"stated_{leg}_partition" in sk:
                print(f"  stated {leg} partition closes: bare "
                      f"{sk[f'stated_{leg}_closes_bare']}, safety on radius "
                      f"{sk[f'stated_{leg}_closes_safety_on_radius']}, safety on both "
                      f"{sk[f'stated_{leg}_closes_safety_on_both']}")
        print(f"  Lean contour T1 = {c['T1']}: Q = {c['quarter_turns_Q']}, "
              f"count {c['count']} (exact {c['count_exact']}), Lean budget "
              f"{c['count_lean_budget']}, margin {c['lean_margin_to_other_integers']}")
        for k in TAYLOR_ORDERS:
            ck = plan["lean_contour"]["by_taylor_order"][str(k)]
            print(f"  order {k}: bottom {ck['legs']['bottom']['n_subsegments']} / top "
                  f"{ck['legs']['top']['n_subsegments']} sub-segments, "
                  f"{ck['term_boxes_total']} term boxes, worst Lean margin "
                  f"{ck['worst_lean_margin']}")
        if fails:
            status = 1
            print("  FAILURES:", *fails, sep="\n    ")
        path = plan_path(T)
        if args.check:
            on_disk = path.read_text(encoding="utf-8") if path.is_file() else None
            if on_disk != text:
                status = 1
                print(f"  {path.name} differs from a fresh build")
        else:
            path.write_text(text, encoding="utf-8")
            print(f"  wrote {path.relative_to(ROOT)}")
    return status


if __name__ == "__main__":
    sys.exit(main())

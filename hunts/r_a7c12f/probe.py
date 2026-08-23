"""Does the far-field constant `637/1000` survive at depth 1?

`K2-TWO-SPECIES.md` section 2 records, as a correction a depth-1 argument
must carry:

    far constant `sup Dam*(s^2-2)/y'^2` | 0.6220 (proved <= 0.637) | **0.6636 (> 0.637)**
    ... `no_damage`'s `28/5` and `Wt_tail_le`'s `637/1000` do NOT survive at depth 1.

This probe re-derives that entry.  It asks four separate questions that the
one sentence had merged into one:

1. **What does `Wt_tail_le` actually say?**  It is
   `Wt w <= (637/1000)/w` for `w >= 1368`, an inequality between two explicit
   rational functions of a single variable.  No depth appears in it.
2. **Over what range of `s` is `637/1000` asserted?**  `w = s^2 - 2 >= 1368`
   is `s >= 37.0135...`.  `two_species.far_constant` scans `[8, 400]`.
3. **Where does the `0.6636` sup actually sit?**  If it sits below
   `s = 37.0135` then it is not a value `637/1000` ever claimed to dominate.
4. **On the range it IS asserted, does the constant hold at depth 1?**  This
   is the question the brief names, and it is answered here with
   `ball_field.D_enclosure`, which takes the depth as an interval.

Plus the two follow-ons that decide what a `k >= 3` pass actually inherits:

5. At what depth does `637/1000` genuinely fail on its own range?
6. Does `Qim_far_sq` (`Qim y s ^ 2 <= y^2 * Wt (s^2 - 2)`, hypothesis
   `hy : y <= 1/2`) extend to depth 1?

The float half is double precision and is labelled `measured`.  The ball half
uses Arb through `hunts/r_a97060/ball_field.py` at 96 bits and is labelled
`enclosure-carrying`; the reserved word of `zeta/rigor.py` is not used here.
Nothing in this file is evidence about RH.

Run: `.venv/bin/python hunts/r_a7c12f/probe.py`
"""
from __future__ import annotations

import cmath
import json
import math
import sys
import time
from pathlib import Path

_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(_ROOT / "hunts" / "frontier_math"))
sys.path.insert(0, str(_ROOT / "hunts" / "r_a97060"))

import ball_field as bf  # noqa: E402
import gram_form as gf  # noqa: E402

# --- the two constants, exactly as the Lean file states them ---------------

#: `Wt w = 5/(8w) + (611/50)/w^2 + (6711/100)/w^3 + (2583/25)/w^4`
#: (`Zeta23Ext/EForm3/FarField.lean:35`).
WT_COEFFS = (5 / 8, 611 / 50, 6711 / 100, 2583 / 25)

#: `Wt_tail_le {w} (hw : 1368 <= w) : Wt w <= (637/1000)/w`
#: (`Zeta23Ext/EForm3/Counting.lean:93`).  No `y` occurs in the statement.
W_THRESHOLD = 1368.0
FAR_CONST = 637 / 1000

#: `w = s^2 - 2 >= 1368`  <=>  `s >= sqrt(1370)`.
S_THRESHOLD = math.sqrt(W_THRESHOLD + 2.0)

#: the range `two_species.far_constant` scans.
SCAN_LO, SCAN_HI = 8.0, 400.0

#: `cos(1/sqrt 2)`, the interference factor in the far field.
_COS_R = math.cos(1 / math.sqrt(2.0))


def Wt(w: float) -> float:
    a, b, c, d = WT_COEFFS
    return a / w + b / w ** 2 + c / w ** 3 + d / w ** 4


def qre_qim(y: float, s: float) -> tuple[float, float]:
    """`ghat(y + i s) = Qre + i Qim`, the same `_ghat` as `gram_form`."""
    g = gf._ghat(y, s)
    return g.real, g.imag


def dam(y: float, s: float) -> float:
    return max(0.0, gf.damage(y, s))


def far_asymptote(y: float) -> float:
    """`limsup_{s->inf} Dam(y,s)*(s^2-2)/y^2`, in closed form.

    To leading order `ghat(y+is) = -2 sinh(y/2) cos(1/sqrt2) cos(s/2)/s + O(1/s^2)`
    in its imaginary part and `O(1/s)` with a `cosh(y/2) sin` numerator in its
    real part, so the rectified damage `Qim^2 - Qre^2` has limsup
    `4 sinh(y/2)^2 cos(1/sqrt2)^2 / y^2` after the `(s^2-2)/y^2` normalisation.
    Checked against the ball pass below rather than asserted.
    """
    return 4 * math.sinh(y / 2) ** 2 * _COS_R ** 2 / y ** 2


# --- question 3: where the 0.6636 sup actually sits -------------------------

def far_constant_arg(y: float, lo: float = SCAN_LO, hi: float = SCAN_HI,
                     step: float = 5e-3) -> tuple[float, float]:
    """`two_species.far_constant`, but returning the argmax too."""
    sup, arg, s = 0.0, lo, lo
    while s <= hi:
        v = dam(y, s) * (s * s - 2) / y ** 2
        if v > sup:
            sup, arg = v, s
        s += step
    return sup, arg


# --- question 4: the ball pass over the range the constant is asserted on ---

def ball_sup(y_lo: float, y_hi: float, s_lo: float, s_hi: float,
             coarse: float = 0.05, refine_at: float = 0.50,
             min_cell: float = 1e-4) -> tuple[float, int, int]:
    """Outward upper bound on `sup Dam(y,s)*(s^2-2)/y^2` over the box.

    `Dam <= max(0, D_upper)` and `y^2 >= y_lo^2`, so
    `D_upper(cell) * (s_hi^2 - 2) / y_lo^2` dominates the true value on the
    cell.  Cells whose bound exceeds `refine_at` are bisected, so the coarse
    grid pays only where the profile is actually large.

    Returns `(bound, n_cells_evaluated, n_refinements)`.
    """
    sup, n_eval, n_ref = 0.0, 0, 0
    stack = []
    s = s_lo
    while s < s_hi:
        stack.append((s, min(s + coarse, s_hi)))
        s += coarse
    y2 = y_lo * y_lo
    while stack:
        a, b = stack.pop()
        n_eval += 1
        d = bf.D_upper(y_lo, y_hi, a, b)
        if d <= 0.0:
            continue
        v = d * (b * b - 2.0) / y2
        if v <= sup:
            continue
        if v > refine_at and (b - a) > min_cell:
            m = 0.5 * (a + b)
            stack.append((a, m))
            stack.append((m, b))
            n_ref += 1
            continue
        sup = v
    return sup, n_eval, n_ref


# --- question 5: the depth at which the constant genuinely fails -----------

def break_depth(target: float = FAR_CONST, lo: float = 0.8, hi: float = 2.0,
                step: float = 2e-3) -> float:
    """Smallest `y` (to `1e-4`) with `sup_{s >= S_THRESHOLD} Dam*(s^2-2)/y^2 > target`."""
    def sup_on_range(y: float) -> float:
        sup, s = 0.0, S_THRESHOLD
        while s <= SCAN_HI:
            sup = max(sup, dam(y, s) * (s * s - 2) / y ** 2)
            s += step
        return sup

    a, b = lo, hi
    if sup_on_range(a) > target:
        return float("nan")
    for _ in range(14):
        m = 0.5 * (a + b)
        if sup_on_range(m) > target:
            b = m
        else:
            a = m
    return 0.5 * (a + b)


# --- question 6: does Qim_far_sq extend past its `y <= 1/2` hypothesis? ----

def qim_far_sq_ratio(y: float, lo: float = 28 / 5, hi: float = SCAN_HI,
                     step: float = 1e-3) -> tuple[float, float]:
    """`max_s Qim(y,s)^2 / (y^2 Wt(s^2-2))` — the lemma holds iff this is <= 1."""
    worst, arg, s = 0.0, lo, lo
    while s <= hi:
        r = qre_qim(y, s)[1] ** 2 / (y * y * Wt(s * s - 2))
        if r > worst:
            worst, arg = r, s
        s += step
    return worst, arg


def qim_far_sq_break() -> float:
    """The depth at which `Qim_far_sq`'s asymptotic content fails.

    Asymptotically `Qim^2 (s^2-2)/y^2 -> 4 sinh(y/2)^2 cos(1/sqrt2)^2/y^2`
    while `Wt(w) w -> 5/8`, so the lemma's leading order holds iff
    `far_asymptote(y) <= 5/8`.
    """
    a, b = 0.2, 2.0
    for _ in range(60):
        m = 0.5 * (a + b)
        if far_asymptote(m) > WT_COEFFS[0]:
            b = m
        else:
            a = m
    return 0.5 * (a + b)


def main() -> dict:
    t0 = time.time()
    out: dict = {
        "hunt": "r_a7c12f",
        "question": ("does the far-field constant 637/1000 survive at depth 1, "
                     "as K2-TWO-SPECIES.md section 2 says it does not"),
        "backend": "python-flint (Arb) at 96 bits, via hunts/r_a97060/ball_field.py",
    }

    # 1-2. what the constant says and over what range.
    out["statement"] = {
        "lemma": "Wt_tail_le",
        "source": "hunts/frontier_math/zeta23ext/Zeta23Ext/EForm3/Counting.lean:93",
        "text": "Wt w <= (637/1000)/w  for  1368 <= w",
        "depth_variable_occurs": False,
        "w_threshold": W_THRESHOLD,
        "s_threshold": S_THRESHOLD,
        "Wt_times_w_at_threshold": Wt(W_THRESHOLD) * W_THRESHOLD,
        "Wt_times_w_limit": WT_COEFFS[0],
        "depth_carrying_lemma": "Qim_far_sq / Qim_far_sq_abs (FarField.lean:227,232)",
        "depth_carrying_hypothesis": "hy : y <= 1/2",
    }

    # 3. where the K2 measurement's sup actually sits.
    rows = []
    for y in (0.5, 1.0):
        sup, arg = far_constant_arg(y)
        w = arg * arg - 2
        rows.append({
            "depth": y,
            "far_constant_on_8_400": sup,
            "argmax_s": arg,
            "argmax_w": w,
            "inside_asserted_range": bool(w >= W_THRESHOLD),
            "proved_envelope_Wt_w_times_w_at_argmax": Wt(w) * w,
        })
    out["k2_measurement_relocated"] = rows

    # 4. the ball pass, on the range the constant is asserted on.
    ladder = []
    for y in (0.25, 0.5, 0.75, 1.0):
        b, ne, nr = ball_sup(y, y, S_THRESHOLD, SCAN_HI)
        f = 0.0
        s = S_THRESHOLD
        while s <= SCAN_HI:
            f = max(f, dam(y, s) * (s * s - 2) / y ** 2)
            s += 1e-3
        ladder.append({
            "depth": y,
            "ball_upper_bound": b,
            "float_scan_sup": f,
            "enclosure_cost_ratio": b / f,
            "asymptote_closed_form": far_asymptote(y),
            "holds_vs_637_1000": bool(b <= FAR_CONST),
            "margin": FAR_CONST - b,
            "cells": ne,
            "refinements": nr,
        })
    out["ball_pass_on_asserted_range"] = {
        "s_range": [S_THRESHOLD, SCAN_HI],
        "note": ("s > 400 is NOT enclosed here; see tail_not_enclosed. The "
                 "s-interval is the same [.., 400] the k=2 far rows use before "
                 "their closed-form tail."),
        "ladder": ladder,
    }

    # 4b. the depth as a genuine interval, which is what D_enclosure takes.
    iv = []
    for y_lo, y_hi in ((0.99, 1.0), (0.995, 1.0), (0.999, 1.0)):
        b, ne, nr = ball_sup(y_lo, y_hi, S_THRESHOLD, SCAN_HI)
        iv.append({
            "depth_interval": [y_lo, y_hi],
            "ball_upper_bound": b,
            "holds_vs_637_1000": bool(b <= FAR_CONST),
            "y_normalisation_inflation": (y_hi / y_lo) ** 2,
            "cells": ne,
        })
    out["depth_interval_pass"] = {
        "note": ("the `/y^2` normalisation is divided by the cell's smallest "
                 "y, so a depth cell of relative width r inflates the bound by "
                 "r^2; the margin at depth 1 is 0.84%, so cells wider than "
                 "~0.4% cannot close."),
        "cells": iv,
    }

    # 5. where the constant genuinely breaks.
    yb = break_depth()
    out["break_depth"] = {
        "value": yb,
        "grade": "measured (float scan over s in [S_THRESHOLD, 400])",
        "asymptotic_break_depth": _asym_break(FAR_CONST),
        "note": "depth at which sup Dam*(s^2-2)/y^2 over the ASSERTED range first exceeds 637/1000",
    }

    # 6. the lemma that does carry the depth.
    ratios = []
    for y in (0.5, 0.75, 0.95, 0.97, 1.0, 1.25):
        r, a = qim_far_sq_ratio(y)
        ratios.append({"depth": y, "max_ratio_Qim2_over_y2Wt": r,
                       "argmax_s": a, "holds": bool(r <= 1.0)})
    out["qim_far_sq_extension"] = {
        "lemma": "Qim y s ^ 2 <= y^2 * Wt (s^2 - 2)   (hy : y <= 1/2)",
        "ratios": ratios,
        "asymptotic_break_depth": qim_far_sq_break(),
        "grade": "measured",
    }

    # 7. the tail, named rather than closed.
    tail = {}
    for y in (0.5, 1.0):
        sup, s = 0.0, SCAN_HI
        while s <= 4000.0:
            sup = max(sup, dam(y, s) * (s * s - 2) / y ** 2)
            s += 2e-3
        tail[str(y)] = {"float_sup_on_400_4000": sup,
                        "asymptote_closed_form": far_asymptote(y)}
    out["tail_not_enclosed"] = {
        "note": ("s > 400 is closed in the k=2 far rows by composing "
                 "Wt_tail_le with Qim_far_sq. Qim_far_sq is exactly the step "
                 "that fails at depth 1, so the depth-1 tail has no enclosure "
                 "here and is reported at float grade only."),
        "measured": tail,
    }

    out["elapsed_s"] = time.time() - t0
    return out


def _asym_break(target: float) -> float:
    a, b = 0.2, 3.0
    for _ in range(60):
        m = 0.5 * (a + b)
        if far_asymptote(m) > target:
            b = m
        else:
            a = m
    return 0.5 * (a + b)


if __name__ == "__main__":
    res = main()
    path = Path(__file__).with_name("results.json")
    path.write_text(json.dumps(res, indent=2) + "\n")
    print(json.dumps(res, indent=2))
    print(f"\nwrote {path}")

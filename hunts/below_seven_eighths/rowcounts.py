"""Hunt #136, lane `rowcounts`: the row counts of OpenAI's Part II assembly, loss by loss.

The 7/8 preprint (github.com/openai/math at adc7f124, paper.tex, sha256 42a5ee0f...c6a3)
bounds the number of physical rows in a dynamic bin by U^{R_*}, with

    R_*(delta, x) = 1 - delta + (alpha - delta) delta P_x / (2 J),     J = (alpha - delta) D_x + delta P_x

(Proposition "Row counts from the witnesses", lines 15185 to 15446, and Eq.
target-cutoff, line 15963).  D_x and P_x are built from two moment-lemma capacities and
the sextic amplification slope:

    inverse (marked) capacity  z_M(r) = c_M (1 - r),          paper c_M = 1/2  (line 15182)
    plain capacity             z_P(m) = c_P (1 - 2m),         paper c_P = 2/9  (line 15327)
    amplified inverse moment   e(r) = 1 - alpha + alpha r,   paper alpha = 5/6 (line 15300)

Lemma marked has a second strict condition, 2r + 8z <= 3m - c_2 (line 9254), which at row
width one caps the marked capacity at z <= c_M2 (3/2 - r) with c_M2 = 1/4.  It comes from the
second canonical invariant 4F - 3M - 6 z_0 >= c (line 9809, initialized at line 12209), and
the paper uses z_M only where it is slack (lines 15182 to 15183).  At the paper's c_M = 1/2 it
is slack at every inverse row; it starts to bind once c_M passes 37/65 (`marked_second_threshold`).
The closed form R_* ignores it, so it is used only below that threshold; the measured
evaluator `sigma_general` imposes it.

This module

1. rewrites the row-count algebra with (alpha, c_M, c_P) free and reproduces 39 selected
   constants of the row-count proposition, and 10 of the endpoint and frequency-range
   text, in exact rational arithmetic (not every constant printed in the ranges read);
2. re-implements the minimal part of hunt #134's probe (target, C_0, -E_*) and gives an
   exact evaluator of the smallest target this assembly allows as a function of the
   inputs: the optimum on the binding slice x = 1/2 is an algebraic number (a quadratic
   irrationality for fixed inputs, a cubic when the plain capacity is tied to the
   target), bracketed by an exact rational LP lower bound and an exact rational upper
   bound whose feasibility over the whole (delta, x) box is checked by Bernstein
   subdivision in rational arithmetic;
3. prices each input by an exact shadow price and an exact break-even value, finds the
   x = 0 wall that no capacity can pass at b >= 0, and evaluates perfect inputs with every
   selected capacity capped by the slot supply and by Lemma marked's second condition (a
   float evaluator, graded measured).  The rows d <= 1/2, which the paper counts at t = 1
   with no selected primes (line 16146), are slack at the paper's inputs but bind at every
   perfect input; the evaluator takes them as the paper counts them (`d_half='paper'`) or
   recounted at the balancing t (`d_half='balanced'`, an inferred reading), and the exact
   walls of both cases are `slice_on_dhalf_line`, `alpha_zero_paper_dhalf` and the x = 0 slice;
4. tests every count step that can be enumerated, by exact enumeration at small cases:
   the greedy slot selection, the use of all detector lengths t at once, slots beyond
   capacity, one copy against two, the conductor strata, the sextic reciprocity factor
   and the exceptional Gram frequencies in Z[omega], the local correlation factor
   L_{p^c} (including p dividing one of n1, n2), and the sixth-power lift count.

Grades follow MISSION.md: cited, derived, inferred, measured.  Nothing here checks the
moment lemmas themselves; they are inputs at the exponents the paper proves.

    .venv/bin/python hunts/below_seven_eighths/rowcounts.py
    .venv/bin/python hunts/below_seven_eighths/rowcounts.py --paper PATH --probe134 PATH
"""
from __future__ import annotations

import argparse
import hashlib
import os
import importlib.util
import itertools
import json
import sys
from dataclasses import dataclass, replace
from fractions import Fraction as Fr
from math import comb, isqrt
from pathlib import Path

HERE = Path(__file__).resolve().parent

PAPER_SHA256 = "42a5ee0febca59fd1def55cfd6c6808c322ef4237d7726303ea52f711deac6a3"
PAPER_DEFAULT = Path(os.environ.get("ZETA_LAB_CACHE", os.path.expanduser("~/.cache/zeta-lab"))) / "openai-math-adc7f124" / "paper.tex"

#: public abscissae as MISSION.md records them (cited from the campaign map, not checked here)
GUO_SIGMA_DAGGER = "0.8749570194"
XU_SANG = Fr(8748867, 10**7)
#: the best Dirichlet abscissa on record as this hunt's FOLLOWUPS.md reports it (tracker PR 68,
#: 2026-10-21); cited there, not checked here
TRACKER_RECORD = Fr(8748087, 10**7)

# ---------------------------------------------------------------------------- citations

#: key -> (line, verbatim snippet of paper.tex at that line)
CITATIONS = {
    "D_x_def": (15192, r"D_x=3-\frac{17x}{9},\qquad"),
    "P_x_def": (15193, r"P_x=\left(2-\frac{8x}{9}\right)(1-x)."),
    "count_statement": (15201, r"U^{\max\{R_{\rm short}(t),L(t)\}+\Delta/4+\epsilon}"),
    "R_short_def": (15206, r"R_{\rm short}(t)=1-\delta+\frac{\delta P_x}{D_x}(3/2-t),"),
    "L_def": (15208, r"L(t)=1-\delta+(\alpha-\delta)(t-1)."),
    "no_slot_t1": (15215, r"U^{1-2\delta/3+\epsilon}(1+T_1)^{A_{\mathcal A}},"),
    "selection_gain": (15118, r"The gained exponent is at least \(qz\): if positive slots suffice"),
    "selection_loss": (15122, r"slot loses at most \((\max_i w_i)\delta/2\).  Thus a fixed"),
    "selection_display": (15127, r"\ge U^{2qz-\delta\max_iw_i}."),
    "z_P": (15175, r"z_P(m)=\frac{1-2m}{6\kappa}"),
    "z_P_cond": (15180, r"so its condition is \(2m+6\kappa z\le1\)."),
    "z_M": (15182, r"\(z_M(r)=(1-r)/2\).  We use this capacity only where the second"),
    "two_moments_marked": (15235, r"\ll U^{1-\delta r-2qz+\epsilon}(1+T_1)^{A_{\mathcal A}},"),
    "two_moments_plain": (15238, r"\ll U^{1-2\delta m-2qz+\epsilon}(1+T_1)^{A_{\mathcal A}},"),
    "no_slot_inverse": (15288, r"1-\delta r,&0\le r\le1,\\"),
    "no_slot_inverse_long": (15289, r"1-\alpha+(\alpha-\delta)r,&r\ge1."),
    "alpha_slope": (15300, r"moment exponent \((1+5r)/6=1-\alpha+\alpha r\)."),
    "baseline_cap": (15327, r"\(2(1-2m)/9\).  Since the actual \(m\) is at least"),
    "A_I": (15331, r"A_I(r)&=1-\delta\{x+(1-x)r\},\\"),
    "S_t": (15333, r"+\left(2-\frac{8x}{9}\right)(t-r)\right\}."),
    "plain_slopes": (15342, r"-2\delta+\frac{8q}{9}<0."),
    "r_cross": (15350, r"\frac{(2-8x/9)t-5x/9}{D_x}."),
    "r_cross_ends": (15355, r"r_*(1)=\frac{2-13x/9}{3-17x/9}\ge\frac{23}{37},"),
    "t_minus_r": (15359, r"t-r_*(t)=\frac{(1-x)t+5x/9}{D_x}."),
    "t_minus_r_one": (15363, r"\((1-4x/9)/(3-17x/9)\ge1/3\)."),
    "marked_margins": (15376, r"3-2r-8z=4(1-r-2z)+(2r-1)>0."),
    "margin_9_37": (15378, r"The second inequality has a margin at least \(9/37\) before its"),
    "cap_7_37": (15382, r"\((1-23/37)/2=7/37\).  On the plain side,"),
    "cap_2_27": (15384, r"\(2/27+O(\epsilon)\).  At \(d=h\) the available length is"),
    "supply_8_39": (15386, r"\frac{\ell}{h}=\frac8{39},\qquad"),
    "cap_compare": (15399, r"&=\frac{24q(1-2m)\Delta}{(9/2)(9/2+12\Delta)}\\"),
    "cap_compare_bound": (15400, r"&\le\frac{\Delta}{4}+O(\epsilon)."),
    "short_average": (15412, r"&=\frac{(2-8x/9)A_I(r)+(1-x)S_t(r)}{D_x}\\"),
    "zero_cap_plain": (15429, r"\(1-2m\le6\kappa\nu_0\le6\nu_0\), and its count is at most"),
    "R_star_def": (15965, r"R_*=L(t)."),
    "t_def": (15964, r"t=1+\frac{\delta P_x}{2\mathcal J},\qquad"),
    "J_bounds": (15976, r"\frac{35}{54}\le\mathcal J\le\frac52."),
    "D_minus_P": (15972, r"D_x-P_x=1+x-\frac{8x^2}{9}>0,"),
    "balance": (15984, r"=\frac{\delta P_x}{2}-\mathcal J(t-1)=0."),
    "endpoint_alpha": (15989, r"and \(R_*=R_{\rm short}(3/2)=L(3/2)=1-\delta\).  The corresponding crossing"),
    "floor_bound": (15847, r"E(h)\le C_0+\frac34\delta_0=-\frac7{1200}<0."),
    "floor_ideal": (15844, r"zero witness.  The ideal count \(R=1\), together with"),
    "slope_4_25": (16133, r"\ge\frac{33}{50}-\frac{\delta}{2}\ge\frac4{25}>0."),
    "R_cap_17_12": (16139, r"R_*\le1-\delta+\frac{\alpha-\delta}{2}\le\frac{17}{12},"),
    "R_cap_139_96": (16141, r"R_*+\Delta/4\le\frac{139}{96},"),
    "marked_lemma": (9254, r"r+2z\le m-c_1,\qquad 2r+8z\le3m-c_2."),
    "canonical_invariant": (9808, r"F-M-Q-z_0\ge c_{\rm node},\qquad"),
    "init_identity": (12208, r"F_c^{\rm init}-M_c^{\rm init}-(P_1+G)-z_0&=m-r-2z+2G,\\"),
    "row_branch": (9904, r"E_{\rm ref}\le M+z_a+\tfrac53\eta"),
    "plain_lemma_cond": (12561, r"n_1+n_2+6\kappa z=A+(6\kappa-1)z\le M."),
    "plain_kappa_range": (12532, r"Let \(3/4\le\kappa\le1\).  Let \(n_1,n_2\ge0\), and let"),
    "pointwise_prime": (12873, r"\le C Z^{\kappa z+\epsilon_1}p_j(\boldsymbol W)^b"),
    "strip_rate": (14259, r"\(d\) decreases \(A_{\rm act}+(6\kappa-1)z_{\rm act}\) by \(6\kappa d\)"),
    "amplified": (12375, r"\ll \max\{U,U^{1/6}D^{5(1+c)/6}\}(UD)^\epsilon."),
    "lift_count": (12410, r"Ideal counting outside the fixed set \(S\) gives at least \(c_S P\)"),
    "lift_injective": (12437, r"Average this bound over the \(a\)'s and sum over \(u\).  The map"),
    "lift_bound": (12449, r"=U^{1/6}H^{5/6}(UD)^\epsilon,"),
    "bin_prime_bound": (15021, r"U^{\epsilon_1}P_i^{a-1/2+O(e)}."),
    "detector_t": (4513, r"For every \(t\in[1,3/2]\),"),
    "detector_lengths": (4521, r"r\le t+O(1/\log U),\qquad"),
    "detector_saturation": (4530, r"\qquad 0\le m\le\tfrac12+O(\epsilon),\\"),
    "gram_statement": (8352, r"\ll (1+|\nu|)^{J_{\mathrm{Gr}}}\frac Q{Y'}"),
    "gram_terms": (8353, r"\left(1+P_a^{1/6}+\frac{P_a^2}{Y'}\right)Z^\epsilon."),
    "gram_coeff": (8366, r"$c_\sigma(s)=1_{s\in\sigma}\chi_s(b_*)/(\tau\xi(s))$, extended by"),
    "gram_exceptional_def": (8439, r"If $k$ has a valuation $e_p$ not divisible by six at a prime outside"),
    "gram_exceptional_count": (8534, r"It remains to count the exceptional nonzero frequencies.  They have"),
    "gram_trivial": (8546, r"Use $K_R=RP_a/C_0$, $|L_C|\le q_C$, and the trivial two-column"),
    "local_L": (7114, r"L_{p^c}=P^{c-1}\chi_p(n_1/n_2)^c"),
    "LC_bound": (7130, r"$|L_C|\le q_C$, and the extension is periodic modulo"),
    "xi_choice": (3350, r"Choose a residue character $\xi$ modulo $b_*$ whose restriction to"),
    "xi_quadratic": (3353, r"use the quadratic character, and the residue field at the prime over"),
    "high_exponent": (15729, r"&=a-\frac78+h\left(\frac{17}{50}-\frac16\right)"),
    "C_0": (15734, r"\qquad C_0=-\frac1{48}."),
    "endpoint_lemma": (16000, r"-E_*\ge\frac{49}{440640}>\frac1{10000}."),
    "rows_counted_times_max": (15810, r"Multiplying by the assumed cardinality proves"),
    # Lemma marked's second condition and where it comes from
    "z_M_second": (15183, r"strict inequality in Lemma~\ref{lem:marked} also has a fixed margin."),
    "two_strict_conditions": (15380, r"conditions of Lemma~\ref{lem:marked} at row width one."),
    "second_invariant": (9809, r"4F-3M-6z_0\ge c_{\rm node}."),
    "init_identity_second": (12209, r"4F_c^{\rm init}-3M_c^{\rm init}-6z_0&=3m-2r-8z+10G+2P_1."),
    # the local factor when p divides one of n1, n2
    "local_L_one_divides": (7122, r"If $p$ divides exactly one of $n_1,n_2$, the local factor is"),
    "local_L_one_value": (7123, r"$P^{c-1}(P-1)1_{6\mid c}1_{p\nmid k}$.  On the genuine residual locus"),
    # the Gram hypothesis behind b >= 0, and the floor bin
    "gram_hypothesis": (8345, r"P_a=Y'^2/Q\ge1."),
    "gram_P_a_value": (8588, r"P_a=Y'^2/Q=q_{b_*}^{-1}Z^{1/8}."),
    "floor_bin": (15843, r"The floor bin \(a=51/100\) has \(\delta_0=1/50\) and requires no"),
    # constants of the endpoint and frequency-range text rebuilt in endpoint_reproductions
    "actual_plain_slope": (15341, r"-2\delta+\frac{4q}{9/2+12\Delta}<0,\qquad"),
    "large_delta_endpoint": (15945, r"=-\frac1{48}-\frac{\delta}{16}+O(\epsilon)<0."),
    "m_hi": (16101, r"&=-\frac{49}{440640}-\frac{51}{64}\Delta"),
    "zeta_range": (16123, r"0<\zeta<5\ell-h=\frac1{48},"),
    "margin_2_185": (16126, r"\(1/5\), whose margin above \(7/37\) is \(2/185\)."),
    "R_76_75": (16151, r"R=\frac{76}{75}-\frac23\delta."),
    "R_76_75_floor": (16153, r"At \(\delta=1/50\) it equals one, so it also covers the floor."),
    "slope_101_150": (16154, r"Its slope is \(101/150-\delta/6>0\) on this range."),
    "E_half": (16159, r"\le-\frac{529}{2400}+\frac{25}{96}\delta+O(\epsilon)"),
    "E_half_bound": (16160, r"\le-\frac{49}{14400}+O(\epsilon)<0."),
    # the rows d <= 1/2: the paper's t = 1, and the no-slot counts that hold at every t
    "d_half_t1": (16146, r"For \(d_{\min}\le d\le1/2\) and \(\delta\le\alpha\), choose \(t=1\)"),
    "no_slot_every_t": (15453, r"of the current Part~II bin ceiling.  Consequently, for each fixed"),
    "no_slot_every_t_2": (15454, r"\(t\in[1,3/2]\), the bound in Equation~\eqref{eq:no-slot-inverse-count}"),
    "plain_zero_slot": (12557, r"\item \(z=0\).  There is no restriction on the bounded nonnegative"),
}


def verify_citations(paper: Path) -> list[str]:
    """Return the citation keys whose snippet is not on its stated line (sha256 checked first)."""
    text = paper.read_bytes()
    if hashlib.sha256(text).hexdigest() != PAPER_SHA256:
        return ["<sha256 mismatch: not the pinned paper.tex>"]
    lines = text.decode("utf-8").splitlines()
    return [k for k, (n, snip) in CITATIONS.items() if snip not in lines[n - 1]]


# ------------------------------------------------------------------------- the inputs

@dataclass(frozen=True)
class Inputs:
    """The moment-lemma constants that the row counts consume.

    alpha  slope of the amplified inverse moment, e(r) = 1 - alpha + alpha r for r >= 1
    c_M    marked (inverse) capacity coefficient from Lemma marked's first condition
           r + 2z <= 1 at width one: z <= c_M (1 - r)
    c_P    plain capacity coefficient, z_P(m) = c_P (1 - 2m); the paper's 2/9 = 1/(6 kappa_0)
    c_M2   Lemma marked's second condition 2r + 8z <= 3 at width one: z <= c_M2 (3/2 - r),
           paper 1/4 (line 9254).  The closed form R_* uses z_M(r) = c_M (1 - r) and is exact
           only while this cap is slack at every inverse row (`marked_second_margin`); the
           measured evaluator imposes z_M(r) = min(c_M (1 - r), c_M2 (3/2 - r), supply).
    """

    alpha: Fr = Fr(5, 6)
    c_M: Fr = Fr(1, 2)
    c_P: Fr = Fr(2, 9)
    c_M2: Fr = Fr(1, 4)


PAPER = Inputs()
HALF = Fr(1, 2)
#: the paper's floor bin a = 51/100, delta_0 = 1/50 (line 15843)
DELTA0 = Fr(1, 50)


def d_x(x, inp: Inputs = PAPER):
    """D_x = 3 - 2 x c_M - 4 x c_P: the sum of the two crossing slopes (paper 3 - 17x/9)."""
    return 3 - 2 * x * inp.c_M - 4 * x * inp.c_P


def p_x(x, inp: Inputs = PAPER):
    """P_x = (1 - 2 x c_M)(2 - 4 x c_P): their product (paper (2 - 8x/9)(1 - x))."""
    return (1 - 2 * x * inp.c_M) * (2 - 4 * x * inp.c_P)


def j_cal(delta, x, inp: Inputs = PAPER):
    """J = (alpha - delta) D_x + delta P_x (Eq. target-cutoff, line 15963)."""
    return (inp.alpha - delta) * d_x(x, inp) + delta * p_x(x, inp)


def count_marked(delta, x, r, inp: Inputs = PAPER):
    """Lemma marked with the full capacity: 1 - delta r - 2 q z_M(r), q = x delta (line 15235)."""
    return 1 - delta * r - 2 * x * delta * inp.c_M * (1 - r)


def count_plain(delta, x, m, inp: Inputs = PAPER):
    """Lemma plain, two copies, full capacity: 1 - 2 delta m - 2 q z_P(m) (line 15238)."""
    return 1 - 2 * delta * m - 2 * x * delta * inp.c_P * (1 - 2 * m)


def count_long(delta, r, inp: Inputs = PAPER):
    """Amplified no-slot inverse count for r >= 1: e(r) - delta r = 1 - alpha + (alpha - delta) r."""
    return 1 - inp.alpha + (inp.alpha - delta) * r


def r_cross(x, t, inp: Inputs = PAPER):
    """Crossing of the marked count with the plain count at m = t - r (paper line 15350)."""
    return ((2 - 4 * x * inp.c_P) * t + 2 * x * (inp.c_P - inp.c_M)) / d_x(x, inp)


def r_short(delta, x, t, inp: Inputs = PAPER):
    """R_short(t) = 1 - delta + (delta P_x / D_x)(3/2 - t) (line 15206), general inputs."""
    return 1 - delta + delta * p_x(x, inp) / d_x(x, inp) * (Fr(3, 2) - t)


def l_count(delta, t, inp: Inputs = PAPER):
    """L(t) = 1 - delta + (alpha - delta)(t - 1) (line 15208)."""
    return 1 - delta + (inp.alpha - delta) * (t - 1)


def t_balance(delta, x, inp: Inputs = PAPER):
    """t = 1 + delta P_x / (2 J) (line 15964): where R_short(t) = L(t)."""
    return 1 + delta * p_x(x, inp) / (2 * j_cal(delta, x, inp))


def r_star(delta, x, inp: Inputs = PAPER):
    """R_* = 1 - delta + (alpha - delta)_+ delta P_x / (2 J)."""
    if delta >= inp.alpha:
        return 1 - delta
    return 1 - delta + (inp.alpha - delta) * delta * p_x(x, inp) / (2 * j_cal(delta, x, inp))


def marked_second_margin(x, inp: Inputs = PAPER):
    """D_x {c_M2 (3/2 - r) - c_M (1 - r)} at r = r_*(1): Lemma marked's second condition, exactly.

    The inverse count is used only for r_*(t) <= r < 1 (line 15370), r_*(t) >= r_*(1), and the
    ratio (3/2 - r)/(1 - r) increases with r, so the second condition 2r + 8z <= 3 holds at
    every inverse row the closed form uses iff this is >= 0.  With D_x (1 - r_*(1)) = 1 - 2x c_P
    and D_x (3/2 - r_*(1)) = 5/2 - x c_M - 4x c_P it is affine in x, so x = 0 and x = 1/2
    decide.  At the paper's inputs and x = 1/2 it is 1/16, the paper's margin 9/37 of 2r - 1
    at r = 23/37 (line 15378) in other units.
    """
    return inp.c_M2 * (Fr(5, 2) - x * inp.c_M - 4 * x * inp.c_P) - inp.c_M * (1 - 2 * x * inp.c_P)


def marked_second_slack(inp: Inputs = PAPER) -> bool:
    """True iff the closed form R_* respects Lemma marked's second condition on the whole box."""
    return min(marked_second_margin(x, inp) for x in (Fr(0), HALF)) >= 0


def marked_second_threshold(inp: Inputs = PAPER) -> Fr:
    """The largest c_M (other inputs fixed) for which `marked_second_slack` holds, exactly.

    The margin is linear in c_M with negative coefficient -(1 + x c_M2 - 2x c_P), so the
    threshold is the smaller of its zeros at x = 0 and x = 1/2: 37/65 at the paper's c_P, c_M2.
    """
    def zero_at(x):
        return (inp.c_M2 * (Fr(5, 2) - 4 * x * inp.c_P)) / (1 + x * inp.c_M2 - 2 * x * inp.c_P)
    return min(zero_at(Fr(0)), zero_at(HALF))


# -------------------------------------------------------------- paper reproductions

def reproductions(inp: Inputs = None) -> list[dict]:
    """Every constant printed in the row-count section, rebuilt from the general formulas.

    inp defaults to the paper's inputs; other inputs are how the planted-fault test shows
    that these reproductions can fail.
    """
    P0 = PAPER if inp is None else inp
    out = []

    def rec(name, cite, got, want):
        out.append({"name": name, "cite": cite, "line": CITATIONS[cite][0],
                    "got": str(got), "want": str(want), "ok": got == want})

    xs = [Fr(k, 20) for k in range(0, 11)]
    ts = [1 + Fr(k, 20) for k in range(0, 11)]
    ds = [Fr(k, 24) for k in range(1, 20)]
    rec("D_x = 3 - 17x/9", "D_x_def", all(d_x(x, P0) == 3 - Fr(17, 9) * x for x in xs), True)
    rec("P_x = (2 - 8x/9)(1 - x)", "P_x_def",
        all(p_x(x, P0) == (2 - Fr(8, 9) * x) * (1 - x) for x in xs), True)
    rec("A_I(r) = 1 - delta{x + (1-x)r}", "A_I",
        all(count_marked(dl, x, r, P0) == 1 - dl * (x + (1 - x) * r)
            for dl in ds[::4] for x in xs[::2] for r in (Fr(23, 37), Fr(3, 4), Fr(9, 10))), True)
    rec("S_t(r) = 1 - delta{4x/9 + (2 - 8x/9)(t - r)}", "S_t",
        all(count_plain(dl, x, t - r, P0) == 1 - dl * (Fr(4, 9) * x + (2 - Fr(8, 9) * x) * (t - r))
            for dl in ds[::4] for x in xs[::2] for t in ts[::5] for r in (Fr(2, 3), Fr(4, 5))),
        True)
    rec("crossing r_*(t) = ((2 - 8x/9)t - 5x/9)/D_x", "r_cross",
        all(r_cross(x, t, P0) == ((2 - Fr(8, 9) * x) * t - Fr(5, 9) * x) / d_x(x, P0)
            for x in xs for t in ts), True)
    rec("r_*(3/2) = 1", "r_cross_ends", all(r_cross(x, Fr(3, 2), P0) == 1 for x in xs), True)
    rec("r_*(1) = (2 - 13x/9)/(3 - 17x/9) >= 23/37", "r_cross_ends",
        all(r_cross(x, 1, P0) == (2 - Fr(13, 9) * x) / (3 - Fr(17, 9) * x) >= Fr(23, 37)
            for x in xs), True)
    rec("r_*(1) = 23/37 at x = 1/2", "r_cross_ends", r_cross(HALF, 1, P0), Fr(23, 37))
    rec("t - r_*(t) = ((1-x)t + 5x/9)/D_x", "t_minus_r",
        all(t - r_cross(x, t, P0) == ((1 - x) * t + Fr(5, 9) * x) / d_x(x, P0) for x in xs for t in ts),
        True)
    rec("t - r_*(3/2) = 1/2", "t_minus_r", all(Fr(3, 2) - r_cross(x, Fr(3, 2), P0) == HALF for x in xs),
        True)
    rec("1 - r_*(1) at t = 1 is (1 - 4x/9)/(3 - 17x/9) >= 1/3", "t_minus_r_one",
        all(1 - r_cross(x, 1, P0) == (1 - Fr(4, 9) * x) / (3 - Fr(17, 9) * x) >= Fr(1, 3) for x in xs),
        True)
    rec("D_x >= 37/18 on [0, 1/2]", "r_cross", min(d_x(x, P0) for x in xs), Fr(37, 18))
    # R_short is the common value at the crossing and does not depend on r
    ok = True
    for dl in ds[::3]:
        for x in xs[::2]:
            for t in ts:
                rc = r_cross(x, t, P0)
                a, s = count_marked(dl, x, rc, P0), count_plain(dl, x, t - rc, P0)
                avg = ((2 - Fr(8, 9) * x) * count_marked(dl, x, Fr(7, 10), P0)
                       + (1 - x) * count_plain(dl, x, t - Fr(7, 10), P0)) / d_x(x, P0)
                ok = ok and a == s == r_short(dl, x, t, P0) == avg
    rec("R_short = weighted average, independent of r (Eq. 15412)", "short_average", ok, True)
    rec("L(t) = 1 - alpha + (alpha - delta)t", "L_def",
        all(l_count(dl, t, P0) == count_long(dl, t, P0) for dl in ds for t in ts), True)
    rec("e(r) slope: (1 + 5r)/6 = 1 - alpha + alpha r", "alpha_slope",
        all((1 + 5 * r) / 6 == 1 - P0.alpha + P0.alpha * r for r in ts), True)
    rec("no slots, t = 1: R_short(1) = 1 - 2 delta/3 at x = 0", "no_slot_t1",
        all(r_short(dl, Fr(0), 1, P0) == 1 - Fr(2, 3) * dl for dl in ds), True)
    rec("plain slope with baseline capacity: -2 delta + 8q/9 < 0", "plain_slopes",
        all(-2 * dl + Fr(8, 9) * x * dl < 0 for dl in ds for x in xs), True)
    kappa = lambda D: Fr(3, 4) + 2 * D  # noqa: E731
    capc = all(2 * x * dl * (1 - 2 * m) * (Fr(2, 9) - 1 / (6 * kappa(D)))
               == 24 * x * dl * (1 - 2 * m) * D / (Fr(9, 2) * (Fr(9, 2) + 12 * D))
               <= D / 4
               for D in (Fr(1, 1000), Fr(1, 100), Fr(1, 24)) for dl in ds[::5]
               for x in xs[::5] for m in (Fr(1, 3), Fr(2, 5), Fr(1, 2)))
    rec("capacity comparison 24q(1-2m)Delta/((9/2)(9/2+12Delta)) <= Delta/4", "cap_compare", capc,
        True)
    rec("z_P(m) = (1-2m)/(6 kappa) = (1-2m)/(9/2 + 12 Delta)", "z_P",
        all((1 - 2 * m) / (6 * kappa(D)) == (1 - 2 * m) / (Fr(9, 2) + 12 * D)
            for D in (Fr(0), Fr(1, 24)) for m in (Fr(1, 3), Fr(1, 2))), True)
    rec("z_P at Delta = 0 is the baseline 2(1-2m)/9", "baseline_cap",
        all(P0.c_P * (1 - 2 * m) == 2 * (1 - 2 * m) / 9 for m in (Fr(1, 3), Fr(2, 5))), True)
    r0 = Fr(23, 37)
    rec("3 - 2r - 8z = 4(1 - r - 2z) + (2r - 1)", "marked_margins",
        all(3 - 2 * r - 8 * z == 4 * (1 - r - 2 * z) + (2 * r - 1)
            for r in (r0, Fr(4, 5)) for z in (Fr(0), Fr(1, 10))), True)
    rec("margin 2r - 1 >= 9/37 at r >= 23/37", "margin_9_37", 2 * r0 - 1, Fr(9, 37))
    rec("inverse capacity at most (1 - 23/37)/2 = 7/37", "cap_7_37", P0.c_M * (1 - r0), Fr(7, 37))
    rec("plain capacity at most 2/27 (m >= 1/3)", "cap_2_27", P0.c_P * (1 - 2 * Fr(1, 3)),
        Fr(2, 27))
    rec("supply l/h = 8/39 at the paper's geometry", "supply_8_39", Fr(1, 6) / Fr(13, 16), Fr(8, 39))
    rec("8/39 - 7/37 = 23/1443", "supply_8_39", Fr(8, 39) - Fr(7, 37), Fr(23, 1443))
    rec("zero plain capacity: 1 - 2m <= 6 kappa nu_0 <= 6 nu_0", "zero_cap_plain",
        all(6 * kappa(D) <= 6 for D in (Fr(0), Fr(1, 24))), True)
    xs2 = [Fr(k, 40) for k in range(0, 21)]
    rec("37/18 <= D_x <= 3", "J_bounds", (min([d_x(x, P0) for x in xs2]), max([d_x(x, P0) for x in xs2])),
        (Fr(37, 18), Fr(3)))
    rec("7/9 <= P_x <= 2", "J_bounds", (min([p_x(x, P0) for x in xs2]), max([p_x(x, P0) for x in xs2])), (Fr(7, 9), Fr(2)))
    rec("D_x - P_x = 1 + x - 8x^2/9", "D_minus_P",
        all(d_x(x, P0) - p_x(x, P0) == 1 + x - Fr(8, 9) * x * x for x in xs2), True)
    jv = [j_cal(dl, x, P0) for dl in [Fr(k, 60) for k in range(0, 51)] for x in xs2]
    rec("35/54 <= J <= 5/2 on the closed ranges", "J_bounds", (min(jv), max(jv)),
        (Fr(35, 54), Fr(5, 2)))
    bal = all(d_x(x, P0) * (r_short(dl, x, t_balance(dl, x, P0), P0) - l_count(dl, t_balance(dl, x, P0), P0))
              == dl * p_x(x, P0) / 2 - j_cal(dl, x, P0) * (t_balance(dl, x, P0) - 1) == 0
              for dl in ds for x in xs)
    rec("D_x{R_short(t) - L(t)} = delta P_x/2 - J(t - 1) = 0 at the balancing t", "balance", bal, True)
    rec("R_* = L(t) = R_short(t) at the balancing t", "R_star_def",
        all(r_star(dl, x, P0) == l_count(dl, t_balance(dl, x, P0), P0) == r_short(dl, x, t_balance(dl, x, P0), P0)
            for dl in ds for x in xs), True)
    rec("1 < t < 3/2 for 0 < delta < alpha", "t_def",
        all(1 < t_balance(dl, x, P0) < Fr(3, 2) for dl in ds for x in xs), True)
    a = P0.alpha
    rec("delta = alpha: J = alpha P_x, t = 3/2, R_* = 1 - delta", "endpoint_alpha",
        all(j_cal(a, x, P0) == a * p_x(x, P0) and t_balance(a, x, P0) == Fr(3, 2) and r_star(a, x, P0) == 1 - a
            and r_short(a, x, Fr(3, 2), P0) == l_count(a, Fr(3, 2), P0) == 1 - a for x in xs), True)
    rec("R + delta/2 - 17/50 >= 33/50 - delta/2 >= 4/25", "slope_4_25",
        all(r_star(dl, x, P0) + dl / 2 - Fr(17, 50) >= Fr(33, 50) - dl / 2 >= Fr(4, 25)
            for dl in ds for x in xs), True)
    rec("R_* <= 1 - delta + (alpha - delta)/2 <= 17/12", "R_cap_17_12",
        all(r_star(dl, x, P0) <= 1 - dl + (a - dl) / 2 <= Fr(17, 12) for dl in ds for x in xs), True)
    # the paper prints 139/96; 17/12 + Delta/4 with Delta <= 1/24 gives 137/96, so 139/96 is a
    # valid but loose bound (harmless: the margin 139/96 + 1/2 - 17/50 < 2 still holds)
    rec("R_* + Delta/4 <= 17/12 + 1/96 = 137/96 <= 139/96", "R_cap_139_96",
        (Fr(17, 12) + Fr(1, 24) / 4, Fr(17, 12) + Fr(1, 24) / 4 <= Fr(139, 96)), (Fr(137, 96), True))
    rec("139/96 + 1/2 - 17/50 < 2", "R_cap_139_96", Fr(139, 96) + HALF - Fr(17, 50) < 2, True)
    return out


def e_half_R(delta, ell, M, b, R):
    """E(1/2) from the first line of Eq. common-high-exponent (line 15729) with row exponent R.

    For the rows d <= 1/2 no primes are selected, so R does not depend on q and the worst
    amplitude is q = delta/2, where the term (delta/2 - q) ell vanishes; the target replaces 7/8.
    """
    a = (1 + delta) / 2
    h = h_of(ell, M, b)
    l_y = (M + b) / 2
    q = delta / 2
    return (a - target(ell, M, b) + h * (Fr(17, 50) - Fr(1, 6)) - a * l_y - (1 - a) * ell
            - (delta / 2 - q) * ell + HALF * (R + delta / 2 - Fr(17, 50)))


def e_half(delta, ell, M, b, R_const=Fr(76, 75)):
    """E(1/2) as the paper counts the rows d <= 1/2: t = 1, no selected primes, R = 76/75 - 2 delta/3.

    That R (line 16151) also covers the floor bin at delta = 1/50.  Affine in delta, so its
    maximum over [1/50, 5/6] sits at an end.
    """
    return e_half_R(delta, ell, M, b, R_const - Fr(2, 3) * delta)


def e_half_max(ell, M, b, R_const=Fr(76, 75)):
    """max of E(1/2) over 1/50 <= delta <= 5/6 with the paper's count (exact; the ends decide)."""
    return max(e_half(DELTA0, ell, M, b, R_const), e_half(Fr(5, 6), ell, M, b, R_const))


def d_half_line():
    """E(5/6) <= 0 with the paper's count, on M + ell = 1, as ell <= L0 + k b; returns (L0, k).

    E(5/6) is affine in (ell, b), so three evaluations give it exactly: (188/1593, 223/531).
    Near every geometry in this lane the end delta = 1/50 is slack and this line is the whole
    constraint (checked where it is used).
    """
    f = lambda l_, b_: e_half(Fr(5, 6), l_, 1 - l_, b_)  # noqa: E731
    c = f(Fr(0), Fr(0))
    cl, cb = f(Fr(1), Fr(0)) - c, f(Fr(0), Fr(1)) - c
    return -c / cl, -cb / cl


def r_noslot_balanced(delta, alpha):
    """The no-slot row count at the balancing t: 1 - delta + (alpha - delta)_+ delta/(3 alpha - delta).

    With no selected primes the counts are 1 - delta r (r < 1, e(r) = 1), 1 - 2 delta m (the
    zero-slot plain case) and L(t) (r >= 1), so the short count is 1 - 2 delta t/3, the x = 0
    form of R_short, and balancing it against L(t) gives R_*(delta, 0).  The paper uses this
    only at t = 1 (1 - 2 delta/3, line 15215, used for the rows d <= 1/2 at line 16146); that
    the same counts hold at every t is a reading of lines 15438 to 15466 (the inverse side for
    each fixed t, line 15453) and of case z = 0 of Lemma plain (line 12557) (inferred).
    """
    if delta >= alpha:
        return 1 - delta
    return 1 - delta + (alpha - delta) * delta / (3 * alpha - delta)


def e_half_max_balanced(ell, M, b, inp: Inputs = PAPER) -> dict:
    """E(1/2) when the rows d <= 1/2 are counted at the balancing t: exact sign, and the max.

    The floor bin (delta = 1/50, R = 1) and, above it, R = r_noslot_balanced.  On
    [1/50, alpha) the product (3 alpha - delta) E(1/2) is a quadratic in delta, so its sign is
    decided exactly at the two ends and the vertex; on [alpha, 5/6] E(1/2) is affine.  The
    returned `max` is the largest value at those points and on a 400-point rational grid.
    """
    al = inp.alpha
    pts = [DELTA0]
    vals = [e_half_R(DELTA0, ell, M, b, Fr(1))]
    ok = vals[0] < 0
    top = min(al, Fr(5, 6))
    if top > DELTA0:
        Q = lambda d: (3 * al - d) * e_half_R(d, ell, M, b, r_noslot_balanced(d, al))  # noqa: E731
        q0, q1, q2 = Q(DELTA0), Q((DELTA0 + top) / 2), Q(top)
        # the quadratic through three points, in u = (d - DELTA0)/(top - DELTA0)
        A2 = 2 * (q2 - 2 * q1 + q0)
        A1 = q2 - q0 - A2
        cands = [Fr(0), Fr(1)]
        if A2 != 0:
            u = -A1 / (2 * A2)
            if 0 < u < 1:
                cands.append(u)
        for u in cands:
            ok = ok and (A2 * u * u + A1 * u + q0) < 0
        grid = [DELTA0 + (top - DELTA0) * Fr(k, 400) for k in range(1, 401)]
        pts += grid
        vals += [e_half_R(d, ell, M, b, r_noslot_balanced(d, al)) for d in grid]
    if al < Fr(5, 6):
        for d in (al, Fr(5, 6)):
            v = e_half_R(d, ell, M, b, 1 - d)
            ok = ok and v < 0
            pts.append(d)
            vals.append(v)
    return {"negative": ok, "max": max(vals)}


def endpoint_reproductions(fault=None) -> list[dict]:
    """Ten constants of the endpoint and frequency-range text, rebuilt in exact arithmetic.

    These are outside the 39 of `reproductions`; with them the lane still does not rebuild
    every constant printed in the ranges it read.  fault='R_no_floor' uses R = 1 - 2 delta/3
    for the rows d <= 1/2 instead of the paper's 76/75 - 2 delta/3, a planted fault.
    """
    out = []

    def rec(name, cite, got, want):
        out.append({"name": name, "cite": cite, "line": CITATIONS[cite][0],
                    "got": str(got), "want": str(want), "ok": got == want})

    ell, M, b = Fr(1, 6), Fr(5, 6), Fr(1, 8)
    h = h_of(ell, M, b)
    ds = [Fr(k, 24) for k in range(1, 21)]
    xs = [Fr(k, 10) for k in range(0, 6)]
    rc_ = Fr(1) if fault == "R_no_floor" else Fr(76, 75)

    def plain_actual(dl, x, m, D):
        return 1 - 2 * dl * m - 2 * x * dl * (1 - 2 * m) / (Fr(9, 2) + 12 * D)
    rec("actual plain slope -2 delta + 4q/(9/2 + 12 Delta) < 0", "actual_plain_slope",
        all(2 * (plain_actual(dl, x, HALF, D) - plain_actual(dl, x, Fr(0), D))
            == -2 * dl + 4 * x * dl / (Fr(9, 2) + 12 * D) < 0
            for dl in ds for x in xs for D in (Fr(0), Fr(1, 100), Fr(1, 24))), True)
    al = PAPER.alpha
    worst = max(-neg_e_star(al, x, ell, M, b) for x in xs)
    rec("delta = alpha, R = 1 - delta: E(h) = C_0 + (3/4 - h) delta = -1/48 - delta/16", "large_delta_endpoint",
        (worst == c0(ell, M, b) + (Fr(3, 4) - h) * al,
         all(c0(ell, M, b) + (Fr(3, 4) - h) * dl == Fr(-1, 48) - dl / 16 for dl in ds)), (True, True))
    cert = Fr(49, 440640)
    feas = bernstein_positive(_add2(endpoint_polynomial(PAPER, ell, M, b),
                                    _scale2(j_polynomial(PAPER), -cert)),
                              (Fr(0), Fr(5, 6), Fr(0), HALF))
    rec("-E_* >= 49/440640 > 1/10000 on [0, 5/6] x [0, 1/2] (Bernstein)", "endpoint_lemma",
        (feas["positive"], cert > Fr(1, 10000)), (True, True))
    rec("1 - h/4 = 51/64 at h = 13/16", "m_hi", 1 - h / 4, Fr(51, 64))
    rec("5 ell - h = 1/48", "zeta_range", 5 * ell - h, Fr(1, 48))
    rec("1/5 - 7/37 = 2/185", "margin_2_185", Fr(1, 5) - Fr(7, 37), Fr(2, 185))
    rec("R = 76/75 - 2 delta/3 equals one at delta = 1/50", "R_76_75_floor",
        rc_ - Fr(2, 3) * DELTA0, Fr(1))
    rec("slope R + delta/2 - 17/50 = 101/150 - delta/6 > 0 on delta <= 5/6", "slope_101_150",
        all(rc_ - Fr(2, 3) * dl + dl / 2 - Fr(17, 50) == Fr(101, 150) - dl / 6 > 0 for dl in ds), True)
    rec("E(1/2) = -529/2400 + 25 delta/96 (R = 76/75 - 2 delta/3, q = delta/2)", "E_half",
        all(e_half(dl, ell, M, b, rc_) == Fr(-529, 2400) + Fr(25, 96) * dl for dl in ds), True)
    rec("max of E(1/2) over [1/50, 5/6] is -49/14400, at delta = 5/6", "E_half_bound",
        e_half_max(ell, M, b, rc_), Fr(-49, 14400))
    return out


# ------------------------------------------------- geometry and endpoint (from #134)

def h_of(ell, M, b):
    """h = 1 - l_x + ell with l_x = (M - b)/2 (Definition stage-high-data, line 5586)."""
    return 1 + ell - M / 2 + b / 2


def target(ell, M, b):
    """sigma_0 = 1 - h/6 + b/12 = 5/6 + (M - 2 ell)/12 (hunt #134, derived there)."""
    return 1 - h_of(ell, M, b) / 6 + b / 12


def c0(ell, M, b):
    """C_0 = 1/2 + ell/2 - 3M/4 + b/6 (hunt #134); the paper's -1/48 at (1/6, 5/6, 1/8)."""
    return HALF + ell / 2 - Fr(3, 4) * M + b / 6


def neg_e_star(delta, x, ell, M, b, inp: Inputs = PAPER):
    """-E_* = -C_0 + delta(ell + b)/2 - ell x delta - h (R_* - (1 - delta)) (hunt #134 form)."""
    return (-c0(ell, M, b) + delta * (ell + b) / 2 - ell * x * delta
            - h_of(ell, M, b) * (r_star(delta, x, inp) - (1 - delta)))


def neg_e_star_transcribed(delta, x, ell, M, b, inp: Inputs = PAPER):
    """The same from the first line of Eq. common-high-exponent (line 15729) at d = h.

    E(d) = a - sigma0 + h(17/50 - 1/6) - a l_y - (1-a) ell - (delta/2 - q) ell
           + d (R + delta/2 - 17/50), a = (1 + delta)/2, q = x delta, l_y = (M + b)/2.
    """
    a = (1 + delta) / 2
    h = h_of(ell, M, b)
    l_y = (M + b) / 2
    R = r_star(delta, x, inp)
    e = (a - target(ell, M, b) + h * (Fr(17, 50) - Fr(1, 6)) - a * l_y - (1 - a) * ell
         - (delta / 2 - x * delta) * ell + h * (R + delta / 2 - Fr(17, 50)))
    return -e


def numbers_from_134() -> dict:
    """The exact numbers hunt #134 publishes, recomputed with this module's formulas."""
    ell, M, b = Fr(1, 6), Fr(5, 6), Fr(1, 8)
    out = {"paper_target": target(ell, M, b), "paper_C0": c0(ell, M, b),
           "paper_worst": neg_e_star(Fr(79, 204), HALF, ell, M, b),
           "floor_corner": target(Fr(1, 5), Fr(4, 5), Fr(0)),
           "floor_corner_C0": c0(Fr(1, 5), Fr(4, 5), Fr(0))}
    # #134's robust single-point bound at delta = 223/576, x = 1/2, b = 0, M = 1 - ell
    dl = Fr(223, 576)
    f = lambda l_, b_: neg_e_star(dl, HALF, l_, 1 - l_, b_)  # noqa: E731
    A = f(Fr(0), Fr(0))
    A_l = f(Fr(1), Fr(0)) - A
    out["robust_bound"] = Fr(11, 12) - (-A / A_l) / 4
    return out


# ------------------------------------------------------ exact optimum on the x = 1/2 slice

def _sympy():
    import sympy as sp
    return sp


def _sym_rat(v):
    sp = _sympy()
    if isinstance(v, Fr):
        return sp.Rational(v.numerator, v.denominator)
    return v


def _slice_coeffs(alpha, c_M, c_P, lam=1, x=None):
    """N(delta) = J (-E_*) at a fixed x (default 1/2) on M + ell = 1: A2 delta^2 + A1 delta + A0.

    On M + ell = 1, -E_* = 1/4 - 5 ell/4 - b/6 + delta (ell (1 - 2x) + b)/2 - (1 + 3 ell + b) K/4;
    at x = 1/2 this is 1/4 - 5 ell/4 - b/6 + delta b/2 - (1 + 3 ell + b) K/4
    with K = lam (alpha - delta) delta P / J, P = P_{1/2}, D = D_{1/2}, J = (alpha - delta) D
    + delta P.  The coefficients are affine in (ell, b) for constant inputs; c_P may also be
    a sympy expression in ell (the tied capacity), in which case the denominator is cleared.
    """
    sp = _sympy()
    ell, b, d = sp.symbols("ell b delta", real=True)
    xx = sp.Rational(1, 2) if x is None else _sym_rat(x)
    D = 3 - 2 * xx * c_M - 4 * xx * c_P
    P = (1 - 2 * xx * c_M) * (2 - 4 * xx * c_P)
    u = sp.Rational(1, 4) - sp.Rational(5, 4) * ell - b / 6
    w = 1 + 3 * ell + b
    J = (alpha - d) * D + d * P
    lin = u + d * (ell * (1 - 2 * xx) + b) / 2
    num, den = sp.fraction(sp.together(sp.expand(J * lin - lam * w * (alpha - d) * d * P / 4)))
    num = sp.expand(num)
    A2, A1, A0 = (sp.expand(num.coeff(d, k)) for k in (2, 1, 0))
    return (ell, b, d), (A2, A1, A0), den


def _minpoly_from_ell_poly(poly_ell, ell, sigma_value):
    """Irreducible integer polynomial of sigma = 11/12 - ell/4 from one in ell."""
    sp = _sympy()
    s = sp.Symbol("sigma")
    expr = sp.expand(poly_ell.subs(ell, sp.Rational(11, 3) - 4 * s))
    for fac, _m in sp.factor_list(expr)[1]:
        pf = sp.Poly(fac, s)
        if pf.degree() >= 1 and abs(sp.N(pf.eval(sigma_value), 60)) < sp.Float(10) ** -35:
            coeffs = [sp.Rational(c) for c in pf.all_coeffs()]
            den = sp.ilcm(*[c.q for c in coeffs])
            ints = [int(c * den) for c in coeffs]
            g = 0
            for c in ints:
                g = __import__("math").gcd(g, abs(c))
            ints = [c // g for c in ints]
            if ints[0] < 0:
                ints = [-c for c in ints]
            return ints
    return None


def slice_optimum(inp: Inputs = PAPER, tied: bool = False, lam=1, x=None) -> dict:
    """Largest ell (M = 1 - ell) with N(delta) >= 0 on [0, alpha] at one x (default 1/2), exactly.

    The binding condition is a double root of the quadratic N in delta (discriminant zero)
    at an interior delta, with the discriminant stationary in b, or with b = 0 when the
    stationary b is negative.  For constant inputs the discriminant is a quadratic in
    (ell, b) and its b-derivative is linear, so ell* is a quadratic irrationality.  With
    tied=True the plain capacity follows the target, c_P = 1/(6(2 sigma - 1)) = 1/(5 - 3 ell),
    and ell* is a root of the b-resultant.  Returns exact sympy numbers, the integer minimal
    polynomial of sigma*, and checks.  The slice optimum is a lower bound for the full problem.
    """
    sp = _sympy()
    a = _sym_rat(inp.alpha)
    cm = _sym_rat(inp.c_M)
    ell_s = sp.Symbol("ell", real=True)
    cp = 1 / (5 - 3 * ell_s) if tied else _sym_rat(inp.c_P)
    (ell, b, d), (A2, A1, A0), _den = _slice_coeffs(a, cm, cp, sp.nsimplify(lam), x=x)
    disc = sp.expand(A1 ** 2 - 4 * A0 * A2)
    cands = []
    if not tied:
        bsol = sp.solve(sp.diff(disc, b), b)
        assert len(bsol) == 1
        bsol = bsol[0]
        eq = sp.numer(sp.together(sp.expand(disc.subs(b, bsol))))
        poly_ell = sp.Poly(sp.expand(eq), ell)
        for rt in sp.solve(poly_ell.as_expr(), ell):
            cands.append((sp.radsimp(rt), sp.radsimp(bsol.subs(ell, rt)), poly_ell.as_expr()))
        # boundary b = 0, used when the stationary b is negative
        eq0 = sp.Poly(sp.expand(disc.subs(b, 0)), ell)
        if eq0.degree() >= 1:
            for rt in sp.solve(eq0.as_expr(), ell):
                cands.append((sp.radsimp(rt), sp.Integer(0), eq0.as_expr()))
    else:
        res = sp.resultant(disc, sp.diff(disc, b), b)
        bsol = sp.solve(sp.diff(disc, b), b)
        assert len(bsol) == 1
        bsol = sp.together(bsol[0])
        for fac, _m in sp.factor_list(res)[1]:
            pf = sp.Poly(fac, ell)
            if pf.degree() < 1:
                continue
            for rt in pf.nroots(n=60):
                if not rt.is_real or not (0 < rt < sp.Rational(1, 5)):
                    continue
                bb = sp.N(bsol.subs(ell, rt), 60)
                scale = 1 + abs(sp.N(A0.subs({ell: rt, b: bb}), 60)) ** 2
                if abs(sp.N(disc.subs({ell: rt, b: bb}), 60)) < sp.Float(10) ** -40 * scale:
                    cands.append((rt, bb, pf.as_expr()))
    best = None
    for rt, bb, pe in cands:
        rtn, bbn = sp.N(rt, 50), sp.N(bb, 50)
        if not (rtn.is_real and bbn.is_real):
            continue
        a2 = sp.N(A2.subs({ell: rt, b: bb}), 50)
        a1 = sp.N(A1.subs({ell: rt, b: bb}), 50)
        if a2 <= 0:
            continue
        dv = -a1 / (2 * a2)
        if bbn == 0 and not tied:
            # b = 0 is the optimum only if disc does not decrease into b > 0 there
            if sp.N(sp.diff(disc, b).subs({ell: rt, b: 0}), 50) < 0:
                continue
        if rtn > 0 and bbn >= 0 and 0 < dv < sp.N(a, 50):
            if best is None or rtn > sp.N(best["ell"], 50):
                best = {"ell": rt, "b": bb, "delta_v": dv, "A2": a2, "poly_ell": pe}
    assert best is not None, "no valid slice optimum"
    sigma = sp.Rational(11, 12) - best["ell"] / 4
    best["sigma"] = sp.radsimp(sigma) if not tied else sigma
    best["sigma_float"] = sp.N(sigma, 40)
    best["minpoly_sigma"] = _minpoly_from_ell_poly(sp.sympify(best["poly_ell"]), ell, best["sigma_float"])
    best["disc_bb"] = sp.N(sp.diff(disc, b, 2).subs({ell: best["ell"], b: best["b"]}), 30)
    best["u_at_opt"] = sp.N((sp.Rational(1, 4) - sp.Rational(5, 4) * ell - b / 6).subs(
        {ell: best["ell"], b: best["b"]}), 30)
    best["disc"] = disc
    best["symbols"] = (ell, b, d)
    best["coeffs"] = (A2, A1, A0)
    return best


def slice_fixed_b(inp: Inputs = PAPER, b=Fr(0), x=Fr(0)) -> dict:
    """Largest ell with N(delta) >= 0 on [0, alpha] at one x and one fixed b, exactly.

    Used to price the Gram hypothesis b >= 0 (P_a >= 1, line 8345) on the x = 0 slice: with
    b fixed the discriminant is a quadratic in ell, and the binding root is the largest one
    whose double root in delta is interior with a positive leading coefficient.  A negative
    b is outside Prop. probe-gram as stated; this only says what such a b would be worth.
    """
    sp = _sympy()
    (ell, bs, d), (A2, A1, A0), _den = _slice_coeffs(_sym_rat(inp.alpha), _sym_rat(inp.c_M),
                                                    _sym_rat(inp.c_P), 1, x=x)
    bb = _sym_rat(b)
    disc = sp.expand((A1 ** 2 - 4 * A0 * A2).subs(bs, bb))
    best = None
    for rt in sp.solve(sp.Poly(disc, ell).as_expr(), ell):
        rtn = sp.N(rt, 50)
        if not rtn.is_real or rtn <= 0:
            continue
        a2 = sp.N(A2.subs({ell: rt, bs: bb}), 50)
        a1 = sp.N(A1.subs({ell: rt, bs: bb}), 50)
        if a2 <= 0:
            continue
        dv = -a1 / (2 * a2)
        if 0 < dv < sp.N(_sym_rat(inp.alpha), 50) and (best is None or rtn > sp.N(best, 50)):
            best = sp.radsimp(rt)
    assert best is not None, "no interior double root"
    sigma = sp.radsimp(sp.Rational(11, 12) - best / 4)
    return {"ell": best, "b": bb, "sigma": sigma, "sigma_float": sp.N(sigma, 40)}


def slice_on_dhalf_line(inp: Inputs = PAPER, x=Fr(0)) -> dict:
    """The slice optimum at one x with b on the line where the paper's rows d <= 1/2 bind, exactly.

    With the paper's count of the rows d <= 1/2 (t = 1, R = 76/75 - 2 delta/3), feasible
    geometries satisfy ell <= L0 + k b (`d_half_line`), and the slice constraint at x gives
    ell <= ell_x(b), which decreases in b near these points (checked by the caller with
    `slice_fixed_b`).  The largest ell is then where both bind: disc(ell, (ell - L0)/k) = 0.
    At x = 0 the slice does not involve c_M or c_P, so this bounds every capacity improvement
    under the paper's count of those rows.
    """
    sp = _sympy()
    L0, k = d_half_line()
    (ell, bs, d), (A2, A1, A0), _den = _slice_coeffs(_sym_rat(inp.alpha), _sym_rat(inp.c_M),
                                                    _sym_rat(inp.c_P), 1, x=x)
    b_line = (ell - _sym_rat(L0)) / _sym_rat(k)
    disc = sp.numer(sp.together(sp.expand((A1 ** 2 - 4 * A0 * A2).subs(bs, b_line))))
    best = None
    for rt in sp.solve(sp.Poly(sp.expand(disc), ell).as_expr(), ell):
        rtn = sp.N(rt, 50)
        if not rtn.is_real or not (0 < rtn < sp.Rational(1, 5)):
            continue
        bb = b_line.subs(ell, rt)
        a2 = sp.N(A2.subs({ell: rt, bs: bb}), 50)
        a1 = sp.N(A1.subs({ell: rt, bs: bb}), 50)
        if a2 > 0 and 0 < -a1 / (2 * a2) < sp.N(_sym_rat(inp.alpha), 50) and sp.N(bb, 50) >= 0:
            if best is None or rtn > sp.N(best[0], 50):
                best = (sp.radsimp(rt), sp.radsimp(bb), -a1 / (2 * a2))
    assert best is not None, "no interior double root on the line"
    sigma = sp.radsimp(sp.Rational(11, 12) - best[0] / 4)
    return {"ell": best[0], "b": best[1], "delta_v": best[2], "sigma": sigma,
            "sigma_float": sp.N(sigma, 40)}


def alpha_zero_paper_dhalf() -> dict:
    """alpha = 0 with the paper's floor and the paper's count of the rows d <= 1/2, exactly.

    With alpha = 0 the excess vanishes and, for b >= 0, -E_* >= 0 reduces to C_0 <= 0, implied
    by the floor.  The floor C_0 + (1/2 + 3 ell/2)/50 <= 0 caps ell from above with b entering
    through C_0, the line ell <= L0 + k b caps it from the other side, and the optimum is
    where they cross: 84031/96156.
    """
    L0, k = d_half_line()
    # floor on M = 1 - ell: -1/4 + 5 ell/4 + b/6 + (1/2 + 3 ell/2) delta_0 = 0, with b = (ell - L0)/k
    a_l = Fr(5, 4) + Fr(3, 2) * DELTA0 + 1 / (6 * k)
    c_ = Fr(-1, 4) + HALF * DELTA0 - L0 / (6 * k)
    ell = -c_ / a_l
    b = (ell - L0) / k
    return {"ell": ell, "b": b, "sigma": target(ell, 1 - ell, b),
            "floor": floor_value(ell, 1 - ell, b), "e_half": e_half_max(ell, 1 - ell, b)}


def break_even_on_dhalf_line(param: str, goal, inp: Inputs = PAPER) -> dict:
    """The input value reaching `goal` when b is held on the paper's d <= 1/2 line, exactly.

    Used where the unconstrained break-even geometry violates the paper's count of the rows
    d <= 1/2 (alpha to the tracker record): with ell = 11/3 - 4 goal and b = (ell - L0)/k, the
    condition disc = 0 is one polynomial in the input, whose root nearest the paper's value on
    the improving side is returned with its integer polynomial.
    """
    sp = _sympy()
    th = sp.Symbol("theta", real=True)
    vals = {"alpha": _sym_rat(inp.alpha), "c_M": _sym_rat(inp.c_M), "c_P": _sym_rat(inp.c_P)}
    vals[param] = th
    (ell, bs, d), (A2, A1, A0), _den = _slice_coeffs(vals["alpha"], vals["c_M"], vals["c_P"])
    L0, k = d_half_line()
    lg = sp.Rational(11, 3) - 4 * _sym_rat(goal)
    bl = (lg - _sym_rat(L0)) / _sym_rat(k)
    eq = sp.numer(sp.together(sp.expand((A1 ** 2 - 4 * A0 * A2).subs({ell: lg, bs: bl}))))
    poly = sp.Poly(sp.expand(eq), th)
    base = float(getattr(inp, param))
    improving = (lambda v: v < base) if param == "alpha" else (lambda v: v > base)
    roots = sorted((abs(float(r) - base), float(r)) for r in poly.nroots(n=40)
                   if r.is_real and improving(float(r)) and 0 < float(r) < 1)
    theta = roots[0][1]
    coeffs = [sp.Rational(c) for c in poly.all_coeffs()]
    den = sp.ilcm(*[c.q for c in coeffs])
    ints = [int(c * den) for c in coeffs]
    g = 0
    for c in ints:
        g = __import__("math").gcd(g, abs(c))
    ints = [c // g for c in ints]
    if ints[0] < 0:
        ints = [-c for c in ints]
    return {"param": param, "theta": theta, "relative_change": theta / base - 1, "poly": ints,
            "b_line": bl, "goal": float(goal)}


def shadow_prices(inp: Inputs = PAPER) -> dict:
    """d sigma*/d theta for theta in (alpha, c_M, c_P), by the envelope theorem, exactly.

    On the binding slice disc(ell, b; theta) = 0 and d disc/db = 0, so
    d ell*/d theta = -(d disc/d theta)/(d disc/d ell), and d sigma* = -d ell*/4.
    """
    sp = _sympy()
    al, cm, cp = sp.symbols("alpha c_M c_P", real=True)
    (ell, b, d), (A2, A1, A0), _den = _slice_coeffs(al, cm, cp)
    disc = sp.expand(A1 ** 2 - 4 * A0 * A2)
    opt = slice_optimum(inp)
    sub = {al: _sym_rat(inp.alpha), cm: _sym_rat(inp.c_M), cp: _sym_rat(inp.c_P),
           ell: opt["ell"], b: opt["b"]}
    dl = sp.diff(disc, ell).subs(sub)
    out = {"db_at_opt": float(sp.N(sp.diff(disc, b).subs(sub), 40))}
    for name, th in (("alpha", al), ("c_M", cm), ("c_P", cp)):
        val = sp.radsimp(sp.diff(disc, th).subs(sub) / dl / 4)
        out[name] = val
        out[name + "_float"] = float(sp.N(val, 40))
    return out


def break_even_exact(param: str, goal=XU_SANG, inp: Inputs = PAPER) -> dict:
    """The input value at which the slice optimum equals `goal`, as a root of a polynomial.

    With ell fixed to 11/3 - 4 goal, the conditions disc = 0 and d disc/db = 0 are two
    polynomial equations in (b, theta); eliminating b leaves one polynomial in theta, whose
    real root nearest the paper's value (on the improving side) is returned and then
    confirmed by recomputing the slice optimum at a rational approximation.
    """
    sp = _sympy()
    th = sp.Symbol("theta", real=True)
    vals = {"alpha": _sym_rat(inp.alpha), "c_M": _sym_rat(inp.c_M), "c_P": _sym_rat(inp.c_P)}
    vals[param] = th
    (ell, b, d), (A2, A1, A0), _den = _slice_coeffs(vals["alpha"], vals["c_M"], vals["c_P"])
    disc = sp.expand(A1 ** 2 - 4 * A0 * A2)
    ell_goal = sp.Rational(11, 3) - 4 * _sym_rat(goal)
    dg = sp.expand(disc.subs(ell, ell_goal))
    bsol = sp.solve(sp.diff(dg, b), b)
    assert len(bsol) == 1
    eq = sp.numer(sp.together(sp.expand(dg.subs(b, bsol[0]))))
    poly = sp.Poly(sp.expand(eq), th)
    base = Fr(getattr(inp, param))
    improving = (lambda v: v < base) if param == "alpha" else (lambda v: v > base)
    real = []
    for fac, _m in sp.factor_list(poly.as_expr())[1]:
        pf = sp.Poly(fac, th)
        if pf.degree() < 1:
            continue
        for (lo, hi), _mult in pf.intervals(eps=sp.Rational(1, 10**30)):
            mid = (Fr(int(sp.numer(lo)), int(sp.denom(lo))) + Fr(int(sp.numer(hi)), int(sp.denom(hi)))) / 2
            if improving(mid) and 0 < mid < 1:
                real.append((abs(mid - base), mid, pf.degree()))
    real.sort()
    theta_be = float(real[0][1])
    moved = replace(inp, **{param: Fr(theta_be).limit_denominator(10**12)})
    check = sigma_slice_float(moved)
    # the closed form is exact only while Lemma marked's second condition stays slack
    return {"param": param, "theta": theta_be, "relative_change": theta_be / base - 1,
            "degree": poly.degree(), "check_sigma": check, "goal": float(goal),
            "marked_second_slack": marked_second_slack(moved)}


def sigma_slice_float(inp: Inputs, tied=False, lam=1) -> float:
    return float(slice_optimum(inp, tied=tied, lam=lam)["sigma_float"])


# ---------------------------------------------- exact LP lower bound and exact upper bound

def _affine_in_geometry(delta, x, inp):
    """-E_* at fixed (delta, x) on M + ell = 1 as c + c_l ell + c_b b (exact)."""
    f = lambda l_, b_: neg_e_star(delta, x, l_, 1 - l_, b_, inp)  # noqa: E731
    base = f(Fr(0), Fr(0))
    return base, f(Fr(1), Fr(0)) - base, f(Fr(0), Fr(1)) - base


def lp_lower_bound(inp: Inputs, deltas, x=HALF, gram=False) -> dict:
    """Exact lower bound on the target: max ell s.t. -E_*(delta_i, x) >= 0, b >= 0 (rational LP).

    Each constraint is affine in (ell, b) on M + ell = 1, which is optimal (hunt #134's
    constant-target slope 1 + delta(1/2 - x) > 0, an input-free identity), so this is a
    two-variable LP solved by vertex enumeration in exact rationals.  A geometry feasible
    for every (delta, x) satisfies these finitely many constraints, so sigma_LP <= sigma_min.
    """
    cons = [_affine_in_geometry(dl, x, inp) for dl in deltas]
    cons.append((Fr(0), Fr(0), Fr(1)))  # b >= 0
    if gram:  # b <= 3(1 - 3 ell)/8
        cons.append((Fr(3, 8), Fr(-9, 8), Fr(-1)))
    best = None
    for (c1, l1, b1), (c2, l2, b2) in itertools.combinations(cons, 2):
        det = l1 * b2 - l2 * b1
        if det == 0:
            continue
        ell = (-c1 * b2 + c2 * b1) / det
        b = (-l1 * c2 + l2 * c1) / det
        if all(c + cl * ell + cb * b >= 0 for c, cl, cb in cons):
            if best is None or ell > best[0]:
                best = (ell, b)
    assert best is not None
    ell, b = best
    return {"ell": ell, "b": b, "sigma": Fr(11, 12) - ell / 4}


def _mul2(p, q):
    out = {}
    for (i1, j1), v1 in p.items():
        for (i2, j2), v2 in q.items():
            k = (i1 + i2, j1 + j2)
            out[k] = out.get(k, Fr(0)) + v1 * v2
    return {k: v for k, v in out.items() if v != 0}


def _add2(*ps):
    out = {}
    for p in ps:
        for k, v in p.items():
            out[k] = out.get(k, Fr(0)) + v
    return {k: v for k, v in out.items() if v != 0}


def _scale2(p, c):
    return {k: v * c for k, v in p.items() if v * c != 0}


def _jpx_polynomials(inp: Inputs):
    one, X, Dl = {(0, 0): Fr(1)}, {(0, 1): Fr(1)}, {(1, 0): Fr(1)}
    Dx = _add2(_scale2(one, Fr(3)), _scale2(X, -2 * inp.c_M - 4 * inp.c_P))
    Px = _mul2(_add2(one, _scale2(X, -2 * inp.c_M)), _add2(_scale2(one, Fr(2)), _scale2(X, -4 * inp.c_P)))
    a_minus_d = _add2(_scale2(one, inp.alpha), _scale2(Dl, Fr(-1)))
    J = _add2(_mul2(a_minus_d, Dx), _mul2(Dl, Px))
    return one, X, Dl, Px, a_minus_d, J


def j_polynomial(inp: Inputs) -> dict:
    """J(delta, x) = (alpha - delta) D_x + delta P_x as an exact polynomial."""
    return _jpx_polynomials(inp)[-1]


def endpoint_polynomial(inp: Inputs, ell, M, b) -> dict:
    """N(delta, x) = J (-E_*) as an exact polynomial {(i, j): coeff of delta^i x^j}, delta <= alpha."""
    one, X, Dl, Px, a_minus_d, J = _jpx_polynomials(inp)
    lin = _add2(_scale2(one, -c0(ell, M, b)), _scale2(Dl, (ell + b) / 2), _scale2(_mul2(X, Dl), -ell))
    K_num = _mul2(_mul2(a_minus_d, Dl), Px)
    return _add2(_mul2(J, lin), _scale2(K_num, -h_of(ell, M, b) / 2))


def eval2(p, delta, x):
    return sum(v * delta ** i * x ** j for (i, j), v in p.items())


def _to_unit_box(p, d0, d1, x0, x1):
    """Coefficients of p(d0 + (d1 - d0) s, x0 + (x1 - x0) t) in (s, t)."""
    Ld, Lx = d1 - d0, x1 - x0
    out = {}
    for (i, j), v in p.items():
        for k in range(i + 1):
            ck = comb(i, k) * d0 ** (i - k) * Ld ** k
            if ck == 0:
                continue
            for m in range(j + 1):
                cm = comb(j, m) * x0 ** (j - m) * Lx ** m
                if cm:
                    out[(k, m)] = out.get((k, m), Fr(0)) + v * ck * cm
    return out


def _bernstein_min(p, n, m):
    """Smallest Bernstein coefficient of p (bidegree <= (n, m)) on [0, 1]^2."""
    best = None
    for P_ in range(n + 1):
        for Q_ in range(m + 1):
            val = Fr(0)
            for (k, l_), v in p.items():
                if k <= P_ and l_ <= Q_:
                    val += Fr(comb(P_, k), comb(n, k)) * Fr(comb(Q_, l_), comb(m, l_)) * v
            best = val if best is None or val < best else best
    return best


def bernstein_positive(p, box, max_boxes=400000) -> dict:
    """Exact check that p > 0 on a box: Bernstein coefficients with bisection, all rational.

    A box whose Bernstein coefficients are all positive carries p > 0; a corner with
    p <= 0 refutes positivity; otherwise the longer side is halved.
    """
    n = max((i for i, _ in p), default=0)
    m = max((j for _, j in p), default=0)
    stack, boxes, worst = [box], 0, None
    while stack:
        d0, d1, x0, x1 = stack.pop()
        boxes += 1
        if boxes > max_boxes:
            return {"positive": False, "boxes": boxes, "reason": "box budget exhausted"}
        bmin = _bernstein_min(_to_unit_box(p, d0, d1, x0, x1), n, m)
        if bmin > 0:
            worst = bmin if worst is None or bmin < worst else worst
            continue
        for (dd, xx) in ((d0, x0), (d1, x0), (d0, x1), (d1, x1)):
            if eval2(p, dd, xx) <= 0:
                return {"positive": False, "boxes": boxes, "reason": f"p({dd}, {xx}) <= 0"}
        if d1 - d0 >= x1 - x0:
            dm = (d0 + d1) / 2
            stack += [(d0, dm, x0, x1), (dm, d1, x0, x1)]
        else:
            xm = (x0 + x1) / 2
            stack += [(d0, d1, x0, xm), (d0, d1, xm, x1)]
    return {"positive": True, "boxes": boxes, "min_bernstein": worst}


def floor_value(ell, M, b, delta0=DELTA0):
    """C_0 + (1 + ell - M/2) delta_0: E(h) of the floor bin with R = 1 (line 15847, general form).

    At the paper's geometry 1 + ell - M/2 = 3/4 and this is the printed -1/48 + 3/200 = -7/1200.
    On M + ell = 1 and b = 0 it vanishes at ell = 3/16, which is 167/192 (FOLLOWUPS.md X8).
    """
    return c0(ell, M, b) + (1 + ell - M / 2) * delta0


def side_conditions(ell, M, b, inp: Inputs = PAPER, delta0=DELTA0) -> dict:
    """The other inequalities of the assembly at a geometry, exactly (True means satisfied).

    floor      C_0 + (1 + ell - M/2) delta_0 <= 0 with R = 1 (line 15847, general form)
    floor_lim  C_0 <= 0 (the floor pushed to 1/2)
    d_le_half  E(1/2) < 0 with R = 76/75 - 2 delta/3, q = delta/2, delta in [1/50, 5/6]
               (lines 16151 to 16160)
    dual       M + ell <= 1 (line 8246, hunt #134)
    low_total  M >= (1 + 3 ell)/2: only the unrescaled summand lossless (inferred, #134)
    low_paper  M - 2 ell >= 1/2: every summand lossless (the paper's reading; forces 7/8)
    gram       b <= 3(M - 2 ell)/8 (Prop. probe-gram at d = ell, hunt #134)
    supply     ell/h > the largest selected capacity (inverse at r_*(1), plain at m = 1/3)
    small      h(17/50 - 1/6) - l_y/2 + 2/100 < 0 (line 15885)
    b_nonneg   b >= 0, the Gram hypothesis P_a = Y'^2/Q >= 1 (line 8345; P_a = Z^b, line 8588)
    marked_second  Lemma marked's second condition at every inverse row (`marked_second_slack`)
    """
    h = h_of(ell, M, b)
    l_y = (M + b) / 2
    # D_x vanishes at x = 1/2 only for degenerate inputs such as c_M = c_P = 1; skip such an end
    cap_inv = max(min(inp.c_M * (1 - r_cross(x, Fr(1), inp)),
                      inp.c_M2 * (Fr(3, 2) - r_cross(x, Fr(1), inp)))
                  for x in (Fr(0), HALF) if d_x(x, inp) > 0)
    cap_plain = inp.c_P * (1 - 2 * Fr(1, 3))
    return {
        "floor": floor_value(ell, M, b, delta0) <= 0,
        "floor_lim": c0(ell, M, b) <= 0,
        "d_le_half": e_half_max(ell, M, b) < 0,
        "dual": M + ell <= 1,
        "low_total": M >= (1 + 3 * ell) / 2,
        "low_paper": M - 2 * ell >= HALF,
        "gram": b <= Fr(3, 8) * (M - 2 * ell),
        "supply": ell / h > max(cap_inv, cap_plain),
        "small": h * (Fr(17, 50) - Fr(1, 6)) - l_y / 2 + Fr(2, 100) < 0,
        "b_nonneg": b >= 0,
        "marked_second": marked_second_slack(inp),
    }


def geometry_feasible_exact(inp: Inputs, ell, b, M=None, delta_max=Fr(5, 6)) -> dict:
    """Exact check that -E_*(delta, x) > 0 on (0, delta_max] x [0, 1/2] at a rational geometry.

    For delta <= alpha the sign of -E_* is that of N = J (-E_*), J > 0, and N is checked by
    Bernstein subdivision on [0, alpha] x [0, 1/2] (delta = 0 is the floor limit).  For
    alpha < delta <= delta_max, R_* = 1 - delta and -E_* is affine in delta and in x.
    """
    M = 1 - ell if M is None else M
    top = min(inp.alpha, delta_max)
    if top > 0:
        res = bernstein_positive(endpoint_polynomial(inp, ell, M, b), (Fr(0), top, Fr(0), HALF))
    else:  # alpha = 0: no excess anywhere, only the bilinear tail below decides
        res = {"positive": True, "boxes": 0, "min_bernstein": None}
    res["J_positive"] = min(d_x(x, inp) for x in (Fr(0), HALF)) > 0 and \
        min(p_x(x, inp) for x in (Fr(0), HALF)) > 0
    if inp.alpha < delta_max:
        # R_* = 1 - delta there, so -E_* = -C_0 + delta(ell + b)/2 - ell x delta is bilinear in
        # (delta, x) and its corners decide; at alpha = 0 the corner delta = 0 is the floor limit
        res["tail_ok"] = min(neg_e_star(dl, x, ell, M, b, inp)
                             for dl in (inp.alpha, delta_max) for x in (Fr(0), HALF)) > 0
    else:
        res["tail_ok"] = True
    res["sigma"] = target(ell, M, b)
    res["feasible"] = res["positive"] and res["J_positive"] and res["tail_ok"]
    return res


def tied_capacity(sigma) -> Fr:
    """c_P = 1/(6 kappa_0) with kappa_0 = 2 sigma - 1 (the plain capacity at the target)."""
    return 1 / (6 * (2 * sigma - 1))


def bracket(inp: Inputs = PAPER, tied=False, shrink=Fr(1, 10**8)) -> dict:
    """sigma_LP <= sigma_min <= sigma_up, both exact rationals, around the slice optimum.

    Lower: the rational LP on three delta points around the slice optimum's double root.
    With tied=True the plain capacity is tied to the target; the LP then uses
    c_P = tied_capacity(s_k) for a valid lower bound s_k, starting from 13/15 (no count can
    beat the floor corner) and iterating, since a larger c_P only helps (dK/dc_P <= 0).
    Upper: a rational geometry just inside the slice optimum, checked over the whole box.
    """
    opt = slice_optimum(inp, tied=tied)
    dv = Fr(str(opt["delta_v"])).limit_denominator(10**9)
    deltas = [dv - Fr(1, 400), dv, dv + Fr(1, 400)]
    if tied:
        s_k = Fr(13, 15)
        for _ in range(4):
            lb = lp_lower_bound(replace(inp, c_P=tied_capacity(s_k)), deltas)
            s_k = lb["sigma"]
    else:
        lb = lp_lower_bound(inp, deltas)
    ell_star = Fr(str(opt["ell"].evalf(45))).limit_denominator(10**20)
    ell_up = ell_star - shrink
    b_up = Fr(str(opt["b"].evalf(45))).limit_denominator(10**12)
    inp_up = replace(inp, c_P=tied_capacity(Fr(11, 12) - ell_up / 4)) if tied else inp
    feas = geometry_feasible_exact(inp_up, ell_up, b_up)
    return {"sigma_lp": lb["sigma"], "lp": lb, "sigma_star": opt["sigma"],
            "sigma_star_float": opt["sigma_float"], "sigma_up": feas["sigma"], "ell_up": ell_up,
            "b_up": b_up, "feasibility": feas, "opt": opt,
            "side": side_conditions(ell_up, 1 - ell_up, b_up, inp_up)}


# ------------------------------------- the general evaluator with supply caps (measured)

def _capped_counts(delta, x, inp: Inputs, supply, second=True):
    """The marked count A(r) and plain count S(m) with every capacity capped (numpy).

    z_M(r) = min(c_M (1 - r), c_M2 (3/2 - r), s) (the c_M2 term only with second=True) and
    z_P(m) = min(c_P (1 - 2m), s), s = ell/h the slot supply.  Returns A, S and the
    r-breakpoints of A (the pairwise crossings of its three caps).
    """
    import numpy as np
    cm, cp, s = float(inp.c_M), float(inp.c_P), float(supply)
    c2 = float(inp.c_M2) if second else None

    def zM(r):
        z = np.minimum(cm * (1 - r), s)
        if c2 is not None:
            z = np.minimum(z, c2 * (1.5 - r))
        return np.maximum(z, 0.0)

    def A(r):
        return 1 - delta * r - 2 * x * delta * zM(r)

    def S(m):
        return 1 - 2 * delta * m - 2 * x * delta * np.minimum(cp * np.maximum(1 - 2 * m, 0), s)

    breaks = []
    if cm > 0:
        breaks.append(1 - s / cm)
    if c2 is not None and c2 > 0:
        breaks.append(1.5 - s / c2)
        if cm != c2:
            breaks.append((cm - 1.5 * c2) / (cm - c2))
    return A, S, breaks


def rshort_capped(delta, x, t, inp: Inputs, supply, second=True):
    """The worst short row at one detector length t: max over r in [t - 1/2, 1] of min(A(r), S(t - r)).

    A and S(t - r) are piecewise affine in r and every breakpoint is listed, so on each piece
    min(A, S) is concave and its maximum sits at a breakpoint or at the crossing: the value is
    exact up to float rounding, with no monotonicity assumed (A is not monotone once
    2 x c_M > 1, as at c_M = 10).
    """
    import numpy as np
    delta = np.asarray(delta, dtype=float)
    x = np.asarray(x, dtype=float)
    A, S, breaks = _capped_counts(delta, x, inp, supply, second)
    t = np.broadcast_to(np.asarray(t, dtype=float), np.broadcast(delta, x).shape)
    shape = t.shape
    lo, hi = t - 0.5, np.ones(shape)
    cand = [lo, hi] + [np.broadcast_to(np.asarray(bv, dtype=float), shape) for bv in breaks]
    cp, s = float(inp.c_P), float(supply)
    if cp > 0:
        cand.append(t - (1 - s / cp) / 2)
    pts = np.sort(np.stack([np.clip(c, lo, hi) for c in cand]), axis=0)
    Av, Sv = A(pts), S(t - pts)
    F = Av - Sv
    best = np.max(np.minimum(Av, Sv), axis=0)
    for k in range(pts.shape[0] - 1):
        seg = ((F[k] > 0) & (F[k + 1] < 0)) | ((F[k] < 0) & (F[k + 1] > 0))
        denom = np.where(seg, F[k] - F[k + 1], 1.0)
        rc = pts[k] + F[k] * (pts[k + 1] - pts[k]) / denom
        best = np.where(seg, np.maximum(best, A(rc)), best)
    return best


def r_star_capped(delta, x, inp: Inputs, supply, iters=55, second=True):
    """The bin count with every selected capacity capped (numpy, measured).

    Short rows (r < 1) count `rshort_capped`; long rows (r in [1, t]) count
    min(1 - alpha + (alpha - delta) r, S(t - r)), worst at r = t.  The marked capacity is
    capped by the supply s = ell/h and, with second=True, by Lemma marked's second condition
    c_M2 (3/2 - r); the plain one by the supply.  R_short decreases in t and the long count
    increases, so the best single t per bin is found by bisection.  With s large and the
    second condition slack this reproduces the closed form r_star.
    """
    import numpy as np
    delta = np.asarray(delta, dtype=float)
    x = np.asarray(x, dtype=float)
    al = float(inp.alpha)
    _A, S, _b = _capped_counts(delta, x, inp, supply, second)

    def rshort(t):
        return rshort_capped(delta, x, t, inp, supply, second)

    def lb(t):
        return np.minimum(1 - al + (al - delta) * t, S(np.zeros_like(delta)))

    a_ = np.ones_like(delta)
    b_ = np.full_like(delta, 1.5)
    g_lo = rshort(a_) - lb(a_)
    for _ in range(iters):
        mid = (a_ + b_) / 2
        gm = rshort(mid) - lb(mid)
        a_ = np.where(gm > 0, mid, a_)
        b_ = np.where(gm > 0, b_, mid)
    tc = (a_ + b_) / 2
    val = np.maximum(rshort(tc), lb(tc))
    val = np.where(g_lo <= 0, np.maximum(rshort(np.ones_like(delta)), lb(np.ones_like(delta))), val)
    return np.where(delta >= al, 1 - delta, val)


def _refined_min(neg, ds, xs):
    """Grid minimum of a smooth array neg[delta, x], refined by parabolas through grid neighbours."""
    import numpy as np
    vals = []
    for j in range(neg.shape[1]):
        col = neg[:, j]
        i = int(np.argmin(col))
        v = col[i]
        if 0 < i < len(col) - 1:
            y0, y1, y2 = col[i - 1], col[i], col[i + 1]
            den = y0 - 2 * y1 + y2
            if den > 0:
                v = y1 - (y0 - y2) ** 2 / (8 * den)
        vals.append(v)
    vals = np.array(vals)
    j = int(np.argmin(vals))
    v = vals[j]
    if 0 < j < len(vals) - 1:
        y0, y1, y2 = vals[j - 1], vals[j], vals[j + 1]
        den = y0 - 2 * y1 + y2
        if den > 0:
            v = y1 - (y0 - y2) ** 2 / (8 * den)
    return v


def _d_half_ok_float(ell, b, alpha, mode, grid):
    """The rows d <= 1/2 at one geometry on M + ell = 1, in floats (see `e_half_R`)."""
    import numpy as np
    if mode is None:
        return True

    def eh(d, R):
        a = (1 + d) / 2
        h = 0.5 + 1.5 * ell + b / 2
        l_y = (1 - ell + b) / 2
        sig = 11 / 12 - ell / 4
        return a - sig + h * (17 / 50 - 1 / 6) - a * l_y - (1 - a) * ell + 0.5 * (R + d / 2 - 17 / 50)
    if mode == "paper":
        return max(eh(0.02, 76 / 75 - 0.02 * 2 / 3), eh(5 / 6, 76 / 75 - 5 / 9)) <= 0
    R = np.where(grid < alpha, 1 - grid + np.maximum(alpha - grid, 0) * grid
                 / np.maximum(3 * alpha - grid, 1e-300), 1 - grid)
    return max(eh(0.02, 1.0), float(np.max(eh(grid, R)))) <= 0


def sigma_general(inp: Inputs, cap_supply=True, n_delta=120, n_x=21, s_step=0.002,
                  b_grid=None, iters=34, low="total", delta0=float(DELTA0), second=True,
                  d_half="paper", golden=24) -> dict:
    """Smallest target over geometry on M + ell = 1, with capacity caps (measured, float grids).

    Constraints: the parabola-refined minimum over the (delta, x) grid of -E_* >= 0 with the
    capped R_*; the floor C_0 + (1/2 + 3 ell/2) delta0 <= 0, by default the paper's
    delta_0 = 1/50 (delta0 = 0 pushes the floor to 1/2 and leaves C_0 <= 0); the rows d <= 1/2,
    counted as the paper counts them (d_half='paper': t = 1, R = 76/75 - 2 delta/3), at the
    balancing t without primes (d_half='balanced', `r_noslot_balanced`), or left out
    (d_half=None, which is what the first version of this lane did); the Gram condition
    b <= 3(1 - 3 ell)/8, b >= 0 and the small rows (line 15885); the low side ell <= 1/5
    (total) or 1/6 (paper).  The marked capacity is capped by Lemma marked's second condition
    unless second=False, and both capacities by the supply unless cap_supply=False.  R_*
    depends on the geometry only through the supply s = ell/h and is nonincreasing in s, so it
    is tabulated on an s-grid and read at the grid point below s (the conservative side).
    The b optimum is refined by `golden` steps of golden-section search from a b-grid that
    reaches 0.2 (24 steps leave a b-bracket below 10^-6; the first version used 12).
    """
    import numpy as np
    ds = np.linspace(0, 5 / 6, n_delta + 1)[1:]
    xs = np.linspace(0, 0.5, n_x)
    Dg, Xg = np.meshgrid(ds, xs, indexing="ij")
    ell_cap = 0.2 if low == "total" else 1 / 6
    dgrid = np.linspace(0.02, 5 / 6, 4001)
    al = float(inp.alpha)
    if cap_supply:
        s_grid = np.arange(0.10, 0.30 + 1e-12, s_step)
        table = [r_star_capped(Dg, Xg, inp, sv, second=second) for sv in s_grid]
    else:
        s_grid = np.array([0.0])
        table = [r_star_capped(Dg, Xg, inp, 1e9, second=second)]

    def R_of(s):
        k = int(np.searchsorted(s_grid, s, side="right")) - 1
        return table[max(k, 0)]

    def ell_max(b):
        def ok(ell):
            h = 0.5 + 1.5 * ell + b / 2
            if b > 3 * (1 - 3 * ell) / 8 or h * (17 / 50 - 1 / 6) - (1 - ell + b) / 4 + 0.02 >= 0:
                return False
            if not _d_half_ok_float(ell, b, al, d_half, dgrid):
                return False
            R = R_of(ell / h)
            c0v = -0.25 + 1.25 * ell + b / 6
            neg = -c0v + Dg * (ell + b) / 2 - ell * Xg * Dg - h * (R - (1 - Dg))
            return _refined_min(neg, ds, xs) >= 0 and c0v + (0.5 + 1.5 * ell) * delta0 <= 0
        lo, hi = 0.0, ell_cap
        if ok(hi):
            return hi
        for _ in range(iters):
            mid = (lo + hi) / 2
            lo, hi = (mid, hi) if ok(mid) else (lo, mid)
        return lo
    b_grid = b_grid if b_grid is not None else [k / 50 for k in range(0, 11)]
    vals = [(ell_max(b), b) for b in b_grid]
    i = max(range(len(vals)), key=lambda k: vals[k][0])
    lo_b, hi_b = b_grid[max(i - 1, 0)], b_grid[min(i + 1, len(b_grid) - 1)]
    g = (5 ** 0.5 - 1) / 2
    c_, d_ = hi_b - g * (hi_b - lo_b), lo_b + g * (hi_b - lo_b)
    fc, fd = ell_max(c_), ell_max(d_)
    for _ in range(golden):
        if fc >= fd:
            hi_b, d_, fd = d_, c_, fc
            c_ = hi_b - g * (hi_b - lo_b)
            fc = ell_max(c_)
        else:
            lo_b, c_, fc = c_, d_, fd
            d_ = lo_b + g * (hi_b - lo_b)
            fd = ell_max(d_)
    ell, b = max([vals[i], (fc, c_), (fd, d_)])
    h = 0.5 + 1.5 * ell + b / 2
    return {"ell": ell, "b": b, "sigma": 11 / 12 - ell / 4, "supply": ell / h,
            "C0": -0.25 + 1.25 * ell + b / 6}


# ------------------------------------------------------------------ enumerations

def greedy_selection(w, g, z, ascending=False):
    """The paper's slot selection (lines 15116 to 15128): whole slots of total length <= z.

    Positive amplitudes in decreasing order fill z; the one slot that would overflow is
    dropped together with everything after it.  ascending=True is a planted fault.
    """
    order = sorted((i for i in range(len(w)) if g[i] > 0), key=lambda i: (g[i], -i),
                   reverse=not ascending)
    chosen, used = [], Fr(0)
    for i in order:
        if used + w[i] > z:
            break
        chosen.append(i)
        used += w[i]
    return chosen


def enumerate_selection(fault=None) -> dict:
    """Exhaustive check of the selection inequality on small rational configurations.

    For every slot vector (lengths w_i, amplitudes g_i in [0, delta/2]) and every request
    z <= sum w_i, with q the length-weighted mean amplitude and gain = 2 sum_sel w_i g_i:
      paper    gain >= 2qz - delta max w_i                  (line 15127)
      sharper  gain >= 2q (z - max w_i)                      (2q <= delta, so it implies the paper's)
      worst    with all g_i equal to q the gain is at most 2qz: the mean q is the exact worst case.
    """
    ws = [Fr(1, 12), Fr(1, 6), Fr(1, 4)]
    n_cases = paper_fail = sharp_fail = uniform = uniform_over = 0
    for delta in (Fr(1, 5), Fr(2, 5), Fr(5, 6)):
        gs = [delta / 2 * Fr(k, 4) for k in range(0, 5)]
        for n in (1, 2, 3):
            for w in itertools.product(ws, repeat=n):
                total = sum(w)
                zs = [Fr(k, 24) for k in range(0, int(total * 24) + 1)]
                for g in itertools.product(gs, repeat=n):
                    q = sum(wi * gi for wi, gi in zip(w, g)) / total
                    for z in zs:
                        sel = greedy_selection(w, g, z, ascending=(fault == "ascending"))
                        gain = 2 * sum(w[i] * g[i] for i in sel)
                        n_cases += 1
                        paper_fail += gain < 2 * q * z - delta * max(w)
                        sharp_fail += gain < 2 * q * (z - max(w))
                        if len(set(g)) == 1 and g[0] > 0:
                            uniform += 1
                            uniform_over += gain > 2 * q * z
    return {"cases": n_cases, "paper_fail": paper_fail, "sharp_fail": sharp_fail,
            "uniform_cases": uniform, "uniform_above_2qz": uniform_over}


def adversary_multi_t(delta, x, N_g=12, inp: Inputs = PAPER, fault=None) -> dict:
    """Use the detector at every t at once: what is the worst row type then? (exhaustive)

    A row type is a set A of inverse witness lengths (grid on [1/2, 3/2]) and a plain length
    mbar.  Covering, from Prop. detector-witness at every grid t in [1, 3/2]: some r in A has
    t - mbar <= r <= t.  The type's count is its best available bound,
    min(S(mbar), min_{r in A} f(r)), f the marked count for r < 1 and the amplified one for
    r >= 1.  The adversary maximizes this over all covering types.  fault='no_cover' drops
    the covering constraint, a planted fault: the adversary then beats every bound.
    """
    grid_r = [Fr(1, 2) + Fr(k, N_g) for k in range(0, N_g + 1)]
    grid_t = [Fr(1) + Fr(k, N_g) for k in range(0, N_g // 2 + 1)]
    grid_m = [Fr(k, N_g) for k in range(0, N_g // 2 + 1)]
    fvals = [count_marked(delta, x, r, inp) if r < 1 else count_long(delta, r, inp) for r in grid_r]
    best = None
    for mbar in grid_m:
        s_m = count_plain(delta, x, mbar, inp)
        covers = [sum(1 << i for i, r in enumerate(grid_r) if t - mbar <= r <= t) for t in grid_t]
        for mask in range(1, 1 << len(grid_r)):
            if fault != "no_cover" and not all(mask & c for c in covers):
                continue
            val = min([s_m] + [fvals[i] for i in range(len(grid_r)) if mask >> i & 1])
            if best is None or val > best[0]:
                best = (val, mbar, mask)
    paper_grid = min(max(r_short(delta, x, t, inp), l_count(delta, t, inp)) for t in grid_t)
    A = tuple(r for i, r in enumerate(grid_r) if best[2] >> i & 1)
    return {"adversary": best[0], "mbar": best[1], "A": A, "paper_grid_bound": paper_grid,
            "R_star": r_star(delta, x, inp), "types_checked": len(grid_m) * ((1 << len(grid_r)) - 1)}


def adversary_exact(delta, x, inp: Inputs = PAPER) -> dict:
    """The worst row type for the detector used at every t in [1, 3/2] at once, exactly.

    Upper bound (derived): for any covering type, take t = t_* (the balancing t); some
    r in A has t_* - mbar <= r <= t_*.  If r >= 1 its count is at most L(t_*) = R_*; if r < 1,
    min(S(mbar), A_I(r)) <= min(S(t_* - r), A_I(r)) <= R_short(t_*) = R_*.  Attainment: the
    type A = {r_*(t_*), t_*}, mbar = t_* - r_*(t_*) covers every t in [1, 3/2] (element a covers
    [a, a + mbar]) and its count is exactly R_*.  So the paper's single t loses nothing.
    """
    ts = t_balance(delta, x, inp)
    rp = r_cross(x, ts, inp)
    mbar = ts - rp
    A = [rp, ts]
    while A[-1] + mbar < Fr(3, 2):
        A.append(A[-1] + mbar)
    # element a covers t in [a, a + mbar]; the union must contain [1, 3/2]
    reach, covered = Fr(1), rp <= 1 <= rp + mbar and 0 < mbar <= HALF
    for a in A:
        covered = covered and a <= reach
        reach = max(reach, a + mbar)
    covered = covered and reach >= Fr(3, 2)
    vals = [count_plain(delta, x, mbar, inp)] + [
        count_marked(delta, x, a, inp) if a < 1 else count_long(delta, a, inp) for a in A]
    return {"t_star": ts, "r_prime": rp, "mbar": mbar, "A": A, "covers": covered, "value": min(vals),
            "R_star": r_star(delta, x, inp)}


def beyond_capacity_signs() -> dict:
    """Slots beyond a capacity, paid by a pointwise bound, never help (exact grid).

    plain: a slot of length dz beyond z_P, bounded pointwise, costs kappa dz in the moment
    exponent (Eq. 3.5 at line 12873, the exchange rate at line 14259) and gains 2q dz in the
    spike; marked: the prime bound |Q_i| << P_i^{a - 1/2} (line 15021) costs delta dz.  With
    q <= delta/2 and delta <= kappa both nets kappa - 2q and delta - 2q are >= 0.
    """
    worst_plain = worst_marked = None
    n = 0
    for kd in range(1, 21):
        delta = Fr(5, 6) * Fr(kd, 20)
        for kq in range(0, 11):
            q = delta / 2 * Fr(kq, 10)
            for kk in range(0, 5):
                kappa = max(delta, Fr(3, 4) + Fr(kk, 48))
                n += 1
                wp, wm = kappa - 2 * q, delta - 2 * q
                worst_plain = wp if worst_plain is None or wp < worst_plain else worst_plain
                worst_marked = wm if worst_marked is None or wm < worst_marked else worst_marked
    return {"cases": n, "min_plain_net": worst_plain, "min_marked_net": worst_marked}


def one_copy_vs_two() -> dict:
    """Lemma plain with one copy of S_m (capacity (1 - m)/(6 kappa)) against two (exact grid).

    one minus two = m delta (1 - x/(3 kappa)) > 0 for m > 0: the two-copy count is smaller.
    """
    worst = None
    n = 0
    kappa = Fr(3, 4)
    for kd in range(1, 21):
        delta = Fr(5, 6) * Fr(kd, 20)
        for kx in range(0, 11):
            x = Fr(kx, 20)
            for km in range(1, 11):
                m = Fr(km, 20)
                two = 1 - 2 * delta * m - 2 * x * delta * (1 - 2 * m) / (6 * kappa)
                one = 1 - delta * m - 2 * x * delta * (1 - m) / (6 * kappa)
                assert one - two == m * delta * (1 - x / (3 * kappa))
                n += 1
                worst = one - two if worst is None or one - two < worst else worst
    return {"cases": n, "min_one_minus_two": worst}


def conductor_strata() -> dict:
    """Rows with powerful part of norm U^o: count <= U^{1 - o/2}, conductor <= U^{1 - o/2} (exact grid).

    The row count of the stratum is at most min(1 - o/2, R) and its per-row factor is
    U^{(1 - o/2) delta/2} instead of U^{delta/2} (line 4361: conductor power Q_psi^{a - 1/2}).
    The stratum exponent min(1 - o/2, R) + (1 - o/2) delta/2 is largest at o = 0, where it is
    the paper's R + delta/2, so stratifying by the powerful part buys nothing.
    """
    worst_gap = None
    n = 0
    for kd in range(1, 21):
        delta = Fr(5, 6) * Fr(kd, 20)
        for kx in (0, 5, 10):
            x = Fr(kx, 20)
            R = r_star(delta, x)
            for ko in range(0, 21):
                o = Fr(ko, 20)
                val = min(1 - o / 2, R) + (1 - o / 2) * delta / 2
                gap = (R + delta / 2) - val
                n += 1
                worst_gap = gap if worst_gap is None or gap < worst_gap else worst_gap
    return {"cases": n, "min_gap": worst_gap}


# ----- Z[omega] arithmetic for the Gram and amplification enumerations

def zmul(x, y):
    """(a + b w)(c + d w) with w^2 = -1 - w."""
    a, b = x
    c, d = y
    return (a * c - b * d, a * d + b * c - b * d)


def znorm(x):
    a, b = x
    return a * a - a * b + b * b


def zprimary(x):
    """Primary in the paper's convention: congruent to 1 modulo 3."""
    a, b = x
    return a % 3 == 1 and b % 3 == 0


def _is_prime(n):
    if n < 2:
        return False
    return all(n % p for p in range(2, isqrt(n) + 1))


def split_primes(bound):
    """Primary primes of Z[omega] of rational prime norm p = 1 mod 3, p <= bound."""
    R = isqrt(4 * bound) + 2
    out = [(a, b) for a in range(-R, R + 1) for b in range(-R, R + 1)
           if znorm((a, b)) <= bound and znorm((a, b)) % 3 == 1 and _is_prime(znorm((a, b)))
           and zprimary((a, b))]
    return sorted(out, key=lambda z: (znorm(z), z))


def _omega_image(pi):
    c, d = pi
    p = znorm(pi)
    w = (-c * pow(d, -1, p)) % p
    assert (w * w + w + 1) % p == 0
    return w


ZETA6_POWERS = [(1, 0), (1, 1), (0, 1), (-1, 0), (-1, -1), (0, -1)]  # (1 + w)^k in Z[w]


def sextic_symbol(x, pi):
    """(x/pi)_6 as k mod 6 with value (1 + w)^k, from x^{(p-1)/6} mod pi; None if pi | x."""
    p = znorm(pi)
    w = _omega_image(pi)
    t = pow((x[0] + x[1] * w) % p, (p - 1) // 6, p)
    if t == 0:
        return None
    for k, u in enumerate(ZETA6_POWERS):
        if (u[0] + u[1] * w) % p == t:
            return k
    raise RuntimeError("no sixth root of unity matched")


def reciprocity_factor_table(bound=400, n_pi=6) -> dict:
    """(pi0/m)_6 / (m/pi0)_6 over primary primes m: is it a function of m mod 4? (exhaustive)

    This is the step that turns chi_m(pi0), a function of the modulus m, into the residue
    character (m/pi0)_6 times a factor that depends only on m modulo 4, a fixed 2-power
    modulus of the kind the ray group T absorbs.
    """
    P = split_primes(bound)
    rows = []
    for pi0 in P[:n_pi]:
        table, conflicts = {}, 0
        for m in P:
            if m == pi0:
                continue
            k = (sextic_symbol(pi0, m) - sextic_symbol(m, pi0)) % 6
            key = (m[0] % 4, m[1] % 4)
            conflicts += key in table and table[key] != k
            table.setdefault(key, k)
        rows.append({"pi0": pi0, "norm": znorm(pi0), "classes": len(table), "conflicts": conflicts,
                     "values": sorted(set(table.values()))})
    return {"primes": len(P), "rows": rows, "all_ok": all(r["conflicts"] == 0 for r in rows)}


Z6_BASIS = [(1, 0), (0, 1), (-1, 1), (-1, 0), (0, -1), (1, -1)]  # zeta^r = a + b zeta, zeta^2 = zeta - 1


def _primitive_root(p):
    qs = [q for q in range(2, p) if (p - 1) % q == 0 and _is_prime(q)]
    return next(g for g in range(2, p) if all(pow(g, (p - 1) // q, p) != 1 for q in qs))


def _logs(p):
    g = _primitive_root(p)
    return {pow(g, k, p): k for k in range(p - 1)}


def char_power_sum(p, c):
    """Sum over y in F_p^x of psi(y)^c, psi(g^k) = zeta_6^k, exactly as a + b zeta_6."""
    logs = _logs(p)
    a = b = 0
    for y in range(1, p):
        da, db = Z6_BASIS[(c * logs[y]) % 6]
        a += da
        b += db
    return a, b


def exceptional_gram_means(p_list=(7, 13, 19, 31, 37, 43), fault=None) -> dict:
    """Complete means of lambda_p * kappa_e over (O/pi)^x = F_p^x, for every choice of xi_p.

    lambda_p = psi^{1-j} is the pi-part of chi_s(b_*)/xi(s) when xi_p = psi^j (psi the sextic
    residue character), and kappa_e = psi^e is the pi-part of chi_m(k) for a frequency k with
    pi-valuation e (the identification is the reciprocity step tested above).  The
    exceptional Gram coefficient has nonzero mean iff 1 - j + e = 0 mod 6, so for every
    choice of xi one coset of frequencies keeps it.  fault='wrong_e' expects e = j.
    """
    rows = []
    for p in p_list:
        full = char_power_sum(p, 0)
        for j in range(1, 6):
            nonzero = [e for e in range(6) if char_power_sum(p, 1 - j + e) != (0, 0)]
            want = [(j - 1) % 6] if fault != "wrong_e" else [j % 6]
            rows.append({"p": p, "j": j, "nonzero_e": nonzero, "expected": want,
                         "ok": nonzero == want and full == (p - 1, 0)})
    return {"rows": rows, "all_ok": all(r["ok"] for r in rows), "count": len(rows)}


def _local_L(p, c, n1, n2, k, logs):
    """L_{p^c}(n1, n2; k) = sum over x, y mod p^c with n2 x - n1 y = k of chi(x) conj(chi(y)).

    chi = psi^c as a function of residues mod p (zero on multiples of p); exact in Z[zeta_6].
    """
    mod = p ** c

    def ex(v):
        v %= p
        return None if v == 0 else (c * logs[v]) % 6
    a = b = 0
    if n1 % p:
        inv = pow(n1, -1, mod)
        pairs = (((xx, ((n2 * xx - k) * inv) % mod)) for xx in range(mod))
    else:
        pairs = ((xx, yy) for xx in range(mod) for yy in range(mod) if (n2 * xx - n1 * yy - k) % mod == 0)
    for xx, yy in pairs:
        e1, e2 = ex(xx), ex(yy)
        if e1 is None or e2 is None:
            continue
        da, db = Z6_BASIS[(e1 - e2) % 6]
        a += da
        b += db
    return a, b


def _local_L_np(p, c, n1, n2, k, logs):
    """The same sum as `_local_L`, iterating over whichever of x, y has a unit coefficient.

    Exact integer arithmetic in numpy int64 (p^c * p^c < 2^63 for the cases used); this is
    what makes c = 6 with p dividing n1 feasible, the case the first version of this lane
    skipped because its double loop over (x, y) has p^(2c) terms.
    """
    import numpy as np
    mod = p ** c
    lg = np.full(p, -1, dtype=np.int64)
    for v, e in logs.items():
        lg[v] = e
    if n1 % p:
        xs = np.arange(mod, dtype=np.int64)
        ys = ((n2 * xs - k) % mod) * pow(n1, -1, mod) % mod
    elif n2 % p:
        ys = np.arange(mod, dtype=np.int64)
        xs = ((k + n1 * ys) % mod) * pow(n2, -1, mod) % mod
    else:
        raise ValueError("p divides both n1 and n2: outside the genuine residual locus")
    e1, e2 = lg[xs % p], lg[ys % p]
    keep = (e1 >= 0) & (e2 >= 0)
    counts = np.bincount((c * (e1[keep] - e2[keep])) % 6, minlength=6)
    a = sum(int(counts[r]) * Z6_BASIS[r][0] for r in range(6))
    b = sum(int(counts[r]) * Z6_BASIS[r][1] for r in range(6))
    return a, b


def local_formula(p, c, n1, n2, k, logs, fault=None):
    """The paper's local factor L_{p^c} (lines 7114 to 7123) as a + b zeta_6.

    p not dividing n1 n2: P^{c-1} chi_p(n1/n2)^c times P - 1 (p | k), -1 (p does not divide k,
    6 does not divide c), P - 2 (p does not divide k, 6 | c).  p dividing exactly one of n1, n2:
    P^{c-1}(P - 1) 1_{6|c} 1_{p does not divide k}.  fault='sign' drops the -1 (planted).
    """
    if n1 % p and n2 % p:
        mag = p ** (c - 1) * (p - 1 if k % p == 0 else (p - 2 if c % 6 == 0 else 1))
        sign = -1 if (k % p and c % 6) else 1
        if fault == "sign":
            sign = 1
        r0 = (c * logs[(n1 * pow(n2, -1, p)) % p]) % 6
        return sign * mag * Z6_BASIS[r0][0], sign * mag * Z6_BASIS[r0][1]
    return (p ** (c - 1) * (p - 1) if (c % 6 == 0 and k % p) else 0), 0


LOCAL_CASES = ((7, 1), (13, 1), (19, 1), (7, 2), (13, 2), (7, 6))
#: two single sums at p = 13, c = 6 (13^6 terms each), one in the case the first version skipped
LOCAL_EXTRA = ((13, 6, 1, 1, 1), (13, 6, 13, 1, 1))


def local_correlation_check(cases=LOCAL_CASES, extra=LOCAL_EXTRA, fault=None) -> dict:
    """Brute force L_{p^c} against the paper's local formula, with p dividing n1 or n2 included.

    For each (p, c): n1 in {1, 2, 3, p, 2p}, n2 in {1, 5, p}, pairs with p dividing both left out
    (the genuine locus has (n1, n2) = 1), k in {0, 1, 2, p, 2p}; plus the single sums `extra`.
    Reported per (p, c):
      formula_mismatch      sums that differ from `local_formula` (expected 0)
      totient_violations    |L| > phi(p^c) = P^{c-1}(P - 1) (expected 0: for each unit x there
                            is at most one y, so this bound is the triangle inequality)
      totient_attained      sums with |L| = phi(p^c)
      withdrawn_violations  sums breaking the bound this lane first stated, |L| <= P^{c-1}(P - 1)
                            if p | k, else P^{c-1}(P - 2) if 6 | c, else P^{c-1}; the bound is
                            false exactly when p divides one of n1, n2, 6 | c and p does not
                            divide k (expected > 0 at c = 6, and only in that case)
      withdrawn_outside     such violations outside that case (expected 0)
    """
    rows = []
    jobs = []
    for p, c in cases:
        for n1 in (1, 2, 3, p, 2 * p):
            for n2 in (1, 5, p):
                if n1 % p == 0 and n2 % p == 0:
                    continue
                for k in (0, 1, 2, p, 2 * p):
                    jobs.append((p, c, n1, n2, k))
    jobs += list(extra)
    logs_cache = {}
    for p, c, n1, n2, k in jobs:
        logs = logs_cache.setdefault(p, _logs(p))
        got = _local_L_np(p, c, n1, n2, k, logs)
        want = local_formula(p, c, n1, n2, k, logs, fault)
        mag2 = got[0] ** 2 + got[0] * got[1] + got[1] ** 2
        phi = p ** (c - 1) * (p - 1)
        old = p ** (c - 1) * (p - 1 if k % p == 0 else (p - 2 if c % 6 == 0 else 1))
        one_divides = (n1 % p == 0) != (n2 % p == 0)
        special = one_divides and c % 6 == 0 and k % p != 0
        key = (p, c)
        row = next((r for r in rows if (r["p"], r["c"]) == key), None)
        if row is None:
            row = {"p": p, "c": c, "tested": 0, "formula_mismatch": 0, "totient_violations": 0,
                   "totient_attained": 0, "withdrawn_violations": 0, "withdrawn_outside": 0}
            rows.append(row)
        row["tested"] += 1
        row["formula_mismatch"] += got != want
        row["totient_violations"] += mag2 > phi ** 2
        row["totient_attained"] += mag2 == phi ** 2
        row["withdrawn_violations"] += mag2 > old ** 2
        row["withdrawn_outside"] += mag2 > old ** 2 and not special
    tot = {k: sum(r[k] for r in rows) for k in ("tested", "formula_mismatch", "totient_violations",
                                                "totient_attained", "withdrawn_violations",
                                                "withdrawn_outside")}
    return {"rows": rows, "totals": tot,
            "all_ok": tot["formula_mismatch"] == 0 and tot["totient_violations"] == 0
            and tot["withdrawn_outside"] == 0}


def _primary_elements(bound):
    """Primary elements of Z[omega] of odd norm <= bound: the ideals outside S = {2, 1 - w}."""
    R = isqrt(4 * bound) + 2
    return [(a, b) for a in range(-R, R + 1) for b in range(-R, R + 1)
            if zprimary((a, b)) and 0 < znorm((a, b)) <= bound and znorm((a, b)) % 2 == 1]


def count_primary_ball(bound) -> int:
    """#{a + b w primary, odd norm, 0 < a^2 - ab + b^2 <= bound}, counted line by line in b (exact).

    For fixed b the condition is |2a - b| <= isqrt(4 bound - 3 b^2), an interval of a; the
    congruences a = 1 mod 3, b = 0 mod 3 and (a, b) not both even are counted modulo 6.
    """
    total = 0
    bmax = isqrt(4 * bound // 3) + 1
    for b in range(-bmax, bmax + 1):
        if b % 3 or 4 * bound - 3 * b * b < 0:
            continue
        sq = isqrt(4 * bound - 3 * b * b)
        lo, hi = -((sq - b) // 2), (b + sq) // 2
        for r in range(6):
            if r % 3 != 1 or (r % 2 == 0 and b % 2 == 0):
                continue
            first = lo + ((r - lo) % 6)
            if first <= hi:
                total += (hi - first) // 6 + 1
    return total


def amplification_lift_counts(U=150, P=13) -> dict:
    """The sixth-power lift of Lemma inverse-amplification at small norms (exhaustive).

    Rows u: primary, odd norm, U/2 < N(u) <= U (all sixth-power-free, since the least norm
    of a sixth power of a prime outside S is 7^6 > U).  Lifts a: primary, odd norm, N(a) <= P.
    The map (u, a) -> u a^6 is checked injective (line 12437), the lifts are counted against
    the ideal count (line 12410), and the lifted rows are compared with the whole ball of
    norm at most H = U P^6 that the proof sums over (line 12449): the ratio ball/images is
    the factor the full count gives away, of order P^5.
    """
    rows = [u for u in _primary_elements(U) if 2 * znorm(u) > U]
    lifts = _primary_elements(P)
    images = set()
    collisions = 0
    for u in rows:
        for a in lifts:
            a6 = a
            for _ in range(5):
                a6 = zmul(a6, a)
            v = zmul(u, a6)
            collisions += v in images
            images.add(v)
    H = U * P ** 6
    ball = count_primary_ball(H)
    assert count_primary_ball(U) == len(_primary_elements(U))
    return {"rows": len(rows), "lifts_per_row": len(lifts), "images": len(images),
            "collisions": collisions, "H": H, "ball": ball,
            "ball_over_images": Fr(ball, len(images)), "P_to_5": P ** 5}


# ----------------------------------------------------------------------- the loss table

def loss_table(res: dict) -> list[dict]:
    """Every count loss located, its verdict, and the abscissa it buys."""
    sp_ = res.get("shadow", {})
    return [
        {"key": "selection", "lines": "15116-15134", "kind": "union over slots",
         "verdict": "holds, exact enumeration; buys 0: its loss already tends to 0 with the mesh",
         "buys": 0.0},
        {"key": "single_t", "lines": "15196-15210, 15962-15986", "kind": "one detector length per bin",
         "verdict": "dead: the adversary over all t at once attains R_* exactly (max-min = min-max)",
         "buys": 0.0},
        {"key": "beyond_capacity", "lines": "14259, 12873, 15021", "kind": "capacity cut",
         "verdict": "dead: extra slots paid pointwise have net exponent kappa - 2q >= 0 or delta - 2q >= 0",
         "buys": 0.0},
        {"key": "copies", "lines": "15242, 12557", "kind": "moment shape",
         "verdict": "dead: one copy of S_m counts worse by m delta (1 - x/(3 kappa))", "buys": 0.0},
        {"key": "floor", "lines": "15843-15848", "kind": "full count",
         "verdict": "no sharper count tried; slack at the paper's inputs and at the perfect-capacity "
                    "optima; binds at alpha = 0 (84031/96156 with the paper's count of the rows d <= 1/2, "
                    "167/192 with them recounted, 13/15 with the floor at 1/2)",
         "buys": 0.0},
        {"key": "conductor", "lines": "4354-4367, 15801", "kind": "worst-case row",
         "verdict": "dead: rows with large powerful part have smaller conductor but the max is at o = 0",
         "buys": 0.0},
        {"key": "gram_exceptional", "lines": "8527-8557, 8366", "kind": "trivial bound",
         "verdict": "dead: the coset of frequencies pi^{j-1} times sixth powers restores a nonzero mean",
         "buys": 0.0},
        {"key": "gram_LC", "lines": "7114-7130, 8546", "kind": "trivial bound",
         "verdict": "|L_C| <= phi(C) < q_C (exact enumeration, p | n1 included); buys 0: the C = 1 "
                    "term carries the P_a^{1/6}; the first version's sharper bound is withdrawn",
         "buys": 0.0},
        {"key": "kappa_floor", "lines": "12532, 15327", "kind": "frozen constant",
         "verdict": "matched by a public follow-up (Guo); needs Lemma plain below kappa = 3/4",
         "buys": res.get("tied_gain")},
        {"key": "d_half", "lines": "16146-16160, 15453, 12557", "kind": "one detector length for the rows d <= 1/2",
         "verdict": "holds (inferred available): the no-slot count at the balancing t, R_*(delta, 0); buys 0 at "
                    "the paper's inputs, where t = 1 is slack, but every perfect-input value needs it",
         "buys": 0.0},
        {"key": "numerator", "lines": "15799-15810", "kind": "count times the pointwise maximum",
         "verdict": "real; the bin's count multiplies the pointwise reflected numerator U^{delta/2}; an "
                    "average over the bin is the change Xu and Sang made (per FOLLOWUPS.md), not priced here",
         "buys": None},
        {"key": "amplification", "lines": "12410-12455, 15300", "kind": "full count over sparse lifts",
         "verdict": "real, no recount of it tried; priced", "buys": res.get("ideal_alpha_gain"),
         "shadow": sp_.get("alpha_float"), "break_even": res.get("be_alpha")},
        {"key": "marked_capacity", "lines": "9254, 9808-9809, 12208-12209, 9904", "kind": "moment capacity",
         "verdict": "real, no recount of it tried; priced; the largest leverage near the paper; above "
                    "c_M = 37/65 Lemma marked's second condition binds",
         "buys": res.get("ideal_cM_gain"), "shadow": sp_.get("c_M_float"), "break_even": res.get("be_cM")},
        {"key": "plain_capacity", "lines": "12561, 14259, 15175", "kind": "moment capacity",
         "verdict": "real, no recount of it tried; priced; moved by public follow-ups per FOLLOWUPS.md (I3)",
         "buys": res.get("ideal_cP_gain"), "shadow": sp_.get("c_P_float"), "break_even": res.get("be_cP")},
    ]


# ----------------------------------------------------------------------------- main

def load_probe134(path: Path):
    spec = importlib.util.spec_from_file_location("probe134", path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def cross_check_134(path: Path) -> dict:
    """Compare -E_* with hunt #134's probe.py on an exact grid (an independent code path)."""
    mod = load_probe134(path)
    n = bad = 0
    for ell in (Fr(1, 7), Fr(1, 6), Fr(1, 5)):
        for b in (Fr(0), Fr(1, 8), Fr(1, 5)):
            for dM in (Fr(0), Fr(-1, 20)):
                M = 1 - ell + dM
                for dl in (Fr(1, 10), Fr(7, 18), Fr(2, 3)):
                    for x in (Fr(0), Fr(1, 4), HALF):
                        n += 1
                        bad += mod.endpoint_neg_e(ell, b, dl, x, M) != neg_e_star(dl, x, ell, M, b)
    return {"points": n, "mismatches": bad}


def main(argv=None) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--paper", type=Path, default=None)
    ap.add_argument("--probe134", type=Path, default=None, help="hunt #134 probe.py, for a cross-check")
    ap.add_argument("--quick", action="store_true", help="skip the measured evaluator")
    ap.add_argument("--json", type=Path, default=None, help="write a summary (scratch use only)")
    args = ap.parse_args(argv)
    res = {}

    reps = reproductions()
    eps = endpoint_reproductions()
    bad = [r for r in reps + eps if not r["ok"]]
    for r in reps + eps:
        print(f"{'ok  ' if r['ok'] else 'FAIL'} line {r['line']:>5}  {r['name']}")
    print(f"{len(reps) - len([r for r in reps if not r['ok']])}/{len(reps)} row-count reproductions agree; "
          f"{len(eps) - len([r for r in eps if not r['ok']])}/{len(eps)} endpoint reproductions agree")
    if args.paper:
        cf = verify_citations(args.paper)
        print(f"citations: {len(CITATIONS) - len(cf)}/{len(CITATIONS)} on their stated line", cf or "")
        res["citations_failed"] = cf
    if args.probe134:
        res["cross_134"] = cross_check_134(args.probe134)
        print("cross-check with #134 probe.py:", res["cross_134"])
    print("#134 numbers:", {k: str(v) for k, v in numbers_from_134().items()})

    b0 = bracket(PAPER)
    o0 = b0["opt"]
    print(f"\nslice optimum, paper inputs: sigma* = {b0['sigma_star']} = {b0['sigma_star_float']}")
    print(f"  minimal polynomial of sigma*: {o0['minpoly_sigma']}")
    print(f"  ell* = {o0['ell']} = {o0['ell'].evalf(20)}, b* = {o0['b'].evalf(20)}, "
          f"delta* = {o0['delta_v']}")
    print(f"  bracket [{float(b0['sigma_lp']):.16f}, {float(b0['sigma_up']):.16f}], Bernstein boxes "
          f"{b0['feasibility']['boxes']}, feasible {b0['feasibility']['feasible']}")
    print("  side conditions:", b0["side"])
    bt = bracket(PAPER, tied=True)
    ot = bt["opt"]
    print(f"\ntied plain capacity: sigma = {bt['sigma_star_float']}, minimal polynomial {ot['minpoly_sigma']}")
    print(f"  Guo's sigma_dagger {GUO_SIGMA_DAGGER}; bracket [{float(bt['sigma_lp']):.16f}, "
          f"{float(bt['sigma_up']):.16f}], feasible {bt['feasibility']['feasible']}")
    res["tied_gain"] = float(bt["sigma_star_float"] - b0["sigma_star_float"])

    w0 = slice_optimum(PAPER, x=Fr(0))
    print(f"\nx = 0 wall (rows with no prime amplitude; independent of c_M, c_P): sigma = {w0['sigma']}"
          f" = {w0['sigma_float']}, b = {w0['b']}, minimal polynomial {w0['minpoly_sigma']}")
    res["x0_wall"] = float(w0["sigma_float"])
    for bb in (Fr(-1, 50), Fr(-1, 20)):
        print(f"  x = 0 slice with b = {bb} (outside the Gram hypothesis P_a >= 1): "
              f"{slice_fixed_b(PAPER, bb, Fr(0))['sigma_float']}")
    L0, kk = d_half_line()
    wl = slice_on_dhalf_line(PAPER, Fr(0))
    a0 = alpha_zero_paper_dhalf()
    print(f"\nrows d <= 1/2 as the paper counts them (t = 1): ell <= {L0} + {kk} b; with them the x = 0 rows "
          f"stop every capacity improvement at {wl['sigma_float']} = {wl['sigma']}; alpha = 0 stops at "
          f"{a0['sigma']} = {float(a0['sigma'])}")
    be_line = break_even_on_dhalf_line("alpha", TRACKER_RECORD)
    print(f"  alpha to {float(TRACKER_RECORD)} with b on that line: {be_line['theta']} ({be_line['relative_change']:+.6f})")
    print(f"\nLemma marked's second condition: margin at x = 0, 1/2: "
          f"{marked_second_margin(Fr(0))}, {marked_second_margin(HALF)}; closed form exact for "
          f"c_M <= {marked_second_threshold()}")
    print(f"  c_P = 5/22 (tracker PR 26's prime cost 22/5 read as a plain capacity, inferred): "
          f"slice optimum {sigma_slice_float(replace(PAPER, c_P=Fr(5, 22))):.10f}")

    sp_ = shadow_prices(PAPER)
    res["shadow"] = sp_
    print("\nshadow prices:", {k: v for k, v in sp_.items() if k.endswith("float")})
    for prm in ("alpha", "c_M", "c_P"):
        be = break_even_exact(prm)
        res["be_" + {"alpha": "alpha", "c_M": "cM", "c_P": "cP"}[prm]] = be["theta"]
        print(f"  break-even {prm} to {float(XU_SANG)}: {be}")
        be2 = break_even_exact(prm, goal=TRACKER_RECORD)
        print(f"  break-even {prm} to {float(TRACKER_RECORD)}: {be2}")
    for lam in (Fr(3, 4), Fr(1, 2), Fr(1, 4)):
        print(f"  excess scaled by {lam}: slice optimum {sigma_slice_float(PAPER, lam=lam):.6f}")

    if not args.quick:
        print("\nmeasured evaluator with supply caps and Lemma marked's second condition:")
        base = float(b0["sigma_star_float"])
        meas = {}
        bal = {"d_half": "balanced"}
        for name, inp, kw in (("paper", PAPER, {}), ("alpha=0", replace(PAPER, alpha=Fr(0)), {}),
                              ("c_M=1", replace(PAPER, c_M=Fr(1)), {}),
                              ("c_P=1", replace(PAPER, c_P=Fr(1)), {}),
                              ("alpha=0, d<=1/2 recounted", replace(PAPER, alpha=Fr(0)), bal),
                              ("alpha=0, d<=1/2 recounted, floor at 1/2", replace(PAPER, alpha=Fr(0)),
                               {"d_half": "balanced", "delta0": 0.0}),
                              ("c_M=1, d<=1/2 recounted", replace(PAPER, c_M=Fr(1)), bal),
                              ("c_M=1, d<=1/2 recounted, second condition dropped", replace(PAPER, c_M=Fr(1)),
                               {"d_half": "balanced", "second": False}),
                              ("c_P=1, d<=1/2 recounted", replace(PAPER, c_P=Fr(1)), bal),
                              ("c_M=c_P=1, d<=1/2 recounted", replace(PAPER, c_M=Fr(1), c_P=Fr(1)), bal)):
            meas[name] = sigma_general(inp, **kw)
            print(f"  {name}: {meas[name]}")
        res["measured"] = meas
        res["ideal_alpha_gain"] = meas["alpha=0"]["sigma"] - base
        res["ideal_cM_gain"] = meas["c_M=1"]["sigma"] - base
        res["ideal_cP_gain"] = meas["c_P=1"]["sigma"] - base

    print("\nenumerations:")
    print("  selection:", enumerate_selection())
    adv = adversary_multi_t(Fr(7, 18), HALF)
    print("  multi-t adversary:", {k: str(v) for k, v in adv.items()})
    ex_ok = all(adversary_exact(Fr(5, 6) * Fr(kd, 20), Fr(kx, 20))["covers"] and
                adversary_exact(Fr(5, 6) * Fr(kd, 20), Fr(kx, 20))["value"]
                == r_star(Fr(5, 6) * Fr(kd, 20), Fr(kx, 20)) for kd in range(1, 20) for kx in range(11))
    print("  exact adversary attains R_* on a 19 x 11 grid of (delta, x):", ex_ok)
    print("  conductor strata:", conductor_strata())
    print("  beyond capacity:", beyond_capacity_signs())
    print("  one copy vs two:", one_copy_vs_two())
    print("  reciprocity factor mod 4:", reciprocity_factor_table())
    print("  exceptional Gram means all ok:", exceptional_gram_means()["all_ok"])
    print("  local correlation:", local_correlation_check())
    print("  amplification lifts:", amplification_lift_counts())
    for row in loss_table(res):
        print(f"  [{row['key']}] {row['verdict']} (buys {row['buys']})")
    if args.json:
        args.json.write_text(json.dumps(res, default=str, indent=1))
    return 1 if bad or res.get("citations_failed") else 0


if __name__ == "__main__":
    sys.exit(main())

"""Hunt #136, assembly lane: an exact symbolic model of OpenAI's Part II final assembly.

Source: github.com/openai/math at adc7f124, preprint *The Quasi-Riemann Hypothesis*
(2026-09-30), build/paper.tex, 16,677 lines, sha256 42a5ee0f...c6a3, read as data and
cited by line in CITATIONS.  Hunt #134 (`seven_eighths_pin`, unlanded) rewrote the final
section in the free geometry (ell, M, b); this module starts from its probe.py and makes
every exponent that feeds the row counts a symbol:

    c_M    marked (inverse) capacity slope, z_M(r) = c_M (1 - r)         paper 1/2   line 15182
    c_P    plain capacity slope, z_P(m) = c_P (1 - 2m) = (1-2m)/(6 kappa)  paper 2/9   lines 15175, 15327
    alpha  sextic amplification slope, e(r) = 1 - alpha + alpha r          paper 5/6   lines 15101, 15300
    R_fl   count exponent of the floor bin                                 paper 1     line 15844
    g      Gram exponent: P_a^g in the Gram bound, P_a^(g/2) in the low bound   paper 1/6   lines 8353, 8619
    z_p    the pole of zeta_F(6z), the 1/6 of C(s) and of h(z_0 - 1/6)   paper 1/6   lines 5588, 6090
    n_num  the pointwise reflected-numerator cost U^(n delta), not a row count  paper 1/2   lines 15801, 6052

The frozen choices of the final section (floor bin, contour, bin ceiling, the no-slot
intermediate range, the supply hypothesis, the row-norm bookkeeping) are a separate
record, `Frozen`.

The model is exact: every function below is rational arithmetic and accepts Fractions,
sympy expressions or the quadratic-field numbers `QF`.  The best abscissa of the
assembly is a semi-infinite linear program in the geometry (ell, M, b): every high
exponent is affine in the geometry once (delta, x) is fixed.  It is solved three ways:

* `regime_A`: the closed form when the only binding high constraint is the endpoint
  inequality at amplitude ratio x = 1/2 (the paper's neighbourhood).  Exact in Q(sqrt d).
* `regime_B`: the closed form once the offset b has reached 0 (the alpha axis).
* `sandwich`: an exact bracket for any rational inputs.  A float LP over a refined cut
  set proposes a basis; the lower end is an exact rational dual witness (valid for
  every geometry), the upper end is a rational geometry whose feasibility over the whole
  (delta, x) rectangle is checked exactly (real-root isolation of the discriminant, every
  root-free piece sampled, each cell guarded by a Sturm count: `_sample_points`).
* `lower_bound_from`: a dual witness built from named constraints only, used to
  show that a constraint set which does not involve some input bounds the abscissa for
  every value of that input.

Revised after verifier round 1 (2026-10-21): the intermediate row is imposed only for
delta <= min(alpha, delta_max) (line 16146), the sampler no longer skips a gap whose
isolating intervals share an endpoint, the rows at d < h are checked when the numerator
cost is below 26/125, and every abscissa below 7/8 is conditional on two inferred readings
(total accounting, and the shared analytic lemmas used below their stated range
sigma_0 >= 7/8, lines 5811, 6024, 6178, 6345).  Repair pass: Lemma marked's second width
condition is evaluated at both amplitude ends (marked_width_excess).

Grades: formulas transcribed from a cited line are *cited*; their general-parameter
forms and every number computed here are *derived* (exact arithmetic, pinned by
test_assembly.py), except where a docstring says *inferred* (a reading of a proof that
no computation checks) or *measured* (float search output, used only to propose).

    .venv/bin/python hunts/below_seven_eighths/assembly.py            # everything
    .venv/bin/python hunts/below_seven_eighths/assembly.py --quick    # skip the witness searches past regime A
"""
from __future__ import annotations

import argparse
import hashlib
import os
import itertools
import math
import sys
from dataclasses import dataclass, fields, replace
from fractions import Fraction as Fr
from pathlib import Path

PAPER_SHA256 = "42a5ee0febca59fd1def55cfd6c6808c322ef4237d7726303ea52f711deac6a3"
DEFAULT_PAPER = Path(os.environ.get("ZETA_LAB_CACHE", os.path.expanduser("~/.cache/zeta-lab"))) / "openai-math-adc7f124" / "paper.tex"

# ------------------------------------------------------------------ citations
#: key -> (line, verbatim snippet of the pinned paper.tex on that line)
CITATIONS = {
    # geometry, target, low side
    "C_stage": (5588, r"C(s)=s+\frac{l_x}{2}-1+\frac h6"),
    "h_def": (5586, r"X=Z^{l_x},\qquad Y=Z^{l_y},\qquad h=1-l_x+\ell>0,"),
    "sextic_zeta": (5635, r"\frac{\zeta_F^S(6z)L^S(w,\chi_\bullet(u))}"),
    "W_mellin": (5645, r"X^{1/2-z}Z^{s+z-1}Y^{w-1}"),
    "C_II": (6835, r"C(s)=C_{\mathrm{II}}(s):=s-\frac{11}{16},\qquad"),
    "bootstrap": (6817, r"\Delta:=\beta_*-\frac78,\qquad 0<\Delta\le\frac1{24},"),
    "bin_ceiling": (6825, r"a\le\beta_*,\qquad \delta=2a-1\le\kappa\le\frac56."),
    "geometry": (6860, r"b=\frac18,\qquad h=\frac{13}{16},\qquad \ell=\frac16,"),
    "l_x": (6861, r"l_x=1+\ell-h=\frac{17}{48},\qquad"),
    "M": (6864, r"M=l_x+l_y=\frac56,\qquad M+\ell=1."),
    "dual_length": (8246, r"Since $M'+\ell'-1=-3d$, direct subtraction gives"),
    "row_loss": (8306, r"M'+\frac{1+3\ell'-2M'-2\Delta_H+\theta_N}{4}"),
    "gram_bound": (8353, r"\left(1+P_a^{1/6}+\frac{P_a^2}{Y'}\right)Z^\epsilon."),
    "gram_exceptional": (8541, r"$O_{\rm fixed}(K_R^{1/6})$ choices; if $q_e>C_{\rm sh}K_R$ it is"),
    "P_a": (8588, r"P_a=Y'^2/Q=q_{b_*}^{-1}Z^{1/8}."),
    "lengths": (8596, r"l_x-d\ge3/16,\qquad l_y-d\ge5/16,"),
    "gram_condition": (8597, r"\qquad l_y-d-11b/6\ge1/12."),
    "low_twelfth": (8619, r"&=\bigl[Z^{M'}/Y'\bigr]^{1/2}P_a^{1/12}\\"),
    "low_II": (8570, r"\ll Z^{l_x/2+b/12+\epsilon}=Z^{3/16+\epsilon}."),
    "f_d": (8631, r"f(d)=d-3d/2-d/2=-d\le0."),
    "C_form": (8641, r"C_{\mathrm{II}}(s)=l_x/2+s-1+h/6=s-11/16,"),
    "C_match": (8642, r"C_{\mathrm{II}}(7/8)=3/16=l_x/2+b/12."),
    "C_I": (190, r"C_{\mathrm I}(s)=s-\frac23"),
    "low_I": (3717, r"&=Z^{1/4+\epsilon_1/2}."),
    # the high exponent
    "stage_high": (6090, r"E_{\sigma_0}(d;R,g)=a-\sigma_0+h(z_0-1/6)-a l_y-\ell/2+g"),
    "small_rows_lemma": (6365, r"Z^{C(\beta_*)+h(z_0-1/6)-l_y/2+e+\epsilon}"),
    "small_rows_power": (6432, r"and the row power is $1+3/5-z_0=63/50$."),
    "D1_region": (5572, r"\Re z\ge17/50,\quad \Re w\ge-1/100,"),
    # witnesses and moments
    "witness": (4521, r"r\le t+O(1/\log U),\qquad"),
    "marked_lemma": (9254, r"r+2z\le m-c_1,\qquad 2r+8z\le3m-c_2."),
    "amplification_P": (12369, r"H=\max(2U,D^{1+c}),\qquad P=(H/U)^{1/6}."),
    "amplification_e": (12383, r"e(r)=\max\{1,(1+5r)/6\}."),
    "plain_kappa": (12532, r"Let \(3/4\le\kappa\le1\)."),
    # row counts
    "alpha_def": (15101, r"\alpha:=\frac56."),
    "kappa_def": (15100, r"\kappa=2\beta_*-1=\frac34+2\Delta\in(3/4,5/6],\qquad"),
    "z_P": (15175, r"z_P(m)=\frac{1-2m}{6\kappa}"),
    "z_P_cond": (15180, r"so its condition is \(2m+6\kappa z\le1\)."),
    "z_M": (15182, r"\(z_M(r)=(1-r)/2\)."),
    "D_x_P_x": (15192, r"D_x=3-\frac{17x}{9},\qquad"),
    "supply_hyp": (15195, r"Assume the total available prime length exceeds \(7/37\) by a"),
    "R_short": (15206, r"R_{\rm short}(t)=1-\delta+\frac{\delta P_x}{D_x}(3/2-t),"),
    "L_t": (15208, r"L(t)=1-\delta+(\alpha-\delta)(t-1)."),
    "no_slot_count": (15215, r"U^{1-2\delta/3+\epsilon}(1+T_1)^{A_{\mathcal A}},"),
    "marked_count": (15235, r"\ll U^{1-\delta r-2qz+\epsilon}(1+T_1)^{A_{\mathcal A}},"),
    "plain_count": (15238, r"\ll U^{1-2\delta m-2qz+\epsilon}(1+T_1)^{A_{\mathcal A}},"),
    "amplified_count": (15289, r"1-\alpha+(\alpha-\delta)r,&r\ge1."),
    "e_r": (15300, r"moment exponent \((1+5r)/6=1-\alpha+\alpha r\)."),
    "plain_baseline": (15327, r"\(2(1-2m)/9\).  Since the actual \(m\) is at least"),
    "A_I": (15331, r"A_I(r)&=1-\delta\{x+(1-x)r\},"),
    "S_t": (15333, r"+\left(2-\frac{8x}{9}\right)(t-r)\right\}."),
    "r_cross": (15350, r"\frac{(2-8x/9)t-5x/9}{D_x}."),
    "r_cross_end": (15354, r"r_*(3/2)=1,\qquad"),
    "t_minus_r": (15359, r"t-r_*(t)=\frac{(1-x)t+5x/9}{D_x}."),
    "r_min": (15366, r"r_*(t)\ge\frac{23}{37},\qquad"),
    "inverse_cap": (15382, r"\((1-23/37)/2=7/37\)."),
    "plain_cap": (15384, r"\(2/27+O(\epsilon)\).  At \(d=h\) the available length is"),
    "capacity_comparison": (15399, r"=\frac{24q(1-2m)\Delta}{(9/2)(9/2+12\Delta)}\\"),
    "capacity_quarter": (15400, r"&\le\frac{\Delta}{4}+O(\epsilon)."),
    "R_short_1": (15443, r"gives \(R_{\rm short}(1)=1-2\delta/3\); the long bound is"),
    # the final section
    "m_w": (15674, r"m_w:=\frac{l_y}{20}=\frac{23}{960},\qquad"),
    "m_z": (15675, r"m_z:=\frac h{600}=\frac{13}{9600}."),
    "E_line1": (15729, r"&=a-\frac78+h\left(\frac{17}{50}-\frac16\right)"),
    "C_0": (15734, r"\qquad C_0=-\frac1{48}."),
    "contour": (15742, r"\Re s=a+16e,\qquad \Re w=1-a-6e,\qquad \Re z=\frac{17}{50},"),
    "numerator": (15801, r"\ll{}&U^{\delta/2+O(e)+\epsilon}(1+T_1)^{A_1}\\"),
    "slot_factor": (15803, r"Z^{\ell(17/50-1/2)+q\ell+O(e+\vartheta+\epsilon)}."),
    "floor_bin": (15843, r"The floor bin \(a=51/100\) has \(\delta_0=1/50\) and requires no"),
    "floor": (15847, r"E(h)\le C_0+\frac34\delta_0=-\frac7{1200}<0."),
    "d_min": (15855, r"Set \(d_{\min}=1/100\)."),
    "small": (15878, r"=-\frac{79}{800}."),
    "small_saving": (15886, r"=-\frac{63}{800}+O(e+\epsilon)."),
    "B_0": (15900, r"\(B_0=l_x/2+1+l_y=53/32\)"),
    "large_delta": (15945, r"=-\frac1{48}-\frac{\delta}{16}+O(\epsilon)<0."),
    "t_star": (15964, r"t=1+\frac{\delta P_x}{2\mathcal J},\qquad"),
    "D_bounds": (15970, r"\frac{37}{18}\le D_x\le3,\qquad"),
    "D_minus_P": (15972, r"D_x-P_x=1+x-\frac{8x^2}{9}>0,"),
    "J_bounds": (15976, r"\frac{35}{54}\le\mathcal J\le\frac52."),
    "cert_bound": (16000, r"-E_*\ge\frac{49}{440640}>\frac1{10000}."),
    "j_y": (16011, r"j_y=185+170y+(-138+12y+96y^2)\delta."),
    "D_x": (16015, r"D_x=\frac{37+34y}{18},\qquad"),
    "R_star": (16019, r"From \(R_*=1-\delta+(\alpha-\delta)\delta P_x/(2\mathcal J)\)"),
    "negE_form": (16023, r"\frac{1+(3+8y)\delta}{48}"),
    "quad_0": (16033, r"&=10(37+34y)"),
    "quad_1": (16034, r"-8(237+377y+26y^2)\delta\\"),
    "quad_2": (16036, r"+48(51+131y+94y^2+32y^3)\delta^2."),
    "cert_identity": (16046, r"+265+3485y\bigr\}."),
    "cert_J": (16068, r"-E_*\ge\frac{49}{176256\mathcal J}"),
    "m_hi_101": (16101, r"&=-\frac{49}{440640}-\frac{51}{64}\Delta"),
    "supply": (16116, r"\frac{\ell}{d}\ge\frac8{39}>\frac15>\frac7{37}."),
    "zeta_ext": (16123, r"0<\zeta<5\ell-h=\frac1{48},"),
    "slopes": (16133, r"\ge\frac{33}{50}-\frac{\delta}{2}\ge\frac4{25}>0."),
    "R_star_cap": (16139, r"R_*\le1-\delta+\frac{\alpha-\delta}{2}\le\frac{17}{12},"),
    "intermediate_choice": (16146, r"For \(d_{\min}\le d\le1/2\) and \(\delta\le\alpha\), choose \(t=1\)"),
    "intermediate_R": (16151, r"R=\frac{76}{75}-\frac23\delta."),
    "intermediate": (16159, r"\le-\frac{529}{2400}+\frac{25}{96}\delta+O(\epsilon)"),
    "intermediate_end": (16160, r"\le-\frac{49}{14400}+O(\epsilon)<0."),
    "m_hi": (16182, r"m_{\rm hi}:=\left(1-\frac h4\right)\Delta"),
    # frozen choices named in ASSEMBLY.md
    "detector_floor": (4511, r"Let \(u\) have a bin \((i,a)\) with \(a>51/100\), and assume the"),
    "row_loss_clip": (8325, r"$M'+((d-1/6)/4)_++O(\epsilon_0+\kappa_{\mathrm G}+\epsilon_Z)$."),
    "R_short_indep": (15417, r"is independent of \(r\): the \(r\)-coefficients cancel, and the"),
    "floor_count": (15844, r"The ideal count \(R=1\), together with"),
    "saturation_uniform": (16076, r"The saturation losses are uniform because \(\delta\ge1/50\),"),
    # the range hypothesis of the shared analytic lemmas, and where the paper invokes them
    "shared_range_contour": (5811, r"$\sigma_0\in[7/8,1)$ with $\beta_*>\sigma_0$, put $z_0=17/50$, and let"),
    "shared_range_accounting": (6024, r"$\sigma_0\in[7/8,1)$ with $\beta_*>\sigma_0$, and put $z_0=17/50$."),
    "shared_range_principal": (6178, r"$\sigma_0\in[7/8,1)$ with $\beta_*>\sigma_0$ and $0<e<10^{-3}$."),
    "shared_range_tails": (6345, r"$\sigma_0\in[7/8,1)$ with $\beta_*>\sigma_0$, $0<e<10^{-3}$,"),
    "shared_at_7_8": (15532, r"In the shared analytic lemmas take \(\sigma_0=7/8\)."),
    "accounting_at_7_8": (15823, r"Apply Lemma~\ref{lem:bin-contour-accounting} with \(\sigma_0=7/8\)"),
    # which bins the row counts and the intermediate range cover
    "counts_delta_le_alpha": (15188, r"\(a>51/100\), \(0<\delta=2a-1\le\alpha\), and mean amplitude"),
    "no_slot_beyond_alpha": (15458, r"a>51/100,\qquad 1/50<\delta=2a-1\le1,"),
    "no_slot_needs_neither": (15463, r"but requires neither"),
    "slot_range": (16114, r"For \(1/2\le d\le h\), the available length is"),
    "slot_counts": (16128, r"For \(1/50<\delta<\alpha\), use the ideal row upper exponent"),
    "floor_slope": (16135, r"The floor has a positive slope as well.  Thus \(d=h\) bounds"),
    "intermediate_slope": (16154, r"Its slope is \(101/150-\delta/6>0\) on this range."),
    "intermediate_at_5_6": (16165, r"the last inequality uses \(\delta\le5/6\)."),
    "large_delta_every_d": (16168, r"already control every \(d\le h\)."),
    "marked_margin": (15183, r"strict inequality in Lemma~\ref{lem:marked} also has a fixed margin."),
    "count_at_alpha": (16129, r"For \(\delta=\alpha\), use"),
    "no_slot_remark": (15448, r"\begin{remark}[Unselected inverse witnesses beyond the Part II bin ceiling]"),
    "no_slot_remark_end": (15467, r"\end{remark}"),
    # the range of the final section
    "final_section": (15495, r"\section{The seven-eighths bound}\label{sec:conclusion}"),
    "final_section_end": (16463, r"allowed, and proves Theorem~\ref{thm:main}."),
}


def verify_citations(paper: Path) -> list[str]:
    """Return the citation keys whose snippet is not on its stated line (or a hash flag)."""
    raw = paper.read_bytes()
    if hashlib.sha256(raw).hexdigest() != PAPER_SHA256:
        return ["<sha256 mismatch: not the pinned paper.tex>"]
    lines = raw.decode("utf-8").splitlines()
    return [k for k, (n, snip) in CITATIONS.items() if snip not in lines[n - 1]]


# ------------------------------------------------------------- the two records

@dataclass(frozen=True)
class Inputs:
    """The exponents that feed the row counts and the low side, at the paper's values."""
    c_M: object = Fr(1, 2)
    c_P: object = Fr(2, 9)
    alpha: object = Fr(5, 6)
    R_fl: object = Fr(1)
    g: object = Fr(1, 6)
    z_p: object = Fr(1, 6)
    n_num: object = Fr(1, 2)


INPUT_NAMES = tuple(f.name for f in fields(Inputs))
#: sign of the change that helps (lowers the abscissa) for each input
HELPS = {"c_M": +1, "c_P": +1, "alpha": -1, "R_fl": -1, "g": -1, "z_p": +1, "n_num": -1}
#: what each input is, for tables
INPUT_ROLE = {
    "c_M": "marked inverse capacity slope, z_M(r) = c_M(1 - r) (line 15182)",
    "c_P": "plain capacity slope, z_P(m) = c_P(1 - 2m) (lines 15175, 15327)",
    "alpha": "sextic amplification slope, e(r) = 1 - alpha + alpha r (line 15300)",
    "R_fl": "floor-bin count exponent R (line 15844)",
    "g": "Gram exponent, P_a^g in the Gram bound (line 8353), P_a^(g/2) in the low bound (line 8619)",
    "z_p": "pole of zeta_F(6z), the 1/6 in C(s) (line 5588) and in h(z_0 - 1/6) (line 6090)",
    "n_num": "reflected-numerator exponent per unit delta, U^(n delta) (lines 15801, 6052); not a row count",
}


@dataclass(frozen=True)
class Frozen:
    """Chosen, not proved, constants of the final section, and two bookkeeping readings.

    lossless:     "per_summand" is the paper's own bookkeeping (every rescaled summand of
                  the low estimate lossless, M - 2 ell >= 1/2), "total" is hunt #134's
                  reading (only the unrescaled summand must be lossless; inferred).
    intermediate: "paper" keeps the no-slot range d <= 1/2 with t = 1 for the bins with
                  delta <= alpha only (line 16146: "and delta <= alpha"; Proposition
                  detector-counts is stated for delta <= alpha, line 15188).  Bins with
                  delta in [alpha, delta_max] use R = 1 - delta at every d <= h (the no-slot
                  inverse count holds for delta <= 1, lines 15458 to 15463; line 16168),
                  which the endpoint row at d = h already carries (K = 0 there).
                  "off" drops it (inferred: with slots there too, the endpoint at d = h
                  dominates by the positive d-slope); "perfect" counts those rows at 1 - delta;
                  "at_delta_max" is the 14:36Z version of this lane, which imposed the row at
                  delta_max for every alpha (kept only to reproduce the withdrawn claims).
    counts:       "paper" uses R_* of line 16019; "perfect" sets every count to 1 - delta.
    supply:       "uniform" keeps Proposition detector-counts' hypothesis that ell/h exceeds
                  the largest capacity over t in [1, 3/2] (line 15195); "off" drops it
                  (inferred: a per-bin hypothesis would only need the capacity at t_*).
    """
    delta0: object = Fr(1, 50)
    z0: object = Fr(17, 50)
    delta_max: object = Fr(5, 6)
    d_int: object = Fr(1, 2)
    d_min: object = Fr(1, 100)
    lossless: str = "total"
    intermediate: str = "paper"
    counts: str = "paper"
    supply: str = "uniform"


PAPER = Inputs()
FROZEN = Frozen()                                   # hunt #134's re-optimization frame
FROZEN_PAPER_BOOKKEEPING = Frozen(lossless="per_summand")
ELL_PAPER, M_PAPER, B_PAPER = Fr(1, 6), Fr(5, 6), Fr(1, 8)

# public frontier values used as reference lines (external map of 2026-10-21, not checked here)
XU_SANG = Fr(8748867, 10**7)
GUO = Fr(8749570194, 10**10)
TARGET_087 = Fr(87, 100)
THIRTEEN_FIFTEENTHS = Fr(13, 15)


# ------------------------------------------------------------ exact Q(sqrt c)

class QF:
    """Exact a + b sqrt(c), with a, b, c rational and c > 0 fixed per field.

    Enough arithmetic for the regime-A closed form, with an exact sign: for a, b of
    opposite signs, compare a^2 with b^2 c.
    """
    __slots__ = ("a", "b", "c")

    def __init__(self, a, b=0, c=1):
        self.a, self.b, self.c = Fr(a), Fr(b), Fr(c)

    def _lift(self, o):
        if isinstance(o, QF):
            if o.b != 0 and self.b != 0 and o.c != self.c:
                raise ValueError("different quadratic fields")
            return o if o.b != 0 or o.c == self.c else QF(o.a, 0, self.c)
        return QF(o, 0, self.c)

    def _field(self, o):
        return self.c if self.b != 0 or not isinstance(o, QF) else o.c

    def __add__(self, o):
        o = self._lift(o)
        return QF(self.a + o.a, self.b + o.b, self.c if self.b != 0 else o.c)

    __radd__ = __add__

    def __neg__(self):
        return QF(-self.a, -self.b, self.c)

    def __sub__(self, o):
        return self + (-self._lift(o))

    def __rsub__(self, o):
        return (-self) + o

    def __mul__(self, o):
        o = self._lift(o)
        c = self.c if self.b != 0 else o.c
        return QF(self.a * o.a + self.b * o.b * c, self.a * o.b + self.b * o.a, c)

    __rmul__ = __mul__

    def __truediv__(self, o):
        o = self._lift(o)
        c = self.c if self.b != 0 else o.c
        den = o.a * o.a - o.b * o.b * c
        if den == 0:
            raise ZeroDivisionError("QF division by zero")
        num = self * QF(o.a, -o.b, c)
        return QF(num.a / den, num.b / den, c)

    def __rtruediv__(self, o):
        return QF(o, 0, self.c) / self

    def __pow__(self, n):
        out = QF(1, 0, self.c)
        for _ in range(n):
            out = out * self
        return out

    def sign(self) -> int:
        a, b = self.a, self.b
        sa = (a > 0) - (a < 0)
        sb = (b > 0) - (b < 0)
        if sb == 0:
            return sa
        if sa == 0 or sa == sb:
            return sb
        diff = a * a - b * b * self.c
        return sa if diff > 0 else (sb if diff < 0 else 0)

    def _cmp(self, o):
        return (self - o).sign()

    def __lt__(self, o):
        return self._cmp(o) < 0

    def __le__(self, o):
        return self._cmp(o) <= 0

    def __gt__(self, o):
        return self._cmp(o) > 0

    def __ge__(self, o):
        return self._cmp(o) >= 0

    def __eq__(self, o):
        return isinstance(o, (QF, Fr, int)) and self._cmp(o) == 0

    def __hash__(self):
        return hash((self.a, self.b, self.c))

    def __float__(self):
        return float(self.a) + float(self.b) * math.sqrt(float(self.c))

    def mp(self, dps=50):
        """High-precision value (mpmath); the arithmetic so far was exact."""
        from mpmath import mp, mpf, sqrt
        with mp.workdps(dps):
            return mpf(self.a.numerator) / self.a.denominator + (
                mpf(self.b.numerator) / self.b.denominator
                * sqrt(mpf(self.c.numerator) / self.c.denominator))

    def sympy(self):
        """The exact value as a sympy expression (sqrt of a rational is reduced by sympy)."""
        import sympy as sp
        Rq = lambda q: sp.Rational(q.numerator, q.denominator)
        return Rq(self.a) + Rq(self.b) * sp.sqrt(Rq(self.c))

    def pretty(self) -> str:
        """a + b sqrt(n) with n a squarefree integer."""
        return str(self.sympy())

    def __repr__(self):
        return f"QF({self.a}, {self.b}, {self.c})"


def clip0(v):
    """max(0, v) for exact numbers."""
    return v if v > 0 else 0 * v


# --------------------------------------------------------------------- the model

def geometry(ell, M, b):
    """l_x, l_y, h from M = l_x + l_y, b = l_y - l_x and h = 1 - l_x + ell (line 5586)."""
    l_x = (M - b) / 2
    l_y = (M + b) / 2
    h = 1 - l_x + ell
    return l_x, l_y, h


def mellin_shift(ell, M, b, th: Inputs = PAPER):
    """c with C(s) = s - c, from C(s) = s + l_x/2 - 1 + z_p h (lines 5588, 8641)."""
    l_x, _, h = geometry(ell, M, b)
    return 1 - l_x / 2 - th.z_p * h


def low_exponent(ell, M, b, th: Inputs = PAPER):
    """l_x/2 + (g/2) b: the d = 0 summand of the low bound (lines 8570, 8619), P_a = Z^b."""
    l_x, _, _ = geometry(ell, M, b)
    return l_x / 2 + th.g * b / 2


def target(ell, M, b, th: Inputs = PAPER):
    """sigma_0 where the low bound meets the Mellin signal: 1 - z_p h + g b/2 (derived)."""
    return low_exponent(ell, M, b, th) + mellin_shift(ell, M, b, th)


def row_loss(ell, M, d):
    """Second-branch row-norm loss of Lemma probe-row-norm (line 8306) for summand d.

    ((1 + 3 ell' - 2 M')/4)_+ with ell' = ell - d, M' = M - 2d (derived general form).
    """
    return clip0((1 + 3 * (ell - d) - 2 * (M - 2 * d)) / 4)


def low_loss(ell, M):
    """Extra low exponent max_d (loss(d)/2 - d) = ((1 + 3 ell - 2M)/8)_+ (inferred bookkeeping)."""
    return clip0((1 + 3 * ell - 2 * M) / 8)


def C0(ell, M, b, th: Inputs = PAPER):
    """E(h) at delta = q = 0, R = 1 with the matched target: 1/2 + ell/2 - 3M/4 + b(1/4 - g/2)."""
    return Fr(1, 2) + ell / 2 - Fr(3, 4) * M + b * (Fr(1, 4) - th.g / 2)


# ---- row counts (Proposition detector-counts, lines 15185 to 15446)

def D_x(x, th: Inputs = PAPER):
    """3 - 2x(c_M + 2 c_P); the paper's 3 - 17x/9 (line 15192)."""
    return 3 - 2 * x * (th.c_M + 2 * th.c_P)


def P_x(x, th: Inputs = PAPER):
    """(2 - 4 c_P x)(1 - 2 c_M x); the paper's (2 - 8x/9)(1 - x) (line 15193)."""
    return (2 - 4 * th.c_P * x) * (1 - 2 * th.c_M * x)


def A_I(r, delta, x, th: Inputs = PAPER):
    """Marked count 1 - delta r - 2q z_M(r) with q = x delta (lines 15235, 15331)."""
    return 1 - delta * r - 2 * x * delta * th.c_M * (1 - r)


def S_t(r, t, delta, x, th: Inputs = PAPER):
    """Plain count 1 - 2 delta m - 2 q z_P(m) at the shortest m = t - r (lines 15238, 15332)."""
    m = t - r
    return 1 - 2 * delta * m - 2 * x * delta * th.c_P * (1 - 2 * m)


def L_t(t, delta, th: Inputs = PAPER):
    """Amplified count 1 - alpha + (alpha - delta) t (line 15306)."""
    return 1 - th.alpha + (th.alpha - delta) * t


def r_cross(t, x, th: Inputs = PAPER):
    """Where A_I and S_t cross: ((2 - 4 c_P x) t + 2x(c_P - c_M))/D_x (line 15350, general)."""
    return ((2 - 4 * th.c_P * x) * t + 2 * x * (th.c_P - th.c_M)) / D_x(x, th)


def R_short(t, delta, x, th: Inputs = PAPER):
    """1 - delta + (delta P_x/D_x)(3/2 - t) (lines 15206, 15413; general form derived)."""
    return 1 - delta + delta * P_x(x, th) / D_x(x, th) * (Fr(3, 2) - t)


def J_of(delta, x, th: Inputs = PAPER):
    """(alpha - delta) D_x + delta P_x (line 15963)."""
    return (th.alpha - delta) * D_x(x, th) + delta * P_x(x, th)


def K_formula(delta, x, th: Inputs = PAPER):
    """(alpha - delta) delta P_x / J: twice the row-count excess R_* - (1 - delta)."""
    return (th.alpha - delta) * delta * P_x(x, th) / J_of(delta, x, th)


def K_of(delta, x, th: Inputs = PAPER, counts: str = "paper"):
    """The excess with its branches: 0 for perfect counts and for delta >= alpha (R = 1 - delta)."""
    if counts == "perfect" or delta >= th.alpha:
        return 0 * delta
    return K_formula(delta, x, th)


def t_star(delta, x, th: Inputs = PAPER):
    """1 + delta P_x/(2J) (line 15964): R_short(t) = L(t) there."""
    return 1 + delta * P_x(x, th) / (2 * J_of(delta, x, th))


def R_star(delta, x, th: Inputs = PAPER, counts: str = "paper"):
    """R_* = 1 - delta + (alpha - delta) delta P_x/(2J) (line 16019)."""
    return 1 - delta + K_of(delta, x, th, counts) / 2


# ---- the high exponent (Lemma bin-contour-accounting, line 6090)

def high_exponent(d, delta, q, R, ell, M, b, th: Inputs = PAPER, fr: Frozen = FROZEN, sigma0=None):
    """E_{sigma_0}(d; R, g = q ell) = a - sigma_0 + h(z_0 - z_p) - a l_y - ell/2 + q ell
    + d(R + n delta - z_0), a = (1 + delta)/2, n = 1/2 the reflected-numerator cost U^(delta/2)
    (line 15801); sigma_0 defaults to the matched target."""
    _, l_y, h = geometry(ell, M, b)
    if sigma0 is None:
        sigma0 = target(ell, M, b, th)
    a = (1 + delta) / 2
    return (a - sigma0 + h * (fr.z0 - th.z_p) - a * l_y - ell / 2 + q * ell
            + d * (R + th.n_num * delta - fr.z0))


def neg_E_star(delta, x, ell, M, b, th: Inputs = PAPER, fr: Frozen = FROZEN):
    """-E_* of Lemma balanced-endpoint (lines 15994 to 16072): -E(h) at q = x delta, R = R_*."""
    h = geometry(ell, M, b)[2]
    return -high_exponent(h, delta, x * delta, R_star(delta, x, th, fr.counts), ell, M, b, th, fr)


def neg_E_star_closed(delta, x, ell, M, b, th: Inputs = PAPER, fr: Frozen = FROZEN):
    """Closed form (derived): -C_0 + delta(ell + b)/2 - ell x delta - (h/2) K - h delta (n - 1/2)."""
    h = geometry(ell, M, b)[2]
    return (-C0(ell, M, b, th) + delta * (ell + b) / 2 - ell * x * delta
            - h / 2 * K_of(delta, x, th, fr.counts) - h * delta * (th.n_num - Fr(1, 2)))


def endpoint_requirement(E_star_max, h, Delta):
    """The comparison actually needed (eq:adaptive-endpoint, line 16096): with the observed
    count R_* + Delta/4 the endpoint exponent relative to C(beta_*) is at most
    E_* + h Delta/4 - Delta = E_* - (1 - h/4) Delta, negative for every Delta > 0 iff E_* <= 0."""
    return E_star_max + h * Delta / 4 - Delta


def E_floor(ell, M, b, th: Inputs = PAPER, fr: Frozen = FROZEN):
    """Floor bin at d = h: R = R_fl, delta = delta_0, q = delta_0/2 (line 15847)."""
    h = geometry(ell, M, b)[2]
    return high_exponent(h, fr.delta0, fr.delta0 / 2, th.R_fl, ell, M, b, th, fr)


def R_intermediate(delta, th: Inputs = PAPER, fr: Frozen = FROZEN):
    """The no-slot count of the range d <= 1/2: the common line through the floor point,
    max(R_fl, 1 - 2 delta_0/3) - 2(delta - delta_0)/3 (line 16151: 76/75 - 2 delta/3)."""
    if fr.intermediate == "perfect":
        return 1 - delta
    top = th.R_fl if th.R_fl >= 1 - 2 * fr.delta0 / 3 else 1 - 2 * fr.delta0 / 3
    return top - Fr(2, 3) * (delta - fr.delta0)


def E_intermediate(delta, ell, M, b, th: Inputs = PAPER, fr: Frozen = FROZEN):
    """E(d_int) with q = delta/2 and the no-slot count (eq:adaptive-intermediate, line 16158)."""
    return high_exponent(fr.d_int, delta, delta / 2, R_intermediate(delta, th, fr),
                         ell, M, b, th, fr)


def int_top(th: Inputs = PAPER, fr: Frozen = FROZEN):
    """Top of the delta-range the no-slot intermediate row covers: min(alpha, delta_max).

    The paper takes t = 1 in d <= 1/2 only "for delta <= alpha" (line 16146); larger bins
    carry R = 1 - delta at every d <= h (lines 15458, 16168), which the endpoint at d = h
    bounds.  E_intermediate is affine in delta, so its two range ends are its maxima.
    Returns None when the range [delta_0, min(alpha, delta_max)] is empty."""
    top = Fr(fr.delta_max) if fr.intermediate == "at_delta_max" else min(Fr(th.alpha), Fr(fr.delta_max))
    return top if top >= Fr(fr.delta0) else None


def int_deltas(th: Inputs = PAPER, fr: Frozen = FROZEN) -> list:
    """The two ends of the intermediate range in delta, at which its rows are imposed."""
    top = int_top(th, fr)
    if fr.intermediate == "off" or top is None:
        return []
    return sorted({Fr(fr.delta0), top})


def E_small(ell, M, b, th: Inputs = PAPER, fr: Frozen = FROZEN):
    """Small rows relative to C(beta_*): h(z_0 - z_p) - l_y/2 + 2 d_min (lines 15877, 15885)."""
    _, l_y, h = geometry(ell, M, b)
    return h * (fr.z0 - th.z_p) - l_y / 2 + 2 * fr.d_min


def capacity_max(th: Inputs = PAPER):
    """Largest requested capacity over t in [1, 3/2], x in [0, 1/2] (lines 15381 to 15384).

    Inverse: c_M (1 - min r_*(1, x)); plain: c_P (1 - 2 min (1 - r_*(1, x))).  Both minima
    sit at x = 0 or x = 1/2 (the x-derivatives have the signs of c_P - c_M and c_M - c_P).
    """
    rs = [r_cross(Fr(1), x, th) for x in (Fr(0), Fr(1, 2))]
    ms = [1 - r for r in rs]
    return max(th.c_M * (1 - min(rs)), th.c_P * (1 - 2 * min(ms)))


# ---- the abscissa each constraint allows (the max formulation)

def hard_slacks(ell, M, b, th: Inputs = PAPER, fr: Frozen = FROZEN) -> dict:
    """Constraints that are not traded against the target; each must be >= 0."""
    _, l_y, h = geometry(ell, M, b)
    out = {
        "dual_length": 1 - M - ell,                       # line 8246, derived (M + ell <= 1)
        "b_nonneg": b,                                    # P_a >= 1 (lines 8345, 8591)
        "gram": (M - 2 * ell) - (3 - 2 * th.g) * b,       # l_y - ell - (2 - g) b >= 0 (line 8597)
        "small_rows": -E_small(ell, M, b, th, fr),        # line 15886
    }
    if fr.supply == "uniform":
        out["supply"] = ell - capacity_max(th) * h        # ell/h >= capacity (line 15195)
    if fr.lossless == "per_summand":
        out["per_summand"] = M - 2 * ell - Fr(1, 2)
    return out


# ------------------------------------------------------------------ reproductions

def reproductions() -> list[dict]:
    """Every printed constant the model touches, rebuilt from the general formulas."""
    th, fr = PAPER, FROZEN
    ell, M, b = ELL_PAPER, M_PAPER, B_PAPER
    l_x, l_y, h = geometry(ell, M, b)
    out = []

    def rec(name, cite, got, want):
        out.append({"name": name, "cite": cite, "line": CITATIONS[cite][0],
                    "got": str(got), "want": str(want), "ok": got == want})

    s0 = target(ell, M, b, th)
    rec("h = 13/16", "geometry", h, Fr(13, 16))
    rec("l_x = 17/48", "l_x", l_x, Fr(17, 48))
    rec("M + ell = 1", "M", M + ell, Fr(1))
    rec("C_II shift 11/16 (z_p = 1/6)", "C_II", mellin_shift(ell, M, b, th), Fr(11, 16))
    rec("C_II(s) = l_x/2 + s - 1 + h/6", "C_form", 1 - l_x / 2 - h / 6, Fr(11, 16))
    rec("low exponent l_x/2 + g b/2 = 3/16 (g = 1/6)", "low_II", low_exponent(ell, M, b, th), Fr(3, 16))
    rec("P_a^(g/2) = Z^(b/12)", "low_twelfth", th.g / 2 * b, b / 12)
    rec("target 7/8 from C_II(7/8) = 3/16", "C_match", s0, Fr(7, 8))
    rec("Part I target 11/12 (ell = b = 0, M = 1)", "C_I", target(Fr(0), Fr(1), Fr(0), th), Fr(11, 12))
    rec("Part I shift 2/3", "C_I", mellin_shift(Fr(0), Fr(1), Fr(0), th), Fr(2, 3))
    rec("Part I low exponent 1/4", "low_I", low_exponent(Fr(0), Fr(1), Fr(0), th), Fr(1, 4))
    rec("row loss (d - 1/6)/4 clipped at d = 0", "row_loss", row_loss(ell, M, Fr(0)), Fr(0))
    rec("row loss at d = ell", "row_loss", row_loss(ell, M, ell), Fr(0))
    rec("f(d) = -d leaves the d = 0 summand dominant", "f_d", Fr(1) - Fr(3, 2) - Fr(1, 2), Fr(-1))
    rec("P_a = Z^(l_y - l_x) = Z^(1/8)", "P_a", l_y - l_x, Fr(1, 8))
    rec("l_x - ell = 3/16", "lengths", l_x - ell, Fr(3, 16))
    rec("l_y - ell = 5/16", "lengths", l_y - ell, Fr(5, 16))
    rec("l_y - ell - (2 - g) b = 1/12", "gram_condition", l_y - ell - (2 - th.g) * b, Fr(1, 12))
    rec("Gram slack (M - 2ell) - (3 - 2g) b = 1/6", "gram_condition",
        hard_slacks(ell, M, b, th, fr)["gram"], Fr(1, 6))
    rec("C_0 = -1/48", "C_0", C0(ell, M, b, th), Fr(-1, 48))
    rec("C_0 from the high exponent", "E_line1",
        high_exponent(h, Fr(0), Fr(0), Fr(1), ell, M, b, th, fr), Fr(-1, 48))
    e1 = high_exponent(h, Fr(1), Fr(0), Fr(1), ell, M, b, th, fr, sigma0=Fr(7, 8))
    rec("delta coefficient 2/3", "C_0", e1 - Fr(-1, 48), Fr(2, 3))
    rec("numerator cost U^(delta/2): the d-slope at delta = 1, R = 0 is n - 17/50 = 4/25", "numerator",
        high_exponent(Fr(1), Fr(1), Fr(0), Fr(0), ell, M, b, th, fr) - high_exponent(Fr(0), Fr(1), Fr(0), Fr(0),
                                                                                         ell, M, b, th, fr),
        Fr(4, 25))
    eq = high_exponent(h, Fr(0), Fr(1), Fr(1), ell, M, b, th, fr, sigma0=Fr(7, 8))
    rec("q coefficient ell = 1/6", "C_0", eq - Fr(-1, 48), Fr(1, 6))
    rec("floor bound -7/1200", "floor", E_floor(ell, M, b, th, fr), Fr(-7, 1200))
    rec("large-delta endpoint -1/48 - 5/96 at delta = alpha", "large_delta",
        high_exponent(h, th.alpha, th.alpha / 2, 1 - th.alpha, ell, M, b, th, fr),
        Fr(-1, 48) - th.alpha / 16)
    rec("intermediate count 76/75 - 2 delta/3 at delta = 0", "intermediate_R",
        R_intermediate(Fr(0), th, fr), Fr(76, 75))
    i0 = E_intermediate(Fr(0), ell, M, b, th, fr)
    rec("intermediate constant -529/2400", "intermediate", i0, Fr(-529, 2400))
    rec("intermediate slope 25/96", "intermediate", E_intermediate(Fr(1), ell, M, b, th, fr) - i0,
        Fr(25, 96))
    rec("intermediate at delta = 5/6 is -49/14400", "intermediate_end",
        E_intermediate(fr.delta_max, ell, M, b, th, fr), Fr(-49, 14400))
    rec("intermediate d-slope R + delta/2 - 17/50 = 101/150 - delta/6 (three delta)", "intermediate_slope",
        all(R_intermediate(dl, th, fr) + th.n_num * dl - fr.z0 == Fr(101, 150) - dl / 6
            for dl in (Fr(1, 50), Fr(1, 2), Fr(5, 6))), True)
    rec("small-row margin -79/800", "small", E_small(ell, M, b, th, fr) - 2 * fr.d_min, Fr(-79, 800))
    rec("small-row saving -63/800", "small_saving", E_small(ell, M, b, th, fr), Fr(-63, 800))
    rec("small-row power 1 + 3/5 - z_0 = 63/50", "small_rows_power", 1 + Fr(3, 5) - fr.z0, Fr(63, 50))
    rec("principal margin m_w = l_y/20", "m_w", l_y / 20, Fr(23, 960))
    rec("principal margin m_z = h/600", "m_z", h / 600, Fr(13, 9600))
    rec("large-row B_0 = l_x/2 + 1 + l_y", "B_0", l_x / 2 + 1 + l_y, Fr(53, 32))
    rec("high margin factor 1 - h/4 = 51/64", "m_hi_101", 1 - h / 4, Fr(51, 64))
    rec("slot supply ell/h = 8/39", "supply", ell / h, Fr(8, 39))
    rec("supply excess 8/39 - 7/37 = 23/1443", "supply", ell / h - capacity_max(th), Fr(23, 1443))
    rec("extension ceiling 5 ell - h = 1/48", "zeta_ext", 5 * ell - h, Fr(1, 48))
    # row counts in general form
    rec("D_x at x = 1/2 is 37/18", "D_bounds", D_x(Fr(1, 2), th), Fr(37, 18))
    rec("P_x at x = 1/2 is 7/9", "D_x_P_x", P_x(Fr(1, 2), th), Fr(7, 9))
    rec("D_x - P_x = 1 + x - 8x^2/9 (seven x)", "D_minus_P",
        all(D_x(x, th) - P_x(x, th) == 1 + x - Fr(8, 9) * x * x
            for x in (Fr(0), Fr(1, 7), Fr(1, 3), Fr(1, 2))), True)
    rec("D_x = (37 + 34y)/18, P_x = (7 + 18y + 8y^2)/9 with y = 1/2 - x", "D_x",
        all(D_x(Fr(1, 2) - y, th) == (37 + 34 * y) / 18
            and P_x(Fr(1, 2) - y, th) == (7 + 18 * y + 8 * y * y) / 9
            for y in (Fr(0), Fr(1, 7), Fr(1, 2))), True)
    rec("r_*(1) at x = 1/2 is 23/37", "r_min", r_cross(Fr(1), Fr(1, 2), th), Fr(23, 37))
    rec("r_*(3/2) = 1 (three x)", "r_cross_end",
        all(r_cross(Fr(3, 2), x, th) == 1 for x in (Fr(0), Fr(1, 4), Fr(1, 2))), True)
    rec("t - r_*(t) = ((1 - x) t + 5x/9)/D_x", "t_minus_r",
        all(t - r_cross(t, x, th) == ((1 - x) * t + Fr(5, 9) * x) / D_x(x, th)
            for t in (Fr(1), Fr(5, 4)) for x in (Fr(0), Fr(1, 2))), True)
    rec("inverse capacity bound 7/37", "inverse_cap", th.c_M * (1 - Fr(23, 37)), Fr(7, 37))
    rec("plain capacity bound 2/27", "plain_cap", th.c_P * (1 - 2 * Fr(1, 3)), Fr(2, 27))
    rec("capacity_max = 7/37", "supply_hyp", capacity_max(th), Fr(7, 37))
    rec("plain baseline capacity 2(1-2m)/9 = (1-2m)/(6 kappa) at kappa = 3/4", "plain_baseline",
        1 / (6 * Fr(3, 4)), Fr(2, 9))
    rec("capacity comparison 2q(1-2m)(2/9 - 1/(9/2+12 Delta)) = 24q(1-2m)Delta/((9/2)(9/2+12 Delta))",
        "capacity_comparison",
        all(2 * q * (1 - 2 * m) * (Fr(2, 9) - 1 / (Fr(9, 2) + 12 * dD))
            == 24 * q * (1 - 2 * m) * dD / (Fr(9, 2) * (Fr(9, 2) + 12 * dD))
            for q in (Fr(1, 5), Fr(1, 2)) for m in (Fr(1, 3), Fr(2, 5)) for dD in (Fr(1, 100), Fr(1, 24))), True)
    rec("... and it is at most Delta/4 (2q <= 1, m >= 1/3, Delta <= 1/24)", "capacity_quarter",
        all(Fr(1, 2) * 2 * (1 - 2 * Fr(1, 3)) * (Fr(2, 9) - 1 / (Fr(9, 2) + 12 * dD)) <= dD / 4
            for dD in (Fr(1, 1000), Fr(1, 100), Fr(1, 24))), True)
    rec("A_I(r) = 1 - delta(x + (1-x) r)", "A_I",
        all(A_I(r, dl, x, th) == 1 - dl * (x + (1 - x) * r)
            for r in (Fr(2, 3), Fr(9, 10)) for dl in (Fr(1, 5),) for x in (Fr(0), Fr(1, 2))), True)
    rec("S_t(r) = 1 - delta(4x/9 + (2 - 8x/9)(t - r))", "S_t",
        all(S_t(r, Fr(5, 4), dl, x, th) == 1 - dl * (Fr(4, 9) * x + (2 - Fr(8, 9) * x) * (Fr(5, 4) - r))
            for r in (Fr(2, 3), Fr(9, 10)) for dl in (Fr(1, 5),) for x in (Fr(0), Fr(1, 2))), True)
    rec("R_short independent of r: weighted average of A_I and S_t", "R_short",
        all(((2 - Fr(8, 9) * x) * A_I(r, dl, x, th) + (1 - x) * S_t(r, t, dl, x, th)) / D_x(x, th)
            == R_short(t, dl, x, th)
            for r in (Fr(1, 3), Fr(4, 5)) for t in (Fr(1), Fr(6, 5)) for dl in (Fr(1, 3),)
            for x in (Fr(0), Fr(1, 3), Fr(1, 2))), True)
    rec("R_short(1) = 1 - 2 delta/3 at x = 0", "R_short_1",
        all(R_short(Fr(1), dl, Fr(0), th) == 1 - Fr(2, 3) * dl for dl in (Fr(1, 5), Fr(2, 3))), True)
    rec("R_short(t_*) = L(t_*) = R_*", "t_star",
        all(R_short(t_star(dl, x, th), dl, x, th) == L_t(t_star(dl, x, th), dl, th) == R_star(dl, x, th)
            for dl in (Fr(1, 5), Fr(7, 18)) for x in (Fr(0), Fr(1, 2))), True)
    rec("e(r) slope: 1 - alpha + alpha r = (1 + 5r)/6", "e_r",
        all(1 - th.alpha + th.alpha * r == (1 + 5 * r) / 6 for r in (Fr(1), Fr(3, 2))), True)
    rec("amplification H/P = U^(1/6) H^(5/6) gives alpha = 5/6", "amplification_P", 1 - Fr(1, 6), th.alpha)
    rec("R_* <= 1 - delta + (alpha - delta)/2 <= 17/12", "R_star_cap",
        1 - Fr(0) + th.alpha / 2, Fr(17, 12))
    rec("slope R + delta/2 - 17/50 >= 33/50 - delta/2 >= 4/25 (R >= 1 - delta, delta <= 1)", "slopes",
        (1 - fr.z0, 1 - Fr(1, 2) - fr.z0), (Fr(33, 50), Fr(4, 25)))
    rec("J range [35/54, 5/2] at the corners", "J_bounds",
        (min(J_of(dl, x, th) for dl in (Fr(0), th.alpha) for x in (Fr(0), Fr(1, 2))),
         max(J_of(dl, x, th) for dl in (Fr(0), th.alpha) for x in (Fr(0), Fr(1, 2)))),
        (Fr(35, 54), Fr(5, 2)))
    pts = [(Fr(i, 24), Fr(j, 8)) for i in range(1, 21) for j in range(0, 5)]
    rec("-E_* transcription equals the closed form (100 points)", "R_star",
        all(neg_E_star(dl, x, ell, M, b, th, fr) == neg_E_star_closed(dl, x, ell, M, b, th, fr)
            for dl, x in pts), True)
    rec("-E_* = (1 + (3 + 8y) delta)/48 - (13/32)(5/6 - delta) delta P_x/J", "negE_form",
        all(neg_E_star(dl, Fr(1, 2) - y, ell, M, b, th, fr)
            == (1 + (3 + 8 * y) * dl) / 48
            - Fr(13, 32) * (Fr(5, 6) - dl) * dl * P_x(Fr(1, 2) - y, th) / J_of(dl, Fr(1, 2) - y, th)
            for dl, y in pts), True)
    quad_ok = True
    for dl, x in pts:
        y = Fr(1, 2) - x
        J = J_of(dl, x, th)
        lhs = 10368 * J * neg_E_star(dl, x, ell, M, b, th, fr)
        rhs = (10 * (37 + 34 * y) - 8 * (237 + 377 * y + 26 * y * y) * dl
               + 48 * (51 + 131 * y + 94 * y * y + 32 * y ** 3) * dl * dl)
        quad_ok = quad_ok and lhs == rhs and J == (185 + 170 * y + (-138 + 12 * y + 96 * y * y) * dl) / 108
    rec("10368 J(-E_*) quadratic and J = j_y/108", "quad_0", quad_ok, True)
    ident = True
    for dl, x in pts + [(Fr(0), Fr(1, 2))]:
        y = Fr(1, 2) - x
        v = 51 + 41 * y
        J = J_of(dl, x, th)
        lhs = 10368 * v * J * neg_E_star(dl, x, ell, M, b, th, fr)
        rhs = ((3 + 5 * y) * ((4 * v * dl - 79) ** 2 + 49)
               + 4 * y * (4 * v * dl * ((1 + 3 * y) * (15 + 32 * y) * dl + 9 - 13 * y)
                          + 265 + 3485 * y))
        ident = ident and lhs == rhs
    rec("completed-square identity of the balanced endpoint display", "cert_identity", ident, True)
    rec("endpoint margin floor 49/(176256 * 5/2) = 49/440640", "cert_J", Fr(49, 176256) / Fr(5, 2),
        Fr(49, 440640))
    worst = neg_E_star(Fr(79, 204), Fr(1, 2), ell, M, b, th, fr)
    rec("worst point delta = 79/204, x = 1/2: -E_* = 7/30672 >= 49/440640", "cert_bound",
        (worst, worst >= Fr(49, 440640)), (Fr(7, 30672), True))
    rec("form used at line 16101: E_actual - Delta <= E_* - (1 - h/4) Delta (three Delta)", "m_hi_101",
        all(endpoint_requirement(-Fr(49, 440640), h, dD) == -Fr(49, 440640) - Fr(51, 64) * dD
            for dD in (Fr(1, 1000), Fr(1, 100), Fr(1, 24))), True)
    rec("m_hi = (1 - h/4) Delta = 51/64 Delta", "m_hi", 1 - h / 4, Fr(51, 64))
    return out


# --------------------------------------------- #134's controls in the general model

def robust_single_point_bound(delta, x, th: Inputs = PAPER, fr: Frozen = FROZEN):
    """Exact lower bound on the abscissa from the endpoint inequality at one (delta, x).

    On M = 1 - ell (optimal along constant targets, #134) -E_* = A + A_ell ell + A_b b.
    When A_b <= 0 the bound is valid for every b >= 0: ell <= -A/A_ell.  Needs g = z_p,
    where the target 11/12 - ell/4 does not involve b.  Returns None when A_b > 0.
    """
    def f(l, bb):
        return neg_E_star_closed(delta, x, l, 1 - l, bb, th, fr)
    A = f(Fr(0), Fr(0))
    A_ell = f(Fr(1), Fr(0)) - A
    A_b = f(Fr(0), Fr(1)) - A
    if A_b > 0:
        return None
    ell_star = -A / A_ell
    return target(ell_star, 1 - ell_star, Fr(0), th)


def gram_limited_single_point_bound(delta, x, th: Inputs = PAPER, fr: Frozen = FROZEN):
    """As above with b capped by the Gram condition b <= (M - 2 ell)/(3 - 2g) (#134's 44117/50422)."""
    def f(l, bb):
        return neg_E_star_closed(delta, x, l, 1 - l, bb, th, fr)
    A = f(Fr(0), Fr(0))
    A_ell = f(Fr(1), Fr(0)) - A
    A_b = f(Fr(0), Fr(1)) - A
    if A_b <= 0:
        ell_star = -A / A_ell
    else:
        k = 1 / (3 - 2 * th.g)       # b = k (1 - 3 ell)
        ell_star = -(A + A_b * k) / (A_ell - 3 * A_b * k)
    return target(ell_star, 1 - ell_star, Fr(0), th)


ROBUST_WITNESS = (Fr(223, 576), Fr(1, 2))
GRAM_WITNESS = (Fr(7, 18), Fr(1, 2))


def perfect_count_ceiling(delta0=Fr(0)):
    """The abscissa with every count perfect (R = 1 - delta): an exact two-variable vertex.

    With K = 0 the endpoint family reads -C_0 + delta(ell + b)/2 - ell x delta >= 0 and is
    weakest at delta -> delta_0; the floor rows (R = 1) add C_0 + delta_0 (h - b/2) <= 0.
    At delta_0 -> 0 this is C_0 <= 0, M + ell <= 1, M >= (1 + 3 ell)/2, b >= 0, whose best
    point is (ell, M, b) = (1/5, 4/5, 0) with target 13/15 (#134).  For delta_0 > 0 the
    floor line meets M + ell = 1 at ell = (1 - 2 delta_0)/(5 + 6 delta_0), b = 0.
    """
    ell = (1 - 2 * delta0) / (5 + 6 * delta0)
    M = 1 - ell
    fr = Frozen(delta0=delta0, counts="perfect", intermediate="perfect")
    s = target(ell, M, Fr(0))
    checks = {
        "floor": E_floor(ell, M, Fr(0), PAPER, fr),
        "lossless_slack": 2 * M - 1 - 3 * ell,
        "endpoint_at_floor": neg_E_star(delta0 if delta0 > 0 else Fr(1, 10**9), Fr(1, 2), ell, M,
                                        Fr(0), PAPER, fr),
    }
    return {"ell": ell, "M": M, "b": Fr(0), "sigma": s, "checks": checks}


def fixed_b_optimum(b, th: Inputs = PAPER, fr: Frozen = FROZEN, dps=40):
    """Best abscissa with the offset held at b (M = 1 - ell, x = 1/2): #134's scan at b = 0.12.

    Tangency: -E_*(delta) = 0 and d/d delta = 0.  -E_* is affine in ell, so ell(delta) is
    explicit and the remaining equation in delta is solved to `dps` digits (mpmath on the
    exact rational function); returns (sigma, ell, delta) as mpf.
    """
    from mpmath import mp, mpf, findroot, diff
    with mp.workdps(dps):
        cM, cP, al, g, nu = (mpf(Fr(v).numerator) / Fr(v).denominator
                             for v in (th.c_M, th.c_P, th.alpha, th.g, Fr(th.n_num) - Fr(1, 2)))
        bb = mpf(Fr(b).numerator) / Fr(b).denominator
        D = 3 - (cM + 2 * cP)
        P = (2 - 2 * cP) * (1 - cM)

        def K(d):
            return (al - d) * d * P / ((al - d) * D + d * P)

        def ell_of(d):     # -E_* = 1/4 - K/4 - (5/4 + 3K/4) ell + (-1/4 + g/2 + d/2 - K/4) b - h d nu = 0
            return (mpf(1) / 4 - K(d) / 4 + (-mpf(1) / 4 + g / 2 + d / 2 - K(d) / 4) * bb
                    - (mpf(1) / 2 + bb / 2) * d * nu) / (mpf(5) / 4 + 3 * K(d) / 4 + 3 * d * nu / 2)

        dstar = findroot(lambda d: diff(ell_of, d), mpf("0.39"))
        ell = ell_of(dstar)
        zp = mpf(Fr(th.z_p).numerator) / Fr(th.z_p).denominator
        h = mpf(1) / 2 + 3 * ell / 2 + bb / 2
        return 1 - zp * h + g * bb / 2, ell, dstar


def fixed_b_optimum_exact(b, th: Inputs = PAPER, fr: Frozen = FROZEN):
    """The same optimum with exact root isolation (derived): on M = 1 - ell, x = 1/2,
    -E_* = 0 gives ell(delta) explicitly; the binding delta minimises it, so d ell/d delta
    = 0, a polynomial in delta whose real roots are isolated by sympy.  Needs g = z_p,
    where the target 11/12 - ell/4 does not involve b.  Returns (sigma, ell, delta) exactly."""
    sp = _sp()
    d = sp.Symbol("delta")
    R = lambda v: sp.Rational(Fr(v).numerator, Fr(v).denominator)
    thr = Inputs(*(R(getattr(th, n)) for n in INPUT_NAMES))
    l = sp.Symbol("ell")
    negE = neg_E_star_closed_sym(d, sp.Rational(1, 2), l, 1 - l, R(b), thr)
    ell_d = sp.solve(sp.Eq(negE, 0), l)[0]
    poly = sp.Poly(sp.expand(sp.numer(sp.together(sp.diff(ell_d, d)))), d)
    best = None
    for root in poly.real_roots():
        if R(fr.delta0) < root < thr.alpha:
            val = ell_d.subs(d, root)
            if best is None or sp.N(val, 40) < sp.N(best[0], 40):
                best = (val, root)
    ell_v, root = best
    return target(ell_v, 1 - ell_v, R(b), thr), ell_v, root


# --------------------------------------------------------- regime A, closed form

def regime_A(th: Inputs = PAPER, fr: Frozen = FROZEN) -> dict | None:
    """The optimum when the endpoint at x = 1/2 is the only binding high constraint.

    Derived.  On M = 1 - ell, -E_*(delta, 1/2) = A + A_ell ell + A_b b with
    A = (1 - K)/4, A_ell = -(5 + 3K)/4, A_b = -1/4 + g/2 + delta/2 - K/4.  Minimising the
    target 1 - z_p/2 - (3 z_p/2) ell + ((g - z_p)/2) b subject to -E_* >= 0 for all delta:
    KKT at one active delta_* gives the multiplier mu = 6 z_p/(5 + 3K) and the tangency
    K(delta_*) = k_0 + k_1 delta_*, k_1 = 2 z_p/g - 2(n - 1/2), k_0 = (2 z_p - 5g + 6 g z_p)/(3g),
    a quadratic in delta_*; then -E_* = 0 and d(-E_*)/d delta = 0 fix (ell, b) linearly.
    The numerator exponent n adds -h delta (n - 1/2) to -E_* (zero at the paper's n = 1/2).
    The result lives in Q(sqrt disc).  Returns None if no root lies in (delta_0, alpha).
    """
    cM, cP, al, g, zp = (Fr(v) for v in (th.c_M, th.c_P, th.alpha, th.g, th.z_p))
    nu = Fr(th.n_num) - Fr(1, 2)
    D = 3 - (cM + 2 * cP)
    P = (2 - 2 * cP) * (1 - cM)
    k1 = 2 * zp / g - 2 * nu
    k0 = (2 * zp - 5 * g + 6 * g * zp) / (3 * g)
    qa = k1 * (P - D) + P
    qb = k0 * (P - D) + k1 * al * D - al * P
    qc = k0 * al * D
    disc = qb * qb - 4 * qa * qc
    if disc < 0 or qa == 0:
        return None
    best = None
    for sgn in (1, -1):
        dl = QF(-qb / (2 * qa), Fr(sgn) / (2 * qa), disc)
        if not (Fr(fr.delta0) < dl < al):
            continue
        sol = _regime_A_at(dl, th, fr, D, P, k0, k1)
        if sol is not None and (best is None or sol["sigma"] < best["sigma"]):
            best = sol
    return best


def _regime_A_at(dl, th, fr, D, P, k0, k1):
    cM, cP, al, g, zp = (Fr(v) for v in (th.c_M, th.c_P, th.alpha, th.g, th.z_p))
    nu = Fr(th.n_num) - Fr(1, 2)
    u = al - dl
    J = u * D + dl * P
    K = u * dl * P / J
    if K != k0 + k1 * dl:
        raise AssertionError("tangency identity failed")
    Kp = ((al - 2 * dl) * P * J - u * dl * P * (P - D)) / (J * J)        # dK/d delta
    A = (1 - K) / 4 - dl * nu / 2
    Al = -(5 + 3 * K) / 4 - 3 * dl * nu / 2
    Ab = -Fr(1, 4) + g / 2 + dl / 2 - K / 4 - dl * nu / 2
    Ap, Alp, Abp = -Kp / 4 - nu / 2, -3 * Kp / 4 - 3 * nu / 2, Fr(1, 2) - Kp / 4 - nu / 2
    det = Al * Abp - Ab * Alp
    ell = (-A * Abp + Ab * Ap) / det
    b = (-Al * Ap + A * Alp) / det
    M = 1 - ell
    mu = 6 * zp / (5 + 3 * K + 6 * dl * nu)
    sigma = target(ell, M, b, th)
    h = geometry(ell, M, b)[2]
    # second-order: J(-E_*) is quadratic in delta with a double root at delta_*; its leading
    # coefficient (b/2 - h(n - 1/2))(P - D) + h P/2 must be positive
    lead = (b / 2 - h * nu) * (P - D) + h * P / 2
    if lead <= 0 or mu <= 0:
        return None
    return {"delta": dl, "ell": ell, "M": M, "b": b, "sigma": sigma, "K": K, "Kp": Kp,
            "mu": mu, "h": h, "J": J, "u": u, "D": D, "P": P,
            "nu": mu * (Fr(3, 4) + K / 4 + dl * nu / 2) - zp / 2}


def regime_A_witness(sol: dict, th: Inputs = PAPER, fr: Frozen = FROZEN) -> dict:
    """The KKT multipliers of regime A as an exact dual witness in Q(sqrt d).

    Rows: the low side, the endpoint row at delta_* itself (x = 1/2) and the dual length.
    Weights (1 - mu, mu) on the two soft rows and nu on the hard row cancel the geometry
    gradient exactly; the bound they give, valid for every geometry, equals sigma_*.
    """
    dl = sol["delta"]
    c_low, *g_low = _affine(lambda l, M, b: target(l, M, b, th))
    c_end, *g_end = _affine(lambda l, M, b: target(l, M, b, th)
                            - neg_E_star_closed(dl, Fr(1, 2), l, M, b, th, fr))
    mu, nu = sol["mu"], sol["nu"]
    resid = [(1 - mu) * a + mu * e + nu * d for a, e, d in zip(g_low, g_end, (1, 1, 0))]
    lb = (1 - mu) * c_low + mu * c_end - nu * 1          # hard row ell + M <= 1, c = 1
    return {"lb": lb, "residual": resid, "weights": (1 - mu, mu, nu)}


def regime_A_shadow_prices(sol: dict, th: Inputs = PAPER) -> dict:
    """Envelope theorem at the regime-A optimum: d sigma / d input, exact in Q(sqrt disc).

    For c_M, c_P, alpha the only dependence is through K at (delta_*, 1/2):
    d sigma = mu (h/2) dK.  For g: (1 - mu) b/2 (target +b/2, constraint +b/2).  For z_p:
    -h (the target moves, the constraint does not).  R_fl: the floor is slack, 0.  For the
    numerator exponent n: -E_* carries -h delta (n - 1/2), so d sigma/d n = mu h delta_*.
    """
    cM, cP = Fr(th.c_M), Fr(th.c_P)
    dl, u, J, D, P, h, mu, b = (sol[k] for k in ("delta", "u", "J", "D", "P", "h", "mu", "b"))
    dK_dalpha = dl * dl * P * P / (J * J)
    common = u * u * dl / (J * J)
    dK_dcM = common * (P - D * (2 - 2 * cP))
    dK_dcP = common * (2 * P - 2 * D * (1 - cM))
    return {
        "c_M": mu * h / 2 * dK_dcM,
        "c_P": mu * h / 2 * dK_dcP,
        "alpha": mu * h / 2 * dK_dalpha,
        "R_fl": QF(0, 0, sol["delta"].c),
        "g": (1 - mu) * b / 2,
        "z_p": -h,
        "n_num": mu * h * dl,
    }


def regime_A_slacks(sol: dict, th: Inputs = PAPER, fr: Frozen = FROZEN) -> dict:
    """Every condition that keeps regime A the optimum, exact; each must be >= 0."""
    ell, M, b, dl = sol["ell"], sol["M"], sol["b"], sol["delta"]
    x = Fr(1, 2)
    h = sol["h"]
    # d(-E_*)/dx at (delta_*, 1/2) must be <= 0 (x = 1/2 is a boundary minimum)
    cM, cP, al = Fr(th.c_M), Fr(th.c_P), Fr(th.alpha)
    Dp = -2 * (cM + 2 * cP)
    Pp = -4 * cP * (1 - 2 * cM * x) - 2 * cM * (2 - 4 * cP * x)
    dK_dx = sol["u"] ** 2 * dl * (Pp * sol["D"] - sol["P"] * Dp) / (sol["J"] ** 2)
    dneg_dx = -ell * dl - h / 2 * dK_dx
    out = {"x_boundary": -dneg_dx}
    out.update(hard_slacks(ell, M, b, th, fr))
    out.pop("dual_length")
    out["floor"] = -E_floor(ell, M, b, th, fr)
    ints = int_deltas(th, fr)
    if ints:                                   # the row at delta <= min(alpha, delta_max) only
        out["intermediate"] = min(-E_intermediate(dv, ell, M, b, th, fr) for dv in ints)
    out["lossless"] = 2 * M - 1 - 3 * ell
    out["delta_in_range"] = min(dl - fr.delta0, al - dl)
    return out


# ------------------------------------------------ regime B: the offset b at zero

def regime_B(th: Inputs = PAPER, fr: Frozen = FROZEN) -> dict | None:
    """The optimum once the offset b has reached 0 (derived; numerator cost n = 1/2).

    On M = 1 - ell, b = 0, x = 1/2 the endpoint reads -E_* = (1 - K)/4 - ell (5 + 3K)/4,
    with no g and no z_p, so every bin needs ell <= (1 - K)/(5 + 3K) and the binding bin
    maximises K(delta) = (alpha - delta) delta P/((alpha - delta) D + delta P) (P, D at
    x = 1/2).  1/K = D/(P delta) + 1/(alpha - delta) is least at
    delta_B = alpha (D - sqrt(DP))/(D - P), where K_B = alpha P/(sqrt D + sqrt P)^2.
    Exact in Q(sqrt(D P)), which is Q(sqrt 518) at the paper's capacities (D P = 259/162).
    Returns None when n != 1/2 or delta_B leaves (delta_0, min(alpha, delta_max)).
    """
    if Fr(th.n_num) != Fr(1, 2):
        return None
    cM, cP, al = Fr(th.c_M), Fr(th.c_P), Fr(th.alpha)
    D = 3 - (cM + 2 * cP)
    P = (2 - 2 * cP) * (1 - cM)
    root = QF(0, 1, D * P)                                   # sqrt(D P)
    dl = al * (D - root) / (D - P)
    K = al * P / (D + P + 2 * root)
    if not (Fr(fr.delta0) < dl < min(al, Fr(fr.delta_max))):
        return None
    ell = (1 - K) / (5 + 3 * K)
    M = 1 - ell
    b = QF(0, 0, D * P)
    return {"delta": dl, "K": K, "ell": ell, "M": M, "b": b, "sigma": target(ell, M, b, th),
            "h": geometry(ell, M, b)[2], "D": D, "P": P}


def regime_B_witness(sol: dict, th: Inputs = PAPER, fr: Frozen = FROZEN) -> dict | None:
    """Exact dual witness of regime B in Q(sqrt(DP)): rows low, the endpoint at
    (delta_B, 1/2), the dual length and b >= 0.  Valid for every geometry when its
    weights are >= 0; its bound is then sigma_B."""
    tags = [("low",), ("end", sol["delta"], Fr(1, 2)), ("dual_length",), ("b_nonneg",)]
    rows = _exact_rows_for(th, fr, tags)
    A_ = [list(r["a"]) + [Fr(-1) if r["kind"] == "soft" else Fr(0)] for r in rows]
    beta = [-r["c"] if r["kind"] == "soft" else r["c"] for r in rows]
    AT = [[A_[r][c] for r in range(4)] for c in range(4)]
    y = _solve_fr(AT, [Fr(0), Fr(0), Fr(0), Fr(-1)])
    if y is None:
        return None
    lb = -sum(yi * bi for yi, bi in zip(y, beta))
    return {"lb": lb, "y": dict(zip([t[0] for t in tags], y)), "rows": tags}


def regime_B_slacks(sol: dict, th: Inputs = PAPER, fr: Frozen = FROZEN) -> dict:
    """The conditions that keep regime B the optimum, exact; each must be >= 0."""
    ell, M, b, dl = sol["ell"], sol["M"], sol["b"], sol["delta"]
    w = regime_B_witness(sol, th, fr)
    out = {f"weight_{k}": v for k, v in w["y"].items()}
    x = Fr(1, 2)
    cM, cP = Fr(th.c_M), Fr(th.c_P)
    al = Fr(th.alpha)
    u = al - dl
    D, P = sol["D"], sol["P"]
    J = u * D + dl * P
    Dp = -2 * (cM + 2 * cP)
    Pp = -4 * cP * (1 - 2 * cM * x) - 2 * cM * (2 - 4 * cP * x)
    dK_dx = u * u * dl * (Pp * D - P * Dp) / (J * J)
    out["x_boundary"] = ell * dl + sol["h"] / 2 * dK_dx        # -(d(-E_*)/dx) at x = 1/2
    out.update(hard_slacks(ell, M, b, th, fr))
    out.pop("dual_length")
    out.pop("b_nonneg")
    out["floor"] = -E_floor(ell, M, b, th, fr)
    ints = int_deltas(th, fr)
    if ints:
        out["intermediate"] = min(-E_intermediate(dv, ell, M, b, th, fr) for dv in ints)
    out["lossless"] = 2 * M - 1 - 3 * ell
    return out


def regime_B_ends(th: Inputs = PAPER, fr: Frozen = FROZEN):
    """The alpha-range of regime B in closed form (derived), other inputs held at th.

    delta_B and K_B are proportional to alpha, so each end is linear: b leaves 0 where
    the b-coefficient of -E_* at (delta_B, 1/2), -1/4 + g/2 + delta_B/2 - K_B/4, vanishes;
    the floor binds where ell_B = (1 - 2 delta_0)/(5 + 6 delta_0), i.e. at
    K_B = (1 - 5 ell_f)/(1 + 3 ell_f).  Returns (alpha_floor, alpha_b) in Q(sqrt(DP))."""
    cM, cP, g = Fr(th.c_M), Fr(th.c_P), Fr(th.g)
    D = 3 - (cM + 2 * cP)
    P = (2 - 2 * cP) * (1 - cM)
    root = QF(0, 1, D * P)
    d1 = (D - root) / (D - P)                 # delta_B / alpha
    k1 = P / (D + P + 2 * root)               # K_B / alpha
    alpha_b = (Fr(1, 4) - g / 2) / (d1 / 2 - k1 / 4)
    d0 = Fr(fr.delta0)
    ell_f = (1 - 2 * d0) / (5 + 6 * d0)
    alpha_f = (1 - 5 * ell_f) / (1 + 3 * ell_f) / k1
    return alpha_f, alpha_b


def regime_B_level(level, th: Inputs = PAPER):
    """The alpha at which sigma_B reaches `level` (derived, z_p general, n = 1/2):
    sigma = 1 - z_p (1/2 + 3 ell/2) fixes ell, then K_B = (1 - 5 ell)/(1 + 3 ell) and
    alpha = K_B (sqrt D + sqrt P)^2 / P."""
    cM, cP, zp = Fr(th.c_M), Fr(th.c_P), Fr(th.z_p)
    D = 3 - (cM + 2 * cP)
    P = (2 - 2 * cP) * (1 - cM)
    root = QF(0, 1, D * P)
    ell = (2 * (1 - Fr(level)) / zp - 1) / 3
    K = (1 - 5 * ell) / (1 + 3 * ell)
    return K * (D + P + 2 * root) / P


# ------------------------------------------- exact feasibility over (delta, x)

def _sp():
    import sympy as sp
    return sp


def _nonneg_on(poly, lo, hi) -> bool:
    """Exact: is the univariate rational polynomial >= 0 on [lo, hi]?

    Sound by `_sample_points`: every maximal root-free piece of [lo, hi] holds a sample,
    and poly has one sign on each such piece."""
    if poly.is_zero:
        return True
    pts = _sample_points([poly], lo, hi)
    return all(poly.eval(p) >= 0 for p in pts)


#: test hook: when False, `_sample_points` skips its Sturm-count guard (planted fault only)
_STURM_GUARD = True


def _sample_points(polys, lo, hi):
    """Rational points of [lo, hi], lo and hi included, such that every closed cell
    between two consecutive points holds at most one distinct real root of the squarefree
    product of `polys`.

    Why that suffices: if two consecutive distinct roots r < r' had no sample strictly
    between them, the samples next to them would bound one closed cell holding both.  So
    every open gap between consecutive roots holds a sample, and the pieces [lo, r_1) and
    (r_k, hi] are represented by lo and hi themselves (not roots there).  Every polynomial
    of `polys` has one sign on each such piece, so one sample per piece decides any
    condition built from strict or non-strict signs of them.

    The candidates are lo, hi and every endpoint of sympy's isolating intervals inside
    (lo, hi), midpoints added (isolating intervals may share an endpoint, which lies
    between two roots and must itself be a sample; the version of 2026-10-21 14:36Z skipped
    it).  Soundness does not rest on the interval semantics: every closed cell is then
    checked by a Sturm count (sympy `count_roots`, closed interval), and a cell holding two
    roots is bisected until none does.
    """
    sp = _sp()
    lo, hi = sp.Rational(lo), sp.Rational(hi)
    prod = None
    for p in polys:
        if p.is_zero or p.degree() <= 0:
            continue
        q = p.sqf_part()
        prod = q if prod is None else prod * q
    pts = {lo, hi, (lo + hi) / 2}
    if prod is None:
        return sorted(pts)
    prod = prod.sqf_part()
    for (a, b), _ in prod.intervals():
        for e in (sp.Rational(a), sp.Rational(b)):
            if lo < e < hi:
                pts.add(e)
    base = sorted(pts)
    pts.update((u + v) / 2 for u, v in zip(base, base[1:]))
    if not _STURM_GUARD or prod.count_roots(lo, hi) <= 1:
        return sorted(pts)               # at most one root: every cell holds at most one
    srt = sorted(pts)
    cells = list(zip(srt, srt[1:]))
    while cells:
        u, v = cells.pop()
        if prod.count_roots(u, v) >= 2:
            m = (u + v) / 2
            pts.add(m)
            cells.extend([(u, m), (m, v)])
    return sorted(pts)


#: test hook: when False, the rectangle check skips the delta in [alpha, delta_max] branch
_BILINEAR_BRANCH = True


def _room_rect_ok(ell, M, b, s, th: Inputs, fr: Frozen, d_row=None, quad=True, bilin=True) -> bool:
    """Exact check that s >= target + E(d_row; R, q = x delta) for every bin delta in
    [delta_0, delta_max] and x in [0, 1/2], with the bin's count R = R_* = 1 - delta + K/2
    (K = 0 for delta >= alpha).  d_row = None means d = h, the endpoint E_*.

    Derived form: E(d) = E(h) - (h - d)(R + n delta - z_0), so
    room - E(d) = lin_d - (d/2) K with lin_d affine in delta for fixed x.
    For delta < alpha multiply by J > 0: Q = J (room - E(d)) is quadratic in delta,
    Q = q0(x) + q1(x) delta + q2(x) delta^2.  Q >= 0 on the rectangle iff it is >= 0 on
    the two delta-edges (univariate in x) and the discriminant 4 q0 q2 - q1^2 is >= 0
    wherever q2 > 0 and the vertex -q1/(2 q2) is inside.  All sign conditions change only
    at real roots of q2, q1 + 2 dL q2, q1 + 2 dH q2 and the discriminant, and
    `_sample_points` puts a sample on every root-free piece, so the check is exact.  For
    delta >= alpha the count is 1 - delta and the room is bilinear: four corners.
    """
    sp = _sp()
    d, x = sp.symbols("delta x")
    R = lambda v: sp.Rational(Fr(v).numerator, Fr(v).denominator)
    ell, M, b, s = R(ell), R(M), R(b), R(s)
    thr = Inputs(*(R(getattr(th, n)) for n in INPUT_NAMES))
    if not (thr.c_M < 1 and thr.c_P < 1 and 3 - (thr.c_M + 2 * thr.c_P) > 0):
        raise ValueError("D_x, P_x must stay positive on [0, 1/2] (J > 0)")
    room = s - target(ell, M, b, thr)
    h = geometry(ell, M, b)[2]
    dr = h if d_row is None else R(d_row)
    c0 = C0(ell, M, b, thr)
    z0 = R(fr.z0)
    dL, dmax = R(fr.delta0), R(fr.delta_max)
    dH = min(dmax, thr.alpha)
    lin = (room - c0 + d * (ell + b) / 2 - ell * x * d
           - h * d * (thr.n_num - sp.Rational(1, 2))
           + (h - dr) * (1 - z0 - (1 - thr.n_num) * d))          # room - E(d_row) without K
    X0, X1 = sp.Rational(0), sp.Rational(1, 2)
    if quad and dH > dL:
        if fr.counts != "perfect":
            Dx = 3 - 2 * x * (thr.c_M + 2 * thr.c_P)
            Px = (2 - 4 * thr.c_P * x) * (1 - 2 * thr.c_M * x)
            J = (thr.alpha - d) * Dx + d * Px
            Q = sp.Poly(sp.expand(lin * J - dr / 2 * (thr.alpha - d) * d * Px), d)
        else:
            Q = sp.Poly(sp.expand(lin), d)
        cs = [sp.Poly(c, x) for c in reversed(Q.all_coeffs())]
        while len(cs) < 3:
            cs.append(sp.Poly(0, x))
        q0, q1, q2 = cs
        for dv in (dL, dH):
            if not _nonneg_on(sp.Poly(Q.as_expr().subs(d, dv), x), X0, X1):
                return False
        a1 = q1 + q2 * (2 * dL)
        a2 = q1 + q2 * (2 * dH)
        disc = q0 * q2 * 4 - q1 ** 2
        for xs in _sample_points([q2, a1, a2, disc], X0, X1):
            if q2.eval(xs) > 0 and a1.eval(xs) < 0 and a2.eval(xs) > 0 and disc.eval(xs) < 0:
                return False
    if bilin and _BILINEAR_BRANCH and thr.alpha < dmax:   # [alpha, delta_max]: K = 0, bilinear
        for dv in (max(thr.alpha, dL), dmax):
            for xv in (X0, X1):
                if (lin.subs({d: dv, x: xv})) < 0:
                    return False
    return True


def endpoint_room_ok(ell, M, b, s, th: Inputs = PAPER, fr: Frozen = FROZEN) -> bool:
    """Exact check that s >= target + E_*(delta, x) for every delta in [delta_0, delta_max]
    and x in [0, 1/2], with ell, M, b, s rational (the endpoint d = h; `_room_rect_ok`)."""
    return _room_rect_ok(ell, M, b, s, th, fr)


def n_slope_threshold(fr: Frozen = FROZEN):
    """Below this numerator cost a row at d < h may exceed its d = h row (derived).

    Every count is at least 1 - delta (R_* >= 1 - delta, line 16133), so the d-slope
    R + n delta - z_0 is at least (1 - z_0) - (1 - n) delta >= 0 for every delta <= delta_max
    once n >= 1 - (1 - z_0)/delta_max: 26/125 at the paper's z_0 = 17/50, delta_max = 5/6.
    The paper's slope argument (line 16133) is stated at n = 1/2."""
    return 1 - (1 - Fr(fr.z0)) / Fr(fr.delta_max)


def inner_rows_ok(ell, M, b, s, th: Inputs = PAPER, fr: Frozen = FROZEN) -> bool:
    """Exact check of the rows at d < h that the slope argument removes when n is large.

    Each row is affine in d on its range, so its maximum sits at a range end:
    the slot range d in [1/2, h] for delta < alpha (count R_*, line 16128) at d = 1/2;
    the bins delta in [alpha, delta_max] (count 1 - delta at every d <= h, line 16168) at
    d = d_min; the no-slot intermediate rows (count 76/75 - 2 delta/3) and the floor at
    d = d_min.  The d = h ends are the endpoint and floor rows, the d = 1/2 end of the
    intermediate range is its row in `finite_abscissae`."""
    room = s - target(ell, M, b, th)
    dmin = Fr(fr.d_min)
    for dv in int_deltas(th, fr):
        E = high_exponent(dmin, dv, dv / 2, R_intermediate(dv, th, fr), ell, M, b, th, fr)
        if room - E < 0:
            return False
    if room - high_exponent(dmin, Fr(fr.delta0), Fr(fr.delta0) / 2, th.R_fl, ell, M, b, th, fr) < 0:
        return False
    if not _room_rect_ok(ell, M, b, s, th, fr, d_row=Fr(fr.d_int), quad=True, bilin=False):
        return False
    if not _room_rect_ok(ell, M, b, s, th, fr, d_row=dmin, quad=False, bilin=True):
        return False
    # the bin delta = alpha itself, count 1 - alpha (line 16166).  Kept as a guard although it
    # cannot bind while the intermediate range is on: the intermediate row at the same delta
    # and d = d_min has the larger count 76/75 - 2 alpha/3 and q = alpha/2 >= x alpha, so for
    # ell >= 0 it is at least as large, and no test can isolate this block.
    al = Fr(th.alpha)
    if Fr(fr.delta0) <= al <= Fr(fr.delta_max):
        for xv in (Fr(0), Fr(1, 2)):
            if room - high_exponent(dmin, al, xv * al, 1 - al, ell, M, b, th, fr) < 0:
                return False
    return True


def finite_abscissae(ell, M, b, th: Inputs = PAPER, fr: Frozen = FROZEN) -> dict:
    """The abscissa allowed by each finitely-indexed piece at a geometry (exact)."""
    t0 = target(ell, M, b, th)
    out = {"low": t0}
    if fr.lossless == "total":
        out["low_loss"] = t0 + low_loss(ell, M)
    out["floor"] = t0 + E_floor(ell, M, b, th, fr)
    for dv in int_deltas(th, fr):
        out[f"int@{dv}"] = t0 + E_intermediate(dv, ell, M, b, th, fr)
    return out


def achievable_upper(ell, M, b, th: Inputs = PAPER, fr: Frozen = FROZEN, slack=Fr(1, 10**11),
                     inner=None):
    """An exact upper bound on the best abscissa from one geometry, or None if infeasible.

    s = max(finite pieces) + slack; it is returned only when every hard constraint holds
    and the endpoint family fits under s on the whole rectangle (endpoint_room_ok).  The
    rows at d < h are checked too (inner_rows_ok) whenever the numerator cost is below
    n_slope_threshold, where the slope argument no longer removes them; inner=True forces
    that check at any n.
    """
    hs = hard_slacks(ell, M, b, th, fr)
    if any(v < 0 for v in hs.values()):
        return None
    if inner is None:
        inner = Fr(th.n_num) < n_slope_threshold(fr)
    s = max(finite_abscissae(ell, M, b, th, fr).values()) + slack
    for _ in range(8):
        if endpoint_room_ok(ell, M, b, s, th, fr) and (not inner or inner_rows_ok(ell, M, b, s, th, fr)):
            return s
        slack *= 10
        s += slack
    return None


# ------------------------------------------------------- the exact LP sandwich

def _affine(fun):
    """Coefficients (c, a_ell, a_M, a_b) of a function affine in the geometry (exact)."""
    z = Fr(0)
    c = fun(z, z, z)
    return (c, fun(Fr(1), z, z) - c, fun(z, Fr(1), z) - c, fun(z, z, Fr(1)) - c)


def constraint_rows(th: Inputs, fr: Frozen, cuts) -> list[dict]:
    """All rows of the LP over a finite cut set of (delta, x), exact rational coefficients.

    soft rows: sigma >= c + a . (ell, M, b); hard rows: a . (ell, M, b) <= c.
    """
    rows = []

    def soft(tag, fun):
        c, *a = _affine(fun)
        rows.append({"kind": "soft", "tag": tag, "c": c, "a": a})

    def hard(tag, fun):          # fun >= 0  ->  -fun <= 0  ->  a.v <= c with a = -grad, c = fun(0)
        c, *a = _affine(fun)
        rows.append({"kind": "hard", "tag": tag, "c": c, "a": [-v for v in a]})

    soft(("low",), lambda l, M, b: target(l, M, b, th))
    if fr.lossless == "total":
        soft(("low_loss",), lambda l, M, b: target(l, M, b, th) + (1 + 3 * l - 2 * M) / 8)
    soft(("floor",), lambda l, M, b: target(l, M, b, th) + E_floor(l, M, b, th, fr))
    for dv in int_deltas(th, fr):              # delta <= min(alpha, delta_max) only (line 16146)
        soft(("int", dv), lambda l, M, b, dv=dv: target(l, M, b, th)
             + E_intermediate(dv, l, M, b, th, fr))
    for dv, xv in cuts:
        soft(("end", dv, xv), lambda l, M, b, dv=dv, xv=xv: target(l, M, b, th)
             - neg_E_star_closed(dv, xv, l, M, b, th, fr))
    for name in hard_slacks(Fr(0), Fr(0), Fr(0), th, fr):
        hard((name,), lambda l, M, b, name=name: hard_slacks(l, M, b, th, fr)[name])
    return rows


def _solve_fr(A, rhs):
    """Exact Gaussian elimination over Fractions; None if singular."""
    n = len(A)
    Mx = [list(row) + [r] for row, r in zip(A, rhs)]
    for col in range(n):
        piv = next((i for i in range(col, n) if Mx[i][col] != 0), None)
        if piv is None:
            return None
        Mx[col], Mx[piv] = Mx[piv], Mx[col]
        pv = Mx[col][col]
        Mx[col] = [v / pv for v in Mx[col]]
        for i in range(n):
            if i != col and Mx[i][col] != 0:
                f = Mx[i][col]
                Mx[i] = [vi - f * vc for vi, vc in zip(Mx[i], Mx[col])]
    return [Mx[i][n] for i in range(n)]


def _exact_basis(rows, idx):
    """Solve a 4 x 4 basis exactly: dual multipliers y (must be >= 0) and the vertex.

    LP: min sigma s.t. A w <= beta with w = (ell, M, b, sigma).  Any y >= 0 with
    A^T y = -e_sigma gives the valid lower bound -y . beta (weak duality), whatever the
    vertex does elsewhere.
    """
    A = [list(rows[i]["a"]) + [Fr(-1) if rows[i]["kind"] == "soft" else Fr(0)] for i in idx]
    beta = [-rows[i]["c"] if rows[i]["kind"] == "soft" else rows[i]["c"] for i in idx]
    AT = [[A[r][c] for r in range(4)] for c in range(4)]
    y = _solve_fr(AT, [Fr(0), Fr(0), Fr(0), Fr(-1)])
    if y is None or any(v < 0 for v in y):
        return None
    w = _solve_fr(A, beta)
    if w is None:
        return None
    lb = -sum(yi * bi for yi, bi in zip(y, beta))
    return {"lb": lb, "w": w, "y": y, "idx": list(idx)}


def _float_rows(th: Inputs, fr: Frozen, cuts):
    """Float copies of every row for the proposing LP (vectorised over the cut set)."""
    import numpy as np
    exact = constraint_rows(th, fr, [])
    tags = [r["tag"] for r in exact]
    C = [float(r["c"]) for r in exact]
    Aa = [[float(v) for v in r["a"]] for r in exact]
    kinds = [r["kind"] for r in exact]
    if cuts:
        dl = np.array([float(c[0]) for c in cuts])
        xv = np.array([float(c[1]) for c in cuts])
        cM, cP, al, g, zp, nn = (float(getattr(th, n)) for n in ("c_M", "c_P", "alpha", "g", "z_p", "n_num"))
        D = 3 - 2 * xv * (cM + 2 * cP)
        P = (2 - 4 * cP * xv) * (1 - 2 * cM * xv)
        u = np.maximum(al - dl, 0.0)
        J = u * D + dl * P
        K = np.where(u > 0, u * dl * P / np.where(J > 0, J, 1.0), 0.0)
        if fr.counts == "perfect":
            K = 0 * K

        def f(ell, M, b):            # target + E_* = target - (-E_*)
            h = 1 + ell - M / 2 + b / 2
            t0 = 1 - zp * h + g * b / 2
            c0 = 0.5 + ell / 2 - 0.75 * M + b * (0.25 - g / 2)
            return t0 - (-c0 + dl * (ell + b) / 2 - ell * xv * dl - h / 2 * K - h * dl * (nn - 0.5))
        f0 = f(0.0, 0.0, 0.0)
        a1, a2, a3 = f(1.0, 0.0, 0.0) - f0, f(0.0, 1.0, 0.0) - f0, f(0.0, 0.0, 1.0) - f0
        for i, cut in enumerate(cuts):
            tags.append(("end", cut[0], cut[1]))
            C.append(float(f0[i]))
            Aa.append([float(a1[i]), float(a2[i]), float(a3[i])])
            kinds.append("soft")
    return tags, kinds, C, Aa


def _float_lp_arrays(kinds, C, Aa):
    import numpy as np
    from scipy.optimize import linprog
    A, B = [], []
    for k, c, a in zip(kinds, C, Aa):
        if k == "soft":
            A.append(list(a) + [-1.0]); B.append(-c)
        else:
            A.append(list(a) + [0.0]); B.append(c)
    res = linprog(c=[0, 0, 0, 1], A_ub=np.array(A), b_ub=np.array(B),
                  bounds=[(-1, 2), (-1, 2), (-1, 2), (None, None)], method="highs")
    if res.status != 0:
        raise RuntimeError(res.message)
    return res


def _grid(lo, hi, n):
    return [lo + (hi - lo) * Fr(k, n) for k in range(n + 1)]


def default_cuts(th: Inputs, fr: Frozen, n_delta=120, n_x=10):
    ds = _grid(Fr(fr.delta0), Fr(fr.delta_max), n_delta)
    xs = _grid(Fr(0), Fr(1, 2), n_x)
    return [(dv, xv) for dv in ds for xv in xs]


def _refine(tags, duals, cuts, fr: Frozen, scale):
    """Add a local grid around every active endpoint cut (spacing `scale` in delta)."""
    new = set(cuts)
    for t, y in zip(tags, duals):
        if t[0] != "end" or y <= 1e-12:
            continue
        dv, xv = t[1], t[2]
        for k in range(-6, 7):
            for j in range(-3, 4):
                d2 = dv + scale * k
                x2 = xv + scale * 20 * j
                if Fr(fr.delta0) <= d2 <= Fr(fr.delta_max) and 0 <= x2 <= Fr(1, 2):
                    new.add((d2, x2))
    return sorted(new)


def propose(th: Inputs = PAPER, fr: Frozen = FROZEN, rounds=4, n_delta=120):
    """Measured: float LP over a refined cut set.  Returns (sigma, ranked active tags, vertex)."""
    cuts = default_cuts(th, fr, n_delta=n_delta)
    scale = (Fr(fr.delta_max) - Fr(fr.delta0)) / n_delta
    for _ in range(rounds + 1):
        tags, kinds, C, Aa = _float_rows(th, fr, cuts)
        res = _float_lp_arrays(kinds, C, Aa)
        duals = -res.ineqlin.marginals
        scale = scale / 10
        cuts = _refine(tags, duals, cuts, fr, scale)
    slack = res.ineqlin.residual
    order = sorted(range(len(tags)), key=lambda i: (-int(duals[i] > 1e-12), float(slack[i])))
    return float(res.x[3]), [(tags[i], float(duals[i])) for i in order], res.x


def _exact_rows_for(th: Inputs, fr: Frozen, tags):
    """The named rows, each checked to be a member of the constraint family: an endpoint
    row needs delta in [delta_0, delta_max] and x in [0, 1/2], an intermediate row needs
    delta in [delta_0, min(alpha, delta_max)] (line 16146)."""
    cuts = []
    for t in tags:
        if t[0] == "end":
            if not (Fr(fr.delta0) <= t[1] <= Fr(fr.delta_max) and 0 <= t[2] <= Fr(1, 2)):
                raise ValueError(f"endpoint row {t} lies outside the bins")
            cuts.append((t[1], t[2]))
        elif t[0] == "int":
            top = int_top(th, fr)
            if fr.intermediate == "off" or top is None or not (Fr(fr.delta0) <= t[1] <= top):
                raise ValueError(f"intermediate row {t} is not imposed (delta <= alpha, line 16146)")
    want = set(tags)
    rows = [r for r in constraint_rows(th, fr, cuts) if r["tag"] in want]
    have = {r["tag"] for r in rows}
    for t in tags:                      # an intermediate row strictly inside its range
        if t[0] == "int" and t not in have:
            dv = t[1]
            c, *a = _affine(lambda l, M, b, dv=dv: target(l, M, b, th) + E_intermediate(dv, l, M, b, th, fr))
            rows.append({"kind": "soft", "tag": t, "c": c, "a": a})
    return rows


def lower_bound_from(th: Inputs, fr: Frozen, tags) -> dict | None:
    """Exact dual witness built from the named rows only (each a member of the family).

    Tags name ("low",), ("low_loss",), ("floor",), ("int", delta), ("end", delta, x) or a
    hard row such as ("dual_length",).  The best dual-feasible 4-subset gives a bound that
    holds for every geometry; if none of the rows depends on some input, the bound holds
    for every value of that input.
    """
    rows = _exact_rows_for(th, fr, tags)
    best = None
    for idx in itertools.combinations(range(len(rows)), 4):
        sol = _exact_basis(rows, idx)
        if sol is not None and (best is None or sol["lb"] > best["lb"]):
            best = sol
    if best is None:
        return None
    return {"lb": best["lb"], "rows": [rows[i]["tag"] for i in best["idx"]], "y": best["y"],
            "w": best["w"]}


def _round_geometry(w, q=10**13):
    ell, M, b = w[:3]
    lr = Fr(round(ell * q), q)
    br = Fr(round(b * q), q) if b != 0 else Fr(0)
    Mr = 1 - lr if M + ell == 1 else Fr(round(M * q), q)
    return lr, Mr, br


def sandwich(th: Inputs = PAPER, fr: Frozen = FROZEN, rounds=4, upper=True, top=9) -> dict:
    """Exact bracket [lb, ub] of the best abscissa of the assembly at rational inputs.

    lb: an exact dual witness from rows the float LP marks active (valid for every
    geometry).  ub: the witness's vertex, rounded to a rational geometry, checked over
    the whole (delta, x) rectangle by endpoint_room_ok.  The float LP only proposes.
    """
    fsig, ranked, _ = propose(th, fr, rounds)
    tags = [t for t, _ in ranked[:top]]
    cert = lower_bound_from(th, fr, tags)
    if cert is None:
        raise RuntimeError("no exact dual-feasible basis among the active rows")
    out = {"lb": cert["lb"], "basis": cert["rows"], "y": cert["y"], "w": cert["w"],
           "float_sigma": fsig, "active": [t for t, y in ranked if y > 1e-12]}
    if upper:
        ub = None
        for geo in (_round_geometry(cert["w"]), tuple(cert["w"][:3])):
            ub = achievable_upper(*geo, th, fr)
            if ub is not None:
                out["ub_geometry"] = geo
                break
        out["ub"] = ub
    return out


# ---------------------------------------------------------------- the paths

def with_input(name, value, th: Inputs = PAPER) -> Inputs:
    return replace(th, **{name: Fr(value)})


def regime_A_on_axis(name, value, fr: Frozen = FROZEN):
    th = with_input(name, value)
    sol = regime_A(th, fr)
    return th, sol, (None if sol is None else regime_A_slacks(sol, th, fr))


def _bisect(pred, good, bad, tol):
    """pred(good) and not pred(bad); shrink the bracket to width tol on rationals."""
    while abs(bad - good) > tol:
        mid = (good + bad) / 2
        if pred(mid):
            good = mid
        else:
            bad = mid
    return good, bad


def regime_A_break(name, fr: Frozen = FROZEN, step=Fr(1, 1000), tol=Fr(1, 10**10), max_steps=3000):
    """Walk input `name` alone from the paper's value in its helpful direction while
    regime A holds.  Returns (v_ok, v_bad, failing): every regime-A condition holds at
    v_ok, and at v_bad the conditions named in `failing` are negative.  Exact."""
    v0 = Fr(getattr(PAPER, name))
    sgn = HELPS[name]

    def ok(v):
        _, sol, sl = regime_A_on_axis(name, v, fr)
        return sol is not None and all(x >= 0 for x in sl.values())
    prev = v0
    for k in range(1, max_steps):
        v = v0 + sgn * step * k
        if not ok(v):
            break
        prev = v
    else:
        return prev, None, []
    good, bad = _bisect(ok, prev, v, tol)
    _, sol, sl = regime_A_on_axis(name, bad, fr)
    failing = ["no regime-A root"] if sol is None else sorted(k for k, x in sl.items() if x < 0)
    return good, bad, failing


def regime_A_crossing(name, level, v_end, fr: Frozen = FROZEN, tol=Fr(1, 10**12)):
    """Exact bracket (v_above, v_below) where sigma_A crosses `level` between the paper's
    value and v_end (both inside regime A), or None if it does not cross there."""
    v0 = Fr(getattr(PAPER, name))

    def above(v):
        return regime_A(with_input(name, v), fr)["sigma"] > level
    if not above(v0) or above(v_end):
        return None
    return _bisect(above, v0, Fr(v_end), tol)


def float_crossing(name, level, v_from, v_to, fr: Frozen = FROZEN, tol=1e-9, rounds=3):
    """Measured: bisection on the float LP between v_from (abscissa above `level`) and
    v_to (below it), in either direction.  Returns (v_above, v_below) or None."""
    a, z = float(v_from), float(v_to)
    f = lambda v: propose(with_input(name, Fr(v).limit_denominator(10**12)), fr, rounds)[0]
    if f(a) <= level or f(z) > level:
        return None
    while abs(z - a) > tol:
        mid = (a + z) / 2
        if f(mid) > level:
            a = mid
        else:
            z = mid
    return a, z


def verified_crossing(name, level, v_from, v_to, fr: Frozen = FROZEN, pad=Fr(1, 10**7)):
    """Exact bracket of the input value needed to reach `level`, from two witnesses:
    a dual witness above `level` at v_a and a feasible geometry below it at v_b.
    The float LP only locates the crossing."""
    fc = float_crossing(name, level, v_from, v_to, fr)
    if fc is None:
        return None
    sgn = HELPS[name]
    va = Fr(fc[0]).limit_denominator(10**9) - sgn * pad
    vb = Fr(fc[1]).limit_denominator(10**9) + sgn * pad
    swa = sandwich(with_input(name, va), fr, upper=False)
    swb = sandwich(with_input(name, vb), fr)
    ok = swa["lb"] > level and swb["ub"] is not None and swb["ub"] < level
    return {"va": va, "vb": vb, "ok": ok, "lb_a": swa["lb"], "ub_b": swb["ub"],
            "cert_a": swa["basis"], "geo_b": swb.get("ub_geometry")}


# ------------------------------------------------- capacity tied to the target

def tied_capacity_fixed_point(fr: Frozen = FROZEN, tol=Fr(1, 10**18)):
    """Regime A with the plain capacity tied to the target, c_P = 1/(6 kappa_0),
    kappa_0 = 2 sigma - 1, the dynamic value of line 15100 carried below kappa = 3/4.

    Lemma plain is stated for kappa in [3/4, 1] (line 12532), so this uses the lemma
    outside its stated range (inferred to be harmless near 3/4 by hunt #134).  The fixed
    point solves F(s) = sigma_A(c_P(s)) - s = 0 with F decreasing; the bracket is exact.
    """
    def above(sv):        # F(s) > 0 means the fixed point lies above s
        th = replace(PAPER, c_P=1 / (6 * (2 * sv - 1)))
        return regime_A(th, fr)["sigma"] > sv
    lo, hi = Fr(874957, 10**6), Fr(874958, 10**6)
    assert above(lo) and not above(hi)
    return _bisect(above, lo, hi, tol)


# ------------------------------------------------ exact vertices of other regimes

def _sigma_end_sym(dl, x, ell, M, b, th: Inputs):
    """target + E_*(delta, x) with K written out (no branch), for symbolic delta."""
    h = geometry(ell, M, b)[2]
    return (target(ell, M, b, th)
            - (-C0(ell, M, b, th) + dl * (ell + b) / 2 - ell * x * dl - h / 2 * K_formula(dl, x, th)
               - h * dl * (th.n_num - Fr(1, 2))))


def solve_vertex(th: Inputs, fr: Frozen, tags, end_x=None, dps=40) -> list[dict]:
    """Exact optimum candidates for a named active set (derived).

    `tags` name the active rows besides the endpoint family (soft rows such as ("low",),
    ("floor",), ("int", delta); hard rows such as ("dual_length",), ("gram",)).  With
    end_x set, one endpoint tangency at that x joins them: sigma = target + E_*(delta, x)
    and its delta-derivative vanishes.  The geometry is linear in the rows, so it is
    solved in terms of delta and the tangency leaves one univariate polynomial whose real
    roots in (delta_0, min(alpha, delta_max)) are isolated exactly (sympy CRootOf).
    Without end_x the rows must be four and the vertex is rational.
    """
    sp = _sp()
    l, M, b, sg, d = sp.symbols("ell M b sigma delta")
    R = lambda v: sp.Rational(Fr(v).numerator, Fr(v).denominator)
    rows = _exact_rows_for(th, fr, list(tags))
    eqs = []
    for r in rows:
        av = R(r["a"][0]) * l + R(r["a"][1]) * M + R(r["a"][2]) * b
        # soft: sigma = c + a.v ; hard (a.v <= c) active: a.v = c
        eqs.append(sp.Eq(R(r["c"]) + av, sg) if r["kind"] == "soft" else sp.Eq(av, R(r["c"])))
    thr = Inputs(*(R(getattr(th, n)) for n in INPUT_NAMES))
    out = []
    if end_x is None:
        sol = sp.solve(eqs, [l, M, b, sg], dict=True)
        for so in sol:
            out.append({k: so[v] for k, v in (("ell", l), ("M", M), ("b", b), ("sigma", sg))})
        return out
    xx = R(end_x)
    send = _sigma_end_sym(d, xx, l, M, b, thr)
    lin = sp.solve(eqs + [sp.Eq(send, sg)], [l, M, b, sg], dict=True)
    if not lin:
        return out
    lin = lin[0]
    dsend = sp.diff(send, d).subs(lin)
    num = sp.numer(sp.together(dsend))
    poly = sp.Poly(sp.expand(num), d)
    lo, hi = R(fr.delta0), min(R(fr.delta_max), thr.alpha)
    for root in poly.real_roots():
        if not (lo < root < hi):
            continue
        vals = {k: lin[v].subs(d, root) for k, v in (("ell", l), ("M", M), ("b", b), ("sigma", sg))}
        vals["delta"] = root
        vals["float"] = {k: sp.N(v, dps) for k, v in vals.items()}
        out.append(vals)
    return out


def regime_vertex_sigma(th: Inputs, fr: Frozen, tags, end_x=None, dps=40):
    """The smallest sigma among exact vertex candidates of the active set, as an mpf string."""
    cands = solve_vertex(th, fr, tags, end_x, dps)
    if not cands:
        return None
    sp = _sp()
    vals = sorted(cands, key=lambda c: sp.N(c["sigma"], dps))
    return vals[0]


# -------------------------------------------------------------- ceilings

#: rows that involve none of c_M, c_P, alpha: the low side, the row-norm loss, the floor
#: bin (count R_fl, no zero witness), the dual length and b >= 0
ROW_INPUT_FREE_TAGS = [("low",), ("low_loss",), ("floor",), ("dual_length",), ("b_nonneg",)]


def ceiling_row_inputs(fr: Frozen = FROZEN) -> dict:
    """A lower bound valid for every value of c_M, c_P and alpha at once (derived).

    None of its rows involves the moment capacities or the amplification slope, so the
    dual witness bounds the assembly for any row-count inputs: 167/192 at the paper's
    floor.  (The intermediate row is not among them: it is imposed at delta = min(alpha,
    delta_max), line 16146, so it moves with alpha.)"""
    return lower_bound_from(PAPER, fr, ROW_INPUT_FREE_TAGS)


def four_row_tags(th: Inputs = PAPER, fr: Frozen = FROZEN) -> list:
    """low, floor, the intermediate row at the top of its range, dual length."""
    top = int_top(th, fr)
    tags = [("low",), ("floor",), ("dual_length",)]
    if top is not None and fr.intermediate != "off":
        tags.insert(2, ("int", top))
    return tags


def ceiling_four_rows(th: Inputs = PAPER, fr: Frozen = FROZEN) -> dict:
    """The bound from the four rows low, floor, intermediate at its top, dual length.

    At alpha >= delta_max the intermediate row sits at delta_max and none of the four
    rows involves c_M or c_P: 84031/96156 for every (c_M, c_P) and every alpha >= 5/6
    (derived).  Below alpha = delta_max the row sits at delta = alpha and weakens.  With
    the bin ceiling at the dynamic 3/4 instead of 5/6 the same rows give 368153/422028."""
    return lower_bound_from(th, fr, four_row_tags(th, fr))


def ceiling_no_intermediate(delta0=Fr(1, 50)) -> dict:
    """The intermediate range dropped (inferred relaxation) and the floor at delta_0:
    rows low, low_loss, floor, dual_length, b_nonneg (the same rows as ceiling_row_inputs)."""
    fr = Frozen(delta0=delta0, intermediate="off")
    return lower_bound_from(PAPER, fr, ROW_INPUT_FREE_TAGS)


def x0_tangency(fr: Frozen = FROZEN, th: Inputs = PAPER):
    """The vertex where rows with no prime amplitude (x = 0) and the intermediate range
    bind together; at x = 0 the counts do not involve c_M or c_P (P_0 = 2, D_0 = 3)."""
    return regime_vertex_sigma(th, fr, [("low",), ("int", int_top(th, fr)), ("dual_length",)], end_x=Fr(0))


def ceiling_capacities(fr: Frozen = FROZEN, width=Fr(1, 10**7)) -> dict:
    """A lower bound valid for every c_M and c_P (alpha = 5/6): the x = 0 endpoint rows
    bracketing the tangency, the intermediate range, the low side and the dual length."""
    v = x0_tangency(fr)
    sp = _sp()
    dv = Fr(str(sp.N(v["delta"], 30))).limit_denominator(10**12)
    tags = [("low",), ("end", dv - width, Fr(0)), ("end", dv + width, Fr(0)),
            ("int", int_top(PAPER, fr)), ("dual_length",)]
    out = lower_bound_from(PAPER, fr, tags)
    out["vertex"] = v
    return out


def marked_width_cM_max(th: Inputs = PAPER):
    """Largest c_M for which Lemma marked's second width condition holds (derived).

    Lemma marked (line 9254) needs r + 2z <= m - c_1 and 2r + 8z <= 3m - c_2; the paper
    uses z_M only where the second also has a fixed margin (line 15183).  The model carries
    only the first, as z_M(r) = c_M (1 - r) with m = 1.  The requested r runs over
    [min_x r_*(1, x), 1] (r_* increases in t, r_*(3/2) = 1), and r_*(1, x) is monotone in x,
    so its least value sits at x = 0 (r = 2/3) or x = 1/2 (r = (2 - c_P - c_M)/(3 - c_M - 2 c_P)).
    2r + 8 c_M (1 - r) - 3 is affine in r and equals -1 at r = 1, so the condition holds on
    the whole range iff it holds at both ends in x: c_M <= 5/8 (x = 0) and
    c_M <= (5 - 4 c_P)/(9 - 8 c_P) (x = 1/2).  37/65 at c_P = 2/9."""
    cP = Fr(th.c_P)
    return min(Fr(5, 8), (5 - 4 * cP) / (9 - 8 * cP))


def marked_width_excess(th: Inputs = PAPER):
    """max of 2r + 8 z_M(r) - 3 over the requested r (the ends x = 0, x = 1/2 at t = 1, and
    r = 1): must be negative for Lemma marked's second width condition (exact)."""
    cM = Fr(th.c_M)
    return max(2 * r + 8 * cM * (1 - r) - 3
               for r in (r_cross(Fr(1), Fr(0), th), r_cross(Fr(1), Fr(1, 2), th), Fr(1)))


# ------------------------------------------------------------- the report

AXES = ("z_p", "n_num", "g", "c_M", "alpha", "c_P")
LEVELS = {"xu_sang": XU_SANG, "0.87": TARGET_087, "13/15": THIRTEEN_FIFTEENTHS}

#: the regimes past the first break, as active sets for solve_vertex (from propose; each
#: is then solved exactly and checked by sandwich witnesses)
NEXT_REGIME = {
    "z_p": ([("low",), ("floor",), ("dual_length",)], Fr(1, 2)),
    "g": ([("low",), ("floor",), ("dual_length",)], Fr(1, 2)),
    # regime B (b = 0); the generic solver is a second route to `regime_B`'s closed form
    "alpha": ([("low",), ("dual_length",), ("b_nonneg",)], Fr(1, 2)),
}


def mpf_of(v, dps=40):
    from mpmath import mp, mpf
    with mp.workdps(dps):
        if isinstance(v, QF):
            return v.mp(dps)
        if isinstance(v, Fr):
            return mpf(v.numerator) / v.denominator
        import sympy as sp
        return mpf(str(sp.N(v, dps)))


def vertex_on_axis(name, value, fr: Frozen = FROZEN):
    """Exact vertex of the regime that follows regime A on this axis (NEXT_REGIME)."""
    tags, x = NEXT_REGIME[name]
    return regime_vertex_sigma(with_input(name, value), fr, tags, end_x=x)


def vertex_crossing(name, level, v_from, v_to, fr: Frozen = FROZEN, tol=Fr(1, 10**10)):
    """Bisection on the exact next-regime vertex (sigma decided to 40 digits) for `level`."""
    sp = _sp()

    def above(v):
        return sp.N(vertex_on_axis(name, v, fr)["sigma"], 40) > sp.Rational(level.numerator, level.denominator)
    if not above(Fr(v_from)) or above(Fr(v_to)):
        return None
    return _bisect(above, Fr(v_from), Fr(v_to), tol)


def per_summand_control() -> dict:
    """The paper's own bookkeeping (every rescaled summand lossless): the best abscissa of
    the assembly with the paper's inputs is exactly 7/8.  Lower end: a dual witness;
    upper end: the paper's geometry (1/6, 5/6, 1/8), checked on the whole rectangle."""
    fr = FROZEN_PAPER_BOOKKEEPING
    sw = sandwich(PAPER, fr, upper=False)
    ub = achievable_upper(ELL_PAPER, M_PAPER, B_PAPER, PAPER, fr, slack=Fr(0))
    return {"lb": sw["lb"], "basis": sw["basis"], "ub": ub}


def root_QF(poly, lo, hi):
    """The real root of a rational sympy Poly in (lo, hi) as an exact QF, if its
    irreducible factor has degree at most 2 (None otherwise)."""
    sp = _sp()
    _, facs = poly.factor_list()
    for f, _m in facs:
        cs = [Fr(int(sp.numer(c)), int(sp.denom(c))) for c in f.all_coeffs()]
        if f.degree() == 1:
            r = QF(-cs[1] / cs[0], 0, 1)
            if Fr(lo) < r < Fr(hi):
                return r
        elif f.degree() == 2:
            a2, a1, a0 = cs
            disc = a1 * a1 - 4 * a2 * a0
            if disc < 0:
                continue
            for sg in (1, -1):
                r = QF(-a1 / (2 * a2), Fr(sg) / (2 * a2), disc)
                if Fr(lo) < r < Fr(hi):
                    return r
    return None


def floor_vertex_QF(th: Inputs = PAPER, fr: Frozen = FROZEN) -> dict:
    """The vertex where the floor bin and the endpoint tangency at x = 1/2 meet, exact.

    On M = 1 - ell: the floor line F0 + F_ell ell + F_b b = 0, the endpoint
    A + A_ell ell + A_b b = 0 and its delta-derivative.  (ell, b) are linear in the first
    two; the third leaves a polynomial in delta whose root is taken in Q(sqrt d).
    """
    sp = _sp()
    d = sp.Symbol("delta")
    R = lambda v: sp.Rational(Fr(v).numerator, Fr(v).denominator)
    thr = Inputs(*(R(getattr(th, n)) for n in INPUT_NAMES))
    l, b = sp.symbols("ell b")
    negE = neg_E_star_closed_sym(d, sp.Rational(1, 2), l, 1 - l, b, thr)
    flo = E_floor(l, 1 - l, b, thr, fr)
    lin = sp.solve([sp.Eq(negE, 0), sp.Eq(flo, 0)], [l, b], dict=True)[0]
    tang = sp.diff(negE, d).subs(lin)
    poly = sp.Poly(sp.expand(sp.numer(sp.together(tang))), d)
    dl = root_QF(poly, fr.delta0, min(Fr(fr.delta_max), Fr(th.alpha)))
    if dl is None:
        return None
    # back-substitute exactly in Q(sqrt d): solve the two linear equations at delta = dl
    K = K_formula(dl, Fr(1, 2), th)
    nu = Fr(th.n_num) - Fr(1, 2)
    A = (1 - K) / 4 - dl * nu / 2
    Al = -(5 + 3 * K) / 4 - 3 * dl * nu / 2
    Ab = -Fr(1, 4) + Fr(th.g) / 2 + dl / 2 - K / 4 - dl * nu / 2
    f0 = E_floor(Fr(0), Fr(1), Fr(0), th, fr)
    fl = E_floor(Fr(1), Fr(0), Fr(0), th, fr) - f0
    fb = E_floor(Fr(0), Fr(1), Fr(1), th, fr) - f0
    det = Al * fb - Ab * fl
    ell = (-A * fb + Ab * f0) / det
    bb = (-Al * f0 + A * fl) / det
    h = geometry(ell, 1 - ell, bb)[2]
    return {"delta": dl, "ell": ell, "b": bb, "h": h, "M": 1 - ell,
            "const": 1 + Fr(th.g) * bb / 2}


def neg_E_star_closed_sym(dl, x, ell, M, b, th: Inputs):
    """-E_* with K written out, for symbolic delta."""
    h = geometry(ell, M, b)[2]
    return (-C0(ell, M, b, th) + dl * (ell + b) / 2 - ell * x * dl - h / 2 * K_formula(dl, x, th)
            - h * dl * (th.n_num - Fr(1, 2)))


def zp_floor_regime(fr: Frozen = FROZEN) -> dict:
    """Past z_p's first break the optimum is the floor vertex.  Neither the floor nor the
    endpoint involves z_p (both are measured against the matched target), so the vertex
    is fixed and sigma(z_p) = (1 + g b_v/2) - z_p h_v is affine, exact in Q(sqrt 22829)."""
    v = floor_vertex_QF(PAPER, fr)
    return dict(v, z_13_15=(v["const"] - THIRTEEN_FIFTEENTHS) / v["h"])


def g_supply_regime():
    """The last regime on the g axis: low side, floor bin, dual length and the supply
    hypothesis active together.  All four are affine, so sigma(g) is rational in g."""
    sp = _sp()
    g = sp.Symbol("g")
    l, M, b, sg = sp.symbols("ell M b sigma")
    th = Inputs(g=g)
    hs = hard_slacks(l, M, b, th, FROZEN)
    eqs = [sp.Eq(target(l, M, b, th), sg),
           sp.Eq(target(l, M, b, th) + E_floor(l, M, b, th, FROZEN), sg),
           sp.Eq(hs["dual_length"], 0), sp.Eq(hs["supply"], 0)]
    sol = sp.solve(eqs, [l, M, b, sg], dict=True)[0]
    sig = sp.factor(sp.simplify(sol[sg]))
    g1315 = sp.solve(sp.Eq(sig, sp.Rational(13, 15)), g)
    return {"sigma_of_g": sig, "g_13_15": g1315[0], "geometry": sol}


def g_gram_regime():
    """The middle regime on the g axis: low side, floor bin, dual length and the Gram
    condition b(3 - 2g) = M - 2 ell active together; sigma(g) is rational in g."""
    sp = _sp()
    g = sp.Symbol("g")
    l, M, b, sg = sp.symbols("ell M b sigma")
    th = Inputs(g=g)
    hs = hard_slacks(l, M, b, th, FROZEN)
    eqs = [sp.Eq(target(l, M, b, th), sg),
           sp.Eq(target(l, M, b, th) + E_floor(l, M, b, th, FROZEN), sg),
           sp.Eq(hs["dual_length"], 0), sp.Eq(hs["gram"], 0)]
    sol = sp.solve(eqs, [l, M, b, sg], dict=True)[0]
    # where the supply hypothesis starts to bind along this vertex
    sup = sp.together(hard_slacks(sol[l], sol[M], sol[b], th, FROZEN)["supply"])
    g_sup = [r for r in sp.solve(sp.numer(sup), g) if 0 < r < sp.Rational(1, 6)]
    return {"sigma_of_g": sp.factor(sp.simplify(sol[sg])), "geometry": sol, "g_supply": g_sup}


def floor_vertex_multipliers(th: Inputs = PAPER, fr: Frozen = FROZEN) -> dict | None:
    """KKT multipliers of the floor vertex (low, floor, endpoint at delta_v, dual length),
    exact in Q(sqrt d): sum of soft multipliers 1, gradient in (ell, M, b) zero."""
    v = floor_vertex_QF(th, fr)
    if v is None:
        return None
    dl = v["delta"]
    fns = [lambda l, M, b: target(l, M, b, th),
           lambda l, M, b: target(l, M, b, th) + E_floor(l, M, b, th, fr),
           lambda l, M, b: target(l, M, b, th) - neg_E_star_closed(dl, Fr(1, 2), l, M, b, th, fr)]
    grads = [_affine(f)[1:] for f in fns]
    dual = (Fr(1), Fr(1), Fr(0))                       # gradient of ell + M - 1 <= 0
    # unknowns (lam_low, lam_floor, lam_end, nu): sum lam_i grad_i + nu dual = 0, sum lam = 1
    A = [[grads[0][k], grads[1][k], grads[2][k], dual[k]] for k in range(3)] + [[1, 1, 1, 0]]
    rhs = [0, 0, 0, 1]
    lam = _solve_fr(A, rhs)
    return {"low": lam[0], "floor": lam[1], "end": lam[2], "nu": lam[3], "vertex": v}


def g_floor_to_gram(lo=Fr(5, 100), hi=Fr(1567, 10**4), tol=Fr(1, 10**10)):
    """Where the floor vertex stops being optimal on the g axis: the endpoint multiplier
    reaches zero and the optimum slides along the floor line to the Gram condition.
    Exact multiplier signs in Q(sqrt d) at each bisection step."""
    def end_active(gv):
        m = floor_vertex_multipliers(with_input("g", gv), FROZEN)
        return m is not None and m["end"] > 0
    if not end_active(hi) or end_active(lo):
        return None
    return _bisect(end_active, hi, lo, tol)


def zp_floor_vertex_end(lo=Fr(18, 100), hi=Fr(4, 10), tol=Fr(1, 10**10)):
    """Where the floor vertex stops being optimal on the z_p axis (endpoint multiplier 0)."""
    def end_active(z):
        m = floor_vertex_multipliers(with_input("z_p", z), FROZEN)
        return m is not None and m["end"] > 0
    return _bisect(end_active, Fr(lo), Fr(hi), tol)


def capacity_envelope(name="c_M", fr: Frozen = FROZEN, lo=Fr(5362, 10**4), hi=Fr(545, 1000), n=36):
    """Measured: a stronger capacity can always be used as a weaker one, so the abscissa
    along c_M (or c_P) is the running minimum of the fixed-capacity optimum.  Under the
    uniform supply hypothesis the fixed-capacity optimum rises once the supply binds;
    this scans it on a grid and returns (c, sigma) at the grid minimum, then an exact
    upper end at that c from a checked geometry."""
    best = None
    for k in range(n + 1):
        c = lo + (hi - lo) * Fr(k, n)
        try:
            sg = propose(with_input(name, c), fr, rounds=3)[0]
        except RuntimeError:
            continue
        if best is None or sg < best[1]:
            best = (c, sg)
    sw = sandwich(with_input(name, best[0]), fr)
    return {"c": best[0], "float_sigma": best[1], "lb": sw["lb"], "ub": sw["ub"],
            "geo": sw.get("ub_geometry")}


def n_num_regimes():
    """The regimes past regime A on the numerator axis (derived): first the floor and the
    intermediate range bind together (all rows affine, sigma rational in n), then the floor
    and b >= 0.  The floor rows weaken as n falls, so the n = 0 dual witness from rows
    low, floor, dual length and b >= 0 bounds the abscissa for every n >= 0."""
    sp = _sp()
    n = sp.Symbol("n")
    l, M, b, sg = sp.symbols("ell M b sigma")
    th = Inputs(n_num=n)
    hs = hard_slacks(l, M, b, th, FROZEN)
    low = target(l, M, b, th)
    fl = low + E_floor(l, M, b, th, FROZEN)
    it = low + E_intermediate(sp.Rational(5, 6), l, M, b, th, FROZEN)
    s1 = sp.solve([sp.Eq(low, sg), sp.Eq(fl, sg), sp.Eq(it, sg), sp.Eq(hs["dual_length"], 0)],
                  [l, M, b, sg], dict=True)[0]
    s2 = sp.solve([sp.Eq(low, sg), sp.Eq(fl, sg), sp.Eq(hs["b_nonneg"], 0), sp.Eq(hs["dual_length"], 0)],
                  [l, M, b, sg], dict=True)[0]
    sig1 = sp.factor(sp.simplify(s1[sg]))
    n087 = [r for r in sp.solve(sp.Eq(sig1, sp.Rational(87, 100)), n) if 0 < r < sp.Rational(1, 2)]
    nb0 = [r for r in sp.solve(sp.numer(sp.together(s1[b])), n) if 0 < r < sp.Rational(1, 2)]
    cert0 = lower_bound_from(Inputs(n_num=Fr(0)), FROZEN, [("low",), ("floor",), ("dual_length",), ("b_nonneg",)])
    return {"floor_int_sigma": sig1, "n_087": n087[0], "floor_int_b0_at": nb0[0],
            "floor_b0_sigma": sp.factor(sp.simplify(s2[sg])), "ceiling_all_n": cert0["lb"]}


def regime_A_formula_row_inputs(th: Inputs = PAPER):
    """The closed form of regime A when g = z_p = 1/6 (only c_M, c_P, alpha vary).

    rho = D/P = (3 - c_M - 2 c_P)/((2 - 2 c_P)(1 - c_M)); delta_* is the root in (0, alpha) of
    (3 - 2 rho) d^2 + (2 rho alpha - alpha - 2/3 + 2 rho/3) d - 2 rho alpha/3 = 0, and
    sigma = 11/12 - (5 - 6 delta_*)/(36 (1 + 2 delta_*)).  Returns (rho, coefficients, sigma).
    """
    cM, cP, al = Fr(th.c_M), Fr(th.c_P), Fr(th.alpha)
    rho = (3 - cM - 2 * cP) / ((2 - 2 * cP) * (1 - cM))
    A2, A1, A0 = 3 - 2 * rho, 2 * rho * al - al - Fr(2, 3) + 2 * rho / 3, -2 * rho * al / 3
    disc = A1 * A1 - 4 * A2 * A0
    roots = [QF(-A1 / (2 * A2), Fr(sg) / (2 * A2), disc) for sg in (1, -1)]
    dl = [r for r in roots if 0 < r < al][0]
    return rho, (A2, A1, A0), Fr(11, 12) - (5 - 6 * dl) / (36 * (1 + 2 * dl))


def report(fr: Frozen = FROZEN, verify=True, out=print) -> dict:
    """Everything the lane states, recomputed (a few minutes with verify=True)."""
    sp = _sp()
    res = {}
    base = regime_A(PAPER, fr)
    res["optimum"] = base
    out(f"optimum at the paper's inputs ({fr.lossless} accounting): sigma = {base['sigma'].pretty()}"
        f" = {mpf_of(base['sigma'])}")
    out(f"  delta_* = {base['delta'].pretty()}, ell = {float(base['ell']):.10f}, b = {float(base['b']):.10f},"
        f" h = {float(base['h']):.10f}, mu = {float(base['mu']):.10f}, nu = {float(base['nu']):.10f}")
    tl, th_ = tied_capacity_fixed_point(fr)
    res["tied"] = (tl, th_)
    from mpmath import nstr
    out(f"capacity tied to the target: sigma in [{nstr(mpf_of(tl, 30), 22)}, {nstr(mpf_of(th_, 30), 22)}]"
        f" (Guo 0.8749570194)")
    sh = regime_A_shadow_prices(base)
    res["shadow"] = sh
    ranked = sorted(sh, key=lambda k: -abs(float(sh[k])))
    res["ranking"] = ranked
    for k in ranked:
        el = Fr(getattr(PAPER, k)) * sh[k]
        out(f"  shadow d sigma/d {k:5s} = {float(sh[k]):+.10f}  elasticity {float(el):+.6f}  ({sh[k].pretty()})")
    res["breaks"], res["crossings"] = {}, {}
    for name in AXES:
        ok, bad, failing = regime_A_break(name, fr)
        sA = regime_A(with_input(name, ok), fr)["sigma"]
        res["breaks"][name] = (ok, bad, failing, sA)
        out(f"{name}: regime A holds up to {float(ok):.10f}; next active: {failing};"
            f" sigma there {float(sA):.10f}")
        for lab, lev in LEVELS.items():
            if sA < lev:
                cr = regime_A_crossing(name, lev, ok, fr)
                res["crossings"][(name, lab)] = ("A", cr)
                out(f"   reach {lab}: {name} in ({float(cr[0]):.12f}, {float(cr[1]):.12f}) [regime A]")
    ps = per_summand_control()
    res["per_summand"] = ps
    out(f"paper's own bookkeeping: abscissa in [{ps['lb']}, {ps['ub']}]")
    cf = ceiling_row_inputs(fr)
    res["ceiling_row_inputs"] = cf
    out(f"ceiling for every (c_M, c_P, alpha): {cf['lb']} = {float(cf['lb']):.10f} rows {cf['rows']}")
    c4 = ceiling_four_rows(PAPER, fr)
    c4b = ceiling_four_rows(PAPER, replace(fr, delta_max=Fr(3, 4)))
    res["ceiling_four_rows"] = (c4, c4b)
    out(f"four rows (low, floor, intermediate at its top, dual length): {c4['lb']} at alpha >= 5/6;"
        f" with the bin ceiling at 3/4: {c4b['lb']} = {float(c4b['lb']):.10f}")
    af, ab = regime_B_ends()
    a87 = regime_B_level(TARGET_087)
    res["alpha_regime_B"] = (af, ab, a87)
    out(f"alpha: regime B (b = 0) from alpha = {ab.pretty()} = {float(ab):.10f} down to"
        f" {af.pretty()} = {float(af):.10f} (then 167/192); 0.87 at alpha = {a87.pretty()} = {float(a87):.10f}")
    cc = ceiling_capacities(fr)
    res["ceiling_capacities"] = cc
    out(f"ceiling for every (c_M, c_P), alpha = 5/6: {float(cc['lb']):.12f}; x = 0 vertex"
        f" {sp.N(cc['vertex']['sigma'], 20)} at delta {sp.N(cc['vertex']['delta'], 15)}")
    for d0 in (Fr(1, 50), Fr(0)):
        ci = ceiling_no_intermediate(d0)
        res[("ceiling_no_intermediate", d0)] = ci
        out(f"intermediate dropped, floor delta_0 = {d0}: ceiling {ci['lb']} = {float(ci['lb']):.10f}")
    zf = zp_floor_regime(fr)
    res["zp_floor"] = zf
    out(f"z_p floor regime: sigma(z_p) = ({zf['const'].pretty()}) - z_p ({zf['h'].pretty()});"
        f" delta_v = {zf['delta'].pretty()}; z_p for 13/15 = {zf['z_13_15'].pretty()}"
        f" = {float(zf['z_13_15']):.12f}")
    gfg = g_floor_to_gram()
    res["g_floor_to_gram"] = gfg
    gg = g_gram_regime()
    res["g_gram"] = gg
    gs = g_supply_regime()
    res["g_supply"] = gs
    out(f"g: the floor vertex stops at g in ({float(gfg[1]):.10f}, {float(gfg[0]):.10f}) (endpoint multiplier 0);"
        f" Gram regime sigma(g) = {gg['sigma_of_g']}, supply binds there at g = {gg['g_supply']}")
    nr = n_num_regimes()
    res["n_num"] = nr
    out(f"n_num: floor-and-intermediate regime sigma(n) = {nr['floor_int_sigma']}, 0.87 at n = {nr['n_087']}"
        f" = {sp.N(nr['n_087'], 12)}; b reaches 0 at n = {sp.N(nr['floor_int_b0_at'], 12)}; then sigma(n) ="
        f" {nr['floor_b0_sigma']}; every n >= 0 stays above {nr['ceiling_all_n']}")
    zfe = zp_floor_vertex_end()
    res["zp_floor_end"] = zfe
    out(f"z_p: the floor vertex stops at z_p in ({float(zfe[0]):.10f}, {float(zfe[1]):.10f})")
    out(f"g supply regime: sigma(g) = {gs['sigma_of_g']}, 13/15 at g = {gs['g_13_15']}")
    if verify:
        for name, lev, a, z in (("n_num", TARGET_087, Fr(45, 100), Fr(35, 100)),
                                ("z_p", THIRTEEN_FIFTEENTHS, Fr(17515, 10**5), Fr(19, 100)),
                                ("g", TARGET_087, Fr(1567, 10**4), Fr(5, 100)),
                                ("g", THIRTEEN_FIFTEENTHS, Fr(1, 10), Fr(0))):
            vc = verified_crossing(name, lev, a, z, fr)
            res["crossings"][(name, str(lev))] = ("verified", vc)
            out(f"   reach {lev}: {name} in ({float(vc['va']):.10f}, {float(vc['vb']):.10f}) ok={vc['ok']}"
                f" witness {vc['cert_a']}")
        env = capacity_envelope("c_M", fr)
        res["cM_envelope"] = env
        out(f"c_M under the uniform supply hypothesis: grid minimum at c_M = {float(env['c']):.6f},"
            f" abscissa in [{float(env['lb']):.10f}, {float(env['ub']):.10f}]")
        froff = replace(fr, supply="off")
        bo = regime_A_break("c_M", froff)
        res["cM_supply_off_break"] = bo
        out(f"c_M with the supply hypothesis dropped: regime A holds up to {float(bo[0]):.10f}, next {bo[2]}")
        for a in (Fr(3, 5), Fr(2, 5), Fr(3, 10)):
            th_a = with_input("alpha", a)
            sb = regime_B(th_a, fr)
            ell = Fr(str(sb["ell"].mp(30))).limit_denominator(10**14)
            ub = achievable_upper(ell, 1 - ell, Fr(0), th_a, fr, slack=Fr(1, 10**13))
            out(f"   alpha = {a}: regime B sigma {float(sb['sigma']):.10f}, witness bound equal:"
                f" {regime_B_witness(sb, th_a, fr)['lb'] == sb['sigma']}, checked geometry within"
                f" {float(ub - Fr(str(sb['sigma'].mp(30)))):.1e}")
    return res


# ----------------------------------------------------------------- main

def main(argv=None) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--paper", type=Path, default=DEFAULT_PAPER)
    ap.add_argument("--quick", action="store_true")
    args = ap.parse_args(argv)
    reps = reproductions()
    bad = [r for r in reps if not r["ok"]]
    for r in reps:
        print(f"{'ok  ' if r['ok'] else 'FAIL'} line {r['line']:>5}  {r['name']}: got {r['got']}")
    print(f"{len(reps) - len(bad)}/{len(reps)} reproductions agree")
    cite_fail = None
    if args.paper and args.paper.exists():
        cite_fail = verify_citations(args.paper)
        print(f"citations: {len(CITATIONS) - len(cite_fail)}/{len(CITATIONS)} on their line", cite_fail or "")
    print()
    report(verify=not args.quick)
    return 1 if bad or cite_fail else 0


if __name__ == "__main__":
    sys.exit(main())

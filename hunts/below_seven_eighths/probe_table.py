"""Hunt #136, lane `probe`: what a comparison system other than the sextic one is worth.

OpenAI's 7/8 argument (github.com/openai/math at adc7f124, paper.tex, 16,677 lines,
sha256 42a5ee0f...c6a3) compares a completed cubic-theta sum over F = Q(sqrt(-3)) with
a Mellin signal containing 1/L.  Hunt #134 rewrote its target in the free geometry
(slot length ell, total averaging length M, offset b) as

    sigma_0 = 1 - h/6 + b/12 = 5/6 + (M - 2 ell)/12,      h = 1 - l_x + ell.

This module separates the constants of that assembly into those whose 6 this lane reads
as the order k = 6 of the row characters (the pole of zeta_F(6z) at z = 1/6, the Gram
exponent P_a^{1/12}, the amplification slope 5/6 and the 6 in the plain capacity
6 kappa; the values are cited, the reading of each 6 as k is inferred) and those that
are generic, and then re-prices the whole assembly for a template system of order k:

    pole z_* = 1/k,  Gram term b/(2k),  Gram cap (3 - 2/k) b <= M - 2 ell,
    amplification alpha = 1 - 1/k,  plain capacity (1 - 2m)/(k kappa)  [inferred],

with every other estimate of the paper (reflected energy Z^{M'}, the row-norm loss,
the dual length M + ell <= 1, the rescaling count f(d) = -d, the detector windows, the
inverse capacity (1 - r)/2, the Euler regions, the floor bin and the numerator bound)
held fixed.  The paper's floor bin a = 51/100, delta_0 = 1/50 (line 15843) is the left
edge of the held Euler region x_r >= 51/100 (line 4054) that carries the nonprincipal
contours (line 4069; that the region fixes the bin is inferred), so FLOOR_HELD = 1/50
is the template's own floor; FLOOR_LIMIT = 0 is hunt #134's convention ("as the floor
approaches 1/2"), which also needs that region extended, and both are reported.

That template is a pricing device, not a construction: SYSTEMS records, for each
concrete system, which of the held estimates it would have to re-prove and what kills
it, and `held_inputs_fit` says where the held contour and Euler regions stop fitting.

The tied variant C sets c = 2/(k kappa_0) with kappa_0 = 2 sigma_0 - 1, the limit of
Liu's iteration (arXiv 2610.12234v2, cached source lines 310 and 311).  Where that
equality has no fixed point (k = 2 and 3), Lemma plain still allows any c = 2/(k kappa)
with an admissible kappa: its hypothesis is beta_* <= (1 + kappa)/2 (line 12565), kappa = 1
needs none, and a larger kappa only shrinks its condition (line 12561).  RELAXED_TIES
records the points of that kind priced here; they are admissible points, not optima.

Grades.  cited: a line of the pinned paper (or of a pinned outside source), checked by
`verify_citations` / `verify_outside_citations`.  derived: algebra done here, checked
in exact rational arithmetic (fractions, and sympy for general k) by
test_probe_table.py.  inferred: a reading no computation here checks.  measured: a
float optimisation (labelled as such).  Nothing here is a statement about real part
1/2, and no improvement of the half-plane is claimed: every number below is the price
of an input nobody here has proved.

    .venv/bin/python hunts/below_seven_eighths/probe_table.py           # tables
    .venv/bin/python hunts/below_seven_eighths/probe_table.py --paper   # + citations
"""
from __future__ import annotations

import argparse
import hashlib
import os
import itertools
import sys
from fractions import Fraction as Fr
from math import comb
from pathlib import Path

PAPER = Path(os.environ.get("ZETA_LAB_CACHE", os.path.expanduser("~/.cache/zeta-lab"))) / "openai-math-adc7f124" / "paper.tex"
PAPER_SHA256 = "42a5ee0febca59fd1def55cfd6c6808c322ef4237d7726303ea52f711deac6a3"

#: the campaign's cached copies of the public follow-ups (read as data)
FOLLOWUPS_DIR = Path(os.environ.get("ZETA_LAB_CACHE", os.path.expanduser("~/.cache/zeta-lab"))) / "followups" / "run-2026-10-21T1440Z"
OUTSIDE_SOURCES = {
    "liu_v1": (FOLLOWUPS_DIR / "liu_2610.12234v1" / "combine_v2.tex",
               "2c2f7988c6c1fccd610f22f6623e7a9107f40dddfc6a83b5ef21d6c10cb77e8a"),
    "liu_v2": (FOLLOWUPS_DIR / "liu_2610.12234v2" / "combine_v2-2.tex",
               "ca549f8c3dfa9d1ad7efeb32fba46d78a89aa8305b4ab621a81364833eb426bf"),
    "liu_nf": (FOLLOWUPS_DIR / "src_2610.26835v1" / "number_fields_v2.tex",
               "c55f17c6212777973adcdc06fea0f0cbfeae51c8ddada3b112f0981cde7a626f"),
}
#: key -> (source, line, verbatim snippet of that line)
OUTSIDE_CITATIONS = {
    "liu_v1_closed_form": ("liu_v1", 104, r":=\frac{1507-2\sqrt{921}}{1653}=0.874957069799\ldots."),
    "liu_v1_euler_correction": ("liu_v1", 244, r"Their Euler correction is shown to be"),
    "liu_v1_euler_below": ("liu_v1", 245, r"holomorphic below $7/8$."),
    "liu_v1_fixed_kappa": ("liu_v1", 246,
                           r"$\beta_*\le7/8$, the unweighted moment permits $\kappa=3/4$"),
    "liu_v1_fixed_kappa_eq": ("liu_v1", 2485, r"\kappa=3/4,\qquad\beta_*\le(1+\kappa)/2."),
    "liu_v1_do_not_substitute": ("liu_v1", 2488,
                                 r"$\kappa=2\beta_*-1$ below the allowed moment range."),
    "liu_v2_hypothesis": ("liu_v2", 284, r"\beta_*\le(1+\kappa)/2\qquad(\kappa<1)."),
    "liu_v2_count_class": ("liu_v2", 296, r"$R_\kappa=2/3$ becomes"),
    "liu_v2_count_equation": ("liu_v2", 298,
                              r"(216\kappa-18)\xi^2-(468\kappa-57)\xi+150\kappa-20=0."),
    "liu_v2_iteration": ("liu_v2", 310, r"Iteration reaches the limiting equality"),
    "liu_v2_iteration_limit": ("liu_v2", 311, r"$\kappa_{\mathrm{new}}=2B_{\mathrm{new}}-1$"),
    "liu_v2_value": ("liu_v2", 131, r"=0.874957019420098946\ldots,"),
    "liu_v2_xi": ("liu_v2", 133, r"$\xi_{\mathrm{new}}\in(0.38858,0.38859)$"),
    "liu_v2_cubic": ("liu_v2", 135, r"1188\xi^3-2160\xi^2+171\xi+190=0."),
    "liu_v2_range": ("liu_v2", 282, r"to $13/18\le\kappa\le1$, retaining the indispensable"),
    "liu_v2_ell": ("liu_v2", 302, r"\ell(\xi)=\frac{5-6\xi}{9+18\xi},\qquad"),
    "liu_v2_b": ("liu_v2", 303, r"b(\xi)=\frac{8(3\xi-1)(12\xi^2-40\xi+15)}"),
    "liu_v2_b_den": ("liu_v2", 304, r"{9(2\xi+1)(24\xi^2-20\xi+5)},\qquad"),
    "liu_v2_below": ("liu_v2", 4293, r"\qquad2B_{\mathrm{alg}}-1<3/4."),
    "liu_nf_range": ("liu_nf", 148, r"the latter for $13/18\le\kappa\le1$ as in \Prev{Part}{IV}."),
    "liu_nf_pole": ("liu_nf", 756,
                    r"$\zeta_F^S(6z)L_F^S(w,\chi_\bullet(u))/L_F^S(s,\eta\overline{\chi_\bullet(u)})$"),
    "liu_nf_bflat": ("liu_nf", 122, r"B_\flat=0.874886647039964\ldots<B_{\mathrm{new}},"),
}

#: the thresholds the mission asks about, and the newer one FOLLOWUPS.md reports
THIRTEEN_FIFTEENTHS = Fr(13, 15)
XU_SANG = Fr(8748867, 10000000)          # arXiv 2610.15291v2 abstract (cached copy)
NEWER_RECORD = Fr(8748087, 10000000)     # FOLLOWUPS.md item 3 (tracker PR 68), quoted
#: Liu, arXiv 2610.12234v2 (cached source line 131): optimum of the same comparison
#: system with b, ell, kappa varied.  Used only as an outside value to reproduce.
LIU_B_NEW = 0.874957019420098946
LIU_KAPPA_FLOOR = Fr(13, 18)             # Liu v2's extended moment range (source line 282)

#: the paper's geometry (lines 6860 to 6864)
ELL_P, M_P, B_P = Fr(1, 6), Fr(5, 6), Fr(1, 8)
ALPHA_P = Fr(5, 6)       # line 15101
KAPPA_P = Fr(3, 4)       # bottom of Lemma plain's stated range, line 12532
C_P = Fr(4, 9)           # plain-capacity coefficient 2/(6 kappa) at kappa = 3/4
ZC_P = Fr(17, 50)        # line 15742
#: floor bins: the paper's a = 51/100 (line 15843), the left edge of region one
#: x_r >= 51/100 (line 4054); and the limit a -> 1/2 that hunt #134 used for its 13/15
FLOOR_HELD = Fr(1, 50)
FLOOR_LIMIT = Fr(0)
FLOOR_DELTA = FLOOR_HELD  # the endpoint covers 1/50 < delta < alpha (line 15949)
REGION_TWO_X, REGION_TWO_Z = Fr(7, 8), Fr(33, 200)   # line 4056

KS = (2, 3, 4, 5, 6, 8, 12)

# ------------------------------------------------------------------ citations
#: key -> (line, verbatim snippet of the pinned paper.tex at that line)
CITATIONS = {
    "C_I": (190, r"C_{\mathrm I}(s)=s-\frac23"),
    "C_II": (191, r"C_{\mathrm{II}}(s)=s-\frac{11}{16}"),
    "part_I_target": (509, r"\sigma_0=\frac{11}{12},\qquad C(s)=s-\frac23,"),
    "sextic_symbol": (629, r"symbol $\chi_p(a)=(a/p)_6$"),
    "twist_exponents": (1700, r"choose $j_p\in\{0,1,\ldots,5\}$ for each"),
    "twist": (1703, r"\Psi(n)=\Psi_0(n)\prod_{p\in\mathcal P}\chi_p(n)^{j_p}."),
    "dual_character": (1790, r"\chi_p(x)^{-j_p-2},&j_p\ne0,4,"),
    "dual_ramanujan": (1791, r"q_p^{-1/2}(-1+q_p1_{p\mid x}),&j_p=4,"),
    "quadratic_sieve": (2648, r"\ll_\epsilon (UV)^\epsilon(U+V)\sum_b|c_b|^2."),
    "energy_lemma": (3159, r"\ll Z^{O/2+\max\{M-O,\,2M-O-N\}+\epsilon}"),
    "planar_sieve": (3509, r"\ll (Q+\delta^{-2})\sum_{j=1}^J|a_j|^2."),
    "low_I": (3717, r"&=Z^{1/4+\epsilon_1/2}."),
    "poisson_prefactor": (3752, r"$X^{1/2}/(q_{b_*}^{1/2}q_A)$"),
    "frequency_sixth": (3758, r"$H=ua^6$, where $u$ is a sixth-power-free element"),
    "mellin_positive": (3781, r"M(1/6)>0."),
    "positivity_range": (3784, r"For $0<\sigma<1$,"),
    "coefficient_alpha": (3819, r"\gamma_2(c)\overline{\alpha(A)G(A)}"),
    "weight": (3825, r"X^{1/2-z}Z^{x+z-1}Y^{w-1}"),
    "local_R": (3866, r"V=Q^{-6z},\qquad R=a_p^2Q^{4-6x-6z}"),
    "signal_relation": (3967, r"$\gamma_2(c)=\mu(c)\alpha(c)G(c)/\gamma_1(c)$"),
    "pole_factor": (4045, r"\frac{\zeta_F^S(6z)L^S(w,\chi_\bullet(u))}"),
    "region_one": (4054, r"x_r\ge51/100,\quad z_r\ge17/50,\quad w_r\ge-1/100,"),
    "region_two": (4056, r"x_r\ge7/8,\quad z_r\ge33/200,\quad w_r\ge19/20."),
    "region_one_use": (4069, r"The first region will contain the buffered contours for nonprincipal"),
    "residue_point": (4071, r"principal residue point $w=1$, $z=1/6$"),
    "gauss_pair": (4118, r"=-\alpha(p)\overline{\chi_p(4)}\gamma_3,"),
    "gamma24": (4124, r"$\gamma_2\gamma_4=1$"),
    "sextic_sieve": (4717, r"\bigl\{K+D+(KD)^{2/3}\bigr\}"),
    "bgl_recursion": (4728, r"We follow the higher-order large-sieve recursion of Blomer, Goldmakher,"),
    "part_I_rows": (5196, r"R(\delta)=\min\left\{1,"),
    "unique_principal": (5508, r"every unit of $F$ has sixth power one"),
    "h_def": (5586, r"h=1-l_x+\ell>0,"),
    "stage_C": (5588, r"C(s)=s+\frac{l_x}{2}-1+\frac h6"),
    "stage_C_expanded": (5589, r"=s-\frac56+\frac{l_x}{3}+\frac\ell6."),
    "bootstrap": (6817, r"\Delta:=\beta_*-\frac78,\qquad 0<\Delta\le\frac1{24},"),
    "bootstrap_kappa": (6819, r"\kappa:=2\beta_*-1=\frac34+2\Delta\le\frac56."),
    "geometry": (6860, r"b=\frac18,\qquad h=\frac{13}{16},\qquad \ell=\frac16,"),
    "rescale": (6898, r"(-1)^{|J|}q_{p_J}^{-3/2}"),
    "row_norm": (8116, r"\ll Z^{M'+((d-1/6)/4)_++\epsilon}"),
    "dual_length": (8246, r"Since $M'+\ell'-1=-3d$, direct subtraction gives"),
    "row_loss": (8306, r"M'+\frac{1+3\ell'-2M'-2\Delta_H+\theta_N}{4}"),
    "gram": (8353, r"\left(1+P_a^{1/6}+\frac{P_a^2}{Y'}\right)Z^\epsilon."),
    "gram_nonexceptional": (8530, r"\frac Q{Y'}\frac{P_a^2}{Y'}Z^\epsilon"),
    "gram_exceptional_form": (8535, r"$(k)=a_1^6e$"),
    "gram_exceptional_count": (8541, r"$O_{\rm fixed}(K_R^{1/6})$ choices"),
    "gram_exceptional_sum": (8551, r"Y'^2(RP_a)^{1/6}C_0^{-1/6}D_0^{-1}."),
    "low_II": (8570, r"\ll Z^{l_x/2+b/12+\epsilon}=Z^{3/16+\epsilon}."),
    "P_a": (8588, r"P_a=Y'^2/Q=q_{b_*}^{-1}Z^{1/8}."),
    "gram_cap": (8597, r"l_y-d-11b/6\ge1/12."),
    "cauchy_schwarz": (8619, r"=\bigl[Z^{M'}/Y'\bigr]^{1/2}P_a^{1/12}"),
    "f_d": (8631, r"f(d)=d-3d/2-d/2=-d\le0."),
    "C_form": (8641, r"C_{\mathrm{II}}(s)=l_x/2+s-1+h/6=s-11/16,"),
    "C_match": (8642, r"C_{\mathrm{II}}(7/8)=3/16=l_x/2+b/12."),
    "row_valuations": (8969, r"$u=\epsilon_u\prod_{p\mid u}p^{j_p}$, with $\epsilon_u$ a unit."),
    "amp_P": (12369, r"P=(H/U)^{1/6}"),
    "amp_bound": (12375, r"U^{1/6}D^{5(1+c)/6}"),
    "amp_e": (12383, r"e(r)=\max\{1,(1+5r)/6\}"),
    "plain_kappa": (12532, r"Let \(3/4\le\kappa\le1\)."),
    "plain_condition": (12561, r"n_1+n_2+6\kappa z=A+(6\kappa-1)z\le M."),
    "plain_hypothesis": (12565, r"\(\beta_*\le(1+\kappa)/2\).  If \(\kappa=1\), no zero-free"),
    "plain_threshold": (12594, r"\(A\le5M/6\) is proved first."),
    "plain_sixth_form": (12596, r"their sixth-power form and"),
    "exceptional_rows": (14378, r"\ll Z^{(m'_{\rm act}-f)/6+\epsilon_1}"),
    "dynamic_kappa": (15100, r"\kappa=2\beta_*-1=\frac34+2\Delta\in(3/4,5/6],\qquad"),
    "alpha": (15101, r"\alpha:=\frac56."),
    "alpha_source": (15104, r"from sixth-power amplification."),
    "bin_ceiling": (15107, r"gives \(\delta\le\kappa\le\alpha\) for the current Part~II bins"),
    "z_P": (15175, r"z_P(m)=\frac{1-2m}{6\kappa}"),
    "z_M": (15182, r"\(z_M(r)=(1-r)/2\)."),
    "D_x": (15192, r"D_x=3-\frac{17x}{9},\qquad"),
    "P_x": (15193, r"P_x=\left(2-\frac{8x}{9}\right)(1-x)."),
    "R_short": (15206, r"R_{\rm short}(t)=1-\delta+\frac{\delta P_x}{D_x}(3/2-t),"),
    "slot_weight": (15563, r"W_i(q_p/P_i)q_p^{-5/6},"),
    "A_T": (15576, r"A_T(Z)=(-1)^K Z^{-\ell/6}\prod_{i=1}^K S_i(Z)."),
    "E_line1": (15729, r"&=a-\frac78+h\left(\frac{17}{50}-\frac16\right)"),
    "E_line2": (15730, r"-a l_y-(1-a)\ell-(\delta/2-q)\ell"),
    "C_0": (15734, r"\qquad C_0=-\frac1{48}."),
    "contour": (15742, r"\Re s=a+16e,\qquad \Re w=1-a-6e,\qquad \Re z=\frac{17}{50},"),
    "inverse_capacity": (15382, r"\((1-23/37)/2=7/37\)."),
    "plain_monotone": (15342, r"-2\delta+\frac{8q}{9}<0."),
    "large_delta": (15945, r"=-\frac1{48}-\frac{\delta}{16}+O(\epsilon)<0."),
    "numerator": (15801, r"U^{\delta/2+O(e)+\epsilon}(1+T_1)^{A_1}"),
    "floor_bin": (15843, r"The floor bin \(a=51/100\) has \(\delta_0=1/50\) and requires no"),
    "floor": (15847, r"E(h)\le C_0+\frac34\delta_0=-\frac7{1200}<0."),
    "frequency_slope": (15849, r"Its frequency slope \(R+\delta_0/2-17/50\) is positive, so this"),
    "endpoint_range": (15949, r"Now assume \(1/50<\delta<\alpha\)."),
    "J_def": (15963, r"\mathcal J=(\alpha-\delta)D_x+\delta P_x,\qquad"),
    "t_def": (15964, r"t=1+\frac{\delta P_x}{2\mathcal J},\qquad"),
    "endpoint_margin": (16000, r"-E_*\ge\frac{49}{440640}>\frac1{10000}."),
    "R_star": (16019, r"From \(R_*=1-\delta+(\alpha-\delta)\delta P_x/(2\mathcal J)\)"),
    "supply": (16116, r"\frac{\ell}{d}\ge\frac8{39}>\frac15>\frac7{37}."),
}


def _lines(path: Path, sha256: str) -> list[str] | None:
    data = path.read_bytes()
    if hashlib.sha256(data).hexdigest() != sha256:
        return None
    return data.decode("utf-8").splitlines()


def verify_citations(paper: Path = PAPER) -> list[str]:
    """Citation keys whose snippet is not on its stated line (empty list: all present)."""
    lines = _lines(paper, PAPER_SHA256)
    if lines is None:
        return ["<sha256 mismatch: not the pinned paper.tex>"]
    return [key for key, (n, snip) in CITATIONS.items() if snip not in lines[n - 1]]


def verify_outside_citations() -> list[str]:
    """Outside-source keys whose snippet is not on its stated line, or whose file differs."""
    texts = {}
    for name, (path, sha) in OUTSIDE_SOURCES.items():
        texts[name] = _lines(path, sha) if path.exists() else None
    bad = [f"<{name}: missing or sha256 mismatch>" for name, t in texts.items() if t is None]
    for key, (src, n, snip) in OUTSIDE_CITATIONS.items():
        lines = texts[src]
        if lines is not None and snip not in lines[n - 1]:
            bad.append(key)
    return bad


# ------------------------------------------------------- the provenance table
#: Every constant of the target formula and of the Part II assembly, with where it
#: comes from.  `origin`: "sextic" (a 6 this lane reads as the order k = 6 of the row
#: characters), "cubic-theta" (set by the cubic theta function, its pairing with the
#: sextic twist or the Euler regions of its local identity), "generic" (an estimate
#: whose form does not depend on k), "choice" (a chosen geometry or contour).
#: `template`: its value in the order-k template, or "held" when the template keeps
#: the paper's value.  `grade` is the grade of the provenance claim itself; for the
#: sextic rows the value is cited and the reading of its 6 as k is inferred.
#: `label`, `value`, `enters`, `lines`, `origin`, `template` and `grade` are the seven
#: columns of PROBE.md's section 1 table, which the tests render from this list.
PROVENANCE = [
    dict(key="pole", label="pole", value="1/6", enters="h/6 in C(s)",
         lines=(3758, 4045, 4071, 5588, 8641), origin="sextic", template="1/k",
         grade="cited value; k-reading inferred",
         note="Poisson frequencies H = u a^6 with u sixth-power-free; the a-sum is "
              "zeta_F^S(6z), principal residue at z = 1/6"),
    dict(key="slot_weight", label="slot weight", value="q_p^(-5/6)", enters="+ell/6 in C(s)",
         lines=(15563, 15576, 5589), origin="sextic", template="q_p^(1/k-1)",
         grade="cited value; k-reading inferred",
         note="each slot prime is weighted at the residue z = 1/6, so the slots add "
              "Z^(ell/6) to the signal; this is the ell part of h/6"),
    dict(key="gram_exceptional", label="Gram exceptional", value="P_a^(1/6)",
         enters="additive Gram bound", lines=(8353, 8535, 8541), origin="sextic",
         template="P_a^(1/k)", grade="cited value; k-reading inferred",
         note="exceptional frequencies are sixth powers times a bounded part, "
              "counted as K^(1/6)"),
    dict(key="gram_low", label="Gram in the low bound", value="b/12", enters="l_x/2 + b/12",
         lines=(8570, 8619), origin="sextic", template="b/(2k)",
         grade="cited value; template derived on the inferred k-reading",
         note="Cauchy-Schwarz halves the Gram exponent; b/12 = (1/2)(1/6) b"),
    dict(key="gram_cap", label="Gram cap", value="11b/6", enters="l_y - d >= 11b/6",
         lines=(8530, 8597), origin="sextic", template="(2 - 1/k) b",
         grade="cited value; template derived on the inferred k-reading",
         note="2 from the nonexceptional term P_a^2/Y' (generic), minus the exceptional 1/6"),
    dict(key="alpha", label="amplification", value="alpha = 5/6", enters="L(t), R_*",
         lines=(12369, 12383, 15101), origin="sextic", template="1 - 1/k",
         grade="cited value; k-reading inferred",
         note="amplification by sixth powers a^6 with q_a <= (H/U)^(1/6)"),
    dict(key="plain_capacity", label="plain capacity", value="6 kappa", enters="z_P, c = 4/9",
         lines=(12561, 12594, 12596, 14378, 15175), origin="sextic", template="k kappa",
         grade="inferred",
         note="exceptional rows of the fourth moment are counted as sixth powers; "
              "that the 6 in 6 kappa is the order k is a reading, not checked"),
    dict(key="euler_regions", label="Euler regions", value="51/100, 17/50, 33/200, 19/20, 7/8",
         enters="local identity", lines=(3866, 4054, 4056), origin="cubic-theta",
         template="held; region two misses z = 1/k for k >= 7, and its x_r >= 7/8 misses "
                  "every target below 7/8",
         grade="cited regions; fit derived",
         note="local exponents such as R = a_p^2 Q^(4-6x-6z) come from A = n^3 with "
              "n = p^2 (6 = lcm(3, 6)); they must be re-derived for any other system "
              "(held_inputs_fit says where the held regions stop fitting)"),
    dict(key="floor_bin", label="floor bin", value="delta_0 = 1/50 (a = 51/100)",
         enters="floor rows", lines=(15843, 4054, 4069, 15742), origin="cubic-theta",
         template="held; the limit 0 reported beside it",
         grade="cited bin; inferred that region one fixes it",
         note="a = 51/100 is the left edge x_r >= 51/100 of region one, which carries the "
              "nonprincipal contours Re s = a + 16e"),
    dict(key="gauss_pairing", label="Gauss pairing",
         value="gamma_1 gamma_2 = -alpha(p) chi_p(4)^- gamma_3", enters="scalar Euler identity",
         lines=(3819, 3967, 4118, 4124), origin="cubic-theta", template="none known",
         grade="inferred",
         note="the sextic twist is the one whose Gauss sum times the cubic theta "
              "coefficient is an explicit phase that also cancels the angular factor "
              "alpha-bar(cn^3) of the theta coefficient"),
    dict(key="reflected_energy", label="reflected energy", value="Z^(M')", enters="row norm",
         lines=(1790, 2648, 3159, 8116), origin="cubic-theta", template="held", grade="cited",
         note="the reflection's local column factor at p is chi_p^(-j_p-2) (line 1790), "
              "j_p the exponent of chi_p in the twist (lines 1700, 1703), which is the "
              "valuation of the row at p (line 8969); at j_p = 1 it is quadratic and the "
              "quadratic large sieve gives Z^(M')"),
    dict(key="row_loss", label="row-norm loss", value="(1 + 3 ell' - 2M')/4",
         enters="corner M - 2 ell >= 1/2", lines=(8306,), origin="cubic-theta",
         template="held", grade="cited",
         note="gives the per-summand corner M - 2 ell >= 1/2 (hunt 134)"),
    dict(key="dual_length", label="dual length", value="M + ell <= 1", enters="reflection",
         lines=(8246,), origin="generic", template="held",
         grade="derived subtraction; sufficiency inferred (hunt #134)",
         note="the line-8246 subtraction leaves M + ell - 1 for general parameters"),
    dict(key="poisson_normalisation", label="Poisson normalisation", value="X^(1/2), Z^(x+z-1)",
         enters="weight", lines=(3752, 3825), origin="generic", template="held, cancels",
         grade="derived",
         note="the l_x/2 appears in both the signal and the low bound and cancels "
              "in the target"),
    dict(key="rescaling", label="rescaling", value="q_p^(-3/2), f(d) = -d",
         enters="compensated probe", lines=(6898, 8631), origin="generic", template="held",
         grade="cited"),
    dict(key="planar_sieve", label="additive sieve", value="(Q + delta^-2)",
         enters="additive norm", lines=(3509,), origin="generic", template="held",
         grade="cited"),
    dict(key="sextic_sieve", label="large sieve", value="(KD)^(2/3)",
         enters="Part I count R(delta)", lines=(4717, 4728, 5196), origin="generic",
         template="held", grade="cited; every n >= 3 by BGL Theorem 1.3",
         note="BGL (arXiv 1112.1650) Theorem 1.3, 'valid for all n >= 3', has the same "
              "(MN)^(2/3) term; the paper follows BGL's Section 3 recursion (line 4728); "
              "it enters the 7/8 assembly only through the 11/12 bootstrap"),
    dict(key="inverse_capacity", label="inverse capacity", value="(1 - r)/2",
         enters="Lemma marked", lines=(15182,), origin="generic", template="held",
         grade="inferred"),
    dict(key="detector_windows", label="detector windows", value="t in [1, 3/2], x in [0, 1/2]",
         enters="row counts", lines=(15206, 15964), origin="generic", template="held",
         grade="cited"),
    dict(key="numerator", label="numerator", value="U^(delta/2)", enters="high exponent",
         lines=(15801,), origin="generic", template="held", grade="cited",
         note="the input Xu and Sang average (arXiv 2610.15291v2 abstract)"),
    dict(key="contour", label="contour", value="Re z = 17/50", enters="nonprincipal rows",
         lines=(15742, 15729, 15849), origin="choice",
         template="held for k >= 3; k = 2 needs 1/2 < Re z < 3/4", grade="derived",
         note="its coefficient is h - d, so it cancels at the endpoint d = h"),
    dict(key="geometry", label="geometry", value="ell = 1/6, M = 5/6, b = 1/8", enters="Part II",
         lines=(6860,), origin="choice", template="free", grade="cited"),
    dict(key="mellin_positive", label="Mellin positivity", value="M(1/6) > 0", enters="scalar c_S",
         lines=(3781, 3784), origin="generic", template="M(1/k) > 0, k >= 2",
         grade="cited (the proof covers 0 < sigma < 1)",
         note="the positivity proof is written for every 0 < sigma < 1, which contains "
              "1/k for every k >= 2"),
]


def provenance_row(row: dict) -> str:
    """One row of PROBE.md's section 1 table, rendered from PROVENANCE."""
    lines = ", ".join(str(n) for n in row["lines"])
    return (f"| {row['label']} | {row['value']} | {row['enters']} | {lines} | {row['origin']} "
            f"| {row['template']} | {row['grade']} |")


# ------------------------------------------------------------- the template
def z_pole(k: int) -> Fr:
    """Pole of zeta_F(k z): the paper's z = 1/6 at k = 6 (lines 4045, 4071)."""
    return Fr(1, k)


def gram_low(k: int) -> Fr:
    """Coefficient of b in the low exponent: half the exceptional exponent 1/k."""
    return Fr(1, 2 * k)


def gram_cap_slope(k: int) -> Fr:
    """Gram condition (3 - 2/k) b <= M - 2 ell, the paper's 3(M - 2 ell)/8 at k = 6."""
    return 3 - Fr(2, k)


def alpha_amp(k: int) -> Fr:
    """Amplification slope: P = (H/U)^{1/k} gives e(r) = (1 + (k-1) r)/k = 1 - alpha + alpha r."""
    return 1 - Fr(1, k)


def plain_coeff(k: int, kappa0: Fr) -> Fr:
    """c in D_x = 3 - (1 + 2c) x: z_P(m) = c (1 - 2m)/2 = (1 - 2m)/(k kappa0)  [inferred]."""
    return Fr(2) / (k * kappa0)


def geometry(ell: Fr, M: Fr, b: Fr) -> tuple[Fr, Fr, Fr]:
    """(l_x, l_y, h) with l_x = (M - b)/2, l_y = (M + b)/2, h = 1 - l_x + ell (line 5586)."""
    l_x = (M - b) / 2
    l_y = (M + b) / 2
    return l_x, l_y, 1 - l_x + ell


def signal_shift(k: int, ell: Fr, M: Fr, b: Fr) -> Fr:
    """c with C(s) = s - c, from C(s) = s + l_x/2 - 1 + h z_* (lines 5588, 8641)."""
    l_x, _, h = geometry(ell, M, b)
    return 1 - l_x / 2 - h * z_pole(k)


def low_exponent(k: int, ell: Fr, M: Fr, b: Fr, d: Fr = Fr(0), g: Fr | None = None) -> Fr:
    """Exponent of the rescaled summand d in the compensated low bound (lines 8570, 8631).

    (l_x - d)/2 + g b from Cauchy-Schwarz (line 8619), plus the count d and the
    coefficient -3d/2 of the rescaled tuples: l_x/2 + g b - d.  g defaults to 1/(2k).
    """
    l_x, _, _ = geometry(ell, M, b)
    g = gram_low(k) if g is None else g
    f_d = d - Fr(3, 2) * d - d / 2      # count, coefficient, (X')^(1/2): line 8631
    return l_x / 2 + g * b + f_d


def target(k: int, ell: Fr, M: Fr, b: Fr, g: Fr | None = None) -> Fr:
    """sigma_0 with C(sigma_0) = low exponent: where the direct bound meets the signal."""
    return low_exponent(k, ell, M, b, g=g) + signal_shift(k, ell, M, b)


def target_closed(k: int, ell: Fr, M: Fr) -> Fr:
    """Derived: sigma_0 = 1 - 1/k + (M - 2 ell)/(2k); b cancels because g = z_*/2."""
    return 1 - Fr(1, k) + (M - 2 * ell) / (2 * k)


def part_one_target(k: int) -> Fr:
    """Balanced probe, no slots (ell = b = 0, M = 1): 1 - 1/(2k); 11/12 at k = 6."""
    return target(k, Fr(0), Fr(1), Fr(0))


def corner_target(k: int) -> Fr:
    """Per-summand corner M - 2 ell = 1/2 (hunt 134): 1 - 3/(4k); 7/8 at k = 6."""
    return target(k, ELL_P, M_P, Fr(0))


def row_loss(ell: Fr, M: Fr, d: Fr) -> Fr:
    """Second-branch row-norm loss ((1 + 3 ell' - 2 M')/4)_+, ell' = ell - d, M' = M - 2d."""
    return max(Fr(0), (1 + 3 * (ell - d) - 2 * (M - 2 * d)) / 4)


# ---------------------------------------------------------------- high side
def high_exponent(k: int, ell: Fr, M: Fr, b: Fr, sigma0: Fr, d: Fr, delta: Fr, q: Fr,
                  R: Fr, zc: Fr = ZC_P) -> Fr:
    """Equation common-high-exponent (lines 15729, 15730) with sigma_0, z_* and M free.

    E(d) = a - sigma0 + h(zc - z_*) - a l_y - (1 - a) ell - (delta/2 - q) ell
           + d (R + delta/2 - zc),      a = (1 + delta)/2.
    """
    _, l_y, h = geometry(ell, M, b)
    a = (1 + delta) / 2
    return (a - sigma0 + h * (zc - z_pole(k)) - a * l_y - (1 - a) * ell
            - (delta / 2 - q) * ell + d * (R + delta / 2 - zc))


def c0(k: int, ell: Fr, M: Fr, b: Fr) -> Fr:
    """E(h) at delta = q = 0, R = 1, against the matched target (transcription route)."""
    _, _, h = geometry(ell, M, b)
    return high_exponent(k, ell, M, b, target(k, ell, M, b), h, Fr(0), Fr(0), Fr(1))


def c0_closed(k: int, ell: Fr, M: Fr, b: Fr) -> Fr:
    """Derived: C_0 = 1/2 + ell/2 - 3M/4 + b (1/4 - 1/(2k)); -1/48 at the paper's point."""
    return Fr(1, 2) + ell / 2 - Fr(3, 4) * M + b * (Fr(1, 4) - Fr(1, 2 * k))


def floor_exponent(k: int, ell: Fr, M: Fr, b: Fr, delta0: Fr) -> Fr:
    """Floor rows (no witness, R = 1, q <= delta0/2) at d = h: C_0 + (1 + ell - M/2) delta0."""
    _, _, h = geometry(ell, M, b)
    return high_exponent(k, ell, M, b, target(k, ell, M, b), h, delta0, delta0 / 2, Fr(1))


def d_x(x: Fr, c: Fr) -> Fr:
    """D_x = 3 - (1 + 2c) x; the paper's 3 - 17x/9 (line 15192) at c = 4/9."""
    return 3 - (1 + 2 * c) * x


def p_x(x: Fr, c: Fr) -> Fr:
    """P_x = (2 - 2cx)(1 - x); the paper's (2 - 8x/9)(1 - x) (line 15193) at c = 4/9."""
    return (2 - 2 * c * x) * (1 - x)


def k_excess(delta: Fr, x: Fr, alpha: Fr, c: Fr) -> Fr:
    """K with R_* = 1 - delta + K/2 (line 16019); zero for delta >= alpha (line 15934)."""
    if delta >= alpha:
        return Fr(0)
    J = (alpha - delta) * d_x(x, c) + delta * p_x(x, c)
    return (alpha - delta) * delta * p_x(x, c) / J


def r_star(delta: Fr, x: Fr, alpha: Fr, c: Fr) -> Fr:
    """R_* = 1 - delta + (alpha - delta) delta P_x/(2J) (lines 15963 to 15965, 16019)."""
    return 1 - delta + k_excess(delta, x, alpha, c) / 2


def short_and_long(delta: Fr, x: Fr, alpha: Fr, c: Fr) -> tuple[Fr, Fr, Fr]:
    """(t, R_short(t), L(t)) at the balancing t = 1 + delta P_x/(2J) (lines 15206, 15964)."""
    J = (alpha - delta) * d_x(x, c) + delta * p_x(x, c)
    t = 1 + delta * p_x(x, c) / (2 * J)
    r_short = 1 - delta + delta * p_x(x, c) / d_x(x, c) * (Fr(3, 2) - t)
    long_ = 1 - delta + (alpha - delta) * (t - 1)
    return t, r_short, long_


def endpoint_neg_e(k: int, ell: Fr, M: Fr, b: Fr, delta: Fr, x: Fr, alpha: Fr,
                   c: Fr) -> Fr:
    """-E_* of Lemma balanced-endpoint for system k: -E(h) with q = x delta, R = R_*."""
    _, _, h = geometry(ell, M, b)
    return -high_exponent(k, ell, M, b, target(k, ell, M, b), h, delta, x * delta,
                          r_star(delta, x, alpha, c))


def endpoint_neg_e_closed(k: int, ell: Fr, M: Fr, b: Fr, delta: Fr, x: Fr, alpha: Fr,
                          c: Fr) -> Fr:
    """Derived: -E_* = -C_0(k) + delta (ell + b)/2 - ell x delta - (h/2) K."""
    _, _, h = geometry(ell, M, b)
    return (-c0_closed(k, ell, M, b) + delta * (ell + b) / 2 - ell * x * delta
            - h / 2 * k_excess(delta, x, alpha, c))


def paper_completed_square_identity(delta: Fr, x: Fr) -> bool:
    """The completed square of Lemma balanced-endpoint (line 16048), checked at one point."""
    y = Fr(1, 2) - x
    v = 51 + 41 * y
    J = (ALPHA_P - delta) * d_x(x, C_P) + delta * p_x(x, C_P)
    lhs = 10368 * v * J * endpoint_neg_e_closed(6, ELL_P, M_P, B_P, delta, x, ALPHA_P, C_P)
    rhs = ((3 + 5 * y) * ((4 * v * delta - 79) ** 2 + 49)
           + 4 * y * (4 * v * delta * ((1 + 3 * y) * (15 + 32 * y) * delta + 9 - 13 * y)
                      + 265 + 3485 * y))
    return lhs == rhs


# ------------------------------------------------------------ exact linear programs
def _solve(rows: list[list[Fr]], rhs: list[Fr]) -> list[Fr] | None:
    """Exact Gauss-Jordan solve of a square system; None when singular."""
    n = len(rows)
    a = [list(r) + [v] for r, v in zip(rows, rhs)]
    for col in range(n):
        piv = next((i for i in range(col, n) if a[i][col] != 0), None)
        if piv is None:
            return None
        a[col], a[piv] = a[piv], a[col]
        pv = a[col][col]
        a[col] = [v / pv for v in a[col]]
        for i in range(n):
            if i != col and a[i][col] != 0:
                f = a[i][col]
                a[i] = [vi - f * vc for vi, vc in zip(a[i], a[col])]
    return [a[i][n] for i in range(n)]


def lp_min(objective: list[Fr], constraints: list[tuple[list[Fr], Fr]]) -> tuple[Fr, list[Fr]]:
    """Exact minimum of objective . v subject to coeffs . v <= rhs, by vertex enumeration.

    The feasible set must be bounded (pass box constraints).  Returns (value, vertex).
    """
    n = len(objective)
    best = None
    for subset in itertools.combinations(range(len(constraints)), n):
        sol = _solve([constraints[i][0] for i in subset], [constraints[i][1] for i in subset])
        if sol is None:
            continue
        if all(sum(c * v for c, v in zip(co, sol)) <= r for co, r in constraints):
            val = sum(c * v for c, v in zip(objective, sol))
            if best is None or val < best[0]:
                best = (val, sol)
    if best is None:
        raise ValueError("infeasible linear program")
    return best


def _geometry_constraints(k: int, loss: str, delta0: Fr | None,
                          g: Fr | None = None) -> list[tuple[list[Fr], Fr]]:
    """Linear constraints on (ell, M, b) shared by the walls below.

    dual length M + ell <= 1 (line 8246); b >= 0 (P_a >= 1, line 8345); Gram cap
    (3 - 4g) b <= M - 2 ell (line 8597 generalised; 3 - 2/k at g = 1/(2k)); loss:
    "total" is the inferred d = 0 losslessness 2M >= 1 + 3 ell, "per_summand" is
    M - 2 ell >= 1/2 (line 8306); floor rows C_0 + (1 + ell - M/2) delta0 <= 0 (line
    15847) with C_0 = 1/2 + ell/2 - 3M/4 + (1/4 - g) b, unless delta0 is None.
    """
    g = gram_low(k) if g is None else g
    cons = [
        ([Fr(-1), Fr(0), Fr(0)], Fr(0)),            # ell >= 0
        ([Fr(0), Fr(0), Fr(-1)], Fr(0)),            # b >= 0
        ([Fr(1), Fr(1), Fr(0)], Fr(1)),             # M + ell <= 1
        ([Fr(1), Fr(0), Fr(0)], Fr(1)),             # box
        ([Fr(0), Fr(1), Fr(0)], Fr(1)),
        ([Fr(0), Fr(-1), Fr(0)], Fr(0)),
        ([Fr(0), Fr(0), Fr(1)], Fr(1)),
        ([Fr(2), Fr(-1), 3 - 4 * g], Fr(0)),        # (3 - 4g) b <= M - 2 ell
    ]
    if loss == "total":
        cons.append(([Fr(3), Fr(-2), Fr(0)], Fr(-1)))          # 2M >= 1 + 3 ell
    elif loss == "per_summand":
        cons.append(([Fr(2), Fr(-1), Fr(0)], Fr(-1, 2)))       # M - 2 ell >= 1/2
    else:
        raise ValueError(loss)
    if delta0 is not None:
        # 1/2 + ell/2 - 3M/4 + (1/4 - g) b + (1 + ell - M/2) delta0 <= 0
        cons.append(([Fr(1, 2) + delta0, Fr(-3, 4) - delta0 / 2, Fr(1, 4) - g],
                     -Fr(1, 2) - delta0))
    return cons


def floor_ceiling(k: int, loss: str = "total", delta0: Fr = FLOOR_HELD,
                  g: Fr | None = None) -> dict:
    """Smallest target compatible with the floor rows, which no row count can improve.

    Exact LP over (ell, M, b) for the target 1 - z + z(M - 2 ell)/2 + (g - z/2) b,
    z = 1/k.  With loss "total" and g = 1/(2k) this is floor_wall_closed(k, delta0):
    1 - 25/(32k) at the paper's floor bin delta0 = 1/50 (167/192 at k = 6) and
    1 - 4/(5k) in the limit delta0 = 0 (hunt 134's 13/15 at k = 6); the dual multipliers
    that prove it optimal are floor_dual_multipliers, checked in the tests.
    """
    z = z_pole(k)
    gg = gram_low(k) if g is None else g
    cons = _geometry_constraints(k, loss, delta0, gg)
    obj = [-z, z / 2, gg - z / 2]           # target minus the constant 1 - z
    val, (ell, M, b) = lp_min(obj, cons)
    return {"k": k, "sigma0": 1 - z + val, "ell": ell, "M": M, "b": b,
            "loss": loss, "delta0": delta0, "g": gg}


def floor_wall_closed(k: int, delta0: Fr) -> Fr:
    """Derived: 1 - 1/k + (1 + 6 delta0)/(k (5 + 6 delta0)), the minimum of M - 2 ell being
    (2 + 12 delta0)/(5 + 6 delta0) (2/5 in the limit, 7/16 at the paper's bin)."""
    return 1 - Fr(1, k) + (1 + 6 * delta0) / (k * (5 + 6 * delta0))


def floor_dual_multipliers(k: int, delta0: Fr = FLOOR_HELD) -> tuple[Fr, Fr, Fr, Fr]:
    """Dual multipliers and value proving min (M - 2 ell) = m under the floor rows.

    M - 2 ell - m = y1 (-(C_0 + (1 + ell - M/2) delta0)) + y2 (1 - M - ell) + y3 b
    identically, with y1 = 12/(5 + 6 delta0), y2 = 4/(5 + 6 delta0),
    y3 = y1 (1/4 - 1/(2k)) >= 0 exactly when k >= 2, and m = (2 + 12 delta0)/(5 + 6 delta0).
    """
    s = 5 + 6 * delta0
    y1 = Fr(12) / s
    return y1, Fr(4) / s, y1 * (Fr(1, 4) - Fr(1, 2 * k)), (2 + 12 * delta0) / s


# ------------------------------------------------------------ the endpoint wall
#: variants of the row counts for system k
VARIANTS = {
    "A": "pole and Gram moved; alpha = 5/6 and c = 4/9 held",
    "B": "pole, Gram and amplification alpha = 1 - 1/k moved; c = 4/9 held",
    "C": "pole, Gram, alpha moved; c = 2/(k kappa_0) tied to the target (inferred)",
}


def variant_params(k: int, variant: str) -> tuple[Fr, Fr | None, Fr]:
    """(alpha, c or None when tied, delta_max).  delta_max = 2 sigma_I(k) - 1 = 1 - 1/k.

    The bin ceiling of system k comes from its own Part I analogue, 1 - 1/(2k); at
    k = 6 this is the paper's kappa <= 5/6 (line 6819), and in general it equals the
    amplification slope 1 - 1/k, so the paper's delta <= alpha is automatic (derived).
    """
    delta_max = 2 * part_one_target(k) - 1
    if variant == "A":
        return ALPHA_P, C_P, delta_max
    if variant == "B":
        return alpha_amp(k), C_P, delta_max
    if variant == "C":
        return alpha_amp(k), None, delta_max
    raise ValueError(variant)


def tied_c(k: int, sigma: Fr) -> Fr:
    """c = 2/(k kappa_0) with kappa_0 = 2 sigma - 1 (the paper's 4/9 at k = 6, sigma = 7/8)."""
    return plain_coeff(k, 2 * sigma - 1)


#: Relaxed ties where the equality tie of variant C has no fixed point (k = 2, 3).
#: Lemma plain at kappa needs beta_* <= (1 + kappa)/2 (line 12565; none at kappa = 1),
#: and a larger kappa only shrinks its condition n_1 + n_2 + 6 kappa z <= M (line 12561),
#: so c = 2/(k kappa) with any admissible kappa may be used (on the inferred k kappa
#: reading).  key -> (k, kappa, bound on beta_* the hypothesis needs or None, what
#: supplies that bound inside the template).  Admissible points, not optima: a larger c
#: helps until the slot supply binds, which it already does at k = 2, kappa = 3/4.
RELAXED_TIES = {
    "k2 kappa 1": (2, Fr(1), None, "kappa = 1 needs no zero-free hypothesis"),
    "k3 kappa 3/4": (3, Fr(3, 4), Fr(7, 8), "the order-3 Part I analogue 5/6"),
    "k3 kappa 3/5": (3, Fr(3, 5), Fr(4, 5), "the k = 3, kappa = 3/4 point"),
}


def kappa_of_c(k: int, c: Fr) -> Fr:
    """The kappa whose plain capacity is c on the k kappa reading: 9/(2k) for c = 4/9."""
    return Fr(2) / (k * c)


def plain_count_decreasing(c) -> bool:
    """The plain count 1 - 2 delta m - 2q c(1 - 2m)/2 decreases in m for all x <= 1/2.

    Its m-derivative is delta(-2 + 2cx) (line 15342 at c = 4/9), negative iff c x < 1,
    so the crossing argument of Prop. detector-counts needs c < 2 (derived).
    """
    return c < 2


def multi_point_bound(k: int, points, alpha: Fr, c: Fr, loss: str = "total",
                      delta0: Fr | None = FLOOR_HELD) -> dict:
    """Exact lower bound on the target from the endpoint inequality at finitely many
    points (delta, x), with the LP point (ell, b) where it is attained.

    On M = 1 - ell (optimal for every k: the constant-target slope 1 + delta(1/2 - x)
    is positive and k-free), -E_* = A + A_ell ell + A_b b is affine at each point;
    maximise ell over the polygon cut out by -E_* >= 0 at every point, b >= 0, the Gram
    cap, the loss condition and the floor.  Finitely many points are a relaxation of the
    whole endpoint range, so the result is a valid lower bound.
    """
    beta = Fr(1, 4) - Fr(1, 2 * k)
    g = gram_cap_slope(k)
    cons = [
        ([Fr(-1), Fr(0)], Fr(0)),                # ell >= 0
        ([Fr(0), Fr(-1)], Fr(0)),                # b >= 0
        ([Fr(3), g], Fr(1)),                     # g b <= 1 - 3 ell
        ([Fr(1), Fr(0)], Fr(1, 5) if loss == "total" else Fr(1, 6)),
        ([Fr(0), Fr(1)], Fr(1)),
    ]
    for delta, x in points:
        def f(ell, b):
            return endpoint_neg_e_closed(k, ell, 1 - ell, b, delta, x, alpha, c)
        A = f(Fr(0), Fr(0))
        A_l = f(Fr(1), Fr(0)) - A
        A_b = f(Fr(0), Fr(1)) - A
        cons.append(([-A_l, -A_b], A))           # A + A_l ell + A_b b >= 0
    if delta0 is not None:
        # C_0 + (1/2 + 3 ell/2) delta0 <= 0 on M = 1 - ell
        cons.append(([Fr(5, 4) + Fr(3, 2) * delta0, beta], Fr(1, 4) - delta0 / 2))
    val, (ell, b) = lp_min([Fr(-1), Fr(0)], cons)
    return {"sigma0": 1 - Fr(1, 2 * k) - Fr(3, 2 * k) * (-val), "ell": ell, "b": b}


def single_point_bound(k: int, delta: Fr, x: Fr, alpha: Fr, c: Fr,
                       loss: str = "total", delta0: Fr | None = FLOOR_HELD) -> Fr:
    """Exact lower bound on the target from the endpoint inequality at one (delta, x)."""
    return multi_point_bound(k, [(delta, x)], alpha, c, loss, delta0)["sigma0"]


def _most_violated_point(k, ell, b, alpha, c, d_lo, d_hi) -> tuple[float, float]:
    """Float search for the (delta, x) minimising -E_* at a fixed (ell, M = 1 - ell, b):
    the cutting plane that best_exact_bound adds next (used only to choose points)."""
    import numpy as np

    beta = 0.25 - 1 / (2 * k)

    def grid(dl, dh, xl, xh, nd, nx):
        D, X = np.meshgrid(np.linspace(dl, dh, nd), np.linspace(xl, xh, nx), indexing="ij")
        Dx = 3 - (1 + 2 * c) * X
        Px = (2 - 2 * c * X) * (1 - X)
        am = np.maximum(alpha - D, 0.0)
        with np.errstate(divide="ignore", invalid="ignore"):
            K = np.where(am > 0, am * D * Px / (am * Dx + D * Px), 0.0)
        E = 0.25 - beta * b - 1.25 * ell + D * (ell + b) / 2 - ell * X * D - (1 + 3 * ell + b) * K / 4
        i = np.unravel_index(E.argmin(), E.shape)
        return float(D[i]), float(X[i]), (dh - dl) / (nd - 1), (xh - xl) / (nx - 1)
    dd, xx, sd, sx = grid(d_lo, d_hi, 0.0, 0.5, 400, 26)
    for _ in range(3):
        dd, xx, sd, sx = grid(max(d_lo, dd - 2 * sd), min(d_hi, dd + 2 * sd),
                              max(0.0, xx - 2 * sx), min(0.5, xx + 2 * sx), 41, 41)
    return dd, xx


def _single_point_float(k, delta, x, alpha, c, loss, delta0) -> float:
    """Float version of single_point_bound (used only to locate the best point).

    ell(b) = min of four lines in b (loss cap, Gram cap, floor, endpoint); its maximum
    over 0 <= b <= 1 sits at b = 0, b = 1 or a pairwise intersection.
    """
    K = 0.0
    if delta < alpha:
        Dx = 3 - (1 + 2 * c) * x
        Px = (2 - 2 * c * x) * (1 - x)
        J = (alpha - delta) * Dx + delta * Px
        K = (alpha - delta) * delta * Px / J
    beta = 0.25 - 1 / (2 * k)
    A = 0.25 - K / 4
    A_l = -1.25 + delta / 2 - x * delta - 0.75 * K
    A_b = -beta + delta / 2 - K / 4
    g = 3 - 2 / k
    cap_loss = 0.2 if loss == "total" else 1 / 6
    fl = ((0.25 - delta0 / 2) / (1.25 + 1.5 * delta0), -beta / (1.25 + 1.5 * delta0))
    lines = [(cap_loss, 0.0), (1 / 3, -g / 3), fl, (A / -A_l, A_b / -A_l)]
    cands = [0.0, 1.0]
    for (p0, p1), (q0, q1) in itertools.combinations(lines, 2):
        if p1 != q1:
            b = (q0 - p0) / (p1 - q1)
            if 0.0 <= b <= 1.0:
                cands.append(b)
    best = -1.0
    for b in cands:
        ell = min(p0 + p1 * b for p0, p1 in lines)
        if ell >= 0:
            best = max(best, ell)
    if best < 0:
        return -1.0
    return 1 - 1 / (2 * k) - 3 * best / (2 * k)


def _argmax_point(k, alpha, c, delta_max, loss, delta0) -> tuple[float, float, float]:
    """Float search for the (delta, x) whose single-point bound is largest."""
    d_lo = max(float(delta0), 1e-6)
    lo_d, hi_d, lo_x, hi_x = d_lo, float(delta_max), 0.0, 0.5
    best = (-2.0, lo_d, hi_x)
    nd, nx = 400, 26
    for _ in range(5):
        sd, sx = (hi_d - lo_d) / (nd - 1), (hi_x - lo_x) / (nx - 1)
        for i in range(nd):
            dl = lo_d + i * sd
            for j in range(nx):
                xv = lo_x + j * sx
                v = _single_point_float(k, dl, xv, alpha, c, loss, float(delta0))
                if v > best[0]:
                    best = (v, dl, xv)
        _, dl, xv = best
        lo_d, hi_d = max(d_lo, dl - 3 * sd), min(float(delta_max), dl + 3 * sd)
        lo_x, hi_x = max(0.0, xv - 3 * sx), min(0.5, xv + 3 * sx)
        nd, nx = 41, 13
    return best


def best_exact_bound(k: int, variant: str, loss: str = "total",
                     delta0: Fr = FLOOR_HELD, c: Fr | None = None, cuts: int = 0) -> dict:
    """An exact lower bound on the target of system k: one single-point bound, rationalised.

    The best (delta, x) is located in floats, rounded to a rational with denominator at
    most 10^6 inside the endpoint range delta0 < delta <= delta_max, and the bound is
    then computed exactly there.  For the tied variant C the coefficient c depends on
    the unknown target; the bound is decreasing in c (derived: D_x/P_x increases with
    c), so start from the floor ceiling, which no c moves, and iterate
    sigma_{j+1} = bound(c(sigma_j)); each step is again a valid lower bound.  A given
    `c` replaces the variant's coefficient (the relaxed ties of RELAXED_TIES).
    `cuts` > 0 then adds up to that many cutting planes: the point most violated at the
    current LP solution, located in floats, rationalised and added exactly; every finite
    set of points is a relaxation, so each step is again a valid lower bound.  It is
    needed where two endpoint points bind at once, which one point cannot capture.
    """
    alpha, c_fixed, delta_max = variant_params(k, variant)
    if c is not None:
        c_fixed = c
    floor = floor_ceiling(k, loss, delta0)["sigma0"]
    sigma_lb, point, c = floor, (None, None), c_fixed
    d_lo = max(delta0, FLOOR_LIMIT) + Fr(1, 10 ** 6)

    def rational_point(dl, xv):
        return (min(max(Fr(dl).limit_denominator(10 ** 6), d_lo), delta_max),
                min(max(Fr(xv).limit_denominator(10 ** 6), Fr(0)), Fr(1, 2)))
    for _ in range(1 if c_fixed is not None else 8):
        c = c_fixed if c_fixed is not None else tied_c(k, sigma_lb)
        if not plain_count_decreasing(c):
            return {"k": k, "variant": variant, "sigma0_lower": None, "c": c,
                    "floor": floor, "valid": False}
        _, dl, xv = _argmax_point(k, float(alpha), float(c), delta_max, loss, delta0)
        dlq, xq = rational_point(dl, xv)
        s = single_point_bound(k, dlq, xq, alpha, c, loss, delta0)
        if s > sigma_lb:
            sigma_lb, point = s, (dlq, xq)
    points = [point] if point[0] is not None else []
    for _ in range(cuts if c_fixed is not None else 0):
        lp = multi_point_bound(k, points, alpha, c, loss, delta0)
        nxt = rational_point(*_most_violated_point(k, float(lp["ell"]), float(lp["b"]),
                                                   float(alpha), float(c), float(d_lo),
                                                   float(delta_max)))
        if nxt in points:
            break
        points.append(nxt)
        sigma_lb = max(sigma_lb, multi_point_bound(k, points, alpha, c, loss, delta0)["sigma0"])
    return {"k": k, "variant": variant, "sigma0_lower": sigma_lb, "delta": point[0],
            "x": point[1], "c": c, "floor": floor, "valid": True, "delta0": delta0,
            "points": points}


def endpoint_optimum(k, variant: str, loss: str = "total",
                     floor_delta0: float = float(FLOOR_HELD),
                     gram: float | None = None, alpha: float | None = None,
                     c: float | None = None, n_delta: int = 500, n_x: int = 26) -> dict:
    """Measured optimum of the Part II assembly for system k (float scan, not a bound).

    Maximises ell on M = 1 - ell over b, subject to min over (delta, x) of -E_* >= 0 on
    the endpoint range floor_delta0 <= delta <= 1 - 1/k, the Gram cap, the loss
    condition, the floor rows at floor_delta0 and the slot supply.  The default floor
    bin is the paper's 1/50; pass 0.0 for hunt #134's limit.  For fixed b and c, -E_*
    is affine in ell with negative slope, so the largest ell is min over (delta, x) of
    A/(-A_ell): no bisection.  ell*(b) is concave, so b is found by golden section.
    `gram` overrides the low-bound Gram coefficient g (default 1/(2k)), with the Gram
    cap moved to (3 - 4g) b <= M - 2 ell to match: the target is then sigma_low =
    matched target + (g - 1/(2k)) b, and requiring -E_* >= 0 against it is the minimax
    of the low and high sides.  k may be a float here (pole prices).
    For the tied variant C the result carries valid = False, with the reason, when the
    equality tie has no fixed point (c reaches 2, or the slot supply fails); a given `c`
    replaces the tie (RELAXED_TIES).
    """
    import numpy as np

    kf = float(k)
    if variant == "A":
        a_def, c_def = 5 / 6, 4 / 9
    elif variant == "B":
        a_def, c_def = 1 - 1 / kf, 4 / 9
    elif variant == "C":
        a_def, c_def = 1 - 1 / kf, None
    else:
        raise ValueError(variant)
    al = a_def if alpha is None else alpha
    dmax = 1 - 1 / kf
    d_lo = float(floor_delta0)
    g_low = 1 / (2 * kf) if gram is None else gram
    shift = g_low - 1 / (2 * kf)     # sigma_low - matched target, per unit b
    beta = 0.25 - 1 / (2 * kf)
    # Gram cap: P_a^2/Y' <= P_a^(2g) needs M - 2 ell >= (3 - 4g) b; 3 - 2/k at g = 1/(2k)
    gcap = 3 - 4 * g_low
    lcap = 0.2 if loss == "total" else 1 / 6

    def ell_star(b, cc):
        def grid(d_lo_, d_hi, x_lo, x_hi, nd, nx):
            ds = np.linspace(d_lo_, d_hi, nd)
            xs = np.linspace(x_lo, x_hi, nx)
            D, X = np.meshgrid(ds, xs, indexing="ij")
            Dx = 3 - (1 + 2 * cc) * X
            Px = (2 - 2 * cc * X) * (1 - X)
            am = np.maximum(al - D, 0.0)
            J = am * Dx + D * Px
            # K = 0 where alpha <= delta; this also covers J = 0 at delta = alpha = 0
            with np.errstate(divide="ignore", invalid="ignore"):
                K = np.where(am > 0, am * D * Px / J, 0.0)
            # -E_* on M = 1 - ell against sigma = matched target + shift b
            A = 0.25 - b * beta + D * b / 2 - (1 + b) * K / 4 + shift * b
            Al = -1.25 + D / 2 - X * D - 0.75 * K
            E = A / (-Al)
            i = np.unravel_index(E.argmin(), E.shape)
            return float(E[i]), float(D[i]), float(X[i]), ds[1] - ds[0], xs[1] - xs[0]
        v, dd, xx, sd, sx = grid(d_lo, dmax, 0.0, 0.5, n_delta, n_x)
        for _ in range(3):
            v, dd, xx, sd, sx = grid(max(d_lo, dd - 2 * sd), min(dmax, dd + 2 * sd),
                                     max(0.0, xx - 2 * sx), min(0.5, xx + 2 * sx), 41, 41)
        return v, dd, xx

    def ell_eff(b, cc):
        v, dd, xx = ell_star(b, cc)
        caps = [v, (1 - gcap * b) / 3, lcap]
        # floor rows on M = 1 - ell, against sigma_low:
        # -1/4 + 5 ell/4 + beta b - shift b + (1/2 + 3 ell/2) delta0 <= 0
        caps.append((0.25 - beta * b + shift * b - floor_delta0 / 2)
                    / (1.25 + 1.5 * floor_delta0))
        e = min(caps)
        # slot supply ell/h > s (line 16116), h = 1/2 + 3 ell/2 + b/2 on M = 1 - ell:
        # ell (1 - 3s/2) > s (1 + b)/2, impossible once s >= 2/3 (since ell/h < 2/3)
        s_need = supply_needed_float(cc)
        if s_need >= 2 / 3 or e < s_need * (1 + b) / (2 - 3 * s_need):
            return -1.0, dd, xx
        return e, dd, xx

    def sigma_of(b, cc):
        e = ell_eff(b, cc)[0]
        if e < 0:
            return float("inf")      # infeasible offset (endpoint, floor or slot supply)
        return 1 - 1 / (2 * kf) - 3 * e / (2 * kf) + shift * b

    def best_b(cc):
        # sigma(b) is convex where finite (-ell_eff is a max of affine maps, plus a linear
        # term), and the feasible offsets form an interval: coarse grid, then golden
        # section on the bracket around the best grid point.
        hi_b = 1 / gcap
        grid = [hi_b * i / 60 for i in range(61)]
        vals = [sigma_of(b, cc) for b in grid]
        i = min(range(len(grid)), key=lambda j: vals[j])
        lo, hi = grid[max(0, i - 1)], grid[min(len(grid) - 1, i + 1)]
        phi = (5 ** 0.5 - 1) / 2
        x1, x2 = hi - phi * (hi - lo), lo + phi * (hi - lo)
        f1, f2 = sigma_of(x1, cc), sigma_of(x2, cc)
        for _ in range(60):
            if f1 > f2:
                lo, x1, f1 = x1, x2, f2
                x2 = lo + phi * (hi - lo)
                f2 = sigma_of(x2, cc)
            else:
                hi, x2, f2 = x2, x1, f1
                x1 = hi - phi * (hi - lo)
                f1 = sigma_of(x1, cc)
        b = (lo + hi) / 2
        if vals[i] < sigma_of(b, cc):
            b = grid[i]
        e, dd, xx = ell_eff(b, cc)
        return b, e, dd, xx

    valid, reason = True, None
    if c is not None or c_def is not None:
        cc = c if c is not None else c_def
        b, e, dd, xx = best_b(cc)
        valid = e >= 0
        if not valid:
            reason = "requested capacity exceeds the slot supply"
    else:
        # fixed point c = 2/(k kappa_0), kappa_0 = 2 sigma - 1; valid only if it converges
        # with c < 2 (plain count decreasing in m) and a feasible slot supply.  Failing
        # that is a property of the equality tie, not of the template (RELAXED_TIES).
        cc, valid = 4 / 9, False
        for _ in range(80):
            b, e, dd, xx = best_b(cc)
            if e < 0:
                break
            sigma = 1 - 1 / (2 * kf) - 3 * e / (2 * kf)
            new = 2 / (kf * (2 * sigma - 1))
            if not plain_count_decreasing(new):
                reason = f"no fixed point of the equality tie: it asks for c = {new:.3f} >= 2"
                break
            if abs(new - cc) < 1e-13:
                cc, valid = new, True
                break
            cc = new
        b, e, dd, xx = best_b(cc)
        valid = valid and e >= 0
        if not valid and reason is None:
            reason = ("no fixed point of the equality tie: the requested capacity exceeds "
                      "the slot supply")
    sigma = 1 - 1 / (2 * kf) - 3 * e / (2 * kf) + shift * b
    h = 0.5 + 1.5 * e + b / 2
    return {"k": k, "variant": variant, "loss": loss, "sigma0": sigma, "ell": e, "b": b,
            "M": 1 - e, "h": h, "delta_bind": dd, "x_bind": xx, "c": cc, "alpha": al,
            "supply_ratio": e / h, "gram": g_low, "valid": valid, "reason": reason,
            "kappa0": 2 * sigma - 1, "floor_delta0": floor_delta0}


def supply_needed_float(c: float) -> float:
    """Largest capacity Prop. detector-counts may request (grid route): max over x of the
    inverse capacity (1 - r_*(1))/2 and the plain capacity c(1 - 2 m_min)/2,
    m_min = (1 - cx)/D_x (lines 15371 to 15385; 7/37 at c = 4/9)."""
    best = 0.0
    for i in range(0, 101):
        x = i / 200
        dx = 3 - (1 + 2 * c) * x
        r1 = (2 - 2 * c * x - x * (1 - c)) / dx
        m1 = (1 - c * x) / dx
        best = max(best, (1 - r1) / 2, c * (1 - 2 * m1) / 2)
    return best


def supply_needed(c: Fr) -> Fr:
    """Exact route: the inverse capacity is (1 - cx)/(2 D_x), with x-derivative of sign
    1 - c, and the plain capacity is c(1 - x)/(2 D_x), of sign c - 1 (derived), so both
    maxima over 0 <= x <= 1/2 sit at an endpoint: (2 - c)/(10 - 4c) and c/6 for c <= 1,
    1/6 and c/(10 - 4c) for c >= 1.  7/37 at c = 4/9."""
    if c <= 1:
        return max((2 - c) / (10 - 4 * c), c / 6)
    return max(Fr(1, 6), c / (10 - 4 * c))


def inverse_capacity_max(c: Fr) -> Fr:
    """Largest inverse capacity (1 - r_*(1))/2 over 0 <= x <= 1/2: the paper's 7/37 at c = 4/9."""
    best = Fr(0)
    for i in range(0, 101):
        x = Fr(i, 200)
        r1 = (2 - 2 * c * x - x * (1 - c)) / d_x(x, c)
        best = max(best, (1 - r1) / 2)
    return best


# ------------------------------------------- exact feasibility: an upper bound
def _pmul(p: dict, q: dict) -> dict:
    out: dict = {}
    for (i, j), a in p.items():
        for (r, s), b in q.items():
            out[(i + r, j + s)] = out.get((i + r, j + s), 0) + a * b
    return {key: v for key, v in out.items() if v != 0}


def _padd(*ps: dict) -> dict:
    out: dict = {}
    for p in ps:
        for key, v in p.items():
            out[key] = out.get(key, 0) + v
    return {key: v for key, v in out.items() if v != 0}


def _pscale(p: dict, s) -> dict:
    return {key: v * s for key, v in p.items() if v * s != 0}


def _peval(p: dict, d, x):
    return sum(a * d ** i * x ** j for (i, j), a in p.items())


def endpoint_polynomial(k: int, ell: Fr, b: Fr, alpha: Fr, c: Fr) -> dict:
    """F(delta, x) = J (-E_*) on M = 1 - ell, as {(i, j): coefficient of delta^i x^j}.

    On M = 1 - ell, -E_* = L - K (1 + 3 ell + b)/4 with L = 1/4 - beta b - 5 ell/4
    + delta (ell + b)/2 - ell x delta and K = (alpha - delta) delta P_x / J (derived
    from endpoint_neg_e_closed; the tests check the identity).  For delta < alpha and
    c < 2, J > 0 on 0 <= x <= 1/2, so -E_* > 0 there exactly when F > 0.
    """
    beta = Fr(1, 4) - Fr(1, 2 * k)
    P = _padd({(0, 0): Fr(2), (0, 1): -2 - 2 * c, (0, 2): 2 * c})
    J = endpoint_denominator(alpha, c)
    L = _padd({(0, 0): Fr(1, 4) - beta * b - Fr(5, 4) * ell, (1, 0): (ell + b) / 2,
               (1, 1): -ell})
    amp = {(1, 0): alpha, (2, 0): Fr(-1)}           # (alpha - delta) delta
    return _padd(_pmul(J, L), _pscale(_pmul(amp, P), -(1 + 3 * ell + b) / 4))


def endpoint_denominator(alpha: Fr, c: Fr) -> dict:
    """J(delta, x) = (alpha - delta) D_x + delta P_x as a polynomial (line 15963)."""
    D = {(0, 0): Fr(3), (0, 1): -(1 + 2 * c)}
    P = _padd({(0, 0): Fr(2), (0, 1): -2 - 2 * c, (0, 2): 2 * c})
    return _padd(_pscale(D, alpha), _pmul({(1, 0): Fr(1)}, _padd(P, _pscale(D, -1))))


def _bernstein_min(p: dict, box: tuple) -> Fr:
    """Smallest Bernstein coefficient of p on the box: a lower bound for p there."""
    d1, d2, x1, x2 = box
    m = max((i for i, _ in p), default=0)
    n = max((j for _, j in p), default=0)
    wd, wx = d2 - d1, x2 - x1
    q: dict = {}
    for (i, j), a in p.items():
        for s in range(i + 1):
            cs = a * comb(i, s) * d1 ** (i - s) * wd ** s
            for t in range(j + 1):
                q[(s, t)] = q.get((s, t), 0) + cs * comb(j, t) * x1 ** (j - t) * wx ** t
    lo = None
    for kk in range(m + 1):
        for ll in range(n + 1):
            v = sum(Fr(comb(kk, s), comb(m, s)) * Fr(comb(ll, t), comb(n, t)) * q.get((s, t), 0)
                    for s in range(kk + 1) for t in range(ll + 1))
            lo = v if lo is None or v < lo else lo
    return lo


def positive_on_box(p: dict, box: tuple, max_boxes: int = 100000) -> tuple[bool, object]:
    """Exact: (True, boxes used) when p > 0 on the closed box, by Bernstein subdivision;
    (False, corner) when a corner has p <= 0; (False, None) when the budget runs out."""
    stack, used = [box], 0
    while stack:
        bx = stack.pop()
        used += 1
        if used > max_boxes:
            return False, None
        if _bernstein_min(p, bx) > 0:
            continue
        d1, d2, x1, x2 = bx
        for dd, xx in ((d1, x1), (d1, x2), (d2, x1), (d2, x2)):
            if _peval(p, dd, xx) <= 0:
                return False, (dd, xx)
        dm, xm = (d1 + d2) / 2, (x1 + x2) / 2
        stack += [(d1, dm, x1, xm), (dm, d2, x1, xm), (d1, dm, xm, x2), (dm, d2, xm, x2)]
    return True, used


def point_is_feasible(k: int, ell: Fr, b: Fr, alpha: Fr, c: Fr, delta0: Fr = FLOOR_HELD,
                      loss: str = "total", endpoint: bool = True) -> dict:
    """Exact check, constraint by constraint, that (ell, M = 1 - ell, b) meets the template.

    The endpoint must hold strictly on the whole range delta0 <= delta <= 1 - 1/k,
    0 <= x <= 1/2 (Bernstein subdivision for delta < alpha; for delta >= alpha, K = 0
    and -E_* is bilinear, so its corners decide); the floor rows and the slot supply
    strictly; the Gram cap, the loss cap and b, ell >= 0 as stated.  Every value True
    means the target 1 - 1/(2k) - 3 ell/(2k) is reached: an upper bound on the optimum.
    endpoint=False skips the subdivision (the tests compare the other checks with an
    independent route on many points).
    """
    dmax = 1 - Fr(1, k)
    beta = Fr(1, 4) - Fr(1, 2 * k)
    h = Fr(1, 2) + Fr(3, 2) * ell + b / 2
    out = {
        "ell >= 0": ell >= 0,
        "b >= 0": b >= 0,
        "gram cap": gram_cap_slope(k) * b <= 1 - 3 * ell,
        "loss": ell <= (Fr(1, 5) if loss == "total" else Fr(1, 6)),
        "floor": -Fr(1, 4) + Fr(5, 4) * ell + beta * b + (Fr(1, 2) + Fr(3, 2) * ell) * delta0 < 0,
        "plain count decreasing": plain_count_decreasing(c),
        "slot supply": ell / h > supply_needed(c),
    }
    hi = min(alpha, dmax)
    if endpoint and delta0 < hi:
        box = (delta0, hi, Fr(0), Fr(1, 2))
        # J = (alpha - delta) D_x + delta P_x > 0 on the box, so F > 0 means -E_* > 0
        out["J > 0"] = positive_on_box(endpoint_denominator(alpha, c), box)[0]
        ok, _ = positive_on_box(endpoint_polynomial(k, ell, b, alpha, c), box)
        out["endpoint, delta < alpha"] = ok
    if alpha < dmax:
        def lin(dl, x):
            return Fr(1, 4) - beta * b - Fr(5, 4) * ell + dl * (ell + b) / 2 - ell * x * dl
        out["endpoint, delta >= alpha"] = all(lin(dl, x) > 0 for dl in (alpha, dmax)
                                              for x in (Fr(0), Fr(1, 2)))
    return out


def exact_upper_bound(k: int, variant: str, delta0: Fr = FLOOR_HELD,
                      loss: str = "total", measured: dict | None = None,
                      c: Fr | None = None) -> dict:
    """An exact upper bound on the template optimum of system k: a point that meets every
    constraint, found by stepping back from the measured optimum by eta in ell.

    The measured (ell, b) is rationalised and ell lowered by eta = 0, 10^-10, ..., 10^-6
    until point_is_feasible passes; for variant C the coefficient is tied to the target
    the point reaches, c = tied_c(k, sigma).  Together with best_exact_bound this
    brackets the optimum from both sides in exact arithmetic.  `measured` may pass an
    endpoint_optimum result computed at the same (k, variant, delta0, loss, c).  A given
    `c` replaces the variant's coefficient (the relaxed ties of RELAXED_TIES).
    """
    r = measured if measured is not None else endpoint_optimum(
        k, variant, loss=loss, floor_delta0=float(delta0),
        c=None if c is None else float(c))
    if not r["valid"]:
        return {"k": k, "variant": variant, "valid": False}
    alpha, c_fixed, _ = variant_params(k, variant)
    if c is not None:
        c_fixed = c
    b = max(Fr(r["b"]).limit_denominator(10 ** 9), Fr(0))
    ell0 = Fr(r["ell"]).limit_denominator(10 ** 12)
    checks = {}
    for eta in (Fr(0), Fr(1, 10 ** 10), Fr(1, 10 ** 9), Fr(1, 10 ** 8), Fr(1, 10 ** 7),
                Fr(1, 10 ** 6)):
        ell = ell0 - eta
        sigma = 1 - Fr(1, 2 * k) - Fr(3, 2 * k) * ell
        c = c_fixed if c_fixed is not None else tied_c(k, sigma)
        checks = point_is_feasible(k, ell, b, alpha, c, delta0, loss)
        if all(checks.values()):
            return {"k": k, "variant": variant, "valid": True, "sigma0_upper": sigma,
                    "ell": ell, "b": b, "c": c, "eta": eta, "delta0": delta0}
    return {"k": k, "variant": variant, "valid": False, "checks": checks}


# ------------------------------------------- where the held inputs stop fitting
def held_inputs_fit(k: int) -> dict:
    """Derived from lines 4054, 4056, 15742 and 15849: where the held contour and Euler
    regions still fit system k.

    - The nonprincipal contour Re z = 17/50 must lie right of the pole 1/k, which sits
      in every row (line 4045): true exactly for k >= 3.
    - The principal residue z = 1/k must lie in region two, z_r >= 33/200: k <= 6.
    - Contour window: Re z > 1/k, Re z >= 17/50 (region one) and Re z < (k + 1)/(2k),
      where the frequency slope R + delta/2 - Re z of every row priced here (R >= 1 -
      delta) stays positive for delta <= 1 - 1/k.  For k = 2 that is 1/2 < Re z < 3/4.
    - Region two's x_r >= 7/8 must reach the target; below 7/8 it is not held.
    """
    z = z_pole(k)
    dmax = 1 - Fr(1, k)
    hi = 1 - dmax / 2
    return {"k": k,
            "contour_right_of_pole": ZC_P > z,
            "residue_in_region_two": z >= REGION_TWO_Z,
            "window": (max(z, ZC_P), hi),
            "window_open_below": z >= ZC_P,
            "held_contour_in_window": z < ZC_P < hi}


def frequency_slope_lower(k: int, zc: Fr) -> Fr:
    """min over 0 <= delta <= 1 - 1/k of 1 - delta/2 - zc, a lower bound for the frequency
    slope R + delta/2 - zc of the floor, endpoint and large-delta rows (R >= 1 - delta)."""
    return 1 - (1 - Fr(1, k)) / 2 - zc


# ------------------------------------------------------------------ systems
#: Concrete comparison systems.  `k` is the order of the row characters (the pole is
#: at 1/k); `theta` the completed sum; the status fields are readings (inferred)
#: unless marked otherwise in PROBE.md.  The twist exponent j is this lane's reading:
#: the paper twists by prod_p chi_p^(j_p) with j_p chosen per prime (lines 1700, 1703),
#: and j_p is the valuation of the row u at p (line 8969); a system with one exponent j
#: for every prime is an inference, not a case the paper treats.
SYSTEMS = [
    dict(name="S0 paper", field="Q(sqrt(-3))", theta="cubic (n = 3)", twist="sextic chi (j = 1)",
         k=6, status="the paper; every lemma is OpenAI's, unreviewed"),
    dict(name="S1 cubic twist", field="Q(sqrt(-3))", theta="cubic (n = 3)",
         twist="conjugate cubic chi^4 (j = 4)", k=3,
         status="killed on an inferred reading, for Dirichlet L-functions: gamma_2 "
                "gamma_4 = 1 leaves the angular factor alpha-bar(c), so the denominator is "
                "L(s, eta alpha-bar)"),
    dict(name="S2 quadratic twist", field="Q(sqrt(-3))", theta="cubic (n = 3)",
         twist="quadratic chi^3 (j = 3)", k=2,
         status="killed on an inferred reading: gamma_2 gamma_3 is not an explicit phase, "
                "so no scalar Euler identity is available from the paper's Gauss relations"),
    dict(name="S3 classical theta, quartic twist", field="Q(i)", theta="classical (n = 2)",
         twist="quartic", k=4,
         status="killed on an inferred reading: the classical theta has no coefficients at "
                "squarefree c != 1, so no Moebius c-sum and no 1/L in the principal row"),
    dict(name="S4 biquadratic theta", field="Q(i)", theta="biquadratic (n = 4)",
         twist="quartic", k=4,
         status="open: needs the biquadratic theta coefficients at squarefree indices "
                "(not determined for n >= 4), a twisted reflection, a Gauss pairing "
                "cancelling its angular factor, and every Part II moment lemma"),
    dict(name="S5 quintic theta", field="Q(zeta_5)", theta="quintic (n = 5)", twist="quintic",
         k=5, status="open, as S4, over a quartic field with an infinite unit group"),
    dict(name="S6 cubic theta over F containing mu_12", field="Q(zeta_12), K(zeta_12)",
         theta="cubic exceptional theta", twist="sextic", k=6,
         status="Liu 2610.26835 runs it; the pole stays at 1/6 (zeta_F^S(6z), line 756 of "
                "the cached source): a bigger field does not move the pole"),
    dict(name="S7 higher twists of the cubic theta", field="F containing mu_k",
         theta="cubic (n = 3)", twist="order 9 or 12", k=12,
         status="dead by price: the pole 1/k < 1/6 raises every target"),
    dict(name="S8 biquadratic theta, octic twist", field="Q(zeta_8)", theta="biquadratic (n = 4)",
         twist="octic", k=8, status="dead by price (pole 1/8), and needs S4's lemmas"),
]


def system_prices(k: int) -> dict:
    """The closed-form walls of system k (all exact), with both floor bins."""
    return {"k": k, "part_one": part_one_target(k), "corner": corner_target(k),
            "floor_held": floor_ceiling(k, delta0=FLOOR_HELD)["sigma0"],
            "floor_limit": floor_ceiling(k, delta0=FLOOR_LIMIT)["sigma0"],
            "floor_per_summand": floor_ceiling(k, "per_summand")["sigma0"]}


# --------------------------------------------------------------------- report
def reproductions() -> list[dict]:
    """Values at k = 6 the template must give back.

    source "paper": printed in paper.tex on `line`, with `tex` the printed fragment
    (the tests check it sits there).  source "hunt134": derived by hunt #134 and not
    printed in the paper (the tests check that `absent` does not occur in paper.tex).
    """
    g = geometry(ELL_P, M_P, B_P)
    rows = [
        ("h = 13/16", 6860, g[2], Fr(13, 16), "paper", r"h=\frac{13}{16}"),
        ("C_II shift 11/16", 191, signal_shift(6, ELL_P, M_P, B_P), Fr(11, 16), "paper",
         r"s-\frac{11}{16}"),
        ("low exponent 3/16", 8570, low_exponent(6, ELL_P, M_P, B_P), Fr(3, 16), "paper",
         r"=Z^{3/16+\epsilon}"),
        ("target 7/8", 8642, target(6, ELL_P, M_P, B_P), Fr(7, 8), "paper",
         r"C_{\mathrm{II}}(7/8)=3/16"),
        ("Part I shift 2/3", 190, signal_shift(6, Fr(0), Fr(1), Fr(0)), Fr(2, 3), "paper",
         r"C_{\mathrm I}(s)=s-\frac23"),
        ("Part I low 1/4", 3717, low_exponent(6, Fr(0), Fr(1), Fr(0)), Fr(1, 4), "paper",
         r"=Z^{1/4+\epsilon_1/2}"),
        ("Part I target 11/12", 509, part_one_target(6), Fr(11, 12), "paper",
         r"\sigma_0=\frac{11}{12}"),
        ("C_0 = -1/48", 15734, c0(6, ELL_P, M_P, B_P), Fr(-1, 48), "paper", r"C_0=-\frac1{48}"),
        ("floor -7/1200", 15847,
         high_exponent(6, ELL_P, M_P, B_P, Fr(7, 8), g[2], FLOOR_HELD, FLOOR_HELD / 2, Fr(1)),
         Fr(-7, 1200), "paper", r"=-\frac7{1200}<0"),
        ("large-delta endpoint -1/48 - delta/16 at delta = 5/6", 15945,
         high_exponent(6, ELL_P, M_P, B_P, Fr(7, 8), g[2], ALPHA_P, ALPHA_P / 2, 1 - ALPHA_P),
         Fr(-1, 48) - ALPHA_P / 16, "paper", r"=-\frac1{48}-\frac{\delta}{16}"),
        ("supply 8/39", 16116, ELL_P / g[2], Fr(8, 39), "paper", r"\ge\frac8{39}"),
        ("inverse capacity 7/37", 15382, inverse_capacity_max(C_P), Fr(7, 37), "paper",
         r"=7/37"),
        ("worst point 79/204: -E_* = 7/30672", None,
         endpoint_neg_e(6, ELL_P, M_P, B_P, Fr(79, 204), Fr(1, 2), ALPHA_P, C_P),
         Fr(7, 30672), "hunt134", ("30672", "79/204", r"\frac{79}{204}")),
        ("floor ceiling 13/15 in the limit delta_0 -> 0", None,
         floor_ceiling(6, delta0=FLOOR_LIMIT)["sigma0"], Fr(13, 15), "hunt134",
         ("13/15", r"\frac{13}{15}")),
    ]
    out = []
    for name, line, got, want, source, extra in rows:
        d = {"name": name, "line": line, "got": got, "want": want, "source": source}
        d["tex" if source == "paper" else "absent"] = extra
        out.append(d)
    return out


def main(argv=None) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--paper", action="store_true", help="also check every citation")
    ap.add_argument("--quick", action="store_true", help="skip the float optimisations")
    args = ap.parse_args(argv)

    bad = 0
    print("reproductions at k = 6 (the template must give back the paper and hunt 134):")
    for r in reproductions():
        ok = r["got"] == r["want"]
        bad += not ok
        where = f"line {r['line']:>5}" if r["source"] == "paper" else "hunt 134  "
        print(f"  {'ok  ' if ok else 'FAIL'} {where}  {r['name']}: {r['got']}")
    if args.paper:
        miss = verify_citations()
        bad += len(miss)
        print(f"citations: {len(CITATIONS) - len(miss)}/{len(CITATIONS)} on their line", miss)
        out = verify_outside_citations()
        bad += len(out)
        print(f"outside citations: {len(OUTSIDE_CITATIONS) - len(out)}/{len(OUTSIDE_CITATIONS)}"
              f" on their line", out)

    print("\nclosed-form walls per system order k (exact):")
    print("  k   Part I 1-1/(2k)   corner 1-3/(4k)   floor at 1/50: 1-25/(32k)   limit: 1-4/(5k)")
    for k in KS:
        p = system_prices(k)
        print(f"  {k:<3} {str(p['part_one']):<8} {float(p['part_one']):.6f}"
              f"   {str(p['corner']):<7} {float(p['corner']):.6f}"
              f"   {str(p['floor_held']):<8} {float(p['floor_held']):.7f}"
              f"   {str(p['floor_limit']):<6} {float(p['floor_limit']):.6f}")

    if not args.quick:
        for d0, lab in ((FLOOR_HELD, "paper's floor bin 1/50"), (FLOOR_LIMIT, "limit 0")):
            print(f"\nendpoint optimum (measured) with exact bounds (derived), {lab}:")
            for k in KS:
                for v in ("A", "B", "C"):
                    r = endpoint_optimum(k, v, floor_delta0=float(d0))
                    if not r["valid"]:
                        print(f"  k={k:<2} {v}: {r['reason']}")
                        continue
                    lb = best_exact_bound(k, v, delta0=d0)["sigma0_lower"]
                    ub = exact_upper_bound(k, v, delta0=d0, measured=r)
                    up = f"{float(ub['sigma0_upper']):.10f}" if ub["valid"] else "none"
                    print(f"  k={k:<2} {v}: sigma0 {r['sigma0']:.7f} (ell {r['ell']:.5f},"
                          f" b {r['b']:.4f}, delta {r['delta_bind']:.4f}, x {r['x_bind']:.3f},"
                          f" c {r['c']:.4f})   exact in [{float(lb):.10f}, {up}]")
            print("  relaxed ties (variant C with c = 2/(k kappa), admissible points):")
            for key, (k, kappa, need, source) in RELAXED_TIES.items():
                c = plain_coeff(k, kappa)
                r = endpoint_optimum(k, "C", floor_delta0=float(d0), c=float(c))
                lb = best_exact_bound(k, "C", delta0=d0, c=c, cuts=16)["sigma0_lower"]
                ub = exact_upper_bound(k, "C", delta0=d0, measured=r, c=c)
                up = f"{float(ub['sigma0_upper']):.10f}" if ub["valid"] else "none"
                needs = "nothing" if need is None else f"beta_* <= {need}"
                print(f"  {key}: c = {c}, needs {needs} ({source}): sigma0"
                      f" {r['sigma0']:.7f}   exact in [{float(lb):.10f}, {up}]")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())

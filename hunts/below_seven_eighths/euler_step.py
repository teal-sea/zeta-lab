"""Hunt #136, lane ``eulerstep``: exact local checks of the step where the 7/8
argument consumes the Euler product.

The step is Lemma 7.1 of OpenAI's 7/8 paper (``lem:local-euler``, paper.tex
lines 4010 to 4067), the scalar Euler identity, together with its Gauss-sum
input: Lemma 4.2 (prime Gauss identities, lines 766 to 775) and Lemma 4.4,
equation (4.7) (lines 964 to 969).  The 11/12 paper puts the same Gauss-sum
identity in its Appendix A.1; paper.tex has no appendix, and hunt #120 quotes the
11/12 form, which :func:`composite_signal_checks` checks under the 7/8 paper's
definitions.

What is computed here, and how (grades are those of MISSION.md):

* Exact arithmetic in ``Z[omega][zeta_N]`` (``omega = e^{2 pi i/3}``, ``N``
  prime to 3): an element is a pair of integer coefficient vectors indexed by
  powers of ``zeta_N``; products are exact integer cyclic convolutions
  (python-flint ``fmpz_poly`` or numpy), and equality is decided on the
  canonical coordinates in the power basis of each prime-power factor
  (:func:`canon_vec`).  No floating point enters an equality.
* The sextic residue symbol ``chi_p(a) = a^{(q_p - 1)/6} mod p`` on primary
  primes of ``Z[omega]``, the additive character ``e(z) = exp(2 pi i
  Tr(z/lambda))`` (paper line 610), and the Gauss sums ``G_r = g_{chi_p^r}(p,1)``.
* Lemma 7.1 two ways: generically, as an identity of truncated formal series
  in which the Gauss sums are symbols tied only by the relations the paper's
  proof names (:func:`lemma71_symbolic`); and at actual primes, with the true
  Gauss sums of that prime and no relation assumed, the identity multiplied
  through by G_1 so that gamma_1^{-1} is never formed (:func:`lemma71_at_prime`).
  The evaluation (7.8) of ``C_p`` is checked against its definition (7.7) by
  brute force over ``O/p^t`` (:func:`cp_bruteforce`), and table (7.16), all
  ten rows, completely on a window (:func:`family_table_complete`).
* Gamma(p^t) by direct summation over ``O/p^t``, t <= 3, so that (4.6)
  G(p^3) = gamma_3(p) is summed and not only read off the four-term formula
  (:func:`p_power_quadratic_direct`).
* Where the step binds: the exact exponents of H_p - 1 (every j, so every
  row u) and of Part II's principal multiplier B_p + 1 (:func:`euler_floor`,
  :func:`row_requirements`, :func:`principal_multiplier_report`), and the
  lines of paper.tex that consume the lemma (:func:`consumer_scan`).
* Rivals without an Euler product of the required kind (the
  Davenport-Heilbronn combination and the Epstein zeta of discriminant -15) and
  where the identity fails for them (:func:`rival_report`), with the table of
  EULER_STEP.md generated from the report (:func:`rival_table_rows`).
* Planted faults (:func:`planted_faults`, :func:`citation_faults`).

The word reserved for ``zeta/rigor.py`` appears nowhere here.  The ball
computations below use python-flint ``acb`` and are called *enclosed*.
"""

from __future__ import annotations

import hashlib
import math
import os
import time
from fractions import Fraction as Fr
from functools import lru_cache

import numpy as np

try:  # python-flint: exact polynomial products and ball enclosures
    import flint
    from flint import acb, acb_poly, arb, fmpq, fmpz_poly

    HAVE_FLINT = True
except Exception:  # pragma: no cover - the lab pins python-flint
    HAVE_FLINT = False

PAPER = os.path.join(os.environ.get("ZETA_LAB_CACHE", os.path.expanduser("~/.cache/zeta-lab")), "openai-math-adc7f124", "paper.tex")
PAPER_SHA256 = "42a5ee0febca59fd1def55cfd6c6808c322ef4237d7726303ea52f711deac6a3"
PAPER_LINES = 16677

# ---------------------------------------------------------------------------
# 0. Citations: (line, exact substring of that line of paper.tex)
# ---------------------------------------------------------------------------

CITATIONS = {
    # hypotheses and conventions
    "primary_generator": (581, "ideal coprime to $3$ has a unique generator congruent to $1\\pmod3$; we call"),
    "S_contains_6": (591, "finite set $S$ of prime ideals containing the primes above $6$ and the prime"),
    "sums_exclude_S": (603, "specified, ideal sums exclude $S$ and use primary generators."),
    "residue_field_1_mod_6": (627, "If $p\\notin S$ is prime, its residue field has order $P=q_p\\equiv1\\pmod6$:"),
    "sextic_symbol": (631, "\\chi_p(a)\\equiv a^{(P-1)/6}\\pmod p\\quad(p\\nmid a),"),
    "alpha_def": (575, "write $\\alpha(a)=a/|a|$."),
    "e_def": (610, "e(z)=\\exp\\bigl(2\\pi i\\operatorname{Tr}_{F/\\mathbb Q}(z/\\lambda)\\bigr)."),
    "gamma_def": (642, "\\gamma_j(c)=q_c^{-1/2}\\sum_{v\\bmod c}\\chi_c(v)^j e(v/c),"),
    "zero_power_convention": (639, "$1_{(a,c)=1}$, not the constant function one."),
    "S_contains_small_primes": (3340, "$\\widehat T$, and every prime of norm at most a fixed $P_0$."),
    # Lemma 4.2, 4.3, 4.4
    "lem42_head": (766, "\\begin{lemma}[Prime Gauss identities]\\label{lem:prime-gauss-identities}"),
    "lem42_a": (770, "\\gamma_2(p)^3=-\\alpha(p),\\qquad"),
    "lem42_b": (772, "=\\overline{H(4)}\\gamma_3(p)\\gamma_2(p)^3."),
    "lem42_c": (774, "For $j\\not\\equiv0\\pmod6$, one has $|\\gamma_j(p)|=1$."),
    "lem43_fourterm": (851, "$(1+i^{-b}+i^a+i^{b-a})/2$.  In particular $\\Gamma$ depends only on"),
    "lem43_bichar": (864, "=(-1)^{eh+fg+fh},\\qquad e,f,g,h\\in\\{0,1\\}."),
    "lem44_head": (935, "\\label{lem:fixed-gauss-phase}"),
    "lem44_reciprocity": (938, "\\chi_b(a)=\\mathcal R(a,b)\\chi_a(b),\\qquad"),
    "lem44_G": (946, "G(c)=\\overline{\\chi_c(4)}\\Gamma(c)."),
    "eq45": (951, "G(vw)=G(v)G(w)\\mathcal R(v,w),\\qquad G(1)=1."),
    "eq46_a": (955, "G(p^3)=\\gamma_3(p),\\qquad"),
    "eq46_b": (956, "\\mathcal R(p,p)=\\gamma_3(p)^2=\\chi_p(-1)."),
    "eq47_a": (966, "\\gamma_2(c)^3=\\mu(c)\\alpha(c),\\qquad"),
    "eq47_b": (967, "\\gamma_1(c)\\gamma_2(c)=\\mu(c)\\alpha(c)G(c),\\qquad"),
    "eq47_c": (968, "G(c)=\\overline{\\chi_c(4)}\\gamma_3(c),\\quad |G(c)|=1."),
    # Section 7
    "eq74_coefficient": (3820, "\\eta(A)\\Xi(A)^{-1}\\mathcal R(A,s)."),
    "local_params_rho": (3862, "\\rho=\\chi_p(u/p^j),\\qquad \\omega_p=\\chi_p(-1),\\\\"),
    "local_params_ap": (3863, "a_p=\\overline{\\alpha(p)}^3\\eta(p)^3,\\qquad"),
    "local_params_bp": (3864, "b_p=\\overline{\\alpha(p)}^2\\eta(p)^2\\overline{\\chi_p(4)},"),
    "local_params_R": (3866, "V=Q^{-6z},\\qquad R=a_p^2Q^{4-6x-6z},\\qquad"),
    "gamma_r_def": (3875, "$\\gamma_r=Q^{-1/2}G_r$ for $1\\le r\\le5$."),
    "gauss_lift_a": (3880, "Q^{t-1}G_r1_{j'=t-1},&6\\nmid r,\\\\"),
    "gauss_lift_b": (3881, "Q^t1_{j'\\ge t}-Q^{t-1}1_{j'\\ge t-1},&6\\mid r."),
    "G1Gm1": (3886, "$G_1G_{-1}=\\omega_pQ$."),
    "cp_fourth_case": (3907, "&t>0,\\ k=1,\\ j'\\ge1,\\\\"),
    "separation": (3995, "has therefore separated into prime factors.  In absolute convergence,"),
    "eq710_a": (4000, "(-1)^{e_0}\\gamma_1^{-e_0}\\eta(p)^{e_0}"),
    "eq710_b": (4002, "\\omega_p^{tk-e_0l-l(l-1)/2}C_p(t,k,j+6m)\\\\"),
    "eq710_c": (4004, "Q^{-(x+1/2)e_0-(1+3x)l-wk-6zm},\\qquad t=e_0+3l."),
    "lem71_hyp": (4011, "For every nonzero sixth-power-free $u$ with $(u,S)=1$ and every"),
    "lem71_hyp2": (4012, "prime $p\\notin S$, the factors just defined are"),
    "eq711_a": (4016, "\\frac{R(1-Q^{-1})-\\eta(p)(Q-1)"),
    "eq711_b": (4017, "Q^{-x-w}V^{1_{j\\le1}}}{1-V}+J_j\\right\\},\\\\"),
    "J0": (4025, "0&-\\eta(p)\\rho^{-1}Q^{-x}+W_{\\rm loc}R\\\\"),
    "J1": (4026, "1&\\eta(p)Q^{-x-w}\\\\"),
    "J2": (4027, "2&a_p\\rho^{-3}Q^{3/2-3x}\\\\"),
    "J3a": (4028, "3&-\\eta(p)b_p\\rho^{-2}Q^{2-3x-w}"),
    "J3b": (4029, "+b_p^2\\rho^{-4}Q^{2-4x}\\\\"),
    "J4": (4030, "4&-\\eta(p)a_p\\rho^{-3}Q^{5/2-4x-w}\\\\"),
    "J5": (4031, "5&-a_p^2Q^{3-6x}."),
    "H_def": (4038, "H_p=P_p\\frac{(1-V)(1-W)}{1-D},\\qquad"),
    "region_one": (4054, "x_r\\ge51/100,\\quad z_r\\ge17/50,\\quad w_r\\ge-1/100,\\quad"),
    "region_two": (4056, "x_r\\ge7/8,\\quad z_r\\ge33/200,\\quad w_r\\ge19/20."),
    "cH": (4064, "$c_H=4/5$."),
    "phase_reduction_2": (4121, "=-\\frac{\\overline{\\alpha(p)}}{G(p)}."),
    "H_defect": (4141, "\\frac{D(V+W-VW)-VW+(1-V)(1-W)\\mathcal E_p}{1-D}."),
    "region_two_bounds": (4173, "H_p-1=O(Q^{-363/200})\\quad(p\\nmid u),\\qquad"),
    "region_two_bounds_u": (4174, "H_p-1=O(Q^{-33/40})\\quad(p\\mid u)."),
    "tail_163": (4184, "above $P_0$ is $O(P_0^{-163/200})$ by the ideal count, which implies"),
    "u1_reciprocal": (4192, "$1/L^S(x,\\eta)$, and its numerator has the two principal factors"),
    # consumers
    "H_eta_def": (5520, "H_\\eta(s)=\\mathcal H_{\\eta,1}(s,1,1/6),\\qquad"),
    "H_eta_78": (5525, "Lemma~\\ref{lem:local-euler} makes $H_\\eta$ holomorphic on $\\Re s>7/8$."),
    "prop21_H": (413, "\\sup_{\\Re s>\\sigma_0}|H_\\eta(s)-1|\\le\\frac12."),
    "transfer_local": (6733, "For $p\\notin S_{\\mathbb Q}$, the local factors agree as follows.  If $p$"),
    "transfer_inert": (6741, "=(1-\\chi(p)p^{-s})^{-1}(1+\\chi(p)p^{-s})^{-1}."),
    "partII_G": (8687, "\\frac{(\\overline{\\eta(p)}Q^x-Q^{-w})(1-V)(1-W)P_p^*"),
    "partII_selected": (8718, "\\overline{\\eta(p)}Q^{x+z-1}P_p^*-Q^{z-w-1}P_p"),
    "partII_selected_rhs": (8719, "=\\frac{1-D}{(1-V)(1-W)}Q^{z-1}G_p."),
    "euler_absolute": (386, "Poles are not included. Absolute convergence of the Euler product excludes"),
    # range endpoints quoted in EULER_STEP.md
    "prop21_head": (400, "\\begin{proposition}[Continuation from a common signal]"),
    "F_def": (568, "Let $F=\\mathbb Q(\\sqrt{-3})$, let"),
    "lambda_def": (572, "\\lambda=\\sqrt{-3}=\\omega-\\omega^2=1+2\\omega."),
    "lem42_end": (775, "\\end{lemma}"),
    "lem43_head": (841, "\\begin{lemma}[Quadratic four-term formula]\\label{lem:quadratic-four-term}"),
    "lem43_end": (869, "\\end{lemma}"),
    "lem44_head_line": (934, "\\begin{lemma}[Sextic reciprocity and the fixed Gauss phase]"),
    "lem44_end": (972, "\\end{lemma}"),
    "S_probe": (3336, "Use one excluded set $S$ for the finite family"),
    "g_def": (3359, "g_\\psi(c,k)=\\sum_{d\\bmod c}\\psi(d)e(kd/c),\\qquad"),
    "G_r_def": (3874, "Write $G_r=g_{\\chi_p^r}(p,1)$, with $G_0=-1$, and"),
    "eq77_head": (3892, "\\begin{equation}\\label{eq:local-scalar-definition}"),
    "eq78_head": (3900, "\\begin{equation}\\label{eq:local-scalar-values}"),
    "eq79_head": (3930, "\\begin{equation}\\label{eq:local-unit-factor}"),
    "bstar_start": (3941, "At the primes of $b_*$, one has"),
    "bstar_end": (3951, "ray group $T$."),
    "pair_phases_head": (3953, "\\paragraph{Cancellation of the remaining pair phases.}"),
    "pair_product": (3979, "\\prod_{p<r}\\mathcal R(p,r)^{e_pl_r+e_rl_p+l_pl_r}"),
    "G_cn3": (3987, "$G(c)\\mathcal R(c,n)G(n^3)=G(cn^3)$, which is cancelled by the"),
    "eq710_head": (3997, "\\begin{equation}\\label{eq:local-P}"),
    "lem71_head": (4010, "\\begin{lemma}[The complete local identity]\\label{lem:local-euler}"),
    "lem71_end": (4067, "\\end{lemma}"),
    "gamma3_sq": (4079, "one because $\\gamma_3^2=\\omega_p$, $\\omega_p^2=1$, and $\\rho^6=1$."),
    "eq716_head": (4086, "\\begin{equation}\\label{eq:local-family-table}"),
    "phase_reduction_1": (4118, "=-\\alpha(p)\\overline{\\chi_p(4)}\\gamma_3,"),
    "gamma2gamma4": (4124, "from the first and $\\gamma_2\\gamma_4=1$."),
    "eq717_head": (4139, "\\begin{equation}\\label{eq:local-H-defect}"),
    "epsH": (4166, "Consequently, with $\\epsilon_H=\\min(\\epsilon_0,1/50)$,"),
    "eq102": (5531, "\\label{eq:shared-principal-nonvanishing}"),
    "prop113_head": (6705, "\\begin{proposition}[Quadratic transfer]"),
    "partII_p_divides_u": (8832, "\\overline{\\eta(p)}Q^x(1-V)\\mathcal E_p-Q^{-w}H_p."),
    "jacobi_13": (803, "$J(H,H^3)=H(4)J(H,H)$."),
    "jacobi_22": (834, "$\\tau_2^3=J(H^2,H^2)\\tau_2\\tau_4=-pP$."),
    "supplement_start": (1005, "The element $-2$ is primary and $-1$ is a cube."),
    "supplement_end": (1009, "\\]"),
    "crt_rule": (1043, "\\gamma_j(ab)=\\chi_a(b)^j\\chi_b(a)^j\\gamma_j(a)\\gamma_j(b)."),
    "crt_cross": (1048, "$(\\chi_a(b)\\chi_b(a))^3=\\mathcal R(a,b)$."),
    "units_modulus_one": (3870, "The values $\\rho,a_p,b_p$ have absolute value one, and"),
    "pair_identity_i": (3957, "\\mathcal R(A,s)\\prod_p"),
    "pair_phases_end": (3992, "on the ray class of $p$."),
    "period_R": (4076, "In each family, increasing $r$ by one and the first permitted $m$"),
    "period_V": (4080, "Increasing $m$ further multiplies a summand by $V$."),
    "e_complex": (613, "$e(z)=\\exp(4\\pi i\\operatorname{Im}z/\\sqrt3)$."),
    # table (7.16): ten rows, the first for every j (added in the repair round)
    "four_families": (4075, "$(e_0,l)=(0,2r+2),(1,2r),(0,2r+1),(1,2r+1)$, where $r\\ge0$."),
    "G_p_def_head": (8685, "\\label{old-eq:5.13c}"),
    "eq716_first_row_any_j": (4083, "In its first row $j$ is arbitrary; all"),
    "eq716_omitted_zero": (4084, "Every omitted case is zero by"),
    "eq716_row1": (4089, "(0,2r+2)&0&m\\ge r+1&R(1-Q^{-1})V^{m-r-1}"),
    "eq716_row6": (4094, "(1,2r)&1&m\\ge r+1_{j\\le1}&-\\eta(p)(Q-1)Q^{-x-w}V^{m-r}"),
    "eq716_row10": (4098, "(1,2r+1)&1&j=4,\\ m=r&-\\eta(p)a_p\\rho^{-3}Q^{5/2-4x-w}"),
    # the shared analytic estimates and Part II: where the second region is consumed
    "D1_region": (5571, "\\mathcal D_1(\\epsilon_0)=\\{(s,w,z):{}&\\Re s\\ge51/100,"),
    "D2_region": (5574, "\\mathcal D_2=\\{(s,w,z):{}&\\Re s\\ge7/8,\\quad"),
    "D_regions_are_lemma71": (5578, "These are the two regions in Lemma~\\ref{lem:local-euler}."),
    "D2_holomorphic": (5609, "each point of $\\mathcal D_2$ and of every $\\mathcal D_1(\\epsilon_0)$."),
    "interface_mu_positive": (6201, "$\\mu>0$, chosen independently of $\\eta$, such that"),
    "residue_paths_in_D2": (6232, "The paths lie in $\\mathcal D_2$, so the correction"),
    "residue_paths_in_D2_b": (6239, "$\\mathcal D_2$, and $M(z)$ is holomorphic for $\\Re z>0$."),
    "principal_rectangle_in_D2": (6318, "rectangle lies in $\\mathcal D_2$.  Thus"),
    "large_rows_in_D2": (6479, "For the large rows, $(2,2,v)$ with $v>2$ lies in $\\mathcal D_2$."),
    "unselected_product": (8738, "\\label{eq:unselected-local-product}"),
    "majorant_region_two_a": (8748, "In the second Euler region the same"),
    "majorant_region_two_b": (8749, "argument uses the respective defect exponents $-363/200$ and $-33/40$."),
    "eq168_head": (8810, "G_p+v^{-1}H_p={}&"),
    "principal_local_head": (9051, "\\paragraph{The principal local factor.}"),
    "principal_Hp_lower": (9054, "and $H_p$ is bounded away from zero"),
    "principal_exponents_a": (9068, "-x_r,\\qquad -6z_r,\\qquad 4-5x_r-6z_r,"),
    "principal_exponents_b": (9069, "\\qquad 1-w_r-6z_r."),
    "principal_at_most_78": (9071, "Each is at most $-7/8$ in that region."),
    "principal_approx": (9074, "\\mathcal B_p=-1+O(Q^{-7/8}),"),
    "principal_tuple_majorant": (9081, "unselected product has a bounded positive majorant by the second-region"),
    "sigma0_shared": (15532, "In the shared analytic lemmas take \\(\\sigma_0=7/8\\)."),
    "principal_approx_used": (15597, "\\(\\mathcal B_p=-1+O(q_p^{-7/8})\\)"),
    "residue_point": (15599, "at \\(w=1,z=1/6\\), where"),
    "rho_i_bound": (15613, "|\\rho_i(s)|\\ll P_i^{-7/8}"),
    "kappaP_bound": (15619, "0<\\kappa_P<\\frac78\\min_i\\ell_i."),
    "kappaP_remainder": (15669, "&+Z^{C(\\beta_*)+e-\\kappa_P+\\epsilon},"),
    "kappaP_choice": (16304, "\\kappa_P=\\frac7{16}\\frac{\\ell}{K}=\\frac7{96K},"),
    "kappaP_choice_bound": (16305, "0<\\kappa_P<\\frac78\\min_i\\ell_i=\\frac7{48K},"),
    "mP_def": (16306, "m_P:=\\kappa_P."),
    "G_p_def_end": (8688, "-Q^{-w}(1-VW)}{1-D}."),
    "principal_local_end": (9077, "is the local estimate used to normalize the principal residue."),
    "e_below_mP": (16317, "e+\\epsilon_{\\rm pr}<m_P/4."),
    "m_common": (16366, "m=\\frac14\\min\\{m_{\\rm high},m_w,m_z,m_P\\}>0"),
    # second repair round: the whole local data block (7.6), the subsection's
    # bounds, the interface lemma's range, the dynamic region, p | u
    "local_params_Q_j": (3861, "Q=q_p,\\qquad j=v_p(u)\\in\\{0,\\ldots,5\\},\\qquad"),
    "local_params_Wloc": (3867, "W_{\\rm loc}=\\rho Q^{-w}."),
    "sec72_head": (3847, "\\subsection{The scalar Euler identity}"),
    "sec72_last": (4199, "Section~\\ref{sec:shared-analytic-estimates}."),
    "interface_sigma0_range": (6178, "$\\sigma_0\\in[7/8,1)$ with $\\beta_*>\\sigma_0$ and $0<e<10^{-3}$."),
    "dynamic_region": (8856, "x_r=a+16e,\\qquad w_r=1-a-6e,\\qquad z_r=17/50."),
    "W_D_vanish_at_p_divides_u": (8664, "$W=\\chi_p(u)Q^{-w}$: at $p\\mid u$, the latter and $D$ vanish, while the"),
    "divisor_product": (8747, "satisfies the divisor-product bound.  Omitting selected factors only removes"),
    # every line the consumer scan finds that was not cited above (see
    # CONSUMER_SCAN_LINES): the whole line, so that each is line-specific
    "scan_217": (217, "Section~\\ref{sec:local-euler}"),
    "scan_3380": (3380, "Section~\\ref{sec:local-euler}."),
    "scan_5467": (5467, "Section~\\ref{sec:local-euler}.  Equations~\\eqref{eq:probe-poisson-identity}"),
    "scan_5468": (5468, "and~\\eqref{eq:probe-high} give the actual integral to be estimated:"),
    "scan_5565": (5565, "The scalar quotient in Equation~\\eqref{eq:probe-high} is the part of the"),
    "scan_5655": (5655, "Equations~\\eqref{eq:probe-poisson-identity} and~\\eqref{eq:probe-high}"),
    "scan_5656": (5656, "prove the required identity, and Lemma~\\ref{lem:local-euler} gives the"),
    "scan_5842": (5842, "$\\beta_*+20e$.  These moves stay in $\\mathcal D_1(\\epsilon_0)$ for a fixed"),
    "scan_5859": (5859, "$\\mathcal D_1(\\epsilon_0)$, for example with $\\epsilon_0=10e$, and no"),
    "scan_5879": (5879, "and the other inequalities defining $\\mathcal D_1(10e)$ still hold."),
    "scan_5907": (5907, "For the base correction, Lemma~\\ref{lem:local-euler} verifies the hypotheses"),
    "scan_5910": (5910, "heights in both Euler regions; for $q_u\\le Z^D$, taking $\\epsilon=1$ gives"),
    "scan_5933": (5933, "$\\mathcal D_1(10e)$, so the stronger local estimate in"),
    "scan_5934": (5934, "Lemma~\\ref{lem:local-euler} gives"),
    "scan_6294": (6294, "holomorphic there by Lemma~\\ref{lem:local-euler}, and is bounded there by"),
    "scan_6418": (6418, "$\\mathcal D_1(3/8)$: at the final point"),
    "scan_6469": (6469, "$\\mathcal D_1(3/8)$, since $\\beta_*>11/12$.  The local bound"),
    "scan_6784": (6784, "Suppose that $\\beta_*>11/12$.  Lemma~\\ref{lem:local-euler} and"),
    "scan_8658": (8658, "of Lemma~\\ref{lem:local-euler}; in the shared analytic estimates its variable"),
    "scan_8662": (8662, "Lemma~\\ref{lem:local-euler}, write $x_r=\\Re x$, $w_r=\\Re w$, and $z_r=\\Re z$."),
    "scan_8690": (8690, "At points in the Euler regions where the raw quotient in"),
    "scan_8695": (8695, "Lemma~\\ref{lem:local-euler}, together with its formula for $P_p^*$, show"),
    "scan_8696": (8696, "that $G_p$ is holomorphic in both stated Euler regions, including at zeros"),
    "scan_8699": (8699, "At points in the Euler regions where the selected quotients are defined,"),
    "scan_8714": (8714, "Equation~\\eqref{eq:probe-high} has been extracted.  To verify this assertion,"),
    "scan_8727": (8727, "the scalar quotient in Equation~\\eqref{eq:probe-high} times its summand in"),
    "scan_8729": (8729, "no division by $P_p$ or $H_p$.  At points in the Euler regions where all"),
    "scan_8735": (8735, "Equation~\\eqref{eq:local-region-one}, put"),
    "scan_8737": (8737, "Lemma~\\ref{lem:local-euler} give, uniformly in the selected tuple,"),
    "scan_8757": (8757, "neighborhood of every point in both Euler regions.  It also satisfies"),
    "scan_8775": (8775, "Equations~\\eqref{eq:probe-poisson-identity} and \\eqref{eq:probe-high}"),
    "scan_8817": (8817, "This is an identity of holomorphic local expressions in the Euler regions."),
    "scan_8826": (8826, "and $1-D$, which are nonzero in the Euler regions; hence it gives the"),
    "scan_8909": (8909, "proof of Lemma~\\ref{lem:local-euler} sharpen to"),
    "scan_9046": (9046, "$U^\\epsilon$ by Lemma~\\ref{lem:local-euler}.  Relative to the"),
    "scan_9052": (9052, "In the second Euler region of Lemma~\\ref{lem:local-euler}, take"),
    "scan_9062": (9062, "\\qquad\\text{in the second Euler region}."),
    "scan_9084": (9084, "Euler region and uniformly in all imaginary parts,"),
    "scan_9134": (9134, "Both sets of lines lie in the first Euler region with $\\epsilon_0=3/8$."),
    "scan_15537": (15537, "correction is holomorphic in the two required Euler regions and satisfies"),
    "scan_15557": (15557, "Euler region.  In particular this holds on the entire rectangle in"),
    "scan_15594": (15594, "On the principal second Euler region, Section~\\ref{sec:local-compensation}"),
}

#: Section 7.2 of paper.tex, "The scalar Euler identity" (lines 3847 to 4199,
#: the lemma, its proof and the labels defined there)
SECTION_72 = (3847, 4199)

#: Every line of paper.tex outside Section 7.2 that names Lemma 7.1, refers to
#: a label defined in Section 7.2, says "Euler region", or names D_1 or D_2,
#: with the group EULER_STEP.md assigns it.  Groups: "pointer" (a pointer, the
#: notation or the regions' definitions: no requirement on the local factors);
#: "region_one" (only D_1 or region (7.14), whose floors do not involve the
#: target); "principal" (region two at the row u = 1); "every_row" (region two
#: at every row u, usually with region one); "identity" ((7.13) used as an
#: identity, no bound).  :func:`consumer_scan` repeats the scan.
CONSUMER_SCAN_LINES = {
    217: "pointer", 3380: "pointer", 5467: "pointer", 5571: "pointer", 5574: "pointer",
    5578: "pointer", 8658: "pointer", 8662: "pointer",
    5842: "region_one", 5859: "region_one", 5879: "region_one", 5933: "region_one",
    5934: "region_one", 6418: "region_one", 6469: "region_one", 8735: "region_one",
    8737: "region_one", 8909: "region_one", 9046: "region_one", 9134: "region_one",
    5525: "principal", 6232: "principal", 6239: "principal", 6294: "principal",
    6318: "principal", 6784: "principal", 9052: "principal", 9062: "principal",
    9084: "principal", 15557: "principal", 15594: "principal",
    5609: "every_row", 5656: "every_row", 5907: "every_row", 5910: "every_row",
    6479: "every_row", 8690: "every_row", 8695: "every_row", 8696: "every_row",
    8699: "every_row", 8729: "every_row", 8748: "every_row", 8757: "every_row",
    8817: "every_row", 8826: "every_row", 15537: "every_row",
    5468: "identity", 5565: "identity", 5655: "identity", 8714: "identity",
    8727: "identity", 8775: "identity",
}


def paper_available() -> bool:
    return os.path.isfile(PAPER)


def paper_sha256() -> str:
    with open(PAPER, "rb") as fh:
        return hashlib.sha256(fh.read()).hexdigest()


def check_citations(citations=None) -> dict:
    """Every citation's snippet must occur on its line of the pinned source
    (on that line, not merely somewhere in the file: :func:`citation_faults`
    plants shifted line numbers to show it)."""
    with open(PAPER, encoding="utf-8") as fh:
        lines = fh.read().split("\n")
    out = {}
    for key, (n, snip) in (CITATIONS if citations is None else citations).items():
        out[key] = bool(snip) and 1 <= n <= len(lines) and snip in lines[n - 1]
    return out


def citation_faults() -> dict:
    """Planted faults for the citation checker: every citation moved one line
    down, and every citation moved one line up, must fail (True = all red).  A
    checker weakened to a search of the whole file would let them pass."""
    down = check_citations({k: (n + 1, s) for k, (n, s) in CITATIONS.items()})
    up = check_citations({k: (n - 1, s) for k, (n, s) in CITATIONS.items()})
    one = dict(CITATIONS)
    one["region_two"] = (CITATIONS["region_two"][0] + 1, CITATIONS["region_two"][1])
    return {
        "every_citation_shifted_down_fails": not any(down.values()),
        "every_citation_shifted_up_fails": not any(up.values()),
        "one_wrong_line_fails": check_citations(one)["region_two"] is False,
    }


def consumer_scan() -> dict:
    """The lines of paper.tex outside Section 7.2 that name Lemma 7.1, refer to
    a label defined in Section 7.2, say "Euler region" (any case), or name
    D_1 or D_2: {line: [reasons]}."""
    import re

    with open(PAPER, encoding="utf-8") as fh:
        lines = fh.read().split("\n")
    lo, hi = SECTION_72
    labels = set()
    for n in range(lo, hi + 1):
        labels.update(re.findall(r"\\label\{([^}]*)\}", lines[n - 1]))
    hits = {}
    for n, line in enumerate(lines, 1):
        if lo <= n <= hi:
            continue
        why = []
        if re.search(r"euler region", line, re.I):
            why.append("Euler region")
        if "\\mathcal D_1" in line or "\\mathcal D_2" in line:
            why.append("D_1 or D_2")
        for lab in sorted(labels):
            if re.search(r"ref\{" + re.escape(lab) + r"\}", line):
                why.append(lab)
        if why:
            hits[n] = why
    return hits


def paper_has_appendix() -> bool:
    """paper.tex has no ``\\appendix`` and no appendix section."""
    with open(PAPER, encoding="utf-8") as fh:
        text = fh.read()
    return ("\\appendix" in text) or ("\\begin{appendices}" in text)


# ---------------------------------------------------------------------------
# 1. Z[omega]
# ---------------------------------------------------------------------------
# An element a + b*omega is the tuple (a, b); omega^2 = -1 - omega.

def emul(x, y):
    a, b = x
    c, d = y
    return (a * c - b * d, a * d + b * c - b * d)


def eadd(x, y):
    return (x[0] + y[0], x[1] + y[1])


def esub(x, y):
    return (x[0] - y[0], x[1] - y[1])


def eneg(x):
    return (-x[0], -x[1])


def econj(x):
    return (x[0] - x[1], -x[1])


def enorm(x):
    a, b = x
    return a * a - a * b + b * b


def epow(x, n):
    r = (1, 0)
    for _ in range(n):
        r = emul(r, x)
    return r


#: zeta_6^k for k = 0..5, with zeta_6 = 1 + omega = e^{i pi/3}
UNIT6 = ((1, 0), (1, 1), (0, 1), (-1, 0), (-1, -1), (0, -1))
UA = np.array([u[0] for u in UNIT6], dtype=np.int64)
UB = np.array([u[1] for u in UNIT6], dtype=np.int64)
LAMBDA = (1, 2)  # sqrt(-3) = 1 + 2 omega
OMEGA = (0, 1)


def is_primary(x) -> bool:
    return (x[0] - 1) % 3 == 0 and x[1] % 3 == 0


def primary_associate(x):
    for u in UNIT6:
        y = emul(u, x)
        if is_primary(y):
            return y
    raise ValueError(f"{x} has no primary associate (it meets 3)")


def ediv_exact(x, y):
    n = enorm(y)
    z = emul(x, econj(y))
    if z[0] % n or z[1] % n:
        return None
    return (z[0] // n, z[1] // n)


def ecomplex(x) -> complex:
    return complex(x[0] - x[1] / 2.0, x[1] * math.sqrt(3.0) / 2.0)


def unit_index(x):
    """k with x = zeta_6^k, or None."""
    for k, u in enumerate(UNIT6):
        if u == x:
            return k
    return None


# ---------------------------------------------------------------------------
# 2. Rational primes and the primes of Z[omega]
# ---------------------------------------------------------------------------

def primes_upto(n: int) -> list:
    if n < 2:
        return []
    sieve = np.ones(n + 1, dtype=bool)
    sieve[:2] = False
    for p in range(2, int(n ** 0.5) + 1):
        if sieve[p]:
            sieve[p * p:: p] = False
    return [int(p) for p in np.nonzero(sieve)[0]]


def element_of_norm(ell: int):
    """Some a + b omega with norm ell, or None (exhaustive in b)."""
    bmax = int(math.isqrt(4 * ell // 3)) + 1
    for b in range(0, bmax + 1):
        disc = 4 * ell - 3 * b * b
        if disc < 0:
            break
        r = math.isqrt(disc)
        if r * r == disc and (b + r) % 2 == 0:
            a = (b + r) // 2
            if enorm((a, b)) == ell:
                return (a, b)
    return None


def _xgcd(x: int, y: int):
    """(g, s, t) with s*x + t*y = g = gcd >= 0."""
    old_r, r = x, y
    old_s, s = 1, 0
    old_t, t = 0, 1
    while r:
        q = old_r // r
        old_r, r = r, old_r - q * r
        old_s, s = s, old_s - q * s
        old_t, t = t, old_t - q * t
    if old_r < 0:
        old_r, old_s, old_t = -old_r, -old_s, -old_t
    return old_r, old_s, old_t


def _mod_pow_vec(base, e: int, m: int):
    """Elementwise base**e mod m for an int64 array with entries < m <= 2^31."""
    result = np.ones_like(base)
    b = base % m
    while e:
        if e & 1:
            result = (result * b) % m
        b = (b * b) % m
        e >>= 1
    return result


def _fl_pow_vec(xa, xb, e: int, ell: int):
    """(xa + xb omega)^e in F_ell[omega], elementwise on int64 arrays."""
    ra = np.ones_like(xa)
    rb = np.zeros_like(xb)
    ba, bb = xa % ell, xb % ell
    while e:
        if e & 1:
            ra, rb = (ra * ba - rb * bb) % ell, (ra * bb + rb * ba - rb * bb) % ell
        ba, bb = (ba * ba - bb * bb) % ell, (2 * ba * bb - bb * bb) % ell
        e >>= 1
    return ra, rb


class Prime:
    """A primary prime ``pi`` of Z[omega] outside S (norm prime to 6)."""

    def __init__(self, pi):
        pi = tuple(int(v) for v in pi)
        if not is_primary(pi):
            raise ValueError(f"{pi} is not primary")
        self.pi = pi
        self.Q = enorm(pi)
        if self.Q % 2 == 0 or self.Q % 3 == 0:
            raise ValueError("p must lie outside the primes above 6")
        r = math.isqrt(self.Q)
        if r * r == self.Q and _is_prime(r):
            self.kind, self.ell = "inert", r
            if pi[1] != 0:
                raise ValueError("inert primes are rational up to a unit")
        elif _is_prime(self.Q):
            self.kind, self.ell = "split", self.Q
            # omega -> r in F_ell, from pi = a + b omega = 0 mod pi
            self.r = (-pi[0] * pow(pi[1], -1, self.ell)) % self.ell
            assert (self.r * self.r + self.r + 1) % self.ell == 0
        else:
            raise ValueError(f"{pi} is not prime")
        if (self.Q - 1) % 6:
            raise ValueError("residue field order not 1 mod 6")
        self.e6 = (self.Q - 1) // 6
        # residues of the six roots of unity, for decoding the symbol
        self._roots = {}
        for k, u in enumerate(UNIT6):
            self._roots[self._code_scalar(u)] = k
        assert len(self._roots) == 6, "sixth roots of unity not distinct mod p"

    # residue codes -------------------------------------------------------
    def _code_scalar(self, x):
        if self.kind == "split":
            return (x[0] + x[1] * self.r) % self.ell
        return ((x[0] % self.ell), (x[1] % self.ell))

    def chi_exp(self, x):
        """k with chi_p(x) = zeta_6^k, or None when p | x (zero extension)."""
        if self.kind == "split":
            c = (x[0] + x[1] * self.r) % self.ell
            if c == 0:
                return None
            return self._roots[pow(c, self.e6, self.ell)]
        a, b = x[0] % self.ell, x[1] % self.ell
        if a == 0 and b == 0:
            return None
        ra, rb = _fl_pow_vec(np.array([a]), np.array([b]), self.e6, self.ell)
        return self._roots[(int(ra[0]), int(rb[0]))]

    def chi_vec(self, xa, xb):
        """Vectorised chi_p on arrays: (exponent array, mask of units)."""
        xa = np.asarray(xa, dtype=np.int64)
        xb = np.asarray(xb, dtype=np.int64)
        k = np.zeros(xa.shape, dtype=np.int64)
        if self.kind == "split":
            c = (xa + xb * self.r) % self.ell
            mask = c != 0
            v = _mod_pow_vec(np.where(mask, c, 1), self.e6, self.ell)
            lut = np.full(self.ell, -1, dtype=np.int64)
            for code, kk in self._roots.items():
                lut[code] = kk
            k = lut[v]
        else:
            a, b = xa % self.ell, xb % self.ell
            mask = (a != 0) | (b != 0)
            ra, rb = _fl_pow_vec(np.where(mask, a, 1), np.where(mask, b, 0), self.e6, self.ell)
            lut = np.full(self.ell * self.ell, -1, dtype=np.int64)
            for (ca, cb), kk in self._roots.items():
                lut[ca * self.ell + cb] = kk
            k = lut[ra * self.ell + rb]
        assert np.all(k[mask] >= 0)
        return np.where(mask, k, 0), mask

    def __repr__(self):
        return f"Prime({self.pi}, Q={self.Q}, {self.kind})"


@lru_cache(maxsize=None)
def _is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    f = 3
    while f * f <= n:
        if n % f == 0:
            return False
        f += 2
    return True


def split_primes(ell: int):
    """The two non-associate primary primes above a rational ell = 1 mod 3."""
    x = element_of_norm(ell)
    assert x is not None
    p1 = primary_associate(x)
    p2 = econj(p1)
    assert is_primary(p2) and ediv_exact(p1, p2) is None
    return [Prime(p1), Prime(p2)]


def inert_prime(ell: int):
    return Prime((-ell, 0))


def primes_of_norm_upto(B: int):
    """All primary primes outside S with norm <= B (split and inert)."""
    out = []
    for ell in primes_upto(B):
        if ell in (2, 3):
            continue
        if ell % 3 == 1:
            out.extend(split_primes(ell))
        elif ell * ell <= B:
            out.append(inert_prime(ell))
    out.sort(key=lambda P: (P.Q, P.pi))
    return out


# ---------------------------------------------------------------------------
# 3. Exact cyclotomic arithmetic over Z[omega]
# ---------------------------------------------------------------------------

@lru_cache(maxsize=None)
def _factor(n: int):
    out, d = [], 2
    while d * d <= n:
        if n % d == 0:
            e = 0
            while n % d == 0:
                n //= d
                e += 1
            out.append((d, e))
        d += 1
    if n > 1:
        out.append((n, 1))
    return tuple(out)


@lru_cache(maxsize=None)
def _canon_plan(N: int):
    if N % 3 == 0:
        raise ValueError("Q(omega) is inside Q(zeta_N) when 3 | N; coordinates would not be unique")
    plan = []
    for p, e in _factor(N):
        n = p ** e
        c = pow(N // n, -1, n) if N != n else 1
        plan.append((p, n, c))
    return tuple(plan)


def _canon_tensor(v, N: int):
    plan = _canon_plan(N)
    shape = tuple(n for (_, n, _) in plan)
    T = np.zeros(shape, dtype=v.dtype)
    j = np.arange(N)
    idx = tuple((j * c) % n for (_, n, c) in plan)
    T[idx] = v
    for axis, (p, n, _) in enumerate(plan):
        T = np.moveaxis(T, axis, 0)
        rest = T.shape[1:]
        T = T.reshape((p, n // p) + rest)
        T = T[:-1] - T[-1:]
        T = T.reshape(((p - 1) * (n // p),) + rest)
        T = np.moveaxis(T, 0, axis)
    return T, idx, shape


def canon_vec(v, N: int):
    """Coordinates of sum_j v_j zeta_N^j in the tensor power basis (exact)."""
    v = np.asarray(v)
    if N == 1:
        return v.copy()
    return _canon_tensor(v, N)[0].ravel()


def reduced_vec(v, N: int):
    """A length-N representative of the same element whose nonzero entries are
    exactly its canonical coordinates (keeps products from growing)."""
    v = np.asarray(v)
    if N == 1:
        return v.copy()
    T, idx, shape = _canon_tensor(v, N)
    full = np.zeros(shape, dtype=v.dtype)
    full[tuple(slice(0, s) for s in T.shape)] = T
    return full[idx]


_LIM = 1 << 62


def _height(*arrs) -> int:
    return max((int(np.max(np.abs(a))) if a.size else 0) for a in arrs)


def _conv_cyclic(x, y, N: int):
    """Exact cyclic convolution of two integer vectors of length N.

    int64 inputs use numpy or flint with an int64 result (the caller has bounded
    the result); object inputs (Python integers) use flint's fmpz_poly."""
    big = x.dtype == object or y.dtype == object
    if N == 1:
        return x * y
    if big:
        pz = fmpz_poly([int(t) for t in x]) * fmpz_poly([int(t) for t in y])
        c = [int(t) for t in pz.coeffs()]
        z = np.zeros(2 * N - 1, dtype=object)
        z[:] = 0
        for i, v in enumerate(c):
            z[i] = v
    elif N <= 400 or not HAVE_FLINT:
        z = np.convolve(x, y)
    else:
        pz = fmpz_poly(x.tolist()) * fmpz_poly(y.tolist())
        if pz.height_bits() > 60:
            raise OverflowError("coefficient growth beyond int64")
        c = pz.coeffs()
        z = np.zeros(2 * N - 1, dtype=np.int64)
        if c:
            z[: len(c)] = np.array([int(t) for t in c], dtype=np.int64)
    out = z[:N].copy()
    tail = z[N:]
    out[: len(tail)] += tail
    return out


def _obj(a):
    return a if a.dtype == object else a.astype(object)


class Cyc:
    """An element sum_j (a_j + b_j omega) zeta_N^j of Z[omega][zeta_N]."""

    __slots__ = ("N", "a", "b")

    def __init__(self, N, a, b):
        self.N = int(N)
        a = np.asarray(a)
        b = np.asarray(b)
        if a.dtype == object or b.dtype == object:
            self.a, self.b = _obj(a), _obj(b)
        else:
            self.a = a.astype(np.int64)
            self.b = b.astype(np.int64)

    def big(self):
        return Cyc(self.N, _obj(self.a), _obj(self.b))

    @staticmethod
    def scalar(z, N=1):
        dt = object if max(abs(int(z[0])), abs(int(z[1]))) >= _LIM else np.int64
        a = np.zeros(N, dtype=dt)
        b = np.zeros(N, dtype=dt)
        a[0], b[0] = int(z[0]), int(z[1])
        return Cyc(N, a, b)

    @staticmethod
    def zero(N=1):
        return Cyc(N, np.zeros(N, dtype=np.int64), np.zeros(N, dtype=np.int64))

    def lift(self, M: int):
        if M == self.N:
            return self
        if M % self.N:
            raise ValueError("cannot lift to a non-multiple order")
        dt = object if self.a.dtype == object else np.int64
        a = np.zeros(M, dtype=dt)
        b = np.zeros(M, dtype=dt)
        idx = np.arange(self.N) * (M // self.N)
        a[idx] = self.a
        b[idx] = self.b
        return Cyc(M, a, b)

    def _common(self, other):
        M = self.N * other.N // math.gcd(self.N, other.N)
        return self.lift(M), other.lift(M)

    def __add__(self, other):
        x, y = self._common(other)
        if _height(x.a, x.b) + _height(y.a, y.b) >= _LIM:
            x, y = x.big(), y.big()  # exact Python integers from here on
        return Cyc(x.N, x.a + y.a, x.b + y.b)

    def __sub__(self, other):
        return self + (-other)

    def __neg__(self):
        return Cyc(self.N, -self.a, -self.b)

    def smul(self, z):
        """Multiply by the Z[omega] scalar z = (z0, z1)."""
        z0, z1 = int(z[0]), int(z[1])
        x = self
        if 3 * _height(self.a, self.b) * (abs(z0) + abs(z1)) >= _LIM:
            x = self.big()
        return Cyc(x.N, x.a * z0 - x.b * z1, x.a * z1 + x.b * z0 - x.b * z1)

    def __mul__(self, other):
        if isinstance(other, (int, np.integer)):
            return self.smul((int(other), 0))
        if isinstance(other, tuple):
            return self.smul(other)
        if self.N == 1:
            return other.smul((int(self.a[0]), int(self.b[0])))
        if other.N == 1:
            return self.smul((int(other.a[0]), int(other.b[0])))
        x, y = self._common(other)
        N = x.N
        if 8 * N * _height(x.a, x.b) * _height(y.a, y.b) >= _LIM:
            x, y = x.big(), y.big()
        ac = _conv_cyclic(x.a, y.a, N)
        bd = _conv_cyclic(x.b, y.b, N)
        s = _conv_cyclic(x.a + x.b, y.a + y.b, N)
        return Cyc(N, reduced_vec(ac - bd, N), reduced_vec(s - ac - 2 * bd, N))

    __rmul__ = __mul__

    def conj(self):
        idx = (-np.arange(self.N)) % self.N
        dt = object if self.a.dtype == object else np.int64
        a = np.zeros(self.N, dtype=dt)
        b = np.zeros(self.N, dtype=dt)
        a[idx] = self.a - self.b
        b[idx] = -self.b
        return Cyc(self.N, a, b)

    def canon(self):
        return np.concatenate([canon_vec(self.a, self.N), canon_vec(self.b, self.N)])

    def is_zero(self) -> bool:
        return not np.any(self.canon())

    def __eq__(self, other):
        if not isinstance(other, Cyc):
            return NotImplemented
        return (self - other).is_zero()

    __hash__ = None

    def as_scalar(self):
        """The Z[omega] value if this element lies in Z[omega], else None."""
        ca = canon_vec(self.a, self.N)
        cb = canon_vec(self.b, self.N)
        if np.any(ca[1:]) or np.any(cb[1:]):
            return None
        return (int(ca[0]), int(cb[0]))

    def ball(self, prec: int = 128):
        """Complex ball containing this element (python-flint acb)."""
        old = flint.ctx.prec
        try:
            flint.ctx.prec = prec
            z = acb(arb(fmpq(2, self.N))).exp_pi_i()
            om = acb(arb(-1) / 2, arb(3).sqrt() / 2)
            A = acb_poly([int(t) for t in self.a])
            B = acb_poly([int(t) for t in self.b])
            return A(z) + B(z) * om
        finally:
            flint.ctx.prec = old

    def to_complex(self) -> complex:
        j = np.arange(self.N)
        z = np.exp(2j * np.pi * j / self.N)
        om = complex(-0.5, math.sqrt(3.0) / 2.0)
        return complex(np.sum(self.a * z) + om * np.sum(self.b * z))


# ---------------------------------------------------------------------------
# 4. Residues, additive characters, Gauss sums
# ---------------------------------------------------------------------------

def hnf(m):
    """Basis (A, 0), (B1, g) of the lattice m*O in coordinates (a, b)."""
    ma, mb = m
    v1 = (ma, mb)
    v2 = (-mb, ma - mb)  # m * omega
    g, s, t = _xgcd(mb, ma - mb)
    w2a = s * v1[0] + t * v2[0]
    A = enorm(m) // g
    return A, w2a % A, g


@lru_cache(maxsize=256)
def residues(m):
    """Representatives x + y omega of O/m: 0 <= x < A, 0 <= y < g."""
    A, _, g = hnf(m)
    xs = np.tile(np.arange(A, dtype=np.int64), g)
    ys = np.repeat(np.arange(g, dtype=np.int64), A)
    return xs, ys


def reduce_mod(x, m):
    """The representative of x modulo m in the box of :func:`residues`."""
    A, B1, g = hnf(m)
    q = x[1] // g
    a = x[0] - q * B1
    return (a % A, x[1] - q * g)


@lru_cache(maxsize=None)
def add_order(m) -> int:
    """Exponent N of O/m: e(v/m) is an N-th root of unity."""
    q = enorm(m)
    cm = econj(m)
    k1 = cm[1]
    kw = emul(OMEGA, cm)[1]
    return q // math.gcd(q, abs(k1), abs(kw))


def add_exponent(xs, ys, m, h=(1, 0)):
    """Index j (mod N) with e(h v / m) = zeta_N^j, v = xs + ys omega.

    e(z) = exp(2 pi i Tr(z / lambda)); for z = w / m, Tr(z/lambda) equals the
    omega-coordinate of w * conj(m) divided by N(m) (derived in the docs)."""
    q = enorm(m)
    N = add_order(m)
    g0 = q // N
    p_, q_ = emul(h, econj(m))
    p_, q_ = p_ % q, q_ % q
    K = (xs % q) * q_ + (ys % q) * ((p_ - q_) % q)
    K %= q
    assert np.all(K % g0 == 0)
    return (K // g0) % N, N


def additive_character_crosscheck(trials: int = 400, seed: int = 7) -> float:
    """Second route for e(w/m), measured: the exact index of :func:`add_exponent`
    against exp(4 pi i Im(w/m)/sqrt 3) of paper line 613, in floating point.
    Returns the largest absolute difference over random w and moduli m."""
    rng = np.random.default_rng(seed)
    worst = 0.0
    mods = [P.pi for P in primes_of_norm_upto(200)] + [emul(split_primes(7)[0].pi, split_primes(13)[0].pi),
                                                        epow(split_primes(7)[0].pi, 3), (-5, 0), (25, 0)]
    for _ in range(trials):
        m = mods[int(rng.integers(len(mods)))]
        w = (int(rng.integers(-50, 51)), int(rng.integers(-50, 51)))
        idx, N = add_exponent(np.array([w[0]]), np.array([w[1]]), m)
        exact = np.exp(2j * np.pi * int(idx[0]) / N)
        z = ecomplex(w) / ecomplex(m)
        ref = np.exp(4j * np.pi * z.imag / math.sqrt(3.0))
        worst = max(worst, abs(exact - ref))
    return worst


def _cyc_from(N, idx, kexp, mask=None):
    if mask is not None:
        idx = idx[mask]
        kexp = kexp[mask]
    a = np.bincount(idx, weights=UA[kexp], minlength=N)
    b = np.bincount(idx, weights=UB[kexp], minlength=N)
    return Cyc(N, np.rint(a).astype(np.int64), np.rint(b).astype(np.int64))


def char_on(xs, ys, chars):
    """Combined exponent and unit mask of prod chi_P^e on residues."""
    k = np.zeros(xs.shape, dtype=np.int64)
    mask = np.ones(xs.shape, dtype=bool)
    for P, e in chars:
        kk, mm = P.chi_vec(xs, ys)
        k = (k + e * kk) % 6
        mask &= mm
    return k, mask


_CHAR_CACHE: dict = {}


def _char_table(m, chars):
    key = (m, tuple((P.pi, e) for P, e in chars))
    hit = _CHAR_CACHE.get(key)
    if hit is None:
        xs, ys = residues(m)
        hit = char_on(xs, ys, chars)
        if len(_CHAR_CACHE) > 64:
            _CHAR_CACHE.clear()
        _CHAR_CACHE[key] = hit
    return hit


def gauss_vec(m, chars, h=(1, 0), swap=False):
    """sum_{v mod m} prod chi_P(v)^e e(h v/m), with every zero extension kept.

    ``chars`` is a list of (Prime, exponent); an exponent divisible by six is
    the coprimality indicator (paper line 639).  ``swap=True`` replaces each
    symbol by its conjugate (a planted fault)."""
    xs, ys = residues(m)
    k, mask = _char_table(m, chars)
    if swap:
        k = (-k) % 6
    idx, N = add_exponent(xs, ys, m, h)
    return _cyc_from(N, idx, k, mask)


def quad_gauss_vec(m):
    """sum_{x mod m} e(x^2/m)."""
    xs, ys = residues(m)
    sa = xs * xs - ys * ys
    sb = 2 * xs * ys - ys * ys
    idx, N = add_exponent(sa, sb, m)
    return _cyc_from(N, idx, np.zeros_like(idx))


# ---------------------------------------------------------------------------
# 5. The quadratic phase: four-term formula, square classes, G
# ---------------------------------------------------------------------------

def _ipow(k):
    return [(1, 0), (0, 1), (-1, 0), (0, -1)][k % 4]


def gamma4(c):
    """Lemma 4.3: Gamma(c) = (1 + i^{-b} + i^a + i^{b-a})/2 for odd c = a + b omega.

    Returned as the exponent k with Gamma(c) = i^k (it is a fourth root of
    unity on odd c; asserted)."""
    a, b = c
    terms = [(1, 0), _ipow(-b), _ipow(a), _ipow(b - a)]
    re = sum(t[0] for t in terms)
    im = sum(t[1] for t in terms)
    val = (Fr(re, 2), Fr(im, 2))
    for k in range(4):
        if (Fr(_ipow(k)[0]), Fr(_ipow(k)[1])) == val:
            return k
    raise ValueError(f"Gamma({c}) = {val} is not a unit")


def square_class(c):
    """(e, f) with c = (-1)^e lambda^f u^2 mod 4 for odd c (Lemma 4.3)."""
    cr = (c[0] % 4, c[1] % 4)
    squares = [(1, 0), (0, 1), (-1, -1)]  # 1, omega, omega^2
    for e in (0, 1):
        for f in (0, 1):
            base = emul((-1, 0) if e else (1, 0), LAMBDA if f else (1, 0))
            for s in squares:
                r = emul(base, s)
                if (r[0] % 4, r[1] % 4) == cr:
                    return (e, f)
    raise ValueError(f"{c} is not odd")


def rfrak(c1, c2) -> int:
    """The bicharacter (4.4): r((-1)^e lambda^f, (-1)^g lambda^h) = (-1)^{eh+fg+fh}."""
    e, f = square_class(c1)
    g, h = square_class(c2)
    return (-1) ** (e * h + f * g + f * h)


def chi_c(c_primes, x):
    """chi_c(x) = prod chi_p(x)^{v_p}: exponent mod 6, or None if (x, c) != 1."""
    k = 0
    for P, v in c_primes:
        kk = P.chi_exp(x)
        if kk is None:
            return None
        k = (k + v * kk) % 6
    return k


def G_phase12(c, c_primes) -> int:
    """G(c) = conj(chi_c(4)) Gamma(c) as an exponent of zeta_12."""
    k4 = chi_c(c_primes, (4, 0))
    return (-2 * k4 + 3 * gamma4(c)) % 12


# ---------------------------------------------------------------------------
# 6. Lemma 4.2 and (4.6), (4.7) at a prime: exact checks
# ---------------------------------------------------------------------------

def prime_gauss_checks(P: Prime, balls: bool = True, swap: bool = False, perturb: bool = False) -> dict:
    """Exact checks of Lemma 4.2 and of (4.6), (4.7) at the prime P.

    Unnormalised Gauss sums G_r = Q^{1/2} gamma_r(p) are exact elements of
    Z[omega][zeta_ell]; each identity is restated without square roots:

    * L42a:  gamma_2^3 = -alpha(p)            <=>  G_2^3 = -p Q
    * L42b:  gamma_1 gamma_2 = conj(H(4)) gamma_3 gamma_2^3
                                              <=>  Q G_1 G_2 = conj(chi(4)) G_3 G_2^3
    * E47b:  gamma_1 gamma_2 = mu alpha G     <=>  G_1 G_2 = -p conj(chi(4)) Gq
    * GAMMA: Gamma(p) = gamma_3(p) (used in Lemma 4.4) <=> Gq = G_3
    * |gamma_j| = 1 for j = 1..5 <=> G_j conj(G_j) = Q
    * G1Gm1: G_1 G_{-1} = omega_p Q (paper line 3886)
    * G2G4:  gamma_2 gamma_4 = 1 (line 4124)
    * G3SQ:  gamma_3^2 = chi_p(-1) (4.6)
    * FOUR:  G_3 = Q^{1/2} Gamma_4term(p): the square exactly, the sign by an
             acb ball (``balls=True``), so this entry is enclosed, not exact
    * G_ABS: |G(p)| = 1 <=> Gq conj(Gq) = Q (exact; G(p) = conj(chi_p(4)) Gamma(p))
    * G_p3:  G(p^3) = gamma_3(p) (4.6), here only through the four-term formula
             at the non-squarefree index p^3 (Lemma 4.3 at c = p^3) and
             chi_p(4)^3 = 1.  Gamma(p^3) is not summed here: the direct sum over
             O/p^3 is :func:`p_power_quadratic_direct`, run at small norms only
             because O/p^3 has Q^3 elements.
    * RPP:   R(p, p) = chi_p(-1) (4.6)
    """
    pi, Q = P.pi, P.Q
    chars = lambda r: [(P, r)]
    G = {r: gauss_vec(pi, chars(r), swap=swap) for r in range(1, 6)}
    if perturb:  # plant: one coefficient of G_2 moved by one
        G[2] = Cyc(G[2].N, G[2].a.copy(), G[2].b.copy())
        G[2].a[1] += 1
    Gq = quad_gauss_vec(pi)
    k4 = P.chi_exp((4, 0))
    km1 = P.chi_exp((-1, 0))
    om_p = 1 if km1 == 0 else -1
    assert km1 in (0, 3)
    conj_chi4 = UNIT6[(-k4) % 6]
    out = {}
    G2sq = G[2] * G[2]
    G2cube = G2sq * G[2]
    out["L42a"] = G2cube == Cyc.scalar(emul(eneg(pi), (Q, 0)))
    s = G2cube.as_scalar()
    if s is not None:
        rhs = G[3].smul(emul(conj_chi4, s))
    else:
        rhs = (G[3] * G2cube).smul(conj_chi4)
    G1G2 = G[1] * G[2]
    out["L42b"] = (G1G2 * Q) == rhs
    out["E47b"] = G1G2 == Gq.smul(emul(eneg(pi), conj_chi4))
    out["GAMMA"] = Gq == G[3]
    out["G1Gm1"] = (G[1] * G[5]) == Cyc.scalar((om_p * Q, 0))
    out["G2G4"] = (G[2] * G[4]) == Cyc.scalar((Q, 0))
    out["G3SQ"] = (G[3] * G[3]) == Cyc.scalar((om_p * Q, 0))
    # conjugation symmetry conj(G_j) = chi^{6-j}(-1) G_{6-j}, which with the
    # three products above gives |G_j|^2 = Q for every j = 1..5
    sym = True
    for j in range(1, 6):
        sign = 1 if (((6 - j) * km1) % 6) == 0 else -1
        sym &= G[j].conj() == G[6 - j] * sign
    out["CONJ"] = sym
    out["ABS"] = all((G[j] * G[j].conj()) == Cyc.scalar((Q, 0)) for j in (1, 2, 3)) and sym
    g4 = gamma4(pi)
    gsq = _ipow(2 * g4)  # Gamma(p)^2 = +-1
    out["FOUR_SQ"] = gsq == (om_p, 0) and (G[3] * G[3]) == Cyc.scalar((gsq[0] * Q, 0))
    if balls and HAVE_FLINT:
        v = G[3].ball()
        unit = [acb(1), acb(0, 1), acb(-1), acb(0, -1)][(-g4) % 4]  # conj(Gamma4)
        w = v * unit
        out["FOUR_SIGN"] = bool(w.real > 0) and bool(abs(w.imag) < 1e-20)
    # (4.6): G(p^3) = gamma_3(p) and R(p,p) = chi_p(-1)
    p3 = epow(pi, 3)
    out["G_p3"] = gamma4(p3) == g4 and (3 * k4) % 6 == 0
    out["RPP"] = rfrak(pi, pi) == om_p
    # |G(p)| = 1 (4.7 at a prime), computed: Gamma(p) = Q^{-1/2} Gq, so |Gq|^2 = Q
    out["G_ABS"] = (Gq * Gq.conj()) == Cyc.scalar((Q, 0))
    return out


def p_power_quadratic_direct(P: Prime, tmax: int = 3, balls: bool = True, fault=None) -> dict:
    """Gamma(p^t) by direct summation over O/p^t, t = 1..tmax, exactly.

    Gq_t = sum_{x mod p^t} e(x^2/p^t) = |p^t| Gamma(p^t) = Q^{t/2} Gamma(p^t)
    (Lemma 4.3, line 851).  Checked against the four-term formula at c = p^t:
    for even t, Gq_t = Q^{t/2} i^k exactly (k even is asserted: i is not in
    Q(omega, zeta_N) for odd N); for odd t, Gq_t^2 = Q^t i^{2k} exactly and the
    sign of Gq_t / (Q^{t/2} i^k) by an acb ball (enclosed).  At t = 3 the entry
    (4.6) G(p^3) = gamma_3(p) is checked exactly in the square-root-free form
    conj(chi_p(4))^3 Gq_3 = Q G_3, since G(p^3) = conj(chi_{p^3}(4)) Gamma(p^3)
    (line 946) and chi_{p^3} = chi_p^3.  ``fault='drop_Q'`` compares Gq_3 with
    G_3 instead (a planted fault)."""
    pi, Q = P.pi, P.Q
    k4 = P.chi_exp((4, 0))
    out = {}
    for t in range(1, tmax + 1):
        m = epow(pi, t)
        Gq = quad_gauss_vec(m)
        k = gamma4(m)
        if t % 2 == 0:
            ok_even = k % 2 == 0
            out[f"t{t}_exact"] = ok_even and Gq == Cyc.scalar((_ipow(k)[0] * Q ** (t // 2), 0))
        else:
            out[f"t{t}_square"] = (Gq * Gq) == Cyc.scalar((_ipow(2 * k)[0] * Q ** t, 0))
            if balls and HAVE_FLINT:
                w = Gq.ball() * [acb(1), acb(0, 1), acb(-1), acb(0, -1)][(-k) % 4]
                out[f"t{t}_sign"] = bool(w.real > 0) and bool(abs(w.imag) < 1e-20)
        if t == 3:
            G3 = gauss_vec(pi, [(P, 3)])
            unit = UNIT6[(-3 * k4) % 6]  # conj(chi_p(4))^3
            lhs = Gq.smul(unit)
            rhs = G3 if fault == "drop_Q" else G3 * Q
            out["G_p3_equals_gamma3"] = lhs == rhs
    return out


def p_power_quadratic_run(B: int = 43, tmax: int = 3, inert=((5, 3), (11, 3))) -> dict:
    """:func:`p_power_quadratic_direct` at every split prime of norm <= B and at
    the listed inert primes (ell, tmax)."""
    bad = []
    n = 0
    for ell in primes_upto(B):
        if ell % 3 != 1:
            continue
        for P in split_primes(ell):
            r = p_power_quadratic_direct(P, tmax)
            n += 1
            if not all(r.values()):
                bad.append((P.pi, [k for k, v in r.items() if not v]))
    for ell, tm in inert:
        r = p_power_quadratic_direct(inert_prime(ell), tm)
        n += 1
        if not all(r.values()):
            bad.append(((-ell, 0), [k for k, v in r.items() if not v]))
    return {"n": n, "bad": bad}


def a1_form_at_prime(P: Prime) -> bool:
    """The 11/12 paper's Appendix A.1 identity at a prime, under the 7/8
    definitions: mu(p) gamma_{-1}(p) = chi_p(-1) G(p)^{-1} conj(alpha(p)) gamma_2(p),
    restated as -Q G_5 = chi_p(-1) chi_p(4) conj(p) conj(Gq) G_2 (exact)."""
    G5 = gauss_vec(P.pi, [(P, 5)])
    G2 = gauss_vec(P.pi, [(P, 2)])
    Gq = quad_gauss_vec(P.pi)
    k4 = P.chi_exp((4, 0))
    km1 = P.chi_exp((-1, 0))
    lhs = G5.smul((-P.Q, 0))
    rhs = (Gq.conj() * G2).smul(emul(emul(UNIT6[km1], UNIT6[k4]), econj(P.pi)))
    return lhs == rhs


def jacobi_checks(P: Prime) -> dict:
    """Second route, exact in Z[omega]: the Jacobi sums of Lemma 4.2's proof.

    J(H^2, H^2) = -p (line 834, the unit fixed by the congruence mod 3) and
    J(H, H^3) = H(4) J(H, H) (line 803)."""
    xs, ys = residues(P.pi)
    k, mask = P.chi_vec(xs, ys)
    ys1 = -ys
    xs1 = 1 - xs
    k1, mask1 = P.chi_vec(xs1, ys1)
    both = mask & mask1

    def J(r1, r2):
        e = (r1 * k + r2 * k1) % 6
        e = e[both]
        return (int(UA[e].sum()), int(UB[e].sum()))

    k4 = P.chi_exp((4, 0))
    out = {
        "J22": J(2, 2) == eneg(P.pi),
        "J13": J(1, 3) == emul(UNIT6[k4], J(1, 1)),
        "Jabs": enorm(J(1, 1)) == P.Q and enorm(J(2, 2)) == P.Q,
    }
    return out


def inert_derived_checks(ell: int) -> dict:
    """Inert p = -ell: every G_r (6 does not divide r) equals ell exactly.

    Derivation (exact, checked against brute force for small ell by the tests):
    e(v/p) = zeta_ell^{-y} for v = x + y omega, so the additive character is
    trivial exactly on F_ell; chi_p is trivial on F_ell^* because 6 | ell + 1;
    hence G_r = (ell - 1) - c with c = sum_x chi^r(x + omega) = -1.  The
    relations of Lemma 4.2 then reduce to chi_p(4) = 1 and chi_p(-1) = 1, which
    are computed here by exponentiation."""
    P = inert_prime(ell)
    out = {}
    # premises
    out["trivial_on_Z"] = all(add_exponent(np.array([x]), np.array([0]), P.pi)[0][0] == 0 for x in (1, 2, ell - 1))
    jw, N = add_exponent(np.array([0]), np.array([1]), P.pi)
    out["nontrivial"] = N == ell and int(jw[0]) == (ell - 1) % ell
    out["chi_trivial_on_Fl"] = (ell + 1) % 6 == 0 and ((ell * ell - 1) // 6) % (ell - 1) == 0
    k4 = P.chi_exp((4, 0))
    km1 = P.chi_exp((-1, 0))
    out["chi4_is_1"] = k4 == 0
    out["chim1_is_1"] = km1 == 0
    # with G_r = ell, alpha(p) = -1, Q = ell^2
    Q = ell * ell
    out["L42a"] = ell ** 3 == -(-ell) * Q
    out["L42b"] = (k4 == 0)
    out["G1Gm1"] = (km1 == 0)
    out["FOUR"] = gamma4(P.pi) == 0  # Gamma(-ell) = 1 = G_3 / ell
    out["G_p3"] = gamma4(epow(P.pi, 3)) == 0
    out["RPP"] = rfrak(P.pi, P.pi) == 1
    return out


def inert_bruteforce(Lmax: int, balls: bool = False) -> dict:
    """Inert primes 5 <= ell <= Lmax by direct summation over F_{ell^2}: every
    check of :func:`prime_gauss_checks` and :func:`jacobi_checks`, and the
    reduction G_r = ell of :func:`inert_derived_checks` against the sum."""
    bad = []
    n = 0
    for ell in primes_upto(Lmax):
        if ell < 5 or ell % 3 != 2:
            continue
        P = inert_prime(ell)
        r = prime_gauss_checks(P, balls=balls)
        r.update(jacobi_checks(P))
        r["G_r_is_ell"] = all(gauss_vec(P.pi, [(P, k)]).as_scalar() == (ell, 0) for k in range(1, 6))
        n += 1
        if not all(r.values()):
            bad.append((ell, [k for k, v in r.items() if not v]))
    return {"n": n, "bad": bad}


def run_prime_gauss(B: int, balls: bool = True, jacobi: bool = True):
    """Lemma 4.2 / (4.6) / (4.7) at every prime of norm <= B (brute force)."""
    primes = primes_of_norm_upto(B)
    fails = []
    counts = {"split": 0, "inert": 0}
    t0 = time.time()
    for P in primes:
        r = prime_gauss_checks(P, balls=balls)
        if jacobi:
            r.update(jacobi_checks(P))
        counts[P.kind] += 1
        bad = [k for k, v in r.items() if not v]
        if bad:
            fails.append((P.pi, bad))
    return {"B": B, "counts": counts, "n": len(primes), "fails": fails, "seconds": time.time() - t0}


# ---------------------------------------------------------------------------
# 7. Lemma 7.1: the local series (7.10) and the closed form (7.11)
# ---------------------------------------------------------------------------

class FPoly:
    """Truncated formal series: key = ring exponents + (deg X, deg W, deg Z).

    X = Q^{-x}, W = Q^{-w}, Z = Q^{-z}; truncation is by these three degrees."""

    __slots__ = ("R", "t")

    def __init__(self, R, terms=None):
        self.R = R
        self.t = terms if terms is not None else {}

    def copy(self):
        return FPoly(self.R, dict(self.t))

    def __add__(self, o):
        out = dict(self.t)
        for k, c in o.t.items():
            if k in out:
                v = out[k] + c
                if self.R.czero(v):
                    del out[k]
                else:
                    out[k] = v
            else:
                out[k] = c
        return FPoly(self.R, out)

    def __neg__(self):
        return FPoly(self.R, {k: -c for k, c in self.t.items()})

    def __sub__(self, o):
        return self + (-o)

    def __mul__(self, o):
        if isinstance(o, (int, Fr)):
            if o == 0:
                return FPoly(self.R)
            return FPoly(self.R, {k: c * o for k, c in self.t.items()})
        R = self.R
        TX, TW, TZ = R.trunc
        n = R.nsym
        out = {}
        for k1, c1 in self.t.items():
            for k2, c2 in o.t.items():
                dx = k1[n] + k2[n]
                dw = k1[n + 1] + k2[n + 1]
                dz = k1[n + 2] + k2[n + 2]
                if dx > TX or dw > TW or dz > TZ:
                    continue
                key = R.norm(tuple(a + b for a, b in zip(k1, k2)))
                v = c1 * c2
                if key in out:
                    v = out[key] + v
                    if R.czero(v):
                        del out[key]
                        continue
                out[key] = v
        return FPoly(R, out)

    def __pow__(self, e: int):
        r = self.R.one()
        for _ in range(e):
            r = r * self
        return r

    def is_zero(self):
        return self.R.poly_is_zero(self)


def geometric(R, y: FPoly) -> FPoly:
    """1/(1 - y) truncated (y must have positive degree)."""
    out = R.one()
    term = R.one()
    for _ in range(200):
        term = term * y
        if not term.t:
            return out
        out = out + term
    raise RuntimeError("geometric series did not truncate")


class SymRing:
    """Generic route: every Gauss sum is a symbol.

    Symbols: eta, alpha, chi4 (cube root of unity), rho (sixth root of unity),
    g1 = gamma_1, g3 = gamma_3 with g3^2 = om, om = omega_p = +-1, sQ = Q^{1/2}.
    The only relations imposed are the ones the proof of Lemma 7.1 names:
    gamma_1 gamma_2 = -alpha conj(chi(4)) gamma_3 (line 4118), gamma_2 gamma_4
    = 1 (line 4124), G_1 G_{-1} = omega_p Q (line 3886), gamma_3^2 = omega_p
    (line 4079), and that the unit symbols have modulus one (conj = inverse)."""

    names = ("eta", "alpha", "chi4", "rho", "g1", "g3", "om", "sQ")
    nsym = 8

    def __init__(self, trunc, relations=None):
        self.trunc = trunc
        self.rel = relations or {}

    def czero(self, c):
        return c == 0

    def norm(self, k):
        k = list(k)
        k[2] %= 3
        k[3] %= 6
        q, r = divmod(k[5], 2)
        k[5] = r
        k[6] = (k[6] + q) % 2
        return tuple(k)

    def mono(self, coef=1, X=0, W=0, Z=0, **e):
        key = [0] * (self.nsym + 3)
        for name, v in e.items():
            key[self.names.index(name)] = v
        key[self.nsym], key[self.nsym + 1], key[self.nsym + 2] = X, W, Z
        return FPoly(self, {self.norm(tuple(key)): Fr(coef)})

    def one(self):
        return self.mono(1)

    def zero(self):
        return FPoly(self)

    def Qpow(self, n):
        return self.mono(1, sQ=2 * n)

    def sQpow(self, n):
        return self.mono(1, sQ=n)

    def unit_pow(self, name, n):
        if name == "om":
            return self.mono(1, om=n)
        return self.mono(1, **{name: n})

    def var(self, name):
        return self.mono(1, **{name: 1})

    def const(self, name):
        m = self.mono
        if name == "eta":
            return m(1, eta=1)
        if name == "G1":
            return m(1, sQ=1, g1=1)
        if name == "G2":
            sgn = self.rel.get("G2_sign", -1)
            return m(sgn, sQ=1, alpha=1, chi4=-1, g3=1, g1=-1)
        if name == "G3":
            return m(1, sQ=1, g3=1)
        if name == "G4":
            return m(-1, sQ=1, alpha=-1, chi4=1, g3=-1, g1=1)
        if name == "G5":
            return m(1, sQ=1, om=1, g1=-1)
        if name == "g1inv":
            return m(1, g1=-1)
        if name == "g3bar":
            return m(1, g3=-1)
        if name == "ap":
            return m(1, alpha=-3, eta=3)
        if name == "bp":
            return m(1, alpha=-2, eta=2, chi4=-1)
        raise KeyError(name)

    def poly_is_zero(self, p):
        return not p.t


class CycRing:
    """Prime route: the true Gauss sums of one prime, exact; eta, rho, sQ formal.

    ``const('g1inv')`` = conj(G_1) Q^{-1/2} would use |G_1|^2 = Q.
    :func:`lemma71_at_prime` does not call it: it multiplies the identity
    through by G_1 instead, so route (b) assumes no relation between the
    Gauss sums (``const('g1inv')`` is kept only for other callers)."""

    names = ("eta", "rho", "sQ")
    nsym = 3

    def __init__(self, P: Prime, trunc):
        self.P = P
        self.trunc = trunc
        self.G = {r: gauss_vec(P.pi, [(P, r)]) for r in range(1, 6)}
        k4 = P.chi_exp((4, 0))
        km1 = P.chi_exp((-1, 0))
        self.om = 1 if km1 == 0 else -1
        self.conj_chi4 = UNIT6[(-k4) % 6]
        self.cpi = econj(P.pi)

    def czero(self, c):
        return not (np.any(c.a) or np.any(c.b))

    def norm(self, k):
        k = list(k)
        k[1] %= 6
        return tuple(k)

    def _mono(self, c: Cyc, X=0, W=0, Z=0, **e):
        key = [0] * (self.nsym + 3)
        for name, v in e.items():
            key[self.names.index(name)] = v
        key[3], key[4], key[5] = X, W, Z
        return FPoly(self, {self.norm(tuple(key)): c})

    def mono(self, coef=1, X=0, W=0, Z=0, **e):
        return self._mono(Cyc.scalar((int(coef), 0)), X=X, W=W, Z=Z, **e)

    def one(self):
        return self.mono(1)

    def zero(self):
        return FPoly(self)

    def Qpow(self, n):
        return self.mono(1, sQ=2 * n)

    def sQpow(self, n):
        return self.mono(1, sQ=n)

    def unit_pow(self, name, n):
        if name == "om":
            return self.mono(self.om ** (n % 2))
        return self.mono(1, **{name: n})

    def var(self, name):
        return self.mono(1, **{name: 1})

    def const(self, name):
        if name == "eta":
            return self.mono(1, eta=1)
        if name in ("G1", "G2", "G3", "G4", "G5"):
            return self._mono(self.G[int(name[1])])
        if name == "g1inv":
            return self._mono(self.G[1].conj(), sQ=-1)
        if name == "g3bar":
            return self._mono(self.G[3].conj(), sQ=-1)
        if name == "ap":
            return self._mono(Cyc.scalar(epow(self.cpi, 3)), eta=3, sQ=-3)
        if name == "bp":
            return self._mono(Cyc.scalar(emul(epow(self.cpi, 2), self.conj_chi4)), eta=2, sQ=-2)
        raise KeyError(name)

    def poly_is_zero(self, p):
        """Group by everything but sQ; c0 + c1 sQ = 0 is tested as c0 = c1 = 0."""
        groups = {}
        for k, c in p.t.items():
            groups.setdefault(k[:2] + k[3:], []).append((k[2], c))
        Q = self.P.Q
        for g, lst in groups.items():
            hmin = min(h for h, _ in lst)
            parts = {0: Cyc.zero(), 1: Cyc.zero()}
            for h, c in lst:
                d = h - hmin
                parts[d % 2] = parts[d % 2] + c * (Q ** (d // 2))
            if not (parts[0].is_zero() and parts[1].is_zero()):
                return False
        return True


def gauss_lift(R, r, t, jp):
    """g_{chi_p^r}(p^t, p^{j'}) for t >= 1 (paper lines 3877 to 3883)."""
    if r % 6:
        return R.Qpow(t - 1) * R.const(f"G{r % 6}") if jp == t - 1 else R.zero()
    out = R.zero()
    if jp >= t:
        out = out + R.Qpow(t)
    if jp >= t - 1:
        out = out - R.Qpow(t - 1)
    return out


def Cp_formula(R, t, k, jp, fault=None):
    """The complete evaluation (7.8) of C_p(t, k, j')."""
    if t == 0 and k == 0:
        return R.one()
    if t == 0:
        return R.one() if jp == 0 else R.zero()
    if k == 0:
        return gauss_lift(R, t, t, jp)
    if k == 1 and jp >= 1:
        g = "G5" if fault == "cp_G1_to_G5" else "G1"
        return R.unit_pow("om", -1) * R.const(g) * gauss_lift(R, t - 1, t, jp - 1)
    return R.zero()


def local_series(R, j, fault=None, e0_only=None, drop_g1inv=False):
    """P_p from its definition (7.10), with C_p from (7.8), truncated.

    ``e0_only`` in {0, 1} keeps only the terms with that e_0; ``drop_g1inv``
    omits the factor gamma_1^{-e_0}, so that the caller can multiply the
    identity through by G_1 instead of forming gamma_1^{-1}."""
    TX, TW, TZ = R.trunc
    out = R.zero()
    for e0 in (0, 1):
        if e0_only is not None and e0 != e0_only:
            continue
        for l in range(0, (TX - e0) // 3 + 1):
            t = e0 + 3 * l
            for k in range(0, TW + 1):
                for m in range(0, TZ // 6 + 1):
                    cp = Cp_formula(R, t, k, j + 6 * m, fault=fault)
                    if not cp.t:
                        continue
                    coef = R.one()
                    if e0 and drop_g1inv:
                        coef = -(coef * R.const("eta"))
                    elif e0:
                        coef = -(coef * R.const("g1inv") * R.const("eta"))
                    coef = coef * (R.const("ap") * R.const("g3bar")) ** l
                    coef = coef * R.unit_pow("rho", k - t)
                    om_exp = t * k - e0 * l - (l * (l - 1)) // 2
                    if fault == "om_drop_quadratic":
                        om_exp = t * k - e0 * l
                    coef = coef * R.unit_pow("om", om_exp)
                    coef = coef * cp * R.sQpow(-e0 - 2 * l)
                    coef = coef * R.mono(1, X=t, W=k, Z=6 * m)
                    out = out + coef
    return out


def local_series_star(R, j):
    """P_p^*: the series restricted to t > 0."""
    full = local_series(R, j)
    keep = {k: c for k, c in full.t.items() if k[R.nsym] > 0}
    return FPoly(R, keep)


def J_table(R, j, fault=None):
    eta = R.const("eta")
    X, Wv = R.var("X"), R.var("W")
    ap, bp = R.const("ap"), R.const("bp")
    rho = lambda n: R.unit_pow("rho", n)
    if j == 0:
        Rv = ap * ap * R.Qpow(4) * X ** 6 * R.var("Z") ** 6
        return -(eta * rho(-1) * X) + rho(1) * Wv * Rv
    if j == 1:
        return eta * X * Wv
    if j == 2:
        return ap * rho(-3) * R.sQpow(3) * X ** 3
    if j == 3:
        second = bp * bp * rho(-4) * R.sQpow(4) * X ** 4
        if fault == "J3_sign":
            second = -second
        return -(eta * bp * rho(-2) * R.sQpow(4) * X ** 3 * Wv) + second
    if j == 4:
        return -(eta * ap * rho(-3) * R.sQpow(5) * X ** 4 * Wv)
    if j == 5:
        return -(ap * ap * R.sQpow(6) * X ** 6)
    raise ValueError(j)


def local_closed(R, j, star_only=False, fault=None):
    """The closed form (7.11) of P_p^* and P_p, truncated."""
    X, Wv, Zv = R.var("X"), R.var("W"), R.var("Z")
    eta = R.const("eta")
    ap = R.const("ap")
    Rv = ap * ap * R.Qpow(4) * X ** 6 * Zv ** 6
    V = Zv ** 6
    Wl = R.unit_pow("rho", 1) * Wv
    gR, gV = geometric(R, Rv), geometric(R, V)
    Vind = V if j <= 1 else R.one()
    one = R.one()
    inner = (Rv * (one - R.Qpow(-1)) - eta * (R.Qpow(1) - one) * X * Wv * Vind) * gV + J_table(R, j, fault=fault)
    Pstar = gR * inner
    if star_only:
        return Pstar
    out = gV + Pstar
    if j == 0:
        out = out + Wl * geometric(R, Wl)
    return out


def lemma71_symbolic(trunc=(25, 3, 30), fault=None, relations=None) -> dict:
    """(7.10) == (7.11) for j = 0..5 as truncated formal series, exactly."""
    R = SymRing(trunc, relations=relations)
    out = {}
    for j in range(6):
        ser = local_series(R, j, fault=fault)
        cf = local_closed(R, j, fault=fault)
        diff = ser - cf
        star = local_series_star(R, j) - local_closed(R, j, star_only=True, fault=fault)
        homog = all(k[0] == k[R.nsym] for k in ser.t) and all(k[0] == k[R.nsym] for k in cf.t)
        out[j] = {
            "P_equal": not diff.t,
            "Pstar_equal": not star.t,
            "n_terms": len(ser.t),
            "eta_degree_equals_X_degree": homog,
            "first_mismatch": sorted(diff.t)[0] if diff.t else None,
        }
    return out


def lemma71_support(trunc=(25, 3, 30)) -> dict:
    """For each j: the (deg X, deg W, deg Z) with nonzero coefficient in P_p^*."""
    R = SymRing(trunc)
    out = {}
    for j in range(6):
        ser = local_series_star(R, j)
        out[j] = sorted({k[R.nsym:] for k in ser.t})
    return out


#: the ten rows of table (7.16), paper lines 4089 to 4098, in the paper's order:
#: (family, k, condition on (j, m) given r, name).  Families: "A" = (0, 2r+2),
#: "B" = (1, 2r), "C" = (0, 2r+1), "D" = (1, 2r+1) (line 4075).
TABLE_716_ROWS = (
    ("A", 0, lambda j, m, r: m >= r + 1, "row 1: (0,2r+2), k=0, m>=r+1, every j"),
    ("A", 0, lambda j, m, r: j == 5 and m == r, "row 2: (0,2r+2), k=0, j=5, m=r"),
    ("A", 1, lambda j, m, r: j == 0 and m == r + 1, "row 3: (0,2r+2), k=1, j=0, m=r+1"),
    ("B", 0, lambda j, m, r: j == 0 and m == r, "row 4: (1,2r), k=0, j=0, m=r"),
    ("B", 1, lambda j, m, r: j == 1 and m == r, "row 5: (1,2r), k=1, j=1, m=r"),
    ("B", 1, lambda j, m, r: m >= r + (1 if j <= 1 else 0), "row 6: (1,2r), k=1, m>=r+1_{j<=1}"),
    ("C", 0, lambda j, m, r: j == 2 and m == r, "row 7: (0,2r+1), k=0, j=2, m=r"),
    ("C", 1, lambda j, m, r: j == 3 and m == r, "row 8: (0,2r+1), k=1, j=3, m=r"),
    ("D", 0, lambda j, m, r: j == 3 and m == r, "row 9: (1,2r+1), k=0, j=3, m=r"),
    ("D", 1, lambda j, m, r: j == 4 and m == r, "row 10: (1,2r+1), k=1, j=4, m=r"),
)


def family_table_complete(rmax: int = 10, kmax: int = 2, mspan: int = 3, fault=None) -> dict:
    """Table (7.16) checked completely on a window, against the summand of (7.10).

    For every r <= rmax, each of the four families of line 4075, every
    k <= kmax, every j in 0..5 and every m <= r + mspan, the summand of (7.10)
    must equal R^r times the sum of the entries of the table rows whose
    conditions hold, and zero where no row applies ("Every omitted case is
    zero", line 4084).  Row 1 is stated for every j (line 4083) and row 6 for a
    j-dependent range of m; both are exercised at every j.  ``fault='row6_m_ge_r'``
    plants the wrong condition m >= r in row 6."""
    TX = 6 * rmax + 8
    R = SymRing((TX, kmax, 6 * (rmax + mspan) + 6))
    X, Wv, Zv = R.var("X"), R.var("W"), R.var("Z")
    eta, ap, bp = R.const("eta"), R.const("ap"), R.const("bp")
    rho = lambda n: R.unit_pow("rho", n)
    Rv = ap * ap * R.Qpow(4) * X ** 6 * Zv ** 6
    V = Zv ** 6
    one = R.one()

    def summand(e0, l, k, j, m):
        t = e0 + 3 * l
        cp = Cp_formula(R, t, k, j + 6 * m)
        if not cp.t:
            return R.zero()
        coef = one
        if e0:
            coef = -(coef * R.const("g1inv") * eta)
        coef = coef * (ap * R.const("g3bar")) ** l * rho(k - t)
        coef = coef * R.unit_pow("om", t * k - e0 * l - (l * (l - 1)) // 2)
        return coef * cp * R.sQpow(-e0 - 2 * l) * R.mono(1, X=t, W=k, Z=6 * m)

    def entry(i, j, m, r):
        """R^{-r} times the summand, as row i of the table states it."""
        if i == 0:
            return Rv * (one - R.Qpow(-1)) * V ** (m - r - 1)
        if i == 1:
            return -(ap * ap * R.sQpow(6) * X ** 6)
        if i == 2:
            return rho(1) * Wv * Rv
        if i == 3:
            return -(eta * rho(-1) * X)
        if i == 4:
            return eta * X * Wv
        if i == 5:
            return -(eta * (R.Qpow(1) - one) * X * Wv * V ** (m - r))
        if i == 6:
            return ap * rho(-3) * R.sQpow(3) * X ** 3
        if i == 7:
            return -(eta * bp * rho(-2) * R.sQpow(4) * X ** 3 * Wv)
        if i == 8:
            return bp * bp * rho(-4) * R.sQpow(4) * X ** 4
        if i == 9:
            return -(eta * ap * rho(-3) * R.sQpow(5) * X ** 4 * Wv)
        raise ValueError(i)

    def applies(i, fam, k, j, m, r):
        rf, rk, cond, _ = TABLE_716_ROWS[i]
        if rf != fam or rk != k:
            return False
        if fault == "row6_m_ge_r" and i == 5:
            return m >= r
        return cond(j, m, r)

    families = {"A": lambda r: (0, 2 * r + 2), "B": lambda r: (1, 2 * r),
                "C": lambda r: (0, 2 * r + 1), "D": lambda r: (1, 2 * r + 1)}
    n = n_nonzero = n_zero = 0
    bad = []
    js_by_row = {i: set() for i in range(len(TABLE_716_ROWS))}
    for r in range(rmax + 1):
        Rr = Rv ** r
        for fam, el in families.items():
            e0, l = el(r)
            for k in range(kmax + 1):
                for j in range(6):
                    for m in range(r + mspan + 1):
                        lhs = summand(e0, l, k, j, m)
                        rows = [i for i in range(len(TABLE_716_ROWS)) if applies(i, fam, k, j, m, r)]
                        rhs = R.zero()
                        for i in rows:
                            rhs = rhs + Rr * entry(i, j, m, r)
                            js_by_row[i].add(j)
                        n += 1
                        if rows:
                            n_nonzero += 1
                        else:
                            n_zero += 1
                        if (lhs - rhs).t:
                            bad.append((r, fam, k, j, m))
    return {"checked": n, "row_cases": n_nonzero, "omitted_cases": n_zero, "bad": bad,
            "js_by_row": {i: sorted(v) for i, v in js_by_row.items()}, "n_rows": len(TABLE_716_ROWS)}


def period_ratio_check(lmax: int = 40) -> dict:
    """The period structure (lines 4076 to 4080) for every l <= lmax.

    Going from (e0, l, k, m) to (e0, l + 2, k, m + 1) multiplies the summand of
    (7.10) by R: the omega_p exponent tk - e0 l - l(l-1)/2 changes by
    6k - 2e0 - (2l + 1), and conj(gamma_3)^2 = omega_p adds one more, so the net
    change 6k - 2e0 - 2l is even; the Gauss lift ratio is Q^6; and the remaining
    factor a_p^2 Q^{-2 - 6x - 6z} with Q^6 is R.  Checked here exactly: the parity
    for every (e0, k, l), and the lift ratio as a SymRing identity for t <= 3 lmax."""
    parity_ok = True
    for e0 in (0, 1):
        for k in (0, 1):
            for l in range(lmax + 1):
                t = e0 + 3 * l
                before = t * k - e0 * l - (l * (l - 1)) // 2
                after = (t + 6) * k - e0 * (l + 2) - ((l + 2) * (l + 1)) // 2
                parity_ok &= (after - before + 1) % 2 == 0
    R = SymRing((10 ** 6, 10 ** 6, 10 ** 6))
    lift_ok = True
    for t in range(1, 3 * lmax + 2):
        for r in range(0, 7):
            for jp in range(0, t + 2):
                lhs = gauss_lift(R, r + 6, t + 6, jp + 6)
                rhs = gauss_lift(R, r, t, jp) * R.Qpow(6)
                lift_ok &= not (lhs - rhs).t
    return {"parity": parity_ok, "lift_ratio_Q6": lift_ok}


def lemma71_at_prime(P: Prime, trunc=(13, 2, 18), fault=None) -> dict:
    """(7.10) == (7.11) at one prime with its true Gauss sums, j = 0..5.

    No relation between the Gauss sums is assumed.  The series is
    A + gamma_1^{-1} B (A from e_0 = 0, B from e_0 = 1 without the factor
    gamma_1^{-1}) and the closed form C contains no Gauss sum, so the identity
    A + gamma_1^{-1} B = C is tested in the equivalent form
    G_1 (A - C) + Q^{1/2} B = 0, using only the definition
    gamma_1 = Q^{-1/2} G_1 (line 3875) and G_1 != 0 (checked exactly, entry
    ``G1_nonzero``).  The other constants are definitions: conj(gamma_3) =
    Q^{-1/2} conj(G_3), a_p = conj(p)^3 Q^{-3/2} eta^3, b_p = conj(p)^2 Q^{-1}
    eta^2 conj(chi_p(4)), omega_p = chi_p(-1).  ``fault='multiplier_G5'``
    multiplies by G_5 in place of G_1 (a planted fault)."""
    R = CycRing(P, trunc)
    G1 = R._mono(R.G[5] if fault == "multiplier_G5" else R.G[1])
    sq = R.sQpow(1)
    inner_fault = None if fault == "multiplier_G5" else fault
    out = {"G1_nonzero": not R.G[1].is_zero()}
    for j in range(6):
        A = local_series(R, j, fault=inner_fault, e0_only=0)
        B = local_series(R, j, fault=inner_fault, e0_only=1, drop_g1inv=True)
        C = local_closed(R, j)
        out[j] = (G1 * (A - C) + sq * B).is_zero()
    return out


# ---------------------------------------------------------------------------
# 8. (7.7) by brute force over O/p^t, against (7.8); the Gauss lift formula
# ---------------------------------------------------------------------------

def _gauss_power(P, t, r, h):
    """g_{chi_p^r}(p^t, h) by direct summation over O/p^t."""
    m = epow(P.pi, t)
    return gauss_vec(m, [(P, r)], h=h)


def gauss_lift_bruteforce(P: Prime, tmax: int) -> list:
    """g_{chi_p^r}(p^t, p^{j'}) against lines 3877 to 3883, all r, t <= tmax."""
    G = {r: gauss_vec(P.pi, [(P, r)]) for r in range(1, 6)}
    Q = P.Q
    bad = []
    for t in range(1, tmax + 1):
        for r in range(0, 7):
            for jp in range(0, t + 2):
                direct = _gauss_power(P, t, r, epow(P.pi, jp))
                if r % 6:
                    formula = (G[r % 6] * (Q ** (t - 1))) if jp == t - 1 else Cyc.zero()
                else:
                    formula = Cyc.scalar(((Q ** t if jp >= t else 0) - (Q ** (t - 1) if jp >= t - 1 else 0), 0))
                if not direct == formula:
                    bad.append((t, r, jp))
    return bad


def Cp_direct(P: Prime, t: int, k: int, jp: int, fault=None) -> Cyc:
    """C_p(t, k, j') from its definition (7.7), by summation (exact).

    The sum runs over d mod p^k with p^{j'} = p^t d mod p^k, the summand is
    chi_p^k(d) g_{chi_p^t}(p^t, (p^{j'} - p^t d)/p^k); at modulus one both
    factors mean one (line 3898)."""
    pi = P.pi
    pit, pik, pij = epow(pi, t), epow(pi, k), epow(pi, jp)
    if k == 0:
        dlist = [((0, 0), 0)]
    else:
        xs, ys = residues(pik)
        kk, mask = P.chi_vec(xs, ys)
        dlist = []
        for x, y, e, ok in zip(xs.tolist(), ys.tolist(), kk.tolist(), mask.tolist()):
            if k % 6 == 0:
                if ok:
                    dlist.append(((x, y), 0))
            elif ok:
                dlist.append(((x, y), (k * e) % 6))
    total = Cyc.zero()
    for d, e in dlist:
        diff = esub(pij, emul(pit, d))
        if fault != "drop_congruence":
            if ediv_exact(diff, pik) is None:
                continue
            h = ediv_exact(diff, pik)
        else:
            h = ediv_exact(diff, pik) or diff
        inner = Cyc.scalar((1, 0)) if t == 0 else _gauss_power(P, t, t, h)
        total = total + inner.smul(UNIT6[e])
    return total


def cp_bruteforce(P: Prime, tmax: int, kmax: int, fault=None) -> dict:
    """(7.7) == (7.8) for 0 <= t <= tmax, 0 <= k <= kmax, 0 <= j' <= t + 2."""
    R = CycRing(P, (10 ** 6, 10 ** 6, 10 ** 6))
    bad, n = [], 0
    for t in range(0, tmax + 1):
        for k in range(0, kmax + 1):
            for jp in range(0, t + 3):
                direct = Cp_direct(P, t, k, jp, fault=fault)
                fp = Cp_formula(R, t, k, jp)
                # evaluate the formula (it has no formal symbols): sum c * Q^{h/2}
                val = Cyc.zero()
                ok_form = True
                for key, c in fp.t.items():
                    h = key[2]
                    if h % 2:
                        ok_form = False
                    val = val + c * (P.Q ** (h // 2))
                n += 1
                if not ok_form or not (direct == val):
                    bad.append((t, k, jp))
    return {"checked": n, "bad": bad}


# ---------------------------------------------------------------------------
# 9. Squarefree composites: (4.7), the CRT rule, the 11/12 form, reciprocity
# ---------------------------------------------------------------------------

def _prod(elems):
    r = (1, 0)
    for e in elems:
        r = emul(r, e)
    return r


def composite_signal_checks(primes: list, balls: bool = True, mu_fault: bool = False) -> dict:
    """(4.7) and the 11/12 Appendix A.1 form for c = product of distinct primes.

    Square-root-free restatements (q = q_c, Gq = sum_x e(x^2/c)):
    * gamma_2(c)^3 = mu alpha      <=>  G_2^3 = mu c q
    * gamma_1 gamma_2 = mu alpha G <=>  G_1 G_2 = mu c conj(chi_c(4)) Gq
    * G = conj(chi_c(4)) gamma_3   <=>  Gq = G_3, plus |Gq|^2 = q
    * 11/12 form mu gamma_{-1} = chi_c(-1) G^{-1} conj(alpha) gamma_2
                                   <=>  mu q G_5 = chi_c(-1) chi_c(4) conj(c) conj(Gq) G_2
    * Lemma 4.3 at c: Gq^2 = q Gamma_4term(c)^2 exactly and the sign enclosed.
    """
    c = _prod([P.pi for P in primes])
    cp = [(P, 1) for P in primes]
    q = enorm(c)
    mu = (-1) ** len(primes)
    if mu_fault:
        mu = -mu
    G = {r: gauss_vec(c, [(P, r) for P in primes]) for r in (1, 2, 3, 5)}
    Gq = quad_gauss_vec(c)
    k4 = chi_c(cp, (4, 0))
    km1 = chi_c(cp, (-1, 0))
    out = {}
    out["E47a"] = (G[2] * G[2] * G[2]) == Cyc.scalar(emul((mu, 0), (c[0] * q, c[1] * q)))
    out["E47b"] = (G[1] * G[2]) == Gq.smul(emul((mu, 0), emul(c, UNIT6[(-k4) % 6])))
    out["E47c"] = Gq == G[3]
    out["absGq"] = (Gq * Gq.conj()) == Cyc.scalar((q, 0))
    lhs = G[5].smul((mu * q, 0))
    rhs = (Gq.conj() * G[2]).smul(emul(emul(UNIT6[km1], UNIT6[k4]), econj(c)))
    out["A1_1112"] = lhs == rhs
    g4 = gamma4(c)
    gsq = _ipow(2 * g4)
    out["FOUR_SQ"] = (Gq * Gq) == Cyc.scalar((gsq[0] * q, 0))
    if balls and HAVE_FLINT:
        w = Gq.ball() * [acb(1), acb(0, 1), acb(-1), acb(0, -1)][(-g4) % 4]
        out["FOUR_SIGN"] = bool(w.real > 0) and bool(abs(w.imag) < 1e-20)
    return out


def crt_checks(A: list, B: list) -> dict:
    """gamma_j(ab) = chi_a(b)^j chi_b(a)^j gamma_j(a) gamma_j(b) (line 1043)."""
    a = _prod([P.pi for P in A])
    b = _prod([P.pi for P in B])
    out = {}
    for j in (1, 2, 3):
        Gab = gauss_vec(emul(a, b), [(P, j) for P in A + B])
        Ga = gauss_vec(a, [(P, j) for P in A])
        Gb = gauss_vec(b, [(P, j) for P in B])
        ka = chi_c([(P, 1) for P in A], b)
        kb = chi_c([(P, 1) for P in B], a)
        out[j] = Gab == (Ga * Gb).smul(UNIT6[(j * (ka + kb)) % 6])
    # the cross factor product for j = 1 and 2 is R(a, b) (line 1048)
    out["R"] = ((3 * (ka + kb)) % 6 == 0) == (rfrak(a, b) == 1)
    return out


def reciprocity_checks(B: int) -> dict:
    """Sextic reciprocity chi_b(a) = r(a, b) chi_a(b) on all pairs of primes of
    norm <= B, and the supplement chi_c(4) = (c / -2)_3 (lines 1005 to 1009)."""
    primes = primes_of_norm_upto(B)
    bad = []
    n = 0
    for Pa in primes:
        for Pb in primes:
            if Pa.pi == Pb.pi:
                continue
            ka = Pb.chi_exp(Pa.pi)  # chi_b(a)
            kb = Pa.chi_exp(Pb.pi)  # chi_a(b)
            r = rfrak(Pa.pi, Pb.pi)
            n += 1
            if (ka - kb - (0 if r == 1 else 3)) % 6:
                bad.append((Pa.pi, Pb.pi))
    sup_bad = []
    for P in primes:
        k4 = P.chi_exp((4, 0))  # sixth power residue of 4 = cubic residue of 2
        # the cubic character mod 2: c is congruent mod 2 to a unique cube root of unity
        cr = (P.pi[0] % 2, P.pi[1] % 2)
        cubes = {(1, 0): 0, (0, 1): 2, (1, 1): 4}  # 1, omega, omega^2 mod 2 as zeta_6^k
        if cubes.get(cr) != k4:
            sup_bad.append(P.pi)
    return {"pairs": n, "bad": bad, "primes": len(primes), "supplement_bad": sup_bad}


def lemma43_table() -> dict:
    """(4.4): Gamma on the four square classes and the bicharacter, exactly."""
    reps = {"1": (1, 0), "-1": (-1, 0), "lambda": LAMBDA, "-lambda": eneg(LAMBDA)}
    table = {name: gamma4(c) for name, c in reps.items()}
    ok_table = table == {"1": 0, "-1": 0, "lambda": 1, "-lambda": 3}
    # r(a, b) = Gamma(ab)/(Gamma(a)Gamma(b)) on all odd residues mod 4
    odd = [(a, b) for a in range(4) for b in range(4) if enorm((a, b)) % 2 == 1]
    ok_bichar = True
    for x in odd:
        for y in odd:
            lhs = (gamma4(emul(x, y)) - gamma4(x) - gamma4(y)) % 4
            rhs = 0 if rfrak(x, y) == 1 else 2
            ok_bichar &= lhs == rhs
    # Gamma depends only on c mod 4 and Gamma(c v^2) = Gamma(c)
    ok_mod4 = all(gamma4((a + 4 * s, b + 4 * u)) == gamma4((a, b)) for (a, b) in odd for s in (-1, 1) for u in (0, 2))
    ok_sq = all(gamma4(emul(x, emul(v, v))) == gamma4(x) for x in odd for v in odd)
    return {"table": ok_table, "bichar": ok_bichar, "mod4": ok_mod4, "square_invariance": ok_sq,
            "n_odd_classes": len(odd)}


def pair_phase_checks(primes: list, trials: int = 300, seed: int = 1) -> dict:
    """The pair-phase paragraph of Section 7.2 (lines 3953 to 3992), exactly.

    (i)   R(A,s) prod_p chi_p^{t_p}(s_p) chi_p^{-k_p}(A_p) = prod_p R(p,p)^{t_p k_p}
    (iii) prod_{p<r} R(p,r)^{e_p l_r + e_r l_p + l_p l_r}
          = R(c,n) G(n^3) prod_p conj(G(p^3))^{l_p} R(p,p)^{-e_p l_p - l_p(l_p-1)/2}
    (iv)  G(c) R(c,n) G(n^3) = G(c n^3)
    on random tuples of valuations over the given primes."""
    rng = np.random.default_rng(seed)
    bad = {"i": 0, "iii": 0, "iv": 0}
    for _ in range(trials):
        npr = len(primes)
        e = rng.integers(0, 2, npr).tolist()
        l = rng.integers(0, 3, npr).tolist()
        kv = rng.integers(0, 3, npr).tolist()
        tv = [e[i] + 3 * l[i] for i in range(npr)]
        A = _prod([epow(P.pi, tv[i]) for i, P in enumerate(primes)])
        s = _prod([epow(P.pi, kv[i]) for i, P in enumerate(primes)])
        cc = _prod([epow(P.pi, e[i]) for i, P in enumerate(primes)])
        nn = _prod([epow(P.pi, l[i]) for i, P in enumerate(primes)])
        # (i), all phases as exponents of zeta_6
        lhs = 0 if rfrak(A, s) == 1 else 3
        for i, P in enumerate(primes):
            s_p = _prod([epow(Q_.pi, kv[j]) for j, Q_ in enumerate(primes) if j != i])
            A_p = _prod([epow(Q_.pi, tv[j]) for j, Q_ in enumerate(primes) if j != i])
            lhs += tv[i] * P.chi_exp(s_p) - kv[i] * P.chi_exp(A_p)
        rhs = 0
        for i, P in enumerate(primes):
            rhs += (0 if rfrak(P.pi, P.pi) == 1 else 3) * tv[i] * kv[i]
        if (lhs - rhs) % 6:
            bad["i"] += 1
        # (iii) and (iv), as exponents of zeta_12
        cp_list = [(P, e[i]) for i, P in enumerate(primes)]
        np_list = [(P, 3 * l[i]) for i, P in enumerate(primes)]
        lhs3 = 0
        for i in range(npr):
            for j in range(i + 1, npr):
                ex = e[i] * l[j] + e[j] * l[i] + l[i] * l[j]
                lhs3 += (0 if rfrak(primes[i].pi, primes[j].pi) == 1 else 6) * ex
        n3 = epow(nn, 3)
        rhs3 = (0 if rfrak(cc, nn) == 1 else 6) + G_phase12(n3, np_list)
        for i, P in enumerate(primes):
            gp3 = G_phase12(epow(P.pi, 3), [(P, 3)])
            rhs3 += -gp3 * l[i]
            rpp = 0 if rfrak(P.pi, P.pi) == 1 else 6
            rhs3 += rpp * (-e[i] * l[i] - (l[i] * (l[i] - 1)) // 2)
        if (lhs3 - rhs3) % 12:
            bad["iii"] += 1
        cn3 = emul(cc, n3)
        full = [(P, e[i] + 3 * l[i]) for i, P in enumerate(primes)]
        lhs4 = G_phase12(cc, cp_list) + (0 if rfrak(cc, nn) == 1 else 6) + G_phase12(n3, np_list)
        if (lhs4 - G_phase12(cn3, full)) % 12:
            bad["iv"] += 1
    return {"trials": trials, "bad": bad}


# ---------------------------------------------------------------------------
# 10. Rational-function identities of Lemma 7.1 and Part II (sympy)
# ---------------------------------------------------------------------------

def local_rational_identities() -> dict:
    """(7.17) and the Part II local identities (16.4), (16.8) and the p | u form.

    Symbols: V, W, D, Q^x (= Qx), Q^{-w} (= Qw), eta-bar (= eb), and P^* free;
    P = 1/(1-V) + W/(1-W) + P^* for every p (W = W_loc when p does not divide u;
    W = D = 0 and j > 0 when p | u)."""
    import sympy as sp

    V, W, D, Ps, Qx, Qw, eb, v = sp.symbols("V W D Pstar Qx Qw etabar v")
    P = 1 / (1 - V) + W / (1 - W) + Ps
    H = P * (1 - V) * (1 - W) / (1 - D)
    E = Ps + D
    out = {}
    out["7.17"] = sp.simplify(H - 1 - (D * (V + W - V * W) - V * W + (1 - V) * (1 - W) * E) / (1 - D)) == 0
    Gp = ((eb * Qx - Qw) * (1 - V) * (1 - W) * Ps - Qw * (1 - V * W)) / (1 - D)
    lhs = eb * Qx * Ps - Qw * P  # Q^{z-1} cancels on both sides of (16.4)
    out["16.4"] = sp.simplify(lhs - (1 - D) / ((1 - V) * (1 - W)) * Gp) == 0
    # (16.8) on the raw quotient locus: D = eb^{-1}... with v = chi_p(u):
    # eb*Qx*D = 1/v and W/v = Qw (lines 8804 to 8806)
    Dv = 1 / (eb * Qx * v)
    Wv = v * Qw
    subs = {D: Dv, W: Wv}
    E2 = Ps + Dv
    lhs8 = (Gp + H / v).subs(subs)
    rhs8 = ((1 - V) * (1 - Wv) / (1 - Dv)) * ((1 / v - Qw) * (V / (1 - V) - Dv) + (eb * Qx + 1 / v - Qw) * E2)
    out["16.8"] = sp.simplify(lhs8 - rhs8) == 0
    # p | u: W = D = 0, G_p = eb Q^x (1 - V) E_p - Q^{-w} H_p (line 8832)
    sub0 = {W: 0, D: 0}
    out["16.8_p_divides_u"] = sp.simplify(Gp.subs(sub0) - (eb * Qx * (1 - V) * (Ps) - Qw * H.subs(sub0))) == 0
    return out


# ---------------------------------------------------------------------------
# 11. Exponent bookkeeping of the proof, and where the Euler step binds
# ---------------------------------------------------------------------------

def _hdefect_series(j, trunc=(19, 3, 24)):
    """H_p - 1 for one j as a truncated SymRing series (W = rho Q^{-w} when j = 0,
    W = D = 0 when j > 0)."""
    R = SymRing(trunc)
    X, Wv, Zv = R.var("X"), R.var("W"), R.var("Z")
    eta = R.const("eta")
    rho = R.unit_pow("rho", 1)
    one = R.one()
    P = local_closed(R, j)
    V = Zv ** 6
    if j == 0:
        Wfull = rho * Wv
        Dfull = eta * R.unit_pow("rho", -1) * X
    else:
        Wfull = R.zero()
        Dfull = R.zero()
    # H_p = P_p (1 - V)(1 - W)/(1 - D), the division by 1 - D as a geometric series
    H = P * (one - V) * (one - Wfull)
    if Dfull.t:
        H = H * geometric(R, Dfull)
    return R, H - one


def defect_exponents(j, point, trunc=(19, 3, 24)):
    """max over the monomials of H_p - 1 of Re(exponent of Q) at (x_r, w_r, z_r)."""
    R, Hm1 = _hdefect_series(j, trunc)
    x, w, z = point
    best = None
    for k in Hm1.t:
        h = Fr(k[7], 2)  # sQ exponent / 2
        dx, dw, dz = k[R.nsym:]
        ex = h - dx * x - dw * w - dz * z
        if best is None or ex > best[0]:
            best = (ex, (h, dx, dw, dz))
    return best


def _series_floor(R, series, w, z, threshold):
    """Smallest x_r with every monomial exponent < threshold at (w, z), or None
    when a monomial without X fails at every x_r.  Exponents are linear in x_r
    with slope -deg X <= 0, so the condition is exactly x_r > the returned value."""
    floor = Fr(-10 ** 6)
    for k in series.t:
        h = Fr(k[7], 2)
        dx, dw, dz = k[R.nsym:]
        assert dx >= 0
        base = h - dw * w - dz * z
        if dx == 0:
            if base >= threshold:
                return None
            continue
        floor = max(floor, (base - threshold) / dx)
    return floor


def euler_floor(j, w, z, trunc=(19, 3, 24), threshold=-1):
    """Smallest x_r for which every monomial of H_p - 1 has exponent < threshold
    at (w, z).  threshold = -1 is the floor of normal convergence of the product
    (and of the positive majorant of line 8749); threshold = 0 is the floor for
    H_p - 1 = O(Q^{-delta}) with some delta > 0, which is what "H_p is bounded
    away from zero after the same fixed enlargement of P_0" (line 9054) needs."""
    R, Hm1 = _hdefect_series(j, trunc)
    return _series_floor(R, Hm1, w, z, threshold)


def _principal_series(trunc=(13, 2, 18), v_sign=1):
    """The principal row's local multiplier, exactly: B_p + v^{-1} as a series.

    Part II (lines 9051 to 9077) takes u = 1, so j = 0, and defines
    B_p = G_p / H_p with G_p from lines 8686 to 8688,
    G_p = [(conj(eta(p)) Q^x - Q^{-w})(1-V)(1-W) P_p^* - Q^{-w}(1 - VW)]/(1 - D),
    and H_p from (7.12).  Here P_p, P_p^* are the closed forms (7.11),
    W = v Q^{-w}, D = eta(p) conj(v) Q^{-x}, and v = chi_p(u) is kept as the
    formal unit rho (rho = chi_p(u) when j = 0; v = 1 at u = 1, and no exponent
    depends on it).  Returned: (R, B_p + v^{-1}, H_p - 1), computed as
    (G_p + v^{-1} H_p) times the geometric series for 1/H_p, with every term of
    X-degree >= TX dropped: the factor conj(eta(p)) Q^x lowers the X-degree by
    one, so degree TX is incomplete.  ``v_sign = -1`` plants a fault: it forms
    G_p - v^{-1} H_p, in which the -1 of line 9074 does not cancel."""
    R = SymRing(trunc)
    TX = trunc[0]
    X, Wv, Zv = R.var("X"), R.var("W"), R.var("Z")
    eta = R.const("eta")
    v, vinv = R.unit_pow("rho", 1), R.unit_pow("rho", -1)
    one = R.one()
    V = Zv ** 6
    W = v * Wv
    D = eta * vinv * X
    P = local_closed(R, 0)
    Ps = local_closed(R, 0, star_only=True)
    gD = geometric(R, D)
    H = P * (one - V) * (one - W) * gD
    etabar_Qx = R.mono(1, X=-1, eta=-1)
    G = ((etabar_Qx - Wv) * (one - V) * (one - W) * Ps - Wv * (one - V * W)) * gD
    num = G + vinv * H * v_sign
    B1 = num * geometric(R, one - H)

    def cut(p):
        return FPoly(R, {k: c for k, c in p.t.items() if k[R.nsym] < TX})

    return R, cut(B1), cut(H - one)


def cited_principal_exponents(point):
    """The four error exponents of line 9068 to 9069: -x_r, -6z_r,
    4 - 5x_r - 6z_r, 1 - w_r - 6z_r."""
    x, w, z = point
    return [-x, -6 * z, 4 - 5 * x - 6 * z, 1 - w - 6 * z]


def principal_multiplier_exponents(point, trunc=(13, 2, 18), v_sign=1):
    """(max over the monomials of B_p + 1 of the Q-exponent at the point, the
    sorted list of (h, deg X, deg W, deg Z) attaining it)."""
    R, B1, _ = _principal_series(trunc, v_sign=v_sign)
    x, w, z = point
    vals = []
    for k in B1.t:
        h = Fr(k[7], 2)
        dx, dw, dz = k[R.nsym:]
        vals.append((h - dx * x - dw * w - dz * z, (h, dx, dw, dz)))
    best = max(v for v, _ in vals)
    return best, sorted({m for v, m in vals if v == best})


#: rational points (x_r, w_r, z_r) for the comparison with line 9068: the
#: residue point, the region-two floors and points inside D_2, with x_r from
#: just above the floor 3/5 up to 3/2
PRINCIPAL_GRID = tuple(
    (x, w, z)
    for x in (Fr(61, 100), Fr(2, 3), Fr(7, 10), Fr(3, 4), Fr(4, 5), Fr(7, 8), Fr(9, 10), Fr(1), Fr(3, 2))
    for (w, z) in ((Fr(1), Fr(1, 6)), (Fr(19, 20), Fr(33, 200)), (Fr(1), Fr(33, 200)),
                   (Fr(19, 20), Fr(1, 6)), (Fr(3, 2), Fr(1, 4)), (Fr(2), Fr(1, 2)))
)


def principal_multiplier_float_crosscheck(trials: int = 6, seed: int = 11) -> float:
    """Second route for :func:`_principal_series`, measured: B_p + v^{-1}
    evaluated directly from the closed forms (7.11), (7.12) and the formula for
    G_p (lines 8686 to 8688) in complex floats, against the truncated series
    evaluated at the same point.  Points have Q = 7, random unit phases and real
    parts large enough that the dropped degrees are below 1e-11.  Returns the
    largest absolute difference."""
    rng = np.random.default_rng(seed)
    R, B1, _ = _principal_series()
    worst = 0.0
    for _ in range(trials):
        Q = 7.0
        x = complex(1.5 + rng.random(), 3 * rng.standard_normal())
        w = complex(5.0 + rng.random(), 3 * rng.standard_normal())
        z = complex(0.6 + rng.random() / 2, 3 * rng.standard_normal())
        u = lambda: complex(np.exp(2j * np.pi * rng.random()))
        eta, alpha = u(), u()
        chi4 = complex(np.exp(2j * np.pi * int(rng.integers(3)) / 3))
        v = complex(np.exp(2j * np.pi * int(rng.integers(6)) / 6))
        X, Wv, Zv = Q ** (-x), Q ** (-w), Q ** (-z)
        V = Zv ** 6
        ap = alpha ** -3 * eta ** 3
        Rr = ap ** 2 * Q ** 4 * X ** 6 * Zv ** 6
        Wl = v * Wv
        J0 = -eta / v * X + Wl * Rr
        Ps = (1 / (1 - Rr)) * ((Rr * (1 - 1 / Q) - eta * (Q - 1) * X * Wv * V) / (1 - V) + J0)
        P = 1 / (1 - V) + Wl / (1 - Wl) + Ps
        W = v * Wv
        D = eta / v * X
        H = P * (1 - V) * (1 - W) / (1 - D)
        G = ((1 / (eta * X) - Wv) * (1 - V) * (1 - W) * Ps - Wv * (1 - V * W)) / (1 - D)
        direct = G / H + 1 / v
        vals = {"eta": eta, "alpha": alpha, "chi4": chi4, "rho": v, "sQ": math.sqrt(Q)}
        ser = 0j
        for k, c in B1.t.items():
            assert k[4] == 0 and k[5] == 0 and k[6] == 0  # no Gauss-sum symbol, no omega_p
            term = complex(float(c))
            for i, name in enumerate(("eta", "alpha", "chi4", "rho")):
                term *= vals[name] ** k[i]
            term *= vals["sQ"] ** k[7] * X ** k[R.nsym] * Wv ** k[R.nsym + 1] * Zv ** k[R.nsym + 2]
            ser += term
        worst = max(worst, abs(ser - direct))
    return worst


def principal_multiplier_report(trunc=(13, 2, 18), v_sign=1) -> dict:
    """The Part II consumer of Lemma 7.1 at the principal row, exactly.

    * grid: at every point of PRINCIPAL_GRID the largest exponent of B_p + 1
      equals the largest of the four exponents line 9068 states;
    * the floors: B_p + 1 = O(Q^{-delta}) with delta > 0 exactly when
      x_r > floor, at (w, z) = (1, 1/6) and on the floors (19/20, 33/200);
    * at x_r = 7/8 on the floors the largest exponent is -7/8, attained only by
      the monomial D = eta(p) conj(v) Q^{-x}, exponent -x_r."""
    R, B1, _ = _principal_series(trunc, v_sign=v_sign)
    grid_bad = []
    for pt in PRINCIPAL_GRID:
        x, w, z = pt
        best = max(Fr(k[7], 2) - k[R.nsym] * x - k[R.nsym + 1] * w - k[R.nsym + 2] * z for k in B1.t)
        if best != max(cited_principal_exponents(pt)):
            grid_bad.append(pt)
    at78 = principal_multiplier_exponents((Fr(7, 8), Fr(19, 20), Fr(33, 200)), trunc, v_sign)
    return {
        "n_grid": len(PRINCIPAL_GRID),
        "grid_bad": grid_bad,
        "floor_residue_point": _series_floor(R, B1, Fr(1), Fr(1, 6), 0),
        "floor_region_two": _series_floor(R, B1, Fr(19, 20), Fr(33, 200), 0),
        "max_at_7_8_floors": at78[0],
        "argmax_at_7_8_floors": at78[1],
    }


#: the two (w_r, z_r) at which EULER_STEP.md states floors: the residue point
#: of the principal factorization (line 15599) and the region-two corner
#: (lines 4056, 5574), where every exponent is largest because its
#: coefficients in w_r and z_r are -deg W, -deg Z <= 0
FLOOR_POINTS = {"residue_point": (Fr(1), Fr(1, 6)), "corner": (Fr(19, 20), Fr(33, 200))}


def row_requirements() -> dict:
    """The floors in x_r of every requirement the region-two consumers put on
    the local factors, for every row u (EULER_STEP.md section 6).

    R1: every exponent of H_p - 1 below -1 at p not dividing u (j = 0; the
        code keeps rho = chi_p(u) as a formal sixth root of unity, so this is
        every row u, not only u = 1);
    R2: every exponent of H_p - 1 below 0 at p | u (j = 1..5, W = D = 0), the
        worst j;
    R3: |R| < 1, that is 4 - 6x_r - 6z_r < 0 (|V| < 1 and |D| < 1 hold for
        z_r > 0 and x_r > 0);
    R4: every exponent of H_p - 1 below 0 at j = 0 (H_p bounded away from 0);
    R5: every exponent of the principal multiplier B_p + 1 below 0 (u = 1).
    Also returned: R2 for each j separately."""
    Rp, B1, _ = _principal_series()
    out = {}
    for name, (w, z) in FLOOR_POINTS.items():
        r2 = {j: euler_floor(j, w, z, threshold=0) for j in range(1, 6)}
        out[name] = {
            "R1": euler_floor(0, w, z, threshold=-1),
            "R2": max(r2.values()),
            "R2_by_j": r2,
            "R3": (4 - 6 * z) / 6,
            "R4": euler_floor(0, w, z, threshold=0),
            "R5": _series_floor(Rp, B1, w, z, 0),
        }
    return out


def region_one_bookkeeping(eps0=Fr(1, 100)) -> dict:
    """The region-one bounds of the proof, at the two minimal vertices.

    Region (7.14) is x >= 51/100, z >= 17/50, w >= -1/100, x + w >= 1 + eps0.
    Every exponent of H_p - 1 is linear with nonpositive coefficients, so its
    maximum over the region is at one of the minimal vertices
    (51/100, 49/100 + eps0, 17/50) and (101/100 + eps0, -1/100, 17/50).  The
    expansion is exact in W here (H_p is a polynomial of degree <= 2 in W), so
    negative w_r is admissible.  Claimed (lines 4166 to 4169):
    H_p - 1 = O(Q^{-1-eps_H}) for p not dividing u and O(Q^{-eps_H}) for p | u,
    eps_H = min(eps0, 1/50)."""
    z = Fr(17, 50)
    verts = [(Fr(51, 100), Fr(49, 100) + eps0, z), (Fr(101, 100) + eps0, Fr(-1, 100), z)]
    epsH = min(eps0, Fr(1, 50))
    good = max(defect_exponents(0, v)[0] for v in verts)
    ram = max(defect_exponents(j, v)[0] for j in range(1, 6) for v in verts)
    return {"good_max": good, "ramified_max": ram, "eps_H": epsH,
            "good_ok": good <= -1 - epsH, "ramified_ok": ram <= -epsH}


def region_bookkeeping() -> dict:
    """Exact rational checks of the exponents stated in the proof of Lemma 7.1."""
    out = {}
    x1, z1, w1 = Fr(51, 100), Fr(17, 50), Fr(-1, 100)
    out["R_exp_region1"] = 4 - 6 * x1 - 6 * z1 == Fr(-11, 10)
    out["27/25"] = Fr(-11, 10) + Fr(1, 100) + Fr(1, 100) == Fr(-27, 25)
    out["3/2-3x"] = Fr(3, 2) - 3 * x1 == Fr(-3, 100)
    x2, z2, w2 = Fr(7, 8), Fr(33, 200), Fr(19, 20)
    out["good_region2"] = 1 - x2 - w2 - 6 * z2 == Fr(-363, 200)
    out["ramified_region2"] = 1 - x2 - w2 == Fr(-33, 40)
    out["tail"] = 1 + Fr(-363, 200) == Fr(-163, 200) and Fr(4, 5) < Fr(163, 200)
    # the maxima over the truncated expansion at the corners
    e_good = defect_exponents(0, (x2, w2, z2))
    out["region2_good_max"] = e_good[0]
    e_ram = max((defect_exponents(j, (x2, w2, z2)) for j in range(1, 6)), key=lambda t: t[0])
    out["region2_ramified_max"] = e_ram[0]
    return out


# ---------------------------------------------------------------------------
# 12. Quadratic transfer and the excluded primes (p = 2, 3)
# ---------------------------------------------------------------------------

def kronecker_m3(p: int) -> int:
    """chi_{-3}(p) for a rational prime p."""
    if p == 3:
        return 0
    if p == 2:
        return -1
    return 1 if p % 3 == 1 else -1


def transfer_checks(B: int) -> dict:
    """For every rational prime p <= B: the splitting of p in Z[omega], found by
    exhaustive search for an element of norm p (or p^2 only), against
    chi_{-3}(p); and the local factor identity of Proposition 11.3 as an exact
    polynomial identity in T = p^{-s} and x = chi(p) (lines 6733 to 6741),
    including p = 3 with eta(lambda) := chi(3)."""
    # polynomials in x = chi(p) and T = p^{-s} as dicts {(deg x, deg T): coefficient}
    def pmul(f, g):
        h = {}
        for (a1, b1), c1 in f.items():
            for (a2, b2), c2 in g.items():
                key = (a1 + a2, b1 + b2)
                h[key] = h.get(key, 0) + c1 * c2
        return {k: v for k, v in h.items() if v}

    bad = []
    kinds = {"split": 0, "inert": 0, "ramified": 0}
    for p in primes_upto(B):
        e = element_of_norm(p)
        if p == 3:
            kind = "ramified"
            ok_kind = enorm(LAMBDA) == 3 and emul(LAMBDA, LAMBDA) == (-3, 0)
        elif e is not None:
            kind = "split"  # an element of norm p exists: p = pi conj(pi)
            ok_kind = kronecker_m3(p) == 1
        else:
            kind = "inert"  # exhaustive search found no element of norm p
            ok_kind = kronecker_m3(p) == -1
        kinds[kind] += 1
        one_minus = lambda c, dx, dt: {(0, 0): 1, (dx, dt): -c}
        if kind == "split":
            hecke = pmul(one_minus(1, 1, 1), one_minus(1, 1, 1))  # two ideals of norm p
        elif kind == "inert":
            hecke = one_minus(1, 2, 2)  # one ideal of norm p^2: chi(N) = chi(p)^2
        else:
            hecke = one_minus(1, 1, 1)  # lambda of norm 3, with eta(lambda) := chi(3)
        dirichlet = pmul(one_minus(1, 1, 1), one_minus(kronecker_m3(p), 1, 1))
        dirichlet = {k: v for k, v in dirichlet.items() if v}
        if not ok_kind or hecke != dirichlet:
            bad.append(p)
    return {"B": B, "kinds": kinds, "bad": bad}


def excluded_primes() -> dict:
    """Why Lemma 7.1 says nothing at p | 6: the symbol is undefined there."""
    out = {}
    # lambda: residue field F_3, (3-1)/6 not an integer, omega = 1 mod lambda
    out["lambda_field_order"] = enorm(LAMBDA)
    out["lambda_6_does_not_divide"] = (enorm(LAMBDA) - 1) % 6 != 0
    out["omega_is_1_mod_lambda"] = ediv_exact(esub(OMEGA, (1, 0)), LAMBDA) is not None
    # 2: residue field F_4, (4-1)/6 not an integer, -1 = 1 mod 2
    out["two_field_order"] = enorm((2, 0))
    out["two_6_does_not_divide"] = (enorm((2, 0)) - 1) % 6 != 0
    out["minus1_is_1_mod_2"] = ediv_exact(esub((-1, 0), (1, 0)), (2, 0)) is not None
    # no primary generator at lambda: every element of norm 3 meets 3
    out["no_primary_at_lambda"] = all(not is_primary(emul(u, LAMBDA)) for u in UNIT6)
    return out


# ---------------------------------------------------------------------------
# 13. Rivals
# ---------------------------------------------------------------------------

def dh_kappa_exact():
    """kappa = (sqrt(10 - 2 sqrt 5) - 2)/(sqrt 5 - 1) as a sympy algebraic number."""
    import sympy as sp

    s5 = sp.sqrt(5)
    return (sp.sqrt(10 - 2 * s5) - 2) / (s5 - 1)


def dh_coeff(n: int, kappa):
    return [0, 1, kappa, -kappa, -1][n % 5]


def epstein_r(n: int, form=(1, 1, 4)) -> int:
    """Number of (m, k) != (0, 0) with a m^2 + b m k + c k^2 = n (brute force)."""
    a, b, c = form
    disc = 4 * a * c - b * b
    kmax = int(math.isqrt(4 * a * n // disc)) + 1
    cnt = 0
    for k in range(-kmax, kmax + 1):
        # a m^2 + b k m + (c k^2 - n) = 0
        dd = b * b * k * k - 4 * a * (c * k * k - n)
        if dd < 0:
            continue
        r = math.isqrt(dd)
        if r * r != dd:
            continue
        for sgn in ((1,) if r == 0 else (1, -1)):
            num = -b * k + sgn * r
            if num % (2 * a) == 0:
                m = num // (2 * a)
                if (m, k) != (0, 0):
                    cnt += 1
    return cnt


def _legendre(a: int, p: int) -> int:
    a %= p
    if a == 0:
        return 0
    return 1 if pow(a, (p - 1) // 2, p) == 1 else -1


def _factorint(n: int) -> dict:
    out, d = {}, 2
    while d * d <= n:
        while n % d == 0:
            out[d] = out.get(d, 0) + 1
            n //= d
        d += 1
    if n > 1:
        out[n] = out.get(n, 0) + 1
    return out


def kron(D: int, n: int) -> int:
    """Kronecker symbol (D/n), D = 1 mod 4 (the fundamental discriminants used here)."""
    out = 1
    for p, e in _factorint(n).items():
        if p == 2:
            v = 1 if D % 8 in (1, 7) else -1
        else:
            v = _legendre(D, p)
        out *= v ** e
    return out


def _convolution_prime_power(f, g, p: int, t: int):
    """(f * g)(p^t) for completely multiplicative f, g given at p."""
    return sum(f(p) ** i * g(p) ** (t - i) for i in range(t + 1))


def epstein_coeff(n: int, D: int = -15):
    """a(n) = r_Q(n)/2 for the principal form of discriminant D in {-15, -19},
    from the genus/class formula, multiplicatively:
    D = -15: r = (1 * chi_{-15}) + (chi_{-3} * chi_5);  D = -19: r = 2 (1 * chi_{-19}).
    The formula is checked against the lattice count by :func:`epstein_formula_check`."""
    one = lambda p: 1
    if D == -15:
        c15 = lambda p: kron(-15, p)
        c3 = lambda p: kron(-3, p)
        c5 = lambda p: kron(5, p)
        s1 = s2 = 1
        for p, t in _factorint(n).items():
            s1 *= _convolution_prime_power(one, c15, p, t)
            s2 *= _convolution_prime_power(c3, c5, p, t)
        return Fr(s1 + s2, 2)
    if D == -19:
        c19 = lambda p: kron(-19, p)
        s = 1
        for p, t in _factorint(n).items():
            s *= _convolution_prime_power(one, c19, p, t)
        return Fr(s)
    raise ValueError(D)


def epstein_formula_check(nmax: int = 2000) -> dict:
    """The coefficient formula against the brute-force lattice count, n <= nmax,
    and against ``zeta.epstein.epstein_representation_count`` on n <= 200."""
    ok15 = all(Fr(epstein_r(n, (1, 1, 4)), 2) == epstein_coeff(n, -15) for n in range(1, nmax + 1))
    ok19 = all(Fr(epstein_r(n, (1, 1, 5)), 2) == epstein_coeff(n, -19) for n in range(1, nmax + 1))
    try:
        from zeta.epstein import epstein_representation_count as lab_r

        oklab = all(lab_r(n, (1, 1, 4)) == epstein_r(n, (1, 1, 4)) for n in range(1, 201))
    except Exception:  # pragma: no cover
        oklab = None
    big = 7 ** 6
    return {"D15": ok15, "D19": ok19, "lab_route": oklab,
            "a(7^6)_brute": Fr(epstein_r(big, (1, 1, 4)), 2), "a(7^6)_formula": epstein_coeff(big, -15)}


def is_norm_prime_to_3(n: int) -> bool:
    """n is the norm of an ideal of Z[omega] prime to 3: every prime 2 mod 3
    (including 2) occurs to an even power, and 3 does not divide n."""
    for p, e in _factorint(n).items():
        if p == 3:
            return False
        if p % 3 == 2 and e % 2:
            return False
    return True


def epstein_norm_form_check(nmax: int = 2000) -> dict:
    """On norms of ideals prime to 3 the two genus pieces of r_{Q0} coincide, so
    a(n) = (1 * chi_{-15})(n) there: multiplicative on Z, but not on ideals of
    F, because p and conj(p) have the same norm."""
    norms = [n for n in range(1, nmax + 1) if is_norm_prime_to_3(n)]
    ok = all(epstein_coeff(n, -15) == sum(kron(-15, d) for d in range(1, n + 1) if n % d == 0) for n in norms)
    return {"n_norms": len(norms), "equal": ok}


def _mobius(n):
    if n == 1:
        return 1
    f = _factorint(n)
    if any(e > 1 for e in f.values()):
        return 0
    return (-1) ** len(f)


class ExactValues:
    """Exact equality for a rival's coefficient values.

    ``kind='kappa'``: values are polynomials in the symbol k standing for the
    Davenport-Heilbronn constant, compared modulo its minimal polynomial (so
    equality is equality of algebraic numbers).  ``kind='gauss'``: values in
    Q(i).  ``kind='rational'``: Fractions."""

    def __init__(self, kind):
        import sympy as sp

        self.sp = sp
        self.kind = kind
        self.k = sp.Symbol("k")
        if kind == "kappa":
            self.minpoly = sp.Poly(sp.minimal_polynomial(dh_kappa_exact(), self.k), self.k)

    def conv(self, x):
        sp = self.sp
        if isinstance(x, Fr):
            return sp.Rational(x.numerator, x.denominator)
        return sp.sympify(x)

    def eq(self, x, y) -> bool:
        sp = self.sp
        d = sp.expand(self.conv(x) - self.conv(y))
        if self.kind == "kappa":
            return sp.Poly(d, self.k).rem(self.minpoly).is_zero
        return d == 0

    def is_unit(self, x) -> bool:
        sp = self.sp
        x = self.conv(x)
        if self.kind == "kappa":
            return self.eq(x * x, 1)
        return sp.expand(x * sp.conjugate(x) - 1) == 0


#: the cut-off of the truncated chi_5 control
TRUNCATED_CHI5_CUTOFF = 100


def chi5_truncated(n: int):
    """The completely multiplicative function on Z with a(ell) = chi_5(ell) at
    primes ell <= 100 and a(ell) = 1 at primes ell > 100 (a control).

    Composed with the norm it is completely multiplicative on the ideals of F
    and unimodular at every prime outside S, so it passes (M), (C), (U) and the
    Moebius form by construction; it agrees with chi_5 o N at every prime of
    norm at most 100 and differs from it at primes of larger norm (see
    :func:`truncated_control_differences`).  That it is not a Hecke character
    is the standard density argument applied to the function itself: a Hecke
    character equal to 1 at all but finitely many primes is trivial (its
    L-function would differ from zeta_F by finitely many Euler factors, so it
    would have a pole at s = 1).  This function is 1 at every prime ideal over
    a rational prime above 100, yet equals chi_5(7) = i at the primes of norm
    7, so it is not trivial and hence no Hecke character.  Inferred, not
    computed here (``truncated_control_values`` pins the two values used)."""
    import sympy as sp

    vals = [0, 1, sp.I, -sp.I, -1]
    out = sp.Integer(1)
    for p, e in _factorint(n).items():
        out *= (vals[p % 5] if p <= TRUNCATED_CHI5_CUTOFF else sp.Integer(1)) ** e
    return sp.expand(out)


def truncated_control_differences(norm_bound: int = 200) -> list:
    """The good norms <= norm_bound (outside the primes above 6 and 5) at which
    chi5_truncated differs from chi_5."""
    import sympy as sp

    chi = lambda n: [0, 1, sp.I, -sp.I, -1][n % 5]
    norms = sorted({P.Q for P in good_primes_for(norm_bound, (5,))})
    return [Q for Q in norms if sp.expand(chi5_truncated(Q) - chi(Q)) != 0]


def truncated_control_values() -> dict:
    """The two values the density argument in :func:`chi5_truncated` uses."""
    import sympy as sp

    above = [ell for ell in primes_upto(400) if ell > TRUNCATED_CHI5_CUTOFF and ell % 3 == 1]
    return {"at_norm_7": chi5_truncated(7), "is_i_at_norm_7": sp.expand(chi5_truncated(7) - sp.I) == 0,
            "one_above_cutoff": all(chi5_truncated(ell) == 1 for ell in above)
            and all(chi5_truncated(ell * ell) == 1 for ell in primes_upto(400) if ell > TRUNCATED_CHI5_CUTOFF)}


def good_primes_for(norm_bound: int, conductor_primes=()) -> list:
    """The prime ideals of norm <= norm_bound outside a target's excluded set:
    the primes above 6 (never constructed) and the primes above its conductor
    (the supports of its presentation, paper lines 3336 to 3340)."""
    return [P for P in primes_of_norm_upto(norm_bound) if P.ell not in conductor_primes]


def rival_functions():
    """The rivals and controls: (exact kind, a as a function of a positive
    integer n, the rational primes of its conductor).

    Over F a function a on rational integers acts on ideals by a(N ideal), the
    way Proposition 11.3 turns chi into eta = chi o N.  Each target's excluded
    set S contains the primes above 6 and above its conductor."""
    import sympy as sp

    k = sp.Symbol("k")
    return {
        # Davenport-Heilbronn: ((1 - i kappa)/2) chi_5 + ((1 + i kappa)/2) conj(chi_5), real coefficients
        "DH": ("kappa", lambda n: [0, 1, k, -k, -1][n % 5], (5,)),
        # Epstein zeta of x^2 + xy + 4y^2, normalised a(1) = 1 (discriminant -15: 3 and 5)
        "Epstein_-15": ("rational", lambda n: epstein_coeff(n, -15), (3, 5)),
        # controls: a genuine character, a degree-two Euler product (class number one)
        "chi5_control": ("gauss", lambda n: [0, 1, sp.I, -sp.I, -1][n % 5], (5,)),
        "Epstein_-19_control": ("rational", lambda n: epstein_coeff(n, -19), (19,)),
        # a limit control: completely multiplicative and unimodular, not a Hecke character
        "truncated_chi5_control": ("gauss", chi5_truncated, (5,)),
    }


def _ideals_upto(primes: list, bound: int) -> list:
    """The ideals of norm <= bound built from the given prime ideals, as
    (norm, ((index, exponent), ...)) sorted by norm."""
    out = []

    def rec(i, items, norm):
        if i == len(primes):
            out.append((norm, tuple(items)))
            return
        rec(i + 1, items, norm)
        e, nn = 1, norm * primes[i].Q
        while nn <= bound:
            rec(i + 1, items + [(i, e)], nn)
            e, nn = e + 1, nn * primes[i].Q

    rec(0, [], 1)
    out.sort()
    return out


def moebius_over_F(a, ev, primes: list, bound: int = 200):
    """The Dirichlet inverse b of the ideal function A -> a(N A) over the
    ideals built from ``primes`` (the good primes of one target), against
    mu_F(A) a(N A), the coefficient of 1/L^S(s, eta) when a is eta o N.

    Returns (number of ideals checked, None) when they agree on every ideal of
    norm <= bound, else (number checked, (least norm with a difference, the
    number of ideals of that norm where they differ))."""
    import itertools

    sp = ev.sp
    ideals = _ideals_upto(primes, bound)
    b = {(): sp.Integer(1)}
    diffs = {}
    for norm, A in ideals:
        if not A:
            continue
        s = sp.Integer(0)
        for exps in itertools.product(*[range(e + 1) for _, e in A]):
            Dv = tuple((i, f) for (i, _), f in zip(A, exps) if f)
            if Dv == A:
                continue
            dnorm = 1
            for i, f in Dv:
                dnorm *= primes[i].Q ** f
            s += b[Dv] * ev.conv(a(norm // dnorm))
        b[A] = sp.expand(-s)
        mu = 0 if any(e > 1 for _, e in A) else (-1) ** len(A)
        if not ev.eq(b[A], mu * ev.conv(a(norm))):
            diffs[norm] = diffs.get(norm, 0) + 1
    if not diffs:
        return len(ideals), None
    first = min(diffs)
    return len(ideals), (first, diffs[first])


def first_local_failure(a, ev, Q, t_list):
    """Least t in t_list (t > 0) with a(Q^t) != a(Q)^t, or None."""
    aq = a(Q)
    for t in t_list:
        if t == 0:
            continue
        lhs = a(Q ** t)
        rhs = ev.conv(aq) ** t
        if not ev.eq(lhs, rhs):
            return t
    return None


def rival_report(norm_bound: int = 200, tmax: int = 13) -> dict:
    """Where the Euler step fails for the rivals, exactly.

    Lemma 7.1 consumes three properties of the target eta on good ideals:
    (M) multiplicativity on completed indices A = c n^3 (the separation at
    line 3995: K_eta in (7.4) depends on eta only through the factor eta(A));
    (C) eta(p^t) = eta(p)^t at every good prime for every t in the support of
    P_p^* (the local closed form (7.11)); (U) |eta(p)| = 1 at good primes (the
    unit phases of line 3870 and |D| < 1).  The reciprocal-Moebius form of the
    same structure is the 11/12 input 1/L = sum mu eta N^{-s}.

    For a function a on ideals the local series is homogeneous: every monomial
    of (7.10) and of (7.11) carries eta to the power of its X-degree (checked
    in :func:`lemma71_symbolic`).  So with a(p^t) in place of eta(p)^t the
    coefficient at (t, k, m) of series minus closed form is
    (a(p^t) - a(p)^t) S_{t,k,m}, S the generic coefficient; the identity at p
    fails exactly at the least t in the support with a(p^t) != a(p)^t.

    Every column is counted over the target's own good prime ideals of norm
    <= norm_bound: outside the primes above 6 and above its conductor
    (:func:`good_primes_for`).  The Moebius form is computed over the good
    ideals of F (``moebius_over_F``) and, for comparison, over Q
    (``moebius_first_difference``, all n < 200)."""
    import sympy as sp

    out = {}
    support = lemma71_support()
    t_support = {j: sorted({s[0] for s in support[j]}) for j in range(6)}
    out["t_support"] = t_support
    kap = dh_kappa_exact()
    try:
        from zeta.epstein import KAPPA_REF

        out["kappa_agrees_with_lab"] = bool(abs(sp.N(kap, 50) - sp.Float(KAPPA_REF, 50)) < sp.Float("1e-38"))
    except Exception:  # pragma: no cover
        out["kappa_agrees_with_lab"] = None
    out["kappa_minpoly"] = str(sp.minimal_polynomial(kap, sp.Symbol("k")))
    tl = [t for t in t_support[0] if 0 < t <= tmax]
    for name, (kind, a, conductor) in rival_functions().items():
        ev = ExactValues(kind)
        good = good_primes_for(norm_bound, conductor)
        norms = sorted({P.Q for P in good})
        split_norms = sorted({P.Q for P in good if P.kind == "split"})
        rep = {"conductor_primes": conductor, "norm_bound": norm_bound}
        # (C): the first failing t of the principal row (j = 0) at each good norm
        rep["first_failing_t_principal_row"] = {Q: first_local_failure(a, ev, Q, tl) for Q in norms}
        rep["n_norms"] = len(norms)
        rep["n_norms_failing_C"] = sum(v is not None for v in rep["first_failing_t_principal_row"].values())
        # the same at every j: least t over the support of P_p^* for that row type
        rep["first_failing_t_by_j_at_7"] = {
            j: first_local_failure(a, ev, 7, [t for t in t_support[j] if 0 < t <= tmax]) for j in range(6)}
        # (M): coprime good ideals; distinct norms, and the conjugate pair p, conj(p)
        bad = [(q1, q2) for i, q1 in enumerate(norms) for q2 in norms[i + 1:]
               if not ev.eq(a(q1 * q2), ev.conv(a(q1)) * ev.conv(a(q2)))]
        conj_bad = [q for q in split_norms if not ev.eq(a(q * q), ev.conv(a(q)) ** 2)]
        rep["n_pairs"] = len(norms) * (len(norms) - 1) // 2
        rep["n_pairs_failing_M"] = len(bad)
        rep["first_pairs_failing_M"] = bad[:3]
        rep["n_conjugate_pairs"] = len(split_norms)
        rep["n_conjugate_pairs_failing_M"] = len(conj_bad)
        rep["first_conjugate_pair_failing_M"] = conj_bad[0] if conj_bad else None
        # the first failing coprime pair of good ideals, ordered by the product of the norms
        cands = [(q1 * q2, "distinct norms", (q1, q2)) for q1, q2 in bad] + \
                [(q * q, "conjugate pair", (q, q)) for q in conj_bad]
        rep["first_coprime_pair_failing_M"] = min(cands) if cands else None
        # (U)
        nonunit = [Q for Q in norms if not ev.is_unit(a(Q))]
        rep["n_norms_nonunit_U"] = len(nonunit)
        rep["nonunit_norms_first"] = nonunit[:4]
        # the Moebius form over the good ideals of F (the paper's 1/L^S(s, eta))
        rep["moebius_ideals_checked_F"], rep["moebius_over_F"] = moebius_over_F(a, ev, good, norm_bound)
        # the same over Q, for comparison: first n where the inverse b of a differs from mu a
        b = {1: sp.Integer(1)}
        first = None
        for n in range(2, 200):
            s = sum(b[d] * ev.conv(a(n // d)) for d in range(1, n) if n % d == 0)
            b[n] = sp.expand(-s)
            if first is None and not ev.eq(b[n], _mobius(n) * ev.conv(a(n))):
                first = (n, b[n], _mobius(n) * ev.conv(a(n)))
        rep["moebius_first_difference"] = first
        out[name] = rep
    return out


#: the targets in the order of the table in EULER_STEP.md, with their labels
RIVAL_TABLE_LABELS = (
    ("DH", "Davenport-Heilbronn, ((1 - i kappa)/2) chi_5 + ((1 + i kappa)/2) conj(chi_5)"),
    ("Epstein_-15", "Epstein zeta of x^2 + xy + 4y^2, a = r/2"),
    ("chi5_control", "control: chi_5 composed with the norm, a Hecke character"),
    ("Epstein_-19_control", "control: Epstein zeta of x^2 + xy + 5y^2, 2 zeta(s) L(s, chi_-19), "
                            "an Euler product of degree two"),
    ("truncated_chi5_control", "limit control: the completely multiplicative function equal to chi_5 at "
                               "primes up to 100 and to 1 at larger primes, composed with the norm; "
                               "not a Hecke character"),
)


def rival_table_rows(report: dict) -> list:
    """The rival table of EULER_STEP.md, generated from :func:`rival_report`
    (a test checks that the document contains these lines verbatim).  A
    descriptive phrase is printed only when the report bears it out."""
    head = ("| target | S beyond the primes above 6 | (C): norms failing, first t "
            "| (M): distinct-norm pairs failing | (M): conjugate pairs failing "
            "| (U): norms not unimodular | Moebius form over the good ideals of F |")
    rows = [head, "|---|---|---|---|---|---|---|"]
    for key, label in RIVAL_TABLE_LABELS:
        r = report[key]
        cond = r["conductor_primes"]
        extra = [c for c in cond if c != 3]  # the primes above 3 are already in S
        excl = "the prime above 5" if extra == [5] else (
            "the two primes above 19" if extra == [19] else ", ".join(map(str, extra)))
        ft = r["first_failing_t_principal_row"]
        failing = {Q for Q, t in ft.items() if t is not None}
        c = f"{r['n_norms_failing_C']} of {r['n_norms']}"
        if failing and failing == {Q for Q in ft if Q % 5 in (2, 3)}:
            c += ", exactly the norms 2 or 3 mod 5"
        elif failing and failing == {Q for Q in ft if _is_prime(Q)} and len(failing) < len(ft):
            c += ", exactly the split norms"
        elif failing and failing == set(ft):
            c += ", every good norm"
        ts = sorted({t for t in ft.values() if t is not None})
        if ts:
            c += "; first t = " + ", ".join(map(str, ts))
        m = f"{r['n_pairs_failing_M']} of {r['n_pairs']}"
        if r["first_pairs_failing_M"]:
            m += ", first {}".format(r["first_pairs_failing_M"][0])
        cj = f"{r['n_conjugate_pairs_failing_M']} of {r['n_conjugate_pairs']}"
        if r["first_conjugate_pair_failing_M"] is not None:
            cj += f", first over {r['first_conjugate_pair_failing_M']}"
        u = f"{r['n_norms_nonunit_U']} of {r['n_norms']}"
        mf = r["moebius_over_F"]
        mo = "agrees up to norm {}".format(r["norm_bound"]) if mf is None else f"first differs at norm {mf[0]}"
        rows.append(f"| {label} | {excl} | {c} | {m} | {cj} | {u} | {mo} |")
    return rows


def rival_values() -> dict:
    """The explicit values the prose quotes (exact)."""
    import sympy as sp

    f = rival_functions()
    dh = f["DH"][1]
    ep = f["Epstein_-15"][1]
    k = sp.Symbol("k")
    ev = ExactValues("kappa")
    return {
        "dh_a7": dh(7), "dh_a7_6": dh(7 ** 6), "dh_a13": dh(13), "dh_a91": dh(91),
        "dh_a4": dh(4), "dh_a2": dh(2), "dh_a49": dh(49), "dh_a25": dh(25),
        "dh_a49_differs_from_a7_squared": not ev.eq(dh(49), dh(7) ** 2),
        "dh_kappa6_plus_1_nonzero": not ev.eq(k ** 6 + 1, 0),
        "dh_kappa2_plus_1_nonzero": not ev.eq(k ** 2 + 1, 0),
        "dh_a121": dh(121),
        "ep_a2": ep(2), "ep_a3": ep(3), "ep_a4": ep(4), "ep_a6": ep(6),
        "ep_a7": ep(7), "ep_a7_4": ep(7 ** 4), "ep_a7_6": ep(7 ** 6), "ep_a19": ep(19), "ep_a49": ep(49),
        "kappa_float": float(sp.N(dh_kappa_exact(), 30)),
    }


# ---------------------------------------------------------------------------
# 14. Planted faults: each must turn its check red
# ---------------------------------------------------------------------------

def planted_faults() -> dict:
    """Run every check with a deliberate fault; True means the check went red.

    Every entry is a fault.  The one control that must stay green (the
    unmodified character beside the near miss) is in :func:`fault_controls`."""
    out = {}
    sym_J3 = lemma71_symbolic(trunc=(13, 2, 18), fault="J3_sign")
    out["closed_form_J3_sign"] = (not sym_J3[3]["P_equal"]) and all(sym_J3[j]["P_equal"] for j in (0, 1, 2, 4, 5))
    sym_om = lemma71_symbolic(trunc=(13, 2, 18), fault="om_drop_quadratic")
    out["series_omega_exponent"] = any(not sym_om[j]["P_equal"] for j in range(6))
    sym_cp = lemma71_symbolic(trunc=(13, 2, 18), fault="cp_G1_to_G5")
    out["cp_G1_to_G5"] = any(not sym_cp[j]["P_equal"] for j in range(6))
    sym_g2 = lemma71_symbolic(trunc=(13, 2, 18), relations={"G2_sign": 1})
    out["relation_sign_gamma1gamma2"] = any(not sym_g2[j]["P_equal"] for j in range(6))
    P7 = split_primes(7)[0]
    P13 = split_primes(13)[0]
    r = prime_gauss_checks(P7, balls=False, swap=True)
    out["swap_character_conjugate"] = not r["L42a"] or not r["E47b"]
    r = prime_gauss_checks(P7, balls=False, perturb=True)
    out["perturb_one_gauss_coefficient"] = not r["L42a"]
    # swap the prime: the sextic symbol of the conjugate prime with p's Gauss sums
    G2 = gauss_vec(P7.pi, [(P7, 2)])
    out["swap_prime_in_L42a"] = not ((G2 * G2 * G2) == Cyc.scalar(emul(eneg(econj(P7.pi)), (P7.Q, 0))))
    # omega_p = chi_p(-1) is -1 exactly when Q = 7 mod 12; a fault in the omega
    # exponent can only show at such a prime (see omega_fault_visibility)
    P19 = split_primes(19)[0]
    pr = lemma71_at_prime(P19, trunc=(13, 2, 18), fault="om_drop_quadratic")
    out["prime_route_omega_exponent"] = not all(pr.values())
    pr = lemma71_at_prime(P13, trunc=(13, 2, 18), fault="cp_G1_to_G5")
    out["prime_route_cp_G1_to_G5"] = not all(pr.values())
    cb = cp_bruteforce(P7, 2, 1, fault="drop_congruence")
    out["cp_drop_congruence"] = len(cb["bad"]) > 0
    cs = composite_signal_checks([P7, P13], balls=False, mu_fault=True)
    out["mobius_sign_composite"] = not cs["E47a"] or not cs["E47b"]
    # a near miss: a character at every prime power except a(p^6) = -a(p)^6;
    # the local test must report t = 6 as the first failure of the principal row
    sup = lemma71_support()
    tl = [t for t in sorted({s[0] for s in sup[0]}) if 0 < t <= 13]
    ev = ExactValues("gauss")
    import sympy as sp

    chi = lambda n: [0, 1, sp.I, -sp.I, -1][n % 5]

    def near(n, Q=7):
        t, m = 0, n
        while m % Q == 0:
            m //= Q
            t += 1
        v = chi(n)
        return -v if t == 6 else v

    out["near_miss_fails_at_t6"] = first_local_failure(near, ev, 7, tl) == 6
    # added in the repair round: one fault for each new check
    out["table_row6_condition"] = len(family_table_complete(rmax=2, fault="row6_m_ge_r")["bad"]) > 0
    out["p3_drop_Q"] = not p_power_quadratic_direct(P7, 3, balls=False, fault="drop_Q")["G_p3_equals_gamma3"]
    rep = principal_multiplier_report(v_sign=-1)
    out["principal_multiplier_sign"] = len(rep["grid_bad"]) > 0 and rep["max_at_7_8_floors"] != Fr(-7, 8)
    pr = lemma71_at_prime(P7, trunc=(13, 2, 18), fault="multiplier_G5")
    out["prime_route_multiplier_G5"] = not all(pr[j] for j in range(6))
    return out


def fault_controls() -> dict:
    """The control beside the near-miss fault: the unmodified character chi_5
    must pass the same local test (True means it stayed green, as it should)."""
    import sympy as sp

    sup = lemma71_support()
    tl = [t for t in sorted({s[0] for s in sup[0]}) if 0 < t <= 13]
    ev = ExactValues("gauss")
    chi = lambda n: [0, 1, sp.I, -sp.I, -1][n % 5]
    return {"near_miss_control_passes": first_local_failure(chi, ev, 7, tl) is None}


def omega_fault_visibility() -> dict:
    """A sensitivity limit of the prime route, stated rather than hidden: the
    omega_p exponent of (7.10) has no effect where omega_p = 1 (Q = 1 mod 12),
    so the same planted fault is invisible at norm 13 and visible at norm 19."""
    P13 = split_primes(13)[0]
    P19 = split_primes(19)[0]
    om = {P.Q: (1 if P.chi_exp((-1, 0)) == 0 else -1) for P in (P13, P19)}
    f13 = lemma71_at_prime(P13, trunc=(13, 2, 18), fault="om_drop_quadratic")
    f19 = lemma71_at_prime(P19, trunc=(13, 2, 18), fault="om_drop_quadratic")
    return {"omega_13": om[13], "omega_19": om[19],
            "fault_visible_at_13": not all(f13.values()), "fault_visible_at_19": not all(f19.values())}


# ---------------------------------------------------------------------------
# 15. Driver
# ---------------------------------------------------------------------------

def main() -> None:  # pragma: no cover - the tests call the pieces
    t0 = time.time()
    print("paper sha256 ok:", paper_sha256() == PAPER_SHA256)
    cits = check_citations()
    print("citations ok:", sum(cits.values()), "/", len(cits), [k for k, v in cits.items() if not v])
    print("appendix in paper.tex:", paper_has_appendix())
    print("lemma 7.1 symbolic:", lemma71_symbolic())
    ft = family_table_complete()
    print("family table (7.16):", {k: v for k, v in ft.items() if k != "js_by_row"})
    print("rational identities:", local_rational_identities())
    print("region bookkeeping:", region_bookkeeping())
    for jj, (w, z) in ((0, (Fr(1), Fr(1, 6))), (0, (Fr(19, 20), Fr(33, 200)))):
        print("euler floor", jj, (w, z), euler_floor(jj, w, z), "bounded-below floor", euler_floor(jj, w, z, threshold=0))
    print("principal multiplier:", principal_multiplier_report())
    print("transfer:", transfer_checks(10 ** 4))
    print("excluded:", excluded_primes())
    print("lemma 4.3:", lemma43_table())
    print("reciprocity:", {k: (v if k != 'bad' else len(v)) for k, v in reciprocity_checks(500).items()})
    print("time", time.time() - t0)


if __name__ == "__main__":  # pragma: no cover
    main()

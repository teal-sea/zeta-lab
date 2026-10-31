#!/usr/bin/env python3
"""probe_tower: OpenAI's 7/8 probe as a function of the row-character order k.

Hunt #150 (``hunts/rh_moonshot``), mechanism 6, ``probe_tower``.  Nothing in
this file is a result until the hunt's case log says how it ended.  The
argument is in ``NOTES.md`` beside this file; this module is its arithmetic.

Grades used below:

* *cited*: a line of the pinned ``paper.tex`` (OpenAI, *The Quasi-Riemann
  Hypothesis*, 2026-09-30, ``github.com/openai/math`` commit ``adc7f124``,
  SHA-256 ``42a5ee0f...c6a3``), checked by :func:`verify_citations`;
* *inferred*: a reading of the paper's structure that no computation here
  checks.  The main one: every "6" listed in :data:`K_READINGS` is the order
  k of the row characters, so an order-k system replaces it by k;
* *derived*: algebra done here and checked in exact rational arithmetic
  (``fractions.Fraction``; ``sympy`` for statements symbolic in k);
* *measured*: one floating route (mpmath), used only for the rival functions.

**The construction.**  In the paper the target eta is twisted by sextic
residue symbols chi_A(m).  Poisson summation in m leaves frequencies
H = u a^6 (line 3758), the sum over a is zeta_F(6z) (line 4045), and its pole
at z = 1/6 (line 4071) produces the Mellin signal Z^{C(s)} / L(s, eta).  The
*order-k template* replaces the character order 6 by k wherever a sixth power
is counted (the pole, the slot weight, the Gram bound's exceptional
frequencies) and holds every other estimate at the paper's stated form.  Then
(derived)

    C(s) = s + l_x/2 - 1 + h/k,      low exponent  l_x/2 + b/(2k),
    sigma_0(k) = 1 - 1/k + (M - 2 ell)/(2k),

with l_x = (M - b)/2, l_y = (M + b)/2 and h = 1 - l_x + ell.  At k = 6 this is
hunt #134's 5/6 + (M - 2 ell)/12 and reproduces 11/12 (Part I) and 7/8
(Part II).

**The tower question.**  Does sigma_0(k) tend to 1/2 along probes of growing
degree?  In the template it does the opposite: for every admissible geometry
sigma_0 is strictly increasing in k and tends to 1.  The dual-length condition
alone gives sigma_0 >= 1 - 2/k; with the floor rows counted in full (perfect
row counts) sigma_0 >= 1 - 4/((5 + 6 delta_0) k).  The best order is the
smallest, and k = 2 stops at 3/5.  The formal value k = 1 (no twist, the
Moebius sum itself) gives exactly 1/2, where the direct bound becomes
Littlewood's criterion, which is equivalent to RH.

**The rival gate.**  The step that reads zeta's Euler product is the same at
every k: the principal row is linear in the target's coefficients and carries
the Moebius-weighted squarefree sum of them (line 3967 supplies mu(c)), which
the continuation criterion needs to be H/L with sup |H - 1| <= 1/2
(line 413).  :func:`dh_at_offline_zero`, :func:`epstein_at_offline_zero` and
:func:`wa_at_offline_zero` evaluate that step at each rival's off-line zero.

Run ``tower_template.py --paper`` for the report and the citation check, and
``tower_template.py --write`` to refresh ``results_probe_tower.json``.  The
tests never write into the tree.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import math
import os
import sys
from fractions import Fraction

F = Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
REPO_ROOT = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
RESULTS = os.path.join(HERE, "results_probe_tower.json")

PAPER_SHA256 = "42a5ee0febca59fd1def55cfd6c6808c322ef4237d7726303ea52f711deac6a3"
PAPER_DEFAULT = os.environ.get(
    "ZETA_LAB_OPENAI_PAPER",
    os.path.expanduser("~/.cache/zeta-lab/openai-math-adc7f124/paper.tex"),
)

# ---------------------------------------------------------------------------
# citations: (line, snippet that must occur on that line, what it supplies)
# ---------------------------------------------------------------------------

CITATIONS: tuple[tuple[int, str, str], ...] = (
    (400, r"\begin{proposition}[Continuation from a common signal]", "Proposition 2.1 begins"),
    (432, r"\end{proposition}", "Proposition 2.1 ends"),
    (3866, r"R=a_p^2Q^{4-6x-6z}", "the binding term of the principal correction"),
    (3870, r"The values $\rho,a_p,b_p$ have absolute value one", "unitarity in the local identity"),
    (6705, r"\begin{proposition}[Quadratic transfer]", "the Dirichlet transfer"),
    (190, r"C_{\mathrm I}(s)=s-\frac23", "Part I signal exponent"),
    (191, r"C_{\mathrm{II}}(s)=s-\frac{11}{16}", "Part II signal exponent"),
    (413, r"\sup_{\Re s>\sigma_0}|H_\eta(s)-1|\le\frac12", "the contraction hypothesis on H"),
    (419, r"Z^{C(s)}e^{(s-5/6)^2}", "the Mellin signal"),
    (420, r"\frac{H_\eta(s)}{L_F^{\mathcal S}(s,\eta)}", "the signal carries H / L"),
    (425, r"Z^{C(\sigma_0)+\omega}", "the low (direct) estimate"),
    (427, r"Z^{C(\beta_*)-\sigma}", "the high estimate"),
    (509, r"\sigma_0=\frac{11}{12},\qquad C(s)=s-\frac23", "Part I target"),
    (510, r"C(\sigma_0)=\frac14", "Part I low exponent"),
    (514, r"\sigma_0=\frac78,\qquad C(s)=s-\frac{11}{16}", "Part II target"),
    (515, r"C(\sigma_0)=\frac3{16}", "Part II low exponent"),
    (3717, r"&=Z^{1/4+\epsilon_1/2}.", "Part I direct bound"),
    (3758, r"$H=ua^6$, where $u$ is a sixth-power-free element", "Poisson frequencies"),
    (3825, r"X^{1/2-z}Z^{x+z-1}Y^{w-1}", "the common Mellin weight"),
    (3967, r"$\gamma_2(c)=\mu(c)\alpha(c)G(c)/\gamma_1(c)$.", "where mu(c) enters"),
    (4045, r"\frac{\zeta_F^S(6z)L^S(w,\chi_\bullet(u))}", "scalar factorization, numerator"),
    (4046, r"{L^S(x,\eta\overline{\chi_\bullet(u)})}", "scalar factorization, denominator"),
    (4056, r"x_r\ge7/8,\quad z_r\ge33/200,\quad w_r\ge19/20.", "Euler region two"),
    (4071, r"principal residue point $w=1$, $z=1/6$", "the principal residue"),
    (5586, r"h=1-l_x+\ell>0", "definition of h"),
    (5588, r"C(s)=s+\frac{l_x}{2}-1+\frac h6", "signal exponent, general geometry"),
    (6860, r"b=\frac18,\qquad h=\frac{13}{16},\qquad \ell=\frac16", "Part II geometry"),
    (6861, r"l_x=1+\ell-h=\frac{17}{48}", "Part II l_x"),
    (6862, r"l_y=l_x+b=\frac{23}{48}", "Part II l_y"),
    (6864, r"M=l_x+l_y=\frac56,\qquad M+\ell=1.", "Part II M and the dual length"),
    (8246, r"Since $M'+\ell'-1=-3d$", "the dual-length subtraction"),
    (8353, r"P_a^{1/6}", "Gram bound, exceptional term"),
    (8535, r"$(k)=a_1^6e$, where $e$ is sixth-power-free", "exceptional frequencies are sixth powers"),
    (8541, r"$O_{\rm fixed}(K_R^{1/6})$", "counted as K^(1/6)"),
    (8570, r"\ll Z^{l_x/2+b/12+\epsilon}=Z^{3/16+\epsilon}.", "Part II direct bound"),
    (8619, r"P_a^{1/12}", "Gram term after Cauchy-Schwarz"),
    (8641, r"C_{\mathrm{II}}(s)=l_x/2+s-1+h/6=s-11/16", "Part II signal, general form"),
    (8642, r"C_{\mathrm{II}}(7/8)=3/16=l_x/2+b/12.", "Part II target equation"),
    (15563, r"q_p^{-5/6}", "slot weight q_p^(z-1) at z = 1/6"),
    (15576, r"Z^{-\ell/6}", "slot normaliser"),
    (15729, r"&=a-\frac78+h\left(\frac{17}{50}-\frac16\right)", "high exponent, first line"),
    (15730, r"-a l_y-(1-a)\ell-(\delta/2-q)\ell", "high exponent, first line (cont.)"),
    (15731, r"+d\left(R+\frac\delta2-\frac{17}{50}\right)", "high exponent, first line (end)"),
    (15732, r"&=C_0+\frac23\delta+\frac q6-h(1-R)", "high exponent, second line"),
    (15734, r"C_0=-\frac1{48}", "C_0 at the paper's geometry"),
    (15742, r"\Re z=\frac{17}{50}", "the nonprincipal contour"),
    (8597, r"l_y-d-11b/6\ge1/12", "Gram cap at the paper's geometry"),
    (15843, r"The floor bin \(a=51/100\) has \(\delta_0=1/50\)", "the floor bin"),
    (15847, r"E(h)\le C_0+\frac34\delta_0=-\frac7{1200}<0.", "the floor rows"),
)

#: The sixth powers this mechanism reads as k-th powers (inferred).
K_READINGS: tuple[tuple[str, str, str, tuple[int, ...]], ...] = (
    ("pole of zeta_F(kz) at the principal residue", "1/6", "1/k", (3758, 4045, 4071)),
    ("slot weight q_p^(z* - 1) and its normaliser", "q_p^(-5/6), Z^(-ell/6)", "q_p^(1/k - 1), Z^(-ell/k)", (15563, 15576)),
    ("Gram bound, exceptional frequencies a^6 e", "P_a^(1/6)", "P_a^(1/k)", (8353, 8535, 8541)),
    ("Gram term after Cauchy-Schwarz", "P_a^(1/12) = Z^(b/12)", "Z^(b/(2k))", (8570, 8619)),
)


def verify_citations(path: str = PAPER_DEFAULT) -> tuple[bool, list[tuple[int, str]]]:
    """(sha256 matches, list of (line, snippet) not found on its line)."""
    with open(path, "rb") as fh:
        raw = fh.read()
    sha_ok = hashlib.sha256(raw).hexdigest() == PAPER_SHA256
    lines = raw.decode("utf-8").splitlines()
    missing = [
        (line_no, snippet)
        for line_no, snippet, _ in CITATIONS
        if line_no > len(lines) or snippet not in lines[line_no - 1]
    ]
    return sha_ok, missing


# ---------------------------------------------------------------------------
# the order-k template (exact)
# ---------------------------------------------------------------------------

#: Paper's Part I and Part II geometries (lines 3313-3320 and 6860-6864).
PART_I = (F(0), F(1), F(0))  # (ell, M, b): no slots, X = Y = Z^(1/2)
PART_II = (F(1, 6), F(5, 6), F(1, 8))
CONTOUR = F(17, 50)  # the nonprincipal contour Re z = 17/50 (line 15742); cancels at d = h
FLOOR_BIN = F(1, 50)  # delta_0 of the floor bin a = 51/100 (line 15843)


def geometry(ell, M, b):
    """(l_x, l_y, h) from the free geometry: l_x = (M - b)/2, l_y = (M + b)/2,
    h = 1 - l_x + ell (line 5586; X = Z^l_x, Y = Z^l_y, b = l_y - l_x)."""
    ell, M, b = F(ell), F(M), F(b)
    lx = (M - b) / 2
    ly = (M + b) / 2
    return lx, ly, 1 - lx + ell


def pole(k, *, reading=None):
    """The comparison pole z* of an order-k system: 1/k (inferred reading of
    the 6 in zeta_F(6z)).  ``reading`` lets a test plant a wrong reading."""
    return F(1, 1) / F(k) if reading is None else F(reading(k))


def signal_shift_from_weight(k, ell, M, b, *, reading=None):
    """Route 1 for C(s) = s + c: read c off the Mellin weight at the pole.

    The weight X^(1/2 - z) Z^(x + z - 1) (line 3825) at z = z*, X = Z^l_x,
    times the slot product Z^(ell z*) (each slot prime carries
    q_p^(z* - 1), line 15563, normalised by Z^(-ell z*), line 15576), is
    Z^(x + c) with c = l_x (1/2 - z*) + (z* - 1) + ell z*.
    """
    lx, _, _ = geometry(ell, M, b)
    z = pole(k, reading=reading)
    return lx * (F(1, 2) - z) + (z - 1) + F(ell) * z


def signal_shift(k, ell, M, b, *, reading=None):
    """Route 2: c = l_x/2 - 1 + h z* (line 5588 with 1/6 replaced by z*)."""
    lx, _, h = geometry(ell, M, b)
    return lx / 2 - 1 + h * pole(k, reading=reading)


def low_exponent(k, ell, M, b, *, reading=None):
    """Direct-bound exponent l_x/2 + b z*/2: line 8570 at k = 6 is
    l_x/2 + b/12, the b-term being P_a^(1/12) with P_a = Z^b (lines 8591,
    8619), half of the exceptional count P_a^(1/6) (lines 8353, 8541)."""
    lx, _, _ = geometry(ell, M, b)
    return lx / 2 + F(b) * pole(k, reading=reading) / 2


def target(k, ell, M, b, *, reading=None):
    """sigma_0 with C(sigma_0) = low exponent: sigma_0 = low - c."""
    return low_exponent(k, ell, M, b, reading=reading) - signal_shift(k, ell, M, b, reading=reading)


def target_closed(k, ell, M, b):
    """Closed form 1 - 1/k + (M - 2 ell)/(2k), free of b (derived)."""
    return 1 - F(1) / F(k) + (F(M) - 2 * F(ell)) / (2 * F(k))


def tower_increment(k, ell, M, b):
    """sigma_0(k + 1) - sigma_0(k) = (2 - (M - 2 ell)) / (2 k (k + 1))."""
    return target(k + 1, ell, M, b) - target(k, ell, M, b)


def high_exponent(k, ell, M, b, delta, q, R, d, *, reading=None):
    """Line 15729 (first line) with 7/8 -> sigma_0(k) and 1/6 -> z*:

    E(d) = a - sigma_0 + h (17/50 - z*) - a l_y - (1 - a) ell
           - (delta/2 - q) ell + d (R + delta/2 - 17/50),   a = (1 + delta)/2.
    """
    _, ly, h = geometry(ell, M, b)
    ell, delta, q, R, d = F(ell), F(delta), F(q), F(R), F(d)
    a = (1 + delta) / 2
    s0 = target(k, ell, M, b, reading=reading)
    z = pole(k, reading=reading)
    return (
        a - s0 + h * (CONTOUR - z) - a * ly - (1 - a) * ell
        - (delta / 2 - q) * ell + d * (R + delta / 2 - CONTOUR)
    )


def high_exponent_paper_second_line(delta, q, R, d):
    """Line 15732: E(d) = C_0 + (2/3) delta + q/6 - h(1 - R) + (d - h)(R + delta/2 - 17/50),
    C_0 = -1/48, at the paper's geometry (h = 13/16)."""
    delta, q, R, d = F(delta), F(q), F(R), F(d)
    h = F(13, 16)
    return F(-1, 48) + F(2, 3) * delta + q / 6 - h * (1 - R) + (d - h) * (R + delta / 2 - CONTOUR)


def floor_C0(k, ell, M, b):
    """C_0(k) = 1/2 + ell/2 - 3M/4 + b (1/4 - 1/(2k)) (derived from line 15729)."""
    ell, M, b = F(ell), F(M), F(b)
    return F(1, 2) + ell / 2 - 3 * M / 4 + b * (F(1, 4) - F(1) / (2 * F(k)))


def floor_exponent(k, ell, M, b, delta0):
    """Floor rows (line 15847 generalised): R = 1, q at its largest value
    delta0/2, d = h: E(h) = C_0(k) + (1 + ell - M/2) delta0."""
    ell, M, delta0 = F(ell), F(M), F(delta0)
    return floor_C0(k, ell, M, b) + (1 + ell - M / 2) * delta0


# ---------------------------------------------------------------------------
# exact linear programs by vertex enumeration
# ---------------------------------------------------------------------------


def _solve(rows, rhs):
    """Exact Gauss-Jordan elimination; None when the system is singular."""
    n = len(rows)
    aug = [[F(v) for v in row] + [F(c)] for row, c in zip(rows, rhs)]
    for col in range(n):
        piv = next((r for r in range(col, n) if aug[r][col] != 0), None)
        if piv is None:
            return None
        aug[col], aug[piv] = aug[piv], aug[col]
        for r in range(n):
            if r != col and aug[r][col] != 0:
                fac = aug[r][col] / aug[col][col]
                aug[r] = [x - fac * y for x, y in zip(aug[r], aug[col])]
    return [aug[i][n] / aug[i][i] for i in range(n)]


def _dot(u, v):
    return sum(F(a) * F(b) for a, b in zip(u, v))


def lp_min(objective, constraints):
    """Minimise objective . x over {x : a . x <= c for (a, c) in constraints}.

    Exact vertex enumeration; the caller guarantees a bounded, nonempty
    region (returns None when no vertex is feasible).  Returns
    (value, vertex).
    """
    nv = len(objective)
    best = None
    for idx in itertools.combinations(range(len(constraints)), nv):
        x = _solve([constraints[i][0] for i in idx], [constraints[i][1] for i in idx])
        if x is None:
            continue
        if all(_dot(a, x) <= F(c) for a, c in constraints):
            val = _dot(objective, x)
            if best is None or val < best[0]:
                best = (val, tuple(x))
    return best


# constraints on x = (ell, M, b), each as (a, c) meaning a . x <= c


def cons_admissible(dual_relax=0):
    """ell >= 0, b >= 0, l_x = (M - b)/2 >= 0, and the dual length M + ell <= 1
    (line 8246: the subtraction leaves M + ell - 1 for a general geometry;
    that M + ell <= 1 suffices is hunt #134's reading, inferred).
    ``dual_relax`` = e prices a reflection with a dual longer by Z^e."""
    return [((-1, 0, 0), 0), ((0, 0, -1), 0), ((0, -1, 1), 0), ((1, 1, 0), 1 + F(dual_relax))]


def cons_floor(k, delta0, relax=0):
    """Floor rows: C_0(k) + (1 + ell - M/2) delta0 <= relax (relax = 0 in the
    paper; relax = g prices a gain of Z^g on the floor rows)."""
    d = F(delta0)
    return [((F(1, 2) + d, -F(3, 4) - d / 2, F(1, 4) - F(1) / (2 * F(k))), F(relax) - (F(1, 2) + d))]


def cons_corner(relax=0):
    """Per-summand corner M - 2 ell >= 1/2 (hunt #134's reading of line 8306)."""
    return [((2, -1, 0), F(relax) - F(1, 2))]


def cons_d0(relax=0):
    """Only the unrescaled summand lossless: M >= (1 + 3 ell)/2 (hunt #134, inferred)."""
    return [((F(3, 2), -1, 0), F(relax) - F(1, 2))]


def cons_gram(k):
    """Gram cap (3 - 2/k) b <= M - 2 ell (line 8597's l_y - d >= 11b/6 at d = ell, k = 6)."""
    return [((2, -1, 3 - F(2) / F(k)), 0)]


M_MINUS_2ELL = (-2, 1, 0)  # sigma_0 = 1 - 1/k + (M - 2 ell)/(2k) is increasing in M - 2 ell


def wall(k, *, floor=None, corner=False, d0=False, gram=False, floor_relax=0, dual_relax=0,
         loss_relax=0):
    """The smallest template target for order k under the chosen constraints
    (``loss_relax`` loosens the direct bound's loss condition, corner or d0)."""
    cons = cons_admissible(dual_relax)
    if floor is not None:
        cons += cons_floor(k, floor, floor_relax)
    if corner:
        cons += cons_corner(loss_relax)
    if d0:
        cons += cons_d0(loss_relax)
    if gram:
        cons += cons_gram(k)
    best = lp_min(M_MINUS_2ELL, cons)
    if best is None:
        return None
    m, x = best
    return {"m": m, "sigma0": 1 - F(1) / F(k) + m / (2 * F(k)), "point": x}


def wall_dual_closed(k):
    """Dual length alone: sigma_0 >= 1 - 2/k (vertex ell = 1, M = b = 0)."""
    return 1 - F(2) / F(k)


def wall_floor_closed(k, delta0):
    """Dual length and floor rows: 1 - 4/((5 + 6 delta0) k)."""
    return 1 - F(4) / ((5 + 6 * F(delta0)) * F(k))


def wall_corner_closed(k):
    return 1 - F(3) / (4 * F(k))


def wall_floor_gain_closed(k, g):
    """Floor rows gaining Z^g (delta_0 -> 0, dual length exact):
    1 - (4 + 6g)/(5k) for 0 <= g <= 1, and the dual-length wall 1 - 2/k from g = 1 on."""
    g = F(g)
    return 1 - (4 + 6 * min(g, F(1))) / (5 * F(k))


def wall_floor_and_loss_gain_closed(k, g):
    """Floor rows and the direct bound's loss condition (d0 reading) both gaining
    Z^g, dual length exact: 1 - (4 + 3g)/(5k) for 0 <= g <= 2 (vertex
    ell = (1 + 2g)/5, M = (4 - 2g)/5), the dual-length wall 1 - 2/k from g = 2 on."""
    g = F(g)
    return 1 - (4 + 3 * min(g, F(2))) / (5 * F(k))


def wall_dual_gain_closed(k, e):
    """Dual length longer by Z^e (floor rows exact, delta_0 -> 0): 1 - (4 + 2e)/(5k),
    at the vertex ell = (1 + 3e)/5, M = (4 + 2e)/5, b = 0, admissible for every e >= 0."""
    return 1 - (4 + 2 * F(e)) / (5 * F(k))


def balanced_closed(k):
    """Part I's balanced probe (ell = 0, M = 1): 1 - 1/(2k)."""
    return 1 - F(1) / (2 * F(k))


def floor_dual_multipliers(k, delta0):
    """LP dual multipliers (y1, y2, y3) >= 0 with
    (M - 2 ell) - m* = y1 * (-floor) + y2 * (1 - M - ell) + y3 * b,
    an identity in (ell, M, b) which proves the floor wall for every geometry
    (each term on the right is >= 0 there); y3 >= 0 exactly when k >= 2."""
    d = F(delta0)
    y1 = F(12) / (5 + 6 * d)
    y2 = F(4) / (5 + 6 * d)
    y3 = y1 * (F(1, 4) - F(1) / (2 * F(k)))
    m_star = (2 + 12 * d) / (5 + 6 * d)
    return y1, y2, y3, m_star


#: the price modes: (constraints imposed, constraints relaxed by the common eps)
PRICE_MODES = {
    "common": (("dual", "floor"), ("dual", "floor")),
    "floor": (("dual", "floor"), ("floor",)),
    "dual": (("dual", "floor"), ("dual",)),
    "total": (("dual", "floor", "d0"), ("dual", "floor", "d0")),
    "per_summand": (("dual", "floor", "corner"), ("dual", "floor", "corner")),
}


def price_of_one_half(k, mode="common"):
    """Smallest relaxation eps that admits sigma_0 = 1/2 (M - 2 ell = 2 - k), the
    floor rows taken at delta_0 -> 0.

    Modes (``PRICE_MODES``): 'common' relaxes the dual length and the floor rows
    together; 'floor' and 'dual' relax one of them; 'total' and 'per_summand' add
    the direct bound's loss condition in hunt #134's two readings (only the
    unrescaled summand lossless, M >= (1 + 3 ell)/2; or every summand,
    M - 2 ell >= 1/2) and relax all three together.  Returns None when
    infeasible.  Variables (ell, M, b, eps).
    """
    kk = F(k)
    impose, relax = PRICE_MODES[mode]

    def e(name):
        return -1 if name in relax else 0

    cons = [((-1, 0, 0, 0), 0), ((0, 0, -1, 0), 0), ((0, -1, 1, 0), 0), ((0, 0, 0, -1), 0)]
    cons += [((-2, 1, 0, 0), 2 - kk), ((2, -1, 0, 0), kk - 2)]
    if "dual" in impose:
        cons += [((1, 1, 0, e("dual")), 1)]
    if "floor" in impose:
        cons += [((F(1, 2), -F(3, 4), F(1, 4) - 1 / (2 * kk), e("floor")), -F(1, 2))]
    if "d0" in impose:
        cons += [((F(3, 2), -1, 0, e("d0")), -F(1, 2))]
    if "corner" in impose:
        cons += [((2, -1, 0, e("corner")), -F(1, 2))]
    big = 10**4
    cons += [((1, 0, 0, 0), big), ((0, 1, 0, 0), big), ((0, 0, 1, 0), big), ((0, 0, 0, 1), big)]
    best = lp_min((0, 0, 0, 1), cons)
    if best is None:
        return None
    eps, x = best
    assert eps < big and max(x[:3]) < big, "artificial box reached"
    return eps, x


def price_closed(k, mode="common"):
    kk = F(k)
    if mode == "common":
        return max((5 * kk - 8) / 16, (kk - 4) / 2, F(0))
    if mode == "floor":
        return (5 * kk - 8) / 12 if kk <= 4 else None
    if mode == "dual":
        return 5 * kk / 4 - 2
    if mode == "total":
        return (5 * kk - 8) / 7
    if mode == "per_summand":
        return kk - F(3, 2)
    raise ValueError(mode)


def region_two_contains_pole(k):
    """Is the principal residue z = 1/k inside Euler region two, z_r >= 33/200
    (line 4056)?  True exactly for k <= 6."""
    return pole(k) >= F(33, 200)


def principal_correction_abscissa(shift=F(0)):
    """Where the paper's principal correction H_{eta,1}(x, 1, 1/6) converges
    absolutely (k = 6 only): its binding term is R = a_p^2 Q^(4 - 6x - 6z)
    (line 3866), with |a_p| = 1 for a unitary target (line 3870) and
    |a_p| = Q^(3 shift) for the target eta N^shift.  At z = 1/6 the condition
    6 shift + 3 - 6 Re x < -1 gives Re x > 2/3 + shift (derived)."""
    z = F(1, 6)
    return (4 - 6 * z + 6 * F(shift) + 1) / 6


def wa_shifted_floor(k, shift=F(1, 4)):
    """Template target for the W_a components: coefficients of size N^a raise
    the direct bound by Z^a (inferred), so the best target is wall + a."""
    return wall_floor_closed(k, 0) + F(shift)


# ---------------------------------------------------------------------------
# symbolic checks (sympy)
# ---------------------------------------------------------------------------


def symbolic_checks() -> dict:
    """The template identities with k, ell, M, b, delta, q, R, d as symbols."""
    import sympy as sp

    k, ell, M, b, delta, q, R, d, d0, cz = sp.symbols(
        "k ell M b delta q R d delta0 cz", real=True
    )
    half = sp.Rational(1, 2)
    lx = (M - b) / 2
    ly = (M + b) / 2
    h = 1 - lx + ell
    z = 1 / k
    c_weight = lx * (half - z) + (z - 1) + ell * z
    c_paper = lx / 2 - 1 + h * z
    low = lx / 2 + b * z / 2
    s0 = sp.simplify(low - c_paper)
    a = (1 + delta) / 2
    E = (a - s0 + h * (cz - z) - a * ly - (1 - a) * ell
         - (delta / 2 - q) * ell + d * (R + delta / 2 - cz))
    Eh = sp.expand(E.subs(d, h))
    C0 = half + ell / 2 - 3 * M / 4 + b * (sp.Rational(1, 4) - 1 / (2 * k))
    floor = sp.expand(Eh.subs({R: 1, q: delta / 2}).subs(delta, d0))
    floor_lhs = C0 + (1 + ell - M / 2) * d0
    y1 = 12 / (5 + 6 * d0)
    y2 = 4 / (5 + 6 * d0)
    y3 = y1 * (sp.Rational(1, 4) - 1 / (2 * k))
    mstar = (2 + 12 * d0) / (5 + 6 * d0)
    dual_gap = (M - 2 * ell) - mstar - (y1 * (-floor_lhs) + y2 * (1 - M - ell) + y3 * b)
    h0 = sp.Rational(13, 16)
    second_line = (sp.Rational(-1, 48) + sp.Rational(2, 3) * delta + q / 6 - h0 * (1 - R)
                   + (d - h0) * (R + delta / 2 - sp.Rational(17, 50)))
    at_paper = E.subs({k: 6, cz: sp.Rational(17, 50), ell: sp.Rational(1, 6),
                       M: sp.Rational(5, 6), b: sp.Rational(1, 8)})
    return {
        "weight_equals_line_5588": sp.simplify(c_weight - c_paper) == 0,
        "target_closed_form": sp.simplify(s0 - (1 - 1 / k + (M - 2 * ell) / (2 * k))) == 0,
        "target_free_of_b": sp.simplify(sp.diff(s0, b)) == 0,
        "contour_cancels_at_d_equals_h": sp.simplify(sp.diff(Eh, cz)) == 0,
        "floor_closed_form": sp.simplify(floor - floor_lhs) == 0,
        "floor_dual_multiplier_identity": sp.simplify(dual_gap) == 0,
        "increment_formula": sp.simplify(
            s0.subs(k, k + 1) - s0 - (2 - (M - 2 * ell)) / (2 * k * (k + 1))
        ) == 0,
        "line_15729_equals_line_15732_at_k6": sp.simplify(at_paper - second_line) == 0,
    }


# ---------------------------------------------------------------------------
# the rival gate (mpmath, measured)
# ---------------------------------------------------------------------------


def _repo_on_path() -> None:
    if REPO_ROOT not in sys.path:
        sys.path.insert(0, REPO_ROOT)


def mobius_sieve(n_max: int):
    """mu(0..n_max) and the primes up to n_max, by a linear sieve."""
    mu = [1] * (n_max + 1)
    mu[0] = 0
    composite = bytearray(n_max + 1)
    primes: list[int] = []
    for i in range(2, n_max + 1):
        if not composite[i]:
            primes.append(i)
            mu[i] = -1
        for p in primes:
            if i * p > n_max:
                break
            composite[i * p] = 1
            if i % p == 0:
                mu[i * p] = 0
                break
            mu[i * p] = -mu[i]
    return mu, primes


def _chi5(n: int):
    """The mod-5 character with chi(2) = i, as in zeta.epstein.chi5."""
    return {0: 0, 1: 1, 2: 1j, 3: -1j, 4: -1}[n % 5]


def dh_constituents(s, dps: int = 20):
    """(c1, c2, L(s, chi), L(s, chibar)) with DH = c1 L(chi) + c2 L(chibar),
    c1 = (1 - i kappa)/2, from zeta.epstein's Hurwitz route."""
    _repo_on_path()
    from mpmath import mp
    from zeta import epstein as ep

    with mp.workdps(dps + 10):
        kap = ep.kappa(dps + 10)
        c1 = (1 - mp.mpc(0, 1) * kap) / 2
        c2 = mp.conj(c1)
        L1 = ep.L_chi(s, conjugate=False, dps=dps + 10)
        L2 = ep.L_chi(s, conjugate=True, dps=dps + 10)
        return c1, c2, L1, L2


def dh_H_minus_one(c1, c2, L1, L2):
    """H_DH - 1 = DH * (c1/L1 + c2/L2) - 1 = c1 c2 (L1 - L2)^2 / (L1 L2), using c1 + c2 = 1."""
    return c1 * c2 * (L1 - L2) ** 2 / (L1 * L2)


def dh_at_offline_zero(dps: int = 30) -> dict:
    """The distinguishing step for DH at its zero 0.808517 + 85.699348 i.

    The probe's principal row is linear in the target's coefficients, so for
    the DH coefficients c1 chi + c2 chibar it carries c1/L(chi) + c2/L(chibar)
    (times the constituents' corrections, holomorphic there).  The criterion
    needs it to be H/DH with |H - 1| <= 1/2.  At the zero, DH = 0 while
    L(chi), L(chibar) do not vanish, so H = 0 and |H - 1| = 1.
    """
    _repo_on_path()
    from mpmath import mp
    from zeta import epstein as ep

    with mp.workdps(dps + 10):
        rho = mp.mpc(ep.OFFLINE_ZERO_RE, ep.OFFLINE_ZERO_IM)
        c1, c2, L1, L2 = dh_constituents(rho, dps)
        dh_direct = ep.dh_f(rho, dps=dps + 10)
        dh_combo = c1 * L1 + c2 * L2
        recip = c1 / L1 + c2 / L2
        H = dh_combo * recip
        H_closed = 1 + dh_H_minus_one(c1, c2, L1, L2)
        return {
            "rho": (float(rho.real), float(rho.imag)),
            "abs_dh_direct": float(abs(dh_direct)),
            "abs_dh_combo": float(abs(dh_combo)),
            "abs_L_chi": float(abs(L1)),
            "abs_L_chibar": float(abs(L2)),
            "abs_probe_reciprocal": float(abs(recip)),
            "abs_H": float(abs(H)),
            "abs_H_minus_1": float(abs(H - 1)),
            "abs_H_closed_minus_1": float(abs(H_closed - 1)),
            "abs_H_closed": float(abs(H_closed)),
        }


def _l_chi5_deleted(s, L, conj: bool, primes):
    """L^S(s) = L(s) prod_{p in S} (1 - chi(p) p^-s) for the mod-5 character."""
    from mpmath import mp

    out = L
    for p in primes:
        c = _chi5(p)
        if conj:
            c = c.conjugate() if isinstance(c, complex) else c
        out *= 1 - mp.mpc(c) * mp.power(p, -s)
    return out


def dh_contraction_scan(sigma, t_lo: float, t_hi: float, step: float,
                        delete_upto: int = 1, dps: int = 15) -> dict:
    """max over a t-grid of |H^S - 1| on Re s = sigma for the DH coefficients
    restricted to n prime to S = {p <= delete_upto} (none when delete_upto < 2).

    H^S - 1 = c1 c2 (L1^S - L2^S)^2 / (L1^S L2^S).  Measured, finite grid only.
    """
    _repo_on_path()
    from mpmath import mp
    from zeta import epstein as ep

    _, primes = mobius_sieve(max(delete_upto, 2))
    S = [p for p in primes if p <= delete_upto]
    worst = (-1.0, None)
    over_half = 0
    n = 0
    with mp.workdps(dps):
        kap = ep.kappa(dps)
        c1 = (1 - mp.mpc(0, 1) * kap) / 2
        c2 = mp.conj(c1)
        t = t_lo
        while t <= t_hi + 1e-12:
            s = mp.mpc(sigma, t)
            L1 = ep.L_chi(s, conjugate=False, dps=dps)
            L2 = ep.L_chi(s, conjugate=True, dps=dps)
            if S:
                L1 = _l_chi5_deleted(s, L1, False, S)
                L2 = _l_chi5_deleted(s, L2, True, S)
            val = float(abs(dh_H_minus_one(c1, c2, L1, L2)))
            n += 1
            if val > 0.5:
                over_half += 1
            if val > worst[0]:
                worst = (val, t)
            t += step
    return {"sigma": float(sigma), "t_range": (t_lo, t_hi), "step": step,
            "deleted_primes": S, "points": n, "max_abs_H_minus_1": worst[0],
            "argmax_t": worst[1], "points_over_half": over_half}


def dh_moebius_sum_check(n_max: int = 20000, s_real: float = 2.0) -> dict:
    """Second route for the linear structure, where everything converges:
    the squarefree Moebius sum of the DH coefficients at real s > 1 against
    c1/L(chi) + c2/L(chibar) and against 1/DH.  Tail below 1/n_max."""
    _repo_on_path()
    from mpmath import mp
    from zeta import epstein as ep

    mu, _ = mobius_sieve(n_max)
    with mp.workdps(25):
        kap = float(ep.kappa(25))
    coeff = {1: 1.0, 2: kap, 3: -kap, 4: -1.0, 0: 0.0}
    direct = math.fsum(mu[n] * coeff[n % 5] * n ** (-s_real) for n in range(1, n_max + 1) if mu[n])
    zeta_direct = math.fsum(mu[n] * n ** (-s_real) for n in range(1, n_max + 1) if mu[n])
    with mp.workdps(25):
        c1, c2, L1, L2 = dh_constituents(mp.mpf(s_real), 20)
        linear = c1 / L1 + c2 / L2
        dh_val = c1 * L1 + c2 * L2
        recip_dh = 1 / dh_val
        inv_zeta = 1 / mp.zeta(s_real)
    return {
        "n_max": n_max,
        "s": s_real,
        "direct_sum": direct,
        "linear_combination_of_reciprocals": float(mp.re(linear)),
        "imag_linear": float(mp.im(linear)),
        "reciprocal_of_dh": float(mp.re(recip_dh)),
        "gap_direct_vs_linear": abs(direct - float(mp.re(linear))),
        "gap_direct_vs_reciprocal": abs(direct - float(mp.re(recip_dh))),
        "zeta_control_gap": abs(zeta_direct - float(inv_zeta)),
        "tail_bound": 1.0 / n_max,
    }


def _kronecker_m23(p: int) -> int:
    """The Kronecker symbol (-23 / p) for a prime p."""
    if p == 2:
        return 1  # -23 = 1 mod 8
    if p == 23:
        return 0
    v = pow((-23) % p, (p - 1) // 2, p)
    return 1 if v == 1 else -1


def _r116(n: int) -> int:
    """#{(x, y) in Z^2 : x^2 + xy + 6y^2 = n}, exactly (4n - 23 y^2 = (2x + y)^2)."""
    total = 0
    ymax = math.isqrt(4 * n // 23) + 1
    for y in range(-ymax, ymax + 1):
        disc = 4 * n - 23 * y * y
        if disc < 0:
            continue
        r = math.isqrt(disc)
        if r * r != disc:
            continue
        for sgn in ((1,) if r == 0 else (1, -1)):
            num = sgn * r - y
            if num % 2 == 0:
                total += 1
    return total


def epstein_local_data(p_max: int):
    """For each prime p <= p_max: (p, chi_-23(p), a_1(p), a_psi(p)), where
    a_1 is the Dedekind coefficient 1 + chi(p) and a_psi the class-group
    character's coefficient: 2 at split p with principal prime factors
    (x^2 + xy + 6y^2 = p solvable), -1 at the other split p, 0 at inert p,
    1 at p = 23."""
    _, primes = mobius_sieve(p_max)
    out = []
    for p in primes:
        ch = _kronecker_m23(p)
        if p == 23:
            a1, ap = 1, 1
        elif ch == -1:
            a1, ap = 0, 0
        else:
            a1 = 2
            ap = 2 if _r116(p) > 0 else -1
        out.append((p, ch, a1, ap))
    return out


def _euler_correction(s, data, which: int):
    """prod_p (1 - a(p) p^-s) / (1 - a(p) p^-s + chi(p) p^-2s): the factor H
    with sum mu(n) a(n) n^-s = H / L for a degree-2 Euler product."""
    from mpmath import mp

    out = mp.mpc(1)
    for p, ch, a1, ap in data:
        a = a1 if which == 1 else ap
        x = mp.power(p, -s)
        out *= (1 - a * x) / (1 - a * x + ch * x * x)
    return out


def _l_chi_m23(s):
    """L(s, chi_-23) by the Hurwitz route, sharing no code with the lattice sums."""
    from mpmath import mp

    total = mp.mpc(0)
    for a in range(1, 23):
        total += _kronecker_m23_int(a) * mp.zeta(s, mp.mpf(a) / 23)
    return mp.power(23, -s) * total


def _kronecker_m23_int(a: int) -> int:
    """(-23 / a) for 1 <= a <= 22, multiplicatively from the prime values."""
    from sympy import factorint

    val = 1
    for p, e in factorint(a).items():
        val *= _kronecker_m23(p) ** e
    return val


def epstein_at_offline_zero(dps: int = 25, p_max: int = 10000) -> dict:
    """The distinguishing step for Epstein (1,1,6) at its zero 0.953260 + 16.290216 i.

    Z_Q/2 = (zeta_K + 2 L_psi)/3 with K = Q(sqrt(-23)).  The probe-visible
    reciprocal of f = r_Q/2 is (H_1/zeta_K + 2 H_psi/L_psi)/3, finite where
    zeta_K and L_psi do not vanish.  At the zero, Z_Q = 0, so H_E = 0.
    """
    _repo_on_path()
    from mpmath import mp
    from zeta import epstein as ep

    with mp.workdps(dps + 10):
        rho = mp.mpc("0.953260474794660686250509013566", "16.2902157203903907929631726452")
        z116 = ep.epstein_zeta(rho, (1, 1, 6), dps=dps)
        z213 = ep.epstein_zeta(rho, (2, 1, 3), dps=dps)
        zk_lattice = (z116 + 2 * z213) / 2
        zk_hurwitz = mp.zeta(rho) * _l_chi_m23(rho)
        lpsi = (z116 - z213) / 2
        data = epstein_local_data(p_max)
        H1 = _euler_correction(rho, data, 1)
        Hpsi = _euler_correction(rho, data, 2)
        recip = (H1 / zk_lattice + 2 * Hpsi / lpsi) / 3
        HE = (z116 / 2) * recip
        return {
            "rho": (float(rho.real), float(rho.imag)),
            "abs_Z116": float(abs(z116)),
            "abs_Z213": float(abs(z213)),
            "abs_zeta_K_lattice": float(abs(zk_lattice)),
            "zeta_K_two_route_gap": float(abs(zk_lattice - zk_hurwitz)),
            "abs_L_psi": float(abs(lpsi)),
            "abs_H1": float(abs(H1)),
            "abs_Hpsi": float(abs(Hpsi)),
            "abs_probe_reciprocal": float(abs(recip)),
            "abs_H_E": float(abs(HE)),
            "abs_H_E_minus_1": float(abs(HE - 1)),
            "p_max": p_max,
        }


def wa_correction(s, shift, primes):
    """H_W(s) over the given primes: prod (1 - p^-2s / ((1 - p^(a-s))(1 - p^(-a-s))))."""
    from mpmath import mp

    out = mp.mpc(1)
    for p in primes:
        u = mp.power(p, shift - s)
        v = mp.power(p, -shift - s)
        out *= 1 - mp.power(p, -2 * s) / ((1 - u) * (1 - v))
    return out


def wa_at_offline_zero(deletions=(1, 10, 100), p_max: int = 100000, dps: int = 20) -> dict:
    """The distinguishing step for W_a = zeta(s + 1/4) zeta(s - 1/4) at its
    zero 3/4 + i gamma_1.  The squarefree Moebius sum of its coefficients is
    H_W / W_a with H_W an Euler product converging absolutely on Re s > 1/2;
    deleting the primes p <= P0 brings H_W within 1/2 of 1, so W_a passes the
    step: its probe-visible reciprocal has the pole the criterion needs."""
    from mpmath import mp

    a = mp.mpf(1) / 4
    _, primes = mobius_sieve(p_max)
    out = {"deletions": {}}
    with mp.workdps(dps):
        g1 = mp.im(mp.zetazero(1))
        s1 = mp.mpc(mp.mpf(3) / 4, g1)
        w = mp.zeta(s1 + a) * mp.zeta(s1 - a)
        out["s1"] = (0.75, float(g1))
        out["abs_W_a"] = float(abs(w))
        # each omitted factor is 1 + e_p with |e_p| <= p^-3/2 / ((1 - p^-1/2)(1 - p^-1)),
        # and sum_{n > P} n^-3/2 <= 2 P^-1/2, so the omitted product is within
        # exp(tail) - 1 of 1
        P = float(p_max)
        tail = 2.0 * P ** -0.5 / ((1 - P ** -0.5) * (1 - 1 / P))
        out["omitted_factor_bound"] = math.expm1(tail)
        for P0 in deletions:
            ps = [p for p in primes if p > P0]
            H = wa_correction(s1, a, ps)
            out["deletions"][str(P0)] = {"abs_H": float(abs(H)), "abs_H_minus_1": float(abs(H - 1))}
    return out


def wa_moebius_sum_check(n_max: int = 20000, s_real: float = 3.0) -> dict:
    """Second route for H_W: the squarefree Moebius sum of the W_a coefficients
    a(n) = n^-a sigma_{2a}(n) at s = 3 against H_W(3)/W_a(3)."""
    from mpmath import mp

    a = 0.25
    mu, primes = mobius_sieve(n_max)
    # a(n) on squarefree n is multiplicative: prod (p^a + p^-a)
    spf = list(range(n_max + 1))
    for p in primes:
        for m in range(p * p, n_max + 1, p):
            if spf[m] == m:
                spf[m] = p
    total = 0.0
    for n in range(1, n_max + 1):
        if not mu[n]:
            continue
        val = 1.0
        m = n
        while m > 1:
            p = spf[m]
            val *= p ** a + p ** (-a)
            m //= p
        total += mu[n] * val * n ** (-s_real)
    with mp.workdps(25):
        _, big = mobius_sieve(200000)
        H = wa_correction(mp.mpf(s_real), mp.mpf(a), big)
        W = mp.zeta(s_real + a) * mp.zeta(s_real - a)
        closed = H / W
    return {"direct_sum": total, "H_over_W": float(mp.re(closed)),
            "gap": abs(total - float(mp.re(closed))), "n_max": n_max}


# ---------------------------------------------------------------------------
# report
# ---------------------------------------------------------------------------


def frac(x) -> str:
    return str(F(x))


def exact_tables(ks=(1, 2, 3, 4, 5, 6, 7, 8, 12, 24, 100)) -> dict:
    rows = {}
    for k in ks:
        row = {
            "pole": frac(pole(k)),
            "balanced": frac(target(k, *PART_I)),
            "paper_geometry": frac(target(k, *PART_II)),
            "region_two_contains_pole": region_two_contains_pole(k),
        }
        if k >= 2:
            row.update({
                "wall_dual": frac(wall(k)["sigma0"]),
                "wall_floor_limit": frac(wall(k, floor=0)["sigma0"]),
                "wall_floor_paper_bin": frac(wall(k, floor=FLOOR_BIN)["sigma0"]),
                "wall_corner": frac(wall(k, corner=True)["sigma0"]),
            })
            for mode in PRICE_MODES:
                p = price_of_one_half(k, mode)
                row[f"price_{mode}"] = None if p is None else frac(p[0])
        rows[str(k)] = row
    return rows


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--paper", nargs="?", const=PAPER_DEFAULT, default=None,
                    help="check every citation against the pinned paper.tex")
    ap.add_argument("--write", action="store_true", help="write results_probe_tower.json")
    ap.add_argument("--no-rivals", action="store_true", help="skip the mpmath rival computations")
    args = ap.parse_args(argv)

    doors = {}
    for k in (2, 6):
        doors[str(k)] = {
            "floor_and_loss_gain": {frac(g): frac(wall(k, floor=0, d0=True, floor_relax=g, loss_relax=g)["sigma0"])
                                    for g in (F(0), F(1, 6), F(1), F(2))},
            "floor_gain_with_loss_held": {frac(g): frac(wall(k, floor=0, d0=True, floor_relax=g)["sigma0"])
                                          for g in (F(0), F(1, 6), F(1))},
            "dual_gain": {frac(e): frac(wall(k, floor=0, dual_relax=e)["sigma0"])
                          for e in (F(0), F(1), F(11, 2))},
        }
    out: dict = {"exact": exact_tables(), "doors": doors, "symbolic": symbolic_checks()}
    if args.paper:
        sha_ok, missing = verify_citations(args.paper)
        out["citations"] = {"sha256_ok": sha_ok, "checked": len(CITATIONS), "missing": missing}
    if not args.no_rivals:
        out["dh_zero"] = dh_at_offline_zero()
        out["dh_moebius"] = dh_moebius_sum_check()
        for upto in (1, 3, 100):
            out[f"dh_scan_7_8_deleted_upto_{upto}"] = dh_contraction_scan(
                0.875, 1.0, 300.0, 0.25, delete_upto=upto, dps=12
            )
        out["epstein_zero"] = epstein_at_offline_zero()
        out["wa_zero"] = wa_at_offline_zero()
        out["wa_moebius"] = wa_moebius_sum_check()
    print(json.dumps(out, indent=2, default=str))
    if args.write:
        with open(RESULTS, "w", encoding="ascii") as fh:
            json.dump(out, fh, indent=2, default=str)
            fh.write("\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

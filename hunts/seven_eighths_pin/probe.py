"""Hunt #134: which inequality of OpenAI's 7/8 argument fixes the number 7/8.

Every formula below is transcribed from the LaTeX source of the preprint of
2026-09-30 (github.com/openai/math at adc7f124,
preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex,
sha256 42a5ee0f...c6a3), cited by line and by a verbatim snippet in CITATIONS, and
rewritten as a function of the free geometry of Part II:

    ell   total length of the prime slots, base Z         (paper: 1/6)
    M     l_x + l_y, the two averaging lengths together    (paper: 5/6)
    b     l_y - l_x, the offset between them               (paper: 1/8)

with l_x = (M - b)/2, l_y = (M + b)/2 and h = 1 - l_x + ell (Definition
stage-high-data, line 5586).  ``reproductions()`` evaluates each general formula at
the paper's values and compares with the number the paper prints; a transcription
error shows up there.  Exact rational arithmetic throughout; the float grid scans
are labelled as scans.

    .venv/bin/python hunts/seven_eighths_pin/probe.py              # all of it
    .venv/bin/python hunts/seven_eighths_pin/probe.py --paper PATH # also check citations
"""
from __future__ import annotations

import argparse
import hashlib
import json
import sys
from fractions import Fraction as Fr
from pathlib import Path

HERE = Path(__file__).resolve().parent

PAPER_SHA256 = "42a5ee0febca59fd1def55cfd6c6808c322ef4237d7726303ea52f711deac6a3"

ELL_PAPER = Fr(1, 6)
M_PAPER = Fr(5, 6)
B_PAPER = Fr(1, 8)
ALPHA = Fr(5, 6)    # sextic amplification slope, e(r) = (1 + 5r)/6 = 1 - alpha + alpha r
C_PAPER = Fr(4, 9)  # plain-capacity coefficient 1/(3 kappa_0) at kappa_0 = 2(7/8) - 1
ZC_PAPER = Fr(17, 50)

#: line number and a verbatim snippet of the paper's LaTeX at that line
CITATIONS = {
    "C_I": (190, r"C_{\mathrm I}(s)=s-\frac23"),
    "C_II": (6835, r"C(s)=C_{\mathrm{II}}(s):=s-\frac{11}{16}"),
    "bootstrap": (6817, r"\Delta:=\beta_*-\frac78,\qquad 0<\Delta\le\frac1{24},"),
    "geometry": (6860, r"b=\frac18,\qquad h=\frac{13}{16},\qquad \ell=\frac16,"),
    "l_x": (6861, r"l_x=1+\ell-h=\frac{17}{48}"),
    "M": (6864, r"M=l_x+l_y=\frac56,\qquad M+\ell=1."),
    "low_I": (3717, r"&=Z^{1/4+\epsilon_1/2}."),
    "low_II": (8570, r"\ll Z^{l_x/2+b/12+\epsilon}=Z^{3/16+\epsilon}."),
    "dual_length": (8246, r"Since $M'+\ell'-1=-3d$, direct subtraction gives"),
    "row_loss": (8306, r"M'+\frac{1+3\ell'-2M'-2\Delta_H+\theta_N}{4}"),
    "f_d": (8631, r"f(d)=d-3d/2-d/2=-d\le0."),
    "C_form": (8641, r"C_{\mathrm{II}}(s)=l_x/2+s-1+h/6=s-11/16,"),
    "C_match": (8642, r"C_{\mathrm{II}}(7/8)=3/16=l_x/2+b/12."),
    "alpha_def": (15101, r"\alpha:=\frac56."),
    "D_x_P_x": (15192, r"D_x"),
    "e_r": (15300, r"moment exponent \((1+5r)/6=1-\alpha+\alpha r\)."),
    "m_w": (15674, r"m_w:=\frac{l_y}{20}=\frac{23}{960},\qquad"),
    "m_z": (15675, r"m_z:=\frac h{600}=\frac{13}{9600}."),
    "E_line1": (15729, r"&=a-\frac78+h\left(\frac{17}{50}-\frac16\right)"),
    "C_0": (15734, r"\qquad C_0=-\frac1{48}."),
    "contour": (15742, r"\Re s=a+16e,\qquad \Re w=1-a-6e,\qquad \Re z=\frac{17}{50},"),
    "floor": (15847, r"E(h)\le C_0+\frac34\delta_0=-\frac7{1200}<0."),
    "small": (15878, r"=-\frac{79}{800}."),
    "small_saving": (15886, r"=-\frac{63}{800}+O(e+\epsilon)."),
    "B_0": (15900, r"\(B_0=l_x/2+1+l_y=53/32\)"),
    "large_delta": (15945, r"=-\frac1{48}-\frac{\delta}{16}+O(\epsilon)<0."),
    "cert_bound": (16000, r"-E_*\ge\frac{49}{440640}>\frac1{10000}."),
    "p_y": (16010, r"p_y=7+18y+8y^2,\qquad"),
    "D_x": (16015, r"D_x=\frac{37+34y}{18},\qquad"),
    "P_x": (16016, r"P_x=\frac{p_y}{9},\qquad"),
    "R_star": (16019, r"From \(R_*=1-\delta+(\alpha-\delta)\delta P_x/(2\mathcal J)\)"),
    "cert_identity": (16048, r"\label{eq:balanced-endpoint-certificate}"),
    "m_hi": (16101, r"&=-\frac{49}{440640}-\frac{51}{64}\Delta"),
    "supply": (16116, r"\frac{\ell}{d}\ge\frac8{39}>\frac15>\frac7{37}."),
    "zeta": (16123, r"0<\zeta<5\ell-h=\frac1{48},"),
    "supply_15": (16126, r"\(1/5\), whose margin above \(7/37\) is \(2/185\)."),
    "intermediate": (16159, r"\le-\frac{529}{2400}+\frac{25}{96}\delta+O(\epsilon)"),
    "intermediate_end": (16160, r"\le-\frac{49}{14400}+O(\epsilon)<0."),
    "supply_839": (16271, r"exceeding \(7/37\) by \(23/1443\)."),
}


def verify_citations(paper: Path) -> list[str]:
    """Return the citation keys whose snippet is not on its stated line."""
    text = paper.read_bytes()
    if hashlib.sha256(text).hexdigest() != PAPER_SHA256:
        return ["<sha256 mismatch: not the pinned paper.tex>"]
    lines = text.decode("utf-8").splitlines()
    return [k for k, (n, snip) in CITATIONS.items() if snip not in lines[n - 1]]


# ---------------------------------------------------------------- geometry

def geometry(ell: Fr, b: Fr, M: Fr | None = None) -> dict:
    """Part II geometry with M free; M defaults to the paper's M = 1 - ell."""
    if M is None:
        M = 1 - ell
    l_x = (M - b) / 2
    l_y = (M + b) / 2
    h = 1 - l_x + ell
    return {"ell": ell, "b": b, "M": M, "h": h, "l_x": l_x, "l_y": l_y}


def mellin_shift(ell: Fr, b: Fr, M: Fr | None = None) -> Fr:
    """c with C(s) = s - c, from C(s) = s + l_x/2 - 1 + h/6 (lines 5586, 8641)."""
    g = geometry(ell, b, M)
    return 1 - g["l_x"] / 2 - g["h"] / 6


def low_exponent(ell: Fr, b: Fr, M: Fr | None = None) -> Fr:
    """The compensated low bound Z^(l_x/2 + b/12) (line 8570), set by the d = 0 summand."""
    return geometry(ell, b, M)["l_x"] / 2 + b / 12


def target(ell: Fr, b: Fr, M: Fr | None = None) -> Fr:
    """sigma_0 solving C(sigma_0) = low exponent: where the low side meets the signal."""
    return low_exponent(ell, b, M) + mellin_shift(ell, b, M)


def target_closed(ell: Fr, b: Fr, M: Fr | None = None) -> Fr:
    """Derived closed form: sigma_0 = 1 - h/6 + b/12 = 5/6 + (M - 2 ell)/12."""
    M = 1 - ell if M is None else M
    return Fr(5, 6) + (M - 2 * ell) / 12


def row_loss(ell: Fr, M: Fr, d: Fr) -> Fr:
    """Second-branch row-norm loss of Lemma probe-row-norm (line 8306), general form.

    (1 + 3 ell' - 2 M')/4 clipped at 0, with ell' = ell - d and M' = M - 2d.
    """
    return max(Fr(0), (1 + 3 * (ell - d) - 2 * (M - 2 * d)) / 4)


def low_side_ok_total(ell: Fr, M: Fr) -> bool:
    """Every rescaled summand within the low exponent: -d + loss(d)/2 <= 0 for 0 <= d <= ell.

    The extra exponent of summand d is -d (line 8631) plus half the row loss.  The
    worst case is d = 0, so this is M >= (1 + 3 ell)/2.  Dual length: M + ell <= 1.
    """
    return M + ell <= 1 and 2 * M >= 1 + 3 * ell


def low_side_ok_per_summand(ell: Fr, M: Fr) -> bool:
    """The stricter reading: no row loss in any summand, i.e. M - 2 ell >= 1/2.

    d = ell itself falls in the lossless first branch (line 8326); the summands at
    d = ell - ell/K carry (1 + 4 ell - 2M - ell/K)/4, so as the slot mesh is refined the
    condition is 1 + 4 ell - 2M <= 0, which row_loss(ell, M, ell) evaluates.
    """
    return M + ell <= 1 and row_loss(ell, M, ell) == 0


# ------------------------------------------------------------ high exponent

def high_exponent(ell, b, sigma0, d, delta, q, R, zc=ZC_PAPER, M=None) -> Fr:
    """eq:stage-high-exponent (line 6092) in the form of line 15729, sigma_0 left free.

    E(d) = a - sigma0 + h(zc - 1/6) - a l_y - (1-a) ell - (delta/2 - q) ell
           + d (R + delta/2 - zc),       a = (1 + delta)/2.
    """
    g = geometry(ell, b, M)
    a = (1 + delta) / 2
    return (a - sigma0 + g["h"] * (zc - Fr(1, 6)) - a * g["l_y"] - (1 - a) * ell
            - (delta / 2 - q) * ell + d * (R + delta / 2 - zc))


def c0(ell: Fr, b: Fr, M: Fr | None = None) -> Fr:
    """E(h) at delta = q = 0, R = 1, measured against the matched target."""
    g = geometry(ell, b, M)
    return high_exponent(ell, b, target(ell, b, M), g["h"], Fr(0), Fr(0), Fr(1), M=M)


def c0_closed(ell: Fr, b: Fr, M: Fr | None = None) -> Fr:
    """Derived closed form: C_0 = 1/2 + ell/2 - 3M/4 + b/6 (= -1/4 + 5ell/4 + b/6 at M = 1 - ell)."""
    M = 1 - ell if M is None else M
    return Fr(1, 2) + ell / 2 - Fr(3, 4) * M + b / 6


# ------------------------------------------------------------- row counts

def d_x(x: Fr, c: Fr = C_PAPER) -> Fr:
    """D_x = 3 - (1 + 2c)x; the paper's 3 - 17x/9 (line 15192) at c = 4/9."""
    return 3 - (1 + 2 * c) * x


def p_x(x: Fr, c: Fr = C_PAPER) -> Fr:
    """P_x = (2 - 2cx)(1 - x); the paper's (2 - 8x/9)(1 - x) (line 15192) at c = 4/9."""
    return (2 - 2 * c * x) * (1 - x)


def r_star(delta: Fr, x: Fr, c: Fr = C_PAPER) -> Fr:
    """R_* = 1 - delta + (alpha - delta) delta P_x / (2J) (line 16019)."""
    J = (ALPHA - delta) * d_x(x, c) + delta * p_x(x, c)
    return 1 - delta + (ALPHA - delta) * delta * p_x(x, c) / (2 * J)


def endpoint_neg_e(ell, b, delta, x, M=None, c=C_PAPER) -> Fr:
    """-E_* of Lemma balanced-endpoint: -E(h) at q = x delta, R = R_*, target matched."""
    g = geometry(ell, b, M)
    return -high_exponent(ell, b, target(ell, b, M), g["h"], delta, x * delta,
                          r_star(delta, x, c), M=M)


def endpoint_neg_e_closed(ell, b, delta, x, M=None, c=C_PAPER) -> Fr:
    """Derived closed form of -E_*: -C_0 + delta(ell + b)/2 - ell x delta - (h/2) K."""
    g = geometry(ell, b, M)
    J = (ALPHA - delta) * d_x(x, c) + delta * p_x(x, c)
    K = (ALPHA - delta) * delta * p_x(x, c) / J
    return (-c0_closed(ell, b, g["M"]) + delta * (ell + b) / 2 - ell * x * delta
            - g["h"] / 2 * K)


# ---------------------------------------------------------- reproductions

def reproductions() -> list[dict]:
    """Every printed constant, rebuilt from the general formulas at the paper's values."""
    ell, b, M = ELL_PAPER, B_PAPER, M_PAPER
    g = geometry(ell, b, M)
    h, l_x, l_y = g["h"], g["l_x"], g["l_y"]
    out = []

    def rec(name, cite, got, want):
        out.append({"name": name, "cite": cite, "line": CITATIONS[cite][0],
                    "got": str(got), "want": str(want), "ok": got == want})

    rec("h = 13/16", "geometry", h, Fr(13, 16))
    rec("l_x = 17/48", "l_x", l_x, Fr(17, 48))
    rec("M + ell = 1", "M", M + ell, Fr(1))
    rec("C_II shift 11/16", "C_II", mellin_shift(ell, b, M), Fr(11, 16))
    rec("C_II(s) = l_x/2 + s - 1 + h/6", "C_form", 1 - l_x / 2 - h / 6, Fr(11, 16))
    rec("low exponent 3/16", "low_II", low_exponent(ell, b, M), Fr(3, 16))
    rec("target 7/8 from C_II(7/8) = 3/16", "C_match", target(ell, b, M), Fr(7, 8))
    rec("target closed form 5/6 + (M - 2 ell)/12", "C_match", target_closed(ell, b, M), Fr(7, 8))
    rec("Part I target 11/12 (ell = b = 0, M = 1)", "C_I", target(Fr(0), Fr(0), Fr(1)), Fr(11, 12))
    rec("Part I shift 2/3", "C_I", mellin_shift(Fr(0), Fr(0), Fr(1)), Fr(2, 3))
    rec("Part I low exponent 1/4", "low_I", low_exponent(Fr(0), Fr(0), Fr(1)), Fr(1, 4))
    rec("row loss (d - 1/6)/4 at d = 0 is clipped to 0", "row_loss", row_loss(ell, M, Fr(0)), Fr(0))
    rec("row loss at d = ell is exactly 0", "row_loss", row_loss(ell, M, ell), Fr(0))
    rec("C_0 = -1/48", "C_0", c0(ell, b, M), Fr(-1, 48))
    rec("C_0 closed form", "C_0", c0_closed(ell, b, M), Fr(-1, 48))
    e1 = high_exponent(ell, b, Fr(7, 8), h, Fr(1), Fr(0), Fr(1), M=M)
    rec("delta coefficient 2/3", "C_0", e1 - c0(ell, b, M), Fr(2, 3))
    eq = high_exponent(ell, b, Fr(7, 8), h, Fr(0), Fr(1), Fr(1), M=M)
    rec("q coefficient 1/6", "C_0", eq - c0(ell, b, M), Fr(1, 6))
    d0 = Fr(1, 50)
    rec("floor bound -7/1200", "floor",
        high_exponent(ell, b, Fr(7, 8), h, d0, d0 / 2, Fr(1), M=M), Fr(-7, 1200))
    rec("large-delta endpoint -1/48 - delta/16 at delta = 5/6", "large_delta",
        high_exponent(ell, b, Fr(7, 8), h, ALPHA, ALPHA / 2, 1 - ALPHA, M=M),
        Fr(-1, 48) - ALPHA / 16)

    def inter(delta):
        return high_exponent(ell, b, Fr(7, 8), Fr(1, 2), delta, delta / 2,
                             Fr(76, 75) - Fr(2, 3) * delta, M=M)
    rec("intermediate constant -529/2400", "intermediate", inter(Fr(0)), Fr(-529, 2400))
    rec("intermediate slope 25/96", "intermediate", inter(Fr(1)) - inter(Fr(0)), Fr(25, 96))
    rec("intermediate at delta = 5/6 is -49/14400", "intermediate_end", inter(ALPHA), Fr(-49, 14400))
    rec("small-row margin -79/800", "small", h * (ZC_PAPER - Fr(1, 6)) - l_y / 2, Fr(-79, 800))
    rec("small-row saving 63/800", "small_saving",
        h * (ZC_PAPER - Fr(1, 6)) - l_y / 2 + 2 * Fr(1, 100), Fr(-63, 800))
    rec("principal margin m_w = l_y/20", "m_w", l_y / 20, Fr(23, 960))
    rec("principal margin m_z = h/600", "m_z", h / 600, Fr(13, 9600))
    rec("large-row B_0 = l_x/2 + 1 + l_y", "B_0", l_x / 2 + 1 + l_y, Fr(53, 32))
    rec("high margin factor 1 - h/4", "m_hi", 1 - h / 4, Fr(51, 64))
    rec("slot supply ell/h = 8/39", "supply", ell / h, Fr(8, 39))
    rec("supply excess 8/39 - 7/37", "supply_839", ell / h - Fr(7, 37), Fr(23, 1443))
    rec("extension ceiling 5 ell - h = 1/48", "zeta", 5 * ell - h, Fr(1, 48))
    rec("supply excess 1/5 - 7/37", "supply_15", Fr(1, 5) - Fr(7, 37), Fr(2, 185))
    rec("D_x at c = 4/9 equals (37 + 34y)/18", "D_x",
        all(d_x(Fr(1, 2) - y) == (37 + 34 * y) / 18 for y in (Fr(0), Fr(1, 7), Fr(1, 2))), True)
    rec("P_x at c = 4/9 equals (7 + 18y + 8y^2)/9", "P_x",
        all(p_x(Fr(1, 2) - y) == (7 + 18 * y + 8 * y * y) / 9
            for y in (Fr(0), Fr(1, 7), Fr(1, 2))), True)
    rec("e(r) slope: 1 - alpha + alpha r = (1 + 5r)/6", "e_r",
        all(1 - ALPHA + ALPHA * r == (1 + 5 * r) / 6 for r in (Fr(1), Fr(3, 2), Fr(2))), True)
    pts = [(Fr(i, 24), Fr(j, 8)) for i in range(1, 21) for j in range(0, 5)]
    rec("-E_* transcription equals the closed form (100 points)", "R_star",
        all(endpoint_neg_e(ell, b, dl, x, M) == endpoint_neg_e_closed(ell, b, dl, x, M)
            for dl, x in pts), True)
    ident = True
    for dl, x in pts + [(Fr(0), Fr(1, 2))]:
        y = Fr(1, 2) - x
        v = 51 + 41 * y
        J = (ALPHA - dl) * d_x(x) + dl * p_x(x)
        lhs = 10368 * v * J * endpoint_neg_e_closed(ell, b, dl, x, M)
        rhs = ((3 + 5 * y) * ((4 * v * dl - 79) ** 2 + 49)
               + 4 * y * (4 * v * dl * ((1 + 3 * y) * (15 + 32 * y) * dl + 9 - 13 * y)
                          + 265 + 3485 * y))
        ident = ident and lhs == rhs
    rec("completed-square identity of the certificate", "cert_identity", ident, True)
    worst = endpoint_neg_e(ell, b, Fr(79, 204), Fr(1, 2), M)
    rec("worst point delta = 79/204, x = 1/2: -E_* = 7/30672 >= 49/440640", "cert_bound",
        (worst, worst >= Fr(49, 440640)), (Fr(7, 30672), True))
    return out


# ------------------------------------------------------------- the walls

def floor_corner() -> dict:
    """The smallest target compatible with three conditions that no row count can relax.

    floor rows (R = 1, delta0 -> 0):   C_0 = 1/2 + ell/2 - 3M/4 + b/6 <= 0
    dual length (line 8246):            M + ell <= 1
    target:                             sigma_0 = 5/6 + (M - 2 ell)/12, b >= 0
    C_0 <= 0 gives M >= 2/3 + 2 ell/3 + 2b/9, hence sigma_0 >= 8/9 - ell/9 + b/54; with
    M + ell <= 1 this needs ell <= 1/5 - 2b/15.  The infimum is at b = 0, ell = 1/5,
    M = 4/5, where d = 0 losslessness, M >= (1 + 3 ell)/2, is also tight.
    """
    ell, M, b = Fr(1, 5), Fr(4, 5), Fr(0)
    return {"ell": ell, "M": M, "b": b, "sigma0": target(ell, b, M),
            "C_0": c0_closed(ell, b, M), "dual_slack": 1 - M - ell,
            "d0_lossless_slack": 2 * M - 1 - 3 * ell}


def single_point_bound(delta: Fr, x: Fr, c: Fr = C_PAPER) -> Fr | None:
    """Exact lower bound on the target from the endpoint inequality at one point (delta, x).

    At fixed (delta, x), -E_* is affine in (ell, M, b) and sigma_0 = 5/6 + (M - 2ell)/12.
    Along a line of constant sigma_0 and b, d(-E_*)/d ell = 1 + delta (1/2 - x) > 0 when
    M = 12 sigma_0 - 10 + 2 ell, so the best geometry has M + ell = 1, where
    sigma_0 = 11/12 - ell/4.  There -E_* = A + A_ell ell + A_b b with A_ell < 0.  The
    offset b ranges over [0, 3(1 - 3 ell)/8] (the Gram condition l_y - ell >= 11b/6 of
    Prop. probe-gram at d = ell).  Return the target at the largest ell for which some
    admissible b has -E_* >= 0, or None if every ell >= 0 works.
    """
    def f(ell, b):
        return endpoint_neg_e_closed(ell, b, delta, x, 1 - ell, c)
    A = f(Fr(0), Fr(0))
    A_ell = f(Fr(1), Fr(0)) - A
    A_b = f(Fr(0), Fr(1)) - A
    assert A_ell < 0
    if A_b <= 0:
        ell_star = -A / A_ell
    else:
        # b = 3(1 - 3 ell)/8: A + A_ell ell + A_b 3(1 - 3 ell)/8 = 0
        ell_star = -(A + A_b * Fr(3, 8)) / (A_ell - A_b * Fr(9, 8))
    if ell_star < 0:
        return None
    return Fr(11, 12) - ell_star / 4


def robust_single_point_bound(delta: Fr, x: Fr, c: Fr = C_PAPER) -> Fr | None:
    """As single_point_bound, but valid for every b >= 0 with no upper limit on b.

    Only points where -E_* does not increase with b qualify (A_b <= 0); there b = 0 is
    optimal and the Gram condition is never used.  Returns None at other points.
    """
    def f(ell, b):
        return endpoint_neg_e_closed(ell, b, delta, x, 1 - ell, c)
    A = f(Fr(0), Fr(0))
    A_ell = f(Fr(1), Fr(0)) - A
    A_b = f(Fr(0), Fr(1)) - A
    if A_b > 0:
        return None
    assert A_ell < 0
    ell_star = -A / A_ell
    return None if ell_star < 0 else Fr(11, 12) - ell_star / 4


ROBUST_WITNESS = (Fr(223, 576), Fr(1, 2))


def best_single_point_bound(n_delta: int = 240, xs=(Fr(1, 2),)) -> tuple:
    """Maximize the exact single-point bound over a rational grid of (delta, x)."""
    best = (Fr(0), None, None)
    for i in range(1, n_delta):
        delta = ALPHA * Fr(i, n_delta)
        for x in xs:
            s = single_point_bound(delta, x)
            if s is not None and s > best[0]:
                best = (s, delta, x)
    return best


def endpoint_min_float(ell, b, M=None, c=4 / 9, n_delta=1201, n_x=201, lam=1.0):
    """Float grid minimum of -E_* over 0 < delta < 5/6, 0 <= x <= 1/2 (a scan, not a bound).

    lam scales the row-count excess R_* - (1 - delta); lam = 0 is the ideal count 1 - delta.
    """
    import numpy as np
    M = 1 - ell if M is None else M
    alpha = 5 / 6
    ds = np.linspace(0, alpha, n_delta)[1:]
    xs = np.linspace(0, 0.5, n_x)
    D, X = np.meshgrid(ds, xs)
    Dx = 3 - (1 + 2 * c) * X
    Px = (2 - 2 * c * X) * (1 - X)
    J = (alpha - D) * Dx + D * Px
    h = 1 - (M - b) / 2 + ell
    c0v = 0.5 + ell / 2 - 0.75 * M + b / 6
    v = -c0v + D * (ell + b) / 2 - ell * X * D - lam * h / 2 * (alpha - D) * D * Px / J
    i = np.unravel_index(v.argmin(), v.shape)
    return float(v.min()), float(D[i]), float(X[i])


def endpoint_max_ell_float(b: float, c: float | None = 4 / 9, lam: float = 1.0) -> float:
    """Bisection on the float scan for the largest ell (M = 1 - ell) keeping min -E_* >= 0.

    c = None ties the capacity coefficient to the target, c = 1/(3(2 sigma_0 - 1)), which
    needs Lemma plain below kappa = 3/4 (stated only for kappa in [3/4, 1]).
    """
    lo, hi = 0.0, 0.3
    for _ in range(46):
        m = (lo + hi) / 2
        cc = c if c is not None else 1 / (3 * (2 * (11 / 12 - m / 4) - 1))
        if endpoint_min_float(m, b, c=cc, lam=lam)[0] >= 0:
            lo = m
        else:
            hi = m
    return lo


def excess_curve(lams=(1.0, 0.75, 0.5, 0.25, 0.0), bs=None) -> list[dict]:
    """Best target (M = 1 - ell, best b on a grid) when the row-count excess is scaled by lam.

    Along a line of constant target the slope 1 + delta(1/2 - x) does not involve the
    excess, so M = 1 - ell stays optimal for every lam.  A float scan, not a bound.
    """
    bs = bs if bs is not None else [k / 100 for k in range(0, 19)]
    out = []
    for lam in lams:
        best = None
        for b in bs:
            l = endpoint_max_ell_float(b, lam=lam)
            if best is None or l > best[0]:
                best = (l, b)
        out.append({"lam": lam, "ell": best[0], "b": best[1], "sigma0": 11 / 12 - best[0] / 4})
    return out


# --------------------------------------------------------------------- main

def main(argv=None) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--paper", type=Path, help="path to the pinned paper.tex, to check citations")
    ap.add_argument("--quick", action="store_true", help="skip the float scans")
    args = ap.parse_args(argv)

    reps = reproductions()
    bad = [r for r in reps if not r["ok"]]
    for r in reps:
        flag = "ok  " if r["ok"] else "FAIL"
        print(f"{flag} line {r['line']:>5}  {r['name']}: got {r['got']}, paper {r['want']}")
    print(f"{len(reps) - len(bad)}/{len(reps)} reproductions agree")

    cite_fail = None
    if args.paper:
        cite_fail = verify_citations(args.paper)
        print(f"citations: {len(CITATIONS) - len(cite_fail)}/{len(CITATIONS)} on their stated line",
              cite_fail or "")

    print("\nlow side: target = 5/6 + (M - 2 ell)/12")
    print("  paper corner M + ell = 1 and M - 2 ell = 1/2:",
          "ell = 1/6, M = 5/6, target", target(Fr(1, 6), B_PAPER, Fr(5, 6)))
    print("  per-summand lossless (M - 2 ell >= 1/2) forces target >= 7/8 for every geometry")

    fc = floor_corner()
    print(f"\nfloor-row corner: ell = {fc['ell']}, M = {fc['M']}, b = 0 -> target {fc['sigma0']}"
          f" (C_0 = {fc['C_0']}, dual slack {fc['dual_slack']}, d=0 slack {fc['d0_lossless_slack']})")

    rb = robust_single_point_bound(*ROBUST_WITNESS)
    print(f"\nendpoint inequality, exact bound for every geometry with M + ell <= 1, b >= 0:"
          f"\n  target >= {rb} = {float(rb):.7f} (witness delta = {ROBUST_WITNESS[0]}, x = 1/2)")
    sb, sd, sx = best_single_point_bound()
    print(f"  adding the Gram limit b <= 3(M - 2 ell)/8: target >= {sb} = {float(sb):.7f}"
          f" (witness delta = {sd}, x = {sx})")

    res = {
        "reproductions": reps,
        "citations_failed": cite_fail,
        "floor_corner": {k: str(v) for k, v in fc.items()},
        "robust_bound": {"sigma0": str(rb), "float": float(rb),
                         "delta": str(ROBUST_WITNESS[0]), "x": str(ROBUST_WITNESS[1])},
        "gram_limited_bound": {"sigma0": str(sb), "float": float(sb),
                               "delta": str(sd), "x": str(sx)},
    }
    if not args.quick:
        print("\nendpoint inequality, float scan (M = 1 - ell), largest ell with min -E_* >= 0:")
        scan = []
        for k in range(0, 19):
            b = k / 100
            l_fixed = endpoint_max_ell_float(b)
            l_tied = endpoint_max_ell_float(b, c=None)
            scan.append({"b": b, "ell_max_c_fixed": l_fixed, "sigma0_c_fixed": 11 / 12 - l_fixed / 4,
                         "ell_max_c_tied": l_tied, "sigma0_c_tied": 11 / 12 - l_tied / 4})
        for r in scan[::3]:
            print(f"  b = {r['b']:.2f}: c = 4/9 -> target {r['sigma0_c_fixed']:.6f};"
                  f"  c tied to target -> {r['sigma0_c_tied']:.6f}")
        bf = min(scan, key=lambda r: r["sigma0_c_fixed"])
        bt = min(scan, key=lambda r: r["sigma0_c_tied"])
        print(f"  best, c = 4/9: b = {bf['b']:.2f}, ell = {bf['ell_max_c_fixed']:.6f},"
              f" target {bf['sigma0_c_fixed']:.6f}")
        print(f"  best, c tied:  b = {bt['b']:.2f}, ell = {bt['ell_max_c_tied']:.6f},"
              f" target {bt['sigma0_c_tied']:.6f}")
        curve = excess_curve()
        print("\nrow-count excess scaled by lam (lam = 0: ideal count 1 - delta), best target:")
        for r in curve:
            print(f"  lam = {r['lam']:.2f}: ell = {r['ell']:.6f}, b = {r['b']:.2f}, target {r['sigma0']:.6f}")
        res["excess_curve"] = curve
        res["endpoint_scan"] = scan
        res["endpoint_best_c_fixed"] = bf
        res["endpoint_best_c_tied"] = bt

    (HERE / "results.json").write_text(json.dumps(res, indent=1) + "\n")
    return 1 if bad or cite_fail else 0


if __name__ == "__main__":
    sys.exit(main())

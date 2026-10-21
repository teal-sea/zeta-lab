"""Hunt #136, lane b78-amplification: what the sixth-power amplification slope is worth.

Input I2 of the Part II assembly is Lemma 17.6 of OpenAI's preprint (``Sixth-power
amplification``, paper.tex lines 12362 to 12389): for sixth-power-free rows of norm
about U and an inverse polynomial of length D = U^r,

    sum_u |M_u(U^r; W)|^2  <<  U^(e(r) + eps),     e(r) = max{1, (1 + 5r)/6},

used through the slope alpha = 5/6 (line 15101) in the long count
L(t) = 1 - delta + (alpha - delta)(t - 1) (line 15208).  Input I9 is the direct
estimate Z^(l_x/2 + b/12) (lines 8570, 8641 to 8642).

This module prices both inputs in exact arithmetic, in two comparison systems:

* system P, the pointwise-numerator assembly of the paper as re-read by hunt #134
  (endpoint ``-E_*`` of line 16019 with the geometry (ell, M, b) free), in three frames:
  ``P0`` hunt #134's own system, ``P1`` the paper's frozen side conditions as printed,
  ``P2`` the same with every bin ceiling at delta <= 3/4 (a second step from 7/8);
* system L, Liu's refined comparison system (arXiv:2610.26835v1, lines 9877 to 9998),
  reconstructed from its endpoint (lines 8987 to 8994) and checked against Liu's own
  critical polynomial cr(delta, kappa), his ell*(delta, kappa) and his kappa quartic.

The amplification law is generalised to e(r) = max{1, e0 + alpha r}.  The paper's
family is e0 = 1 - alpha (the slope alone moves); the raw-moment-threshold family is
e0 = 1/6, alpha = 5 theta/6 (sixth-power amplification fed by a mean square valid for
H >= D^theta; theta = 1 is the paper, theta = 99/100 is Guo's Hypothesis 11.1).

Grades (MISSION.md): every number this module returns is *derived* (exact rational or
quadratic-field arithmetic, or an exact root isolation) unless a function says
*measured* (float).  The lemmas behind the formulas are not checked here.

    .venv/bin/python hunts/below_seven_eighths/amplification/price.py            # report
    .venv/bin/python hunts/below_seven_eighths/amplification/price.py --sources  # + citations
"""
from __future__ import annotations

import argparse
import hashlib
import itertools
import math
import sys
from dataclasses import dataclass, field
from fractions import Fraction as Fr
from functools import lru_cache
from pathlib import Path

import numpy as np
import sympy as sp

HERE = Path(__file__).resolve().parent
CACHE = Path("/home/thomas/.cache/zeta-lab")
FOLLOW = CACHE / "followups" / "run-2026-10-21T1440Z"

# ------------------------------------------------------------------ sources

SOURCES = {
    "paper": (CACHE / "openai-math-adc7f124" / "paper.tex",
              "42a5ee0febca59fd1def55cfd6c6808c322ef4237d7726303ea52f711deac6a3"),
    "liu": (FOLLOW / "src_2610.26835v1" / "number_fields_v2.tex",
            "c55f17c6212777973adcdc06fea0f0cbfeae51c8ddada3b112f0981cde7a626f"),
    "guo11": (FOLLOW / "guo_zf" / "source" / "sections" / "11_limits.tex",
              "59442f55c72f7d5244afcb502134b20a6f6cb034da3ab1f3a872235b77772017"),
    "guo06": (FOLLOW / "guo_zf" / "source" / "sections" / "06_geometry.tex",
              "e81e698dadc6a190b2a32cd4bab09f90818c4e8da649b0877dcd729c4cffeb8a"),
    "guo05": (FOLLOW / "guo_zf" / "source" / "sections" / "05_count.tex",
              "579f88ecb740185d06642ba352941bb8a5ace9c0af0edddb17157485d1d6f6a8"),
    "by": (CACHE / "baier-young-0804.2233v3" / "cubicmeanvalues2008-09-01.tex",
           "0d36f78f30565c4756072eb19b7c0a3f91ed64d0971e9a5eff8e2599c2fc7aaa"),
}

#: key -> (source, line, verbatim snippet that must occur on that line)
CITATIONS = {
    # Lemma 17.6 and its inputs
    "raw_moment": ("paper", 12357, r"\ll_{c,\epsilon,W} H(HD)^\epsilon,\qquad H\ge D^{1+c}."),
    "H_P": ("paper", 12369, r"H=\max(2U,D^{1+c}),\qquad P=(H/U)^{1/6}."),
    "amplified_note": ("paper", 12375, r"\ll \max\{U,U^{1/6}D^{5(1+c)/6}\}(UD)^\epsilon."),
    "e_r": ("paper", 12383, r"e(r)=\max\{1,(1+5r)/6\}."),
    "amplifier_count": ("paper", 12411, r"primary ideals \(a\) with \(q_a\le P\)"),
    "sixth_power_invariance": ("paper", 12420, r"\psi_{ua^6}(m)=\psi_u(m)1_{(m,a)=1}."),
    "column_identity": ("paper", 12428, r"\mu(d)\psi_u(d)q_d^{-1/2}M_{ua^6}(D/q_d;W)."),
    "coefficient_mass": ("paper", 12430, r"The coefficient mass is at most \(d_{\mathcal O}(a)\ll_\delta P^\delta\)."),
    "injective_no_coprimality": ("paper", 12443, r"does not require \((u,a)=1\)."),
    "H_over_P": ("paper", 12449, r"=U^{1/6}H^{5/6}(UD)^\epsilon,"),
    "marked_conditions": ("paper", 9254, r"r+2z\le m-c_1,\qquad 2r+8z\le3m-c_2."),
    "marked_bound": ("paper", 9259, r"|M_u(Z^r;W)Q_u|^2\ll Z^{m+\epsilon}."),
    "M_u": ("paper", 5225, r"M_u(D;W)=D^{-1/2}\sum_n\mu(n)\nu(n)\chi_n(u)^{\varsigma}W(q_n/D)"),
    "sextic_large_sieve": ("paper", 4717, r"\bigl\{K+D+(KD)^{2/3}\bigr\}"),
    # its use in the row counts
    "alpha_def": ("paper", 15101, r"\alpha:=\frac56."),
    "R_short": ("paper", 15206, r"R_{\rm short}(t)=1-\delta+\frac{\delta P_x}{D_x}(3/2-t),"),
    "L_t": ("paper", 15208, r"L(t)=1-\delta+(\alpha-\delta)(t-1)."),
    "e_r_with_c": ("paper", 15274, r"\le e(r)+\frac{5cR_0}{6}+(1+R_0)\epsilon_0,"),
    "no_slot_inverse_count": ("paper", 15289, r"1-\alpha+(\alpha-\delta)r,&r\ge1."),
    "moment_exponent": ("paper", 15300, r"moment exponent \((1+5r)/6=1-\alpha+\alpha r\)."),
    "J_def": ("paper", 15963, r"\mathcal J=(\alpha-\delta)D_x+\delta P_x,\qquad"),
    "t_def": ("paper", 15964, r"t=1+\frac{\delta P_x}{2\mathcal J},\qquad"),
    "R_star": ("paper", 16019, r"From \(R_*=1-\delta+(\alpha-\delta)\delta P_x/(2\mathcal J)\)"),
    "E_d": ("paper", 15729, r"&=a-\frac78+h\left(\frac{17}{50}-\frac16\right)"),
    "C0": ("paper", 15734, r"\qquad C_0=-\frac1{48}."),
    "floor": ("paper", 15847, r"E(h)\le C_0+\frac34\delta_0=-\frac7{1200}<0."),
    "intermediate_R": ("paper", 16151, r"R=\frac{76}{75}-\frac23\delta."),
    "intermediate_E": ("paper", 16159, r"\le-\frac{529}{2400}+\frac{25}{96}\delta+O(\epsilon)"),
    "intermediate_ceiling": ("paper", 16165, r"the last inequality uses \(\delta\le5/6\)."),
    "bin_ceiling": ("paper", 15503, r"\delta=2a-1\le\kappa"),
    "direct_estimate": ("paper", 8570, r"\ll Z^{l_x/2+b/12+\epsilon}=Z^{3/16+\epsilon}."),
    "signal": ("paper", 8641, r"C_{\mathrm{II}}(s)=l_x/2+s-1+h/6=s-11/16,"),
    "signal_match": ("paper", 8642, r"C_{\mathrm{II}}(7/8)=3/16=l_x/2+b/12."),
    # Liu's refined system
    "liu_counts": ("liu", 8438, r"R=1-\delta+\frac{(5/6-\delta)\delta P}{2\mathcal J}."),
    "liu_amplification": ("liu", 8431, r"Lemma~\ref{v:lem:general-amplification}, followed by Markov's inequality"),
    "liu_geometry": ("liu", 8909, r"l_x=\frac{1-b-\ell}2,\quad l_y=\frac{1+b-\ell}2,\quad"),
    "liu_R_kappa": ("liu", 8950, r"R_\kappa(\delta,x)=1-\delta+\frac{(5/6-\delta)\delta P_\kappa}"),
    "liu_endpoint_x": ("liu", 8991, r"+\delta x\Bigl\{\ell+c_\kappa\Bigl(\frac h4-\frac{l_y}2\Bigr)\Bigr\}"),
    "liu_endpoint_R": ("liu", 8992, r"-\frac{3h}4\bigl(1-R_\kappa(\delta,x)\bigr),\\"),
    "liu_C0": ("liu", 8993, r"C_0=-\frac14+\frac b6+\frac{5\ell}4,"),
    "liu_small": ("liu", 8999, r"=C_0+\frac\delta2+\ell\delta x\Bigl(\frac12+\frac{2\ell}h\Bigr)"),
    "liu_admissible_1": ("liu", 9012, r"$B(\ell)>437/500$, $l_x>\ell$ and $l_y-\ell>11b/6$;"),
    "liu_admissible_2a": ("liu", 9013, r"\item $6\kappa\ell>3/4$, $\ell/h<1/(6\kappa)$,"),
    "liu_admissible_2b": ("liu", 9014, r"$\ell/h>21/100$ and $h/2<l_y<1/2$;"),
    "liu_ranges_1": ("liu", 9020, r"\max\{C_0,\,C_0+A_{\rm sm}/8\}<-1/250,\qquad"),
    "liu_ranges_2": ("liu", 9021, r"C_0+(1/2+3\ell/2)/50<-1/100,\\"),
    "liu_ranges_3": ("liu", 9022, r"13h/75-l_y/2+1/50<-1/20 ."),
    "liu_cr": ("liu", 9694, r"\mathrm{cr}(\delta,\kappa)&=(3-324\kappa^2)\delta^2+(756\kappa^2-54\kappa-5)\delta"),
    "liu_kappa_quartic": ("liu", 9721, r"16686\kappa_\flat^4-27405\kappa_\flat^3+9936\kappa_\flat^2+1290\kappa_\flat-275=0,\\"),
    "liu_B_quartic": ("liu", 8863, r"133488B_\flat^4-376596B_\flat^3+384534B_\flat^2-167541B_\flat+26231=0,"),
    "liu_scope": ("liu", 9991, r"sharper Gram or reflected-energy estimate, a smaller amplification"),
    "liu_F_prime": ("liu", 9968, r"$0<F_\flat'\le0.0065/4$ on $[\kappa_\flat,3/4]$ (proof of"),
    "liu_kappa_range": ("liu", 9011, r"\item $b>0$, $1/6\le\ell\le1/5$, $7497/10000\le\kappa\le3/4$,"),
    "liu_monotone_rows": ("liu", 9592, r"$d_{\min}\le d\le h+\zeta$ with the count $R_\kappa$ ($\mathscr L>21/100$)."),
    "quasi_rh_open": ("paper", 113, r"In particular, Theorem~\ref{thm:main} resolves the quasi-Riemann"),
    "liu_lambda": ("liu", 9763, r"$\lambda\ge1.068$,"),
    "guo_box_b": ("guo06", 5, r"\frac1{10}\le b\le\frac{13}{100},"),
    "supply": ("paper", 16116, r"\frac{\ell}{d}\ge\frac8{39}>\frac15>\frac7{37}."),
    "endpoint_bound": ("paper", 16000, r"-E_*\ge\frac{49}{440640}>\frac1{10000}."),
    "liu_one_eighth": ("liu", 9892, r"$\delta\ge1/8$ and normalized amplitude $x$, the numerator average of"),
    # Guo, section 11
    "guo_family": ("guo11", 33, r"proves the mean-square bound on the nonzero row ball for $H=D^{1+\vartheta}$, $0<\vartheta\le1/10$"),
    "guo_A_u": ("guo11", 35, r"A_u(D)&=\sum_{(n,S)=1}\mu(n)\nu(n)\chi_n(u)W(q_n/D),\notag\\"),
    "guo_M": ("guo11", 36, r"\mathcal M(D,H)&=\frac1D\sum_{u\in\OO}\Phi(q_u/H)|A_u(D)|^2.\label{eq:meanvaluefamily}"),
    "guo_hypothesis_bound": ("guo11", 43, r"\le C_{\nu,S,I,\Phi,\eps}\,H D^\eps\|W\|_{C^J(I)}^2"),
    "guo_hypothesis_range": ("guo11", 45, r"for all $D\ge2$, $D^{99/100}\le H\le D^{101/100}$"),
    "guo_conditional": ("guo11", 51, r"zero-free in $\Rea s>328/375$."),
    "guo_e99": ("guo11", 63, r"e_{99}(r)=\max\{1,\ 1/6+33r/40\}\qquad(D=U^r),"),
    "guo_long": ("guo11", 67, r"\max\{1-\delta,\ 1/6+(33/40-\delta)t\}+O(\eps)."),
    "guo_J99": ("guo11", 73, r"J_{99}=(33/40-\delta)D_x+\delta P_x,\quad"),
    "guo_t99": ("guo11", 74, r"t_{99}=1+\frac{D_x/120+\delta P_x/2}{J_{99}},\quad"),
    "guo_T99": ("guo11", 75, r"T_{99}=\frac{(97/120-\delta)\delta P_x}{2J_{99}}."),
    "guo_geometry": ("guo11", 81, r"\ell=21/125,\quad b=11/100,\quad"),
    "guo_identity": ("guo11", 86, r"20000(-108J_{99}E_{99})={}&526080\delta^2-406288\delta+79365\\"),
    "guo_square_1": ("guo11", 92, r"4(526080)(79365-900)-406288^2&=45529856>0,\\"),
    "guo_bound": ("guo11", 98, r"E_{99}\le-7/42768<0."),
    "guo_box": ("guo06", 4, r"\frac16\le\ell\le\frac{17}{100},\qquad"),
    "guo_endpoint": ("guo06", 15, r"E_g(\delta,x)=-1/4+b/6+5\ell/4-b\delta/2"),
    "guo_criterion": ("guo06", 22, r"E_g(\delta,x)\le0\qquad(0\le\delta\le3/4,\ 0\le x\le1/2),"),
    "guo_long_paper": ("guo05", 32, r"L(t)&=1-\delta+(5/6-\delta)(t-1).\label{eq:longcount}"),
    # Baier and Young 2010 (arXiv:0804.2233v3)
    "by_cubic_bound": ("by", 171, r"\min\left\{Q^{5/3}+M,Q^{4/3}+Q^{1/2}M,Q^{11/9}+Q^{2/3}M, Q+Q^{1/3}M^{5/3}+M^{12/5}\right\}"),
    "by_sextic": ("by", 205, r"remain valid when the condition $\chi^3=\chi_0$ is replaced by the weaker condition $\chi^6=\chi_0$."),
    "by_heath_brown_cubic": ("by", 195, r"\ll (M + N + (MN)^{2/3})(MN)^{\varepsilon} \sum_{m \leq M} |a_m|^2,"),
}


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def verify_sources() -> dict:
    """SHA-256 of every source file against its pin (measured)."""
    out = {}
    for key, (path, want) in SOURCES.items():
        out[key] = path.is_file() and sha256(path) == want
    return out


def verify_citations() -> list[str]:
    """Citation keys whose snippet is not on its stated line (empty list = all present)."""
    lines = {}
    bad = []
    for key, (src, n, snip) in CITATIONS.items():
        if src not in lines:
            path, want = SOURCES[src]
            raw = path.read_bytes()
            if hashlib.sha256(raw).hexdigest() != want:
                return [f"<{src}: sha256 mismatch>"]
            lines[src] = raw.decode("utf-8").splitlines()
        if snip not in lines[src][n - 1]:
            bad.append(key)
    return bad


# ----------------------------------------------------- quadratic-field numbers

def _squarefree_split(n: int, bound: int = 20000) -> tuple[int, int]:
    """n = k^2 m, square factors removed for primes below ``bound`` (and m = 1 when n
    is a perfect square); m need not be squarefree for large n, which only affects
    how a field is labelled, never the arithmetic.  n > 0."""
    s = math.isqrt(n)
    if s * s == n:
        return s, 1
    k, m, p = 1, n, 2
    while p < bound and p * p <= m:
        while m % (p * p) == 0:
            m //= p * p
            k *= p
        p += 1 if p == 2 else 2
    s = math.isqrt(m)
    if s * s == m:
        return k * s, 1
    return k, m


class Quad:
    """Exact numbers p + q sqrt(n) with rational p, q and squarefree integer n > 1."""

    __slots__ = ("p", "q", "n")

    def __init__(self, p, q=0, n=1):
        self.p, self.q, self.n = Fr(p), Fr(q), int(n)
        if self.n == 1:
            self.p, self.q = self.p + self.q, Fr(0)

    @staticmethod
    def sqrt(r) -> "Quad":
        """sqrt of a nonnegative rational, exactly."""
        r = Fr(r)
        assert r >= 0
        if r == 0:
            return Quad(0)
        num, den = r.numerator, r.denominator
        k1, m1 = _squarefree_split(num * den)
        # sqrt(num/den) = sqrt(num*den)/den = k1 sqrt(m1)/den
        if m1 == 1:
            return Quad(Fr(k1, den))
        return Quad(0, Fr(k1, den), m1)

    def _coerce(self, o):
        if isinstance(o, Quad):
            if o.n != 1 and self.n != 1:
                assert o.n == self.n, "mixed quadratic fields"
            return o
        return Quad(o)

    def _field(self, o):
        return self.n if self.n != 1 else o.n

    def __add__(self, o):
        o = self._coerce(o)
        return Quad(self.p + o.p, self.q + o.q, self._field(o))

    __radd__ = __add__

    def __neg__(self):
        return Quad(-self.p, -self.q, self.n)

    def __sub__(self, o):
        return self + (-self._coerce(o))

    def __rsub__(self, o):
        return self._coerce(o) - self

    def __mul__(self, o):
        o = self._coerce(o)
        n = self._field(o)
        return Quad(self.p * o.p + self.q * o.q * n, self.p * o.q + self.q * o.p, n)

    __rmul__ = __mul__

    def conj(self):
        return Quad(self.p, -self.q, self.n)

    def norm(self) -> Fr:
        return self.p * self.p - self.q * self.q * self.n

    def __truediv__(self, o):
        o = self._coerce(o)
        nrm = o.norm()
        assert nrm != 0
        num = self * o.conj()
        n = self._field(o)
        return Quad(num.p / nrm, num.q / nrm, n)

    def __rtruediv__(self, o):
        return self._coerce(o) / self

    def sign(self) -> int:
        p, q, n = self.p, self.q, self.n
        if q == 0:
            return (p > 0) - (p < 0)
        if p >= 0 and q >= 0:
            return 1 if (p > 0 or q > 0) else 0
        if p <= 0 and q <= 0:
            return -1
        # opposite signs: compare p^2 with q^2 n
        big = p * p - q * q * n
        if p > 0:
            return (big > 0) - (big < 0)
        return (big < 0) - (big > 0)

    def __abs__(self):
        return self if self.sign() >= 0 else -self

    def __lt__(self, o):
        return (self - o).sign() < 0

    def __le__(self, o):
        return (self - o).sign() <= 0

    def __gt__(self, o):
        return (self - o).sign() > 0

    def __ge__(self, o):
        return (self - o).sign() >= 0

    def __eq__(self, o):
        try:
            return (self - o).sign() == 0
        except AssertionError:
            return False

    def __hash__(self):
        return hash((self.p, self.q, self.n))

    def __float__(self):
        return float(self.p) + float(self.q) * math.sqrt(self.n)

    def mp(self, dps: int = 40):
        """High-precision decimal value (measured display of an exact number)."""
        import mpmath
        with mpmath.workdps(dps):
            return mpmath.mpf(self.p.numerator) / self.p.denominator + \
                mpmath.mpf(self.q.numerator) / self.q.denominator * mpmath.sqrt(self.n)

    def bracket(self, digits: int = 30) -> tuple[Fr, Fr]:
        """Rational lo < self < hi of width 2 x 10^-digits (exact)."""
        import mpmath
        scale = 10 ** digits
        with mpmath.workdps(digits + 30):
            guess = Fr(int(mpmath.floor(self.mp(digits + 30) * scale)), scale)
        lo, hi = guess - Fr(1, scale), guess + Fr(1, scale)
        assert Quad(lo) <= self <= Quad(hi)
        return lo, hi

    def __repr__(self):
        if self.q == 0:
            return f"{self.p}"
        return f"{self.p} + ({self.q}) sqrt({self.n})"

    def sympy(self):
        return sp.Rational(self.p.numerator, self.p.denominator) + \
            sp.Rational(self.q.numerator, self.q.denominator) * sp.sqrt(self.n)


def quad_roots(a, b, c) -> list[Quad]:
    """Real roots of a x^2 + b x + c (rational coefficients), smaller first."""
    a, b, c = Fr(a), Fr(b), Fr(c)
    if a == 0:
        return [Quad(-c / b)]
    disc = b * b - 4 * a * c
    if disc < 0:
        return []
    s = Quad.sqrt(disc)
    r1 = (Quad(-b) - s) / (2 * a)
    r2 = (Quad(-b) + s) / (2 * a)
    return sorted([r1, r2], key=float)


# ------------------------------------------------------------- the counts

@dataclass(frozen=True)
class Law:
    """Amplified exponent e(r) = max{1, e0 + alpha r} for r >= 1 (kink at r >= 1)."""

    alpha: Fr
    e0: Fr

    @staticmethod
    def slope(alpha) -> "Law":
        """The paper's form e(r) = max{1, 1 - alpha + alpha r} (line 15300)."""
        alpha = Fr(alpha)
        return Law(alpha, 1 - alpha)

    @staticmethod
    def threshold(theta) -> "Law":
        """Sixth-power amplification fed by a mean square valid for H >= D^theta."""
        theta = Fr(theta)
        return Law(Fr(5, 6) * theta, Fr(1, 6))

    @property
    def delta_e(self) -> Fr:
        """Bins with delta >= delta_e have the ideal count 1 - delta."""
        return 3 * self.alpha + 2 * self.e0 - 2

    def e(self, r):
        return max(Fr(1), self.e0 + self.alpha * Fr(r))

    def check(self):
        assert self.alpha >= 0 and self.e0 + self.alpha <= 1, "kink below r = 1 not supported"
        return self


PAPER_LAW = Law.slope(Fr(5, 6))
GUO_LAW = Law.threshold(Fr(99, 100))
C_PAPER = Fr(4, 9)          # 1/(3 kappa_0) at kappa_0 = 3/4 (hunt #134)


def counts(x, c):
    """D_x = 3 - (1 + 2c) x, P_x = (2 - 2c x)(1 - x) (paper line 15192 at c = 4/9)."""
    return 3 - (1 + 2 * c) * x, (2 - 2 * c * x) * (1 - x)


def excess(delta, x, law: Law, c):
    """X = R_* - (1 - delta): the row count's excess over the ideal 1 - delta.

    R_* = min over t in [1, 3/2] of max{R_short(t), L(t)}, with
    L(t) = max{1 - delta, e0 + (alpha - delta) t}.  For the paper's law this is
    (alpha - delta) delta P_x / (2 J) of line 16019.
    """
    de = law.delta_e
    if delta >= de:
        return delta * 0
    D, P = counts(x, c)
    J = (law.alpha - delta) * D + delta * P
    return delta * P * (de - delta) / (2 * J)


def rstar_bruteforce(delta, x, law: Law, c) -> Fr:
    """R_* by direct minimisation over t (exact; a control for ``excess``)."""
    delta, x = Fr(delta), Fr(x)
    D, P = counts(x, c)

    def rshort(t):
        return 1 - delta + delta * P / D * (Fr(3, 2) - t)

    def longc(t):
        # max over r in [1, t] of e(r) - delta r: endpoints of the two branches
        cands = [law.e(1) - delta, law.e(t) - delta * t]
        kink = (1 - law.e0) / law.alpha if law.alpha else None
        if kink is not None and 1 <= kink <= t:
            cands.append(law.e(kink) - delta * kink)
        return max(cands)

    ts = {Fr(1), Fr(3, 2)}
    # crossings of R_short with 1 - delta (never inside) and with e0 + (alpha - delta) t
    slope = law.alpha - delta
    denom = slope + delta * P / D
    if denom != 0:
        t = (1 - delta + delta * P / D * Fr(3, 2) - law.e0) / denom
        if 1 <= t <= Fr(3, 2):
            ts.add(t)
    return min(max(rshort(t), longc(t)) for t in ts)


# ------------------------------------------- the exact rectangle decision

def _poly(coeffs) -> sp.Poly:
    x = sp.Symbol("x")
    return sp.Poly([sp.Rational(c.numerator, c.denominator) for c in reversed(coeffs)], x, domain="QQ")


def _pmul(a, b):
    out = [Fr(0)] * (len(a) + len(b) - 1)
    for i, u in enumerate(a):
        for j, v in enumerate(b):
            out[i + j] += u * v
    return out


def _padd(*ps):
    n = max(len(p) for p in ps)
    out = [Fr(0)] * n
    for p in ps:
        for i, v in enumerate(p):
            out[i] += v
    return out


def _pscale(p, s):
    return [v * s for v in p]


def _peval(p, x):
    acc = Fr(0)
    for v in reversed(p):
        acc = acc * x + v
    return acc


def _cells(polys, xa: Fr, xb: Fr) -> list[Fr]:
    """Rational sample points, one in every open cell of [xa, xb] cut by the real
    roots of the given polynomials (coefficient lists), plus the two ends."""
    # The two ends are made roots too, so that the pairwise disjoint isolating
    # intervals returned by sympy separate every open cell of [xa, xb]; the gap between
    # two consecutive intervals is a nonempty subset of one cell.
    prod = _poly([-xa, Fr(1)]) * _poly([-xb, Fr(1)])
    for p in polys:
        if all(v == 0 for v in p):
            continue
        P = _poly(p)
        if P.degree() <= 0:
            continue
        prod = prod * P
    sq = prod.sqf_part()

    def fr(v):
        v = sp.Rational(v)
        return Fr(int(v.p), int(v.q))

    def refine(iv):
        lo, hi = iv
        if lo == hi:
            return iv
        a, b = sq.refine_root(sp.Rational(lo.numerator, lo.denominator),
                              sp.Rational(hi.numerator, hi.denominator),
                              eps=sp.Rational((hi - lo).numerator, (hi - lo).denominator) / 64)
        return fr(a), fr(b)

    ivs = sorted((fr(lo), fr(hi)) for (lo, hi), _m in sq.intervals())
    for _ in range(200):
        bad = [i for i in range(len(ivs) - 1) if not ivs[i + 1][0] > ivs[i][1]]
        if not bad:
            break
        for i in bad:
            ivs[i], ivs[i + 1] = refine(ivs[i]), refine(ivs[i + 1])
        ivs.sort()
    else:
        raise RuntimeError("could not separate the isolating intervals")
    ia = next(i for i, (lo, hi) in enumerate(ivs) if lo <= xa <= hi)
    ib = next(i for i, (lo, hi) in enumerate(ivs) if lo <= xb <= hi)
    pts = {xa, xb}
    for i in range(ia, ib):
        pts.add((ivs[i][1] + ivs[i + 1][0]) / 2)
    return sorted(pts)


def _quad_coeffs(A0, A1c, A1x, w, law: Law, c, de):
    """Coefficient polynomials (in x) of N = 2J (A0 + delta A1(x)) - w delta P (de - delta)
    = a0(x) + a1(x) delta + a2(x) delta^2."""
    al = law.alpha
    Dp = [Fr(3), -(1 + 2 * c)]
    Pp = _pmul([Fr(2), -2 * c], [Fr(1), Fr(-1)])
    A1 = [A1c, A1x]
    PmD = _padd(Pp, _pscale(Dp, -1))
    a0 = _pscale(Dp, 2 * al * A0)
    a1 = _padd(_pscale(_pmul(Dp, A1), 2 * al), _pscale(PmD, 2 * A0), _pscale(Pp, -w * de))
    a2 = _padd(_pscale(_pmul(PmD, A1), 2), _pscale(Pp, w))
    return a0, a1, a2


def _penclose(p, x1, x2):
    """Exact rational enclosure of the polynomial p over [x1, x2] (interval Horner)."""
    lo = hi = Fr(0)
    for coef in reversed(p):
        cands = (lo * x1, lo * x2, hi * x1, hi * x2)
        lo, hi = min(cands) + coef, max(cands) + coef
    return lo, hi


def _qmin(c0, c1, c2, d1, d2):
    """Exact minimum of c2 t^2 + c1 t + c0 over [d1, d2]."""
    cands = [c0 + c1 * d1 + c2 * d1 * d1, c0 + c1 * d2 + c2 * d2 * d2]
    if c2 > 0:
        v = -c1 / (2 * c2)
        if d1 < v < d2:
            cands.append(c0 - c1 * c1 / (4 * c2))
    return min(cands)


def rectangle_min_ok(A0, A1c, A1x, w, law: Law, c, da, db, xa=Fr(0), xb=Fr(1, 2), margin=Fr(0),
                     max_depth: int = 90):
    """Exact decision of F(delta, x) >= margin on [da, db] x [xa, xb] (da >= 0), where

        F = A0 + delta (A1c + A1x x) - w X(delta, x),   w >= 0,

    and X is ``excess``.  For delta <= delta_e, F >= margin iff the quadratic-in-delta
    numerator N = 2J (F - margin) is >= 0 (J > 0).  The x-range is cut into rational
    boxes; on a box the coefficient polynomials of N are enclosed in exact rational
    intervals, and since delta >= 0 the quadratic with the lower ends is a lower bound
    whose exact minimum over [da, db] proves the box.  A box that is not proved is
    tested at its midpoint exactly (a negative value is a witness of failure) and
    split.  For delta >= delta_e, F is bilinear and its four corners decide.

    Returns (True, None) when proved, (False, (x, delta-range)) when a point with
    F < margin was found, and (False, "undecided") if the depth limit is hit (this is
    the only possible outcome when the minimum equals the margin exactly)."""
    A0, A1c, A1x, w = Fr(A0) - Fr(margin), Fr(A1c), Fr(A1x), Fr(w)
    da, db, xa, xb = Fr(da), Fr(db), Fr(xa), Fr(xb)
    assert da >= 0
    de = law.delta_e
    lo2 = max(da, de)
    if lo2 <= db:
        for dd in (lo2, db):
            for xx in (xa, xb):
                if A0 + dd * (A1c + A1x * xx) < 0:
                    return False, (xx, dd)
    hi1 = min(db, de)
    if da > hi1:
        return True, None
    a0, a1, a2 = _quad_coeffs(A0, A1c, A1x, w, law, c, de)
    stack = [(xa, xb, 0)]
    while stack:
        x1, x2, depth = stack.pop()
        l0, _ = _penclose(a0, x1, x2)
        l1, _ = _penclose(a1, x1, x2)
        l2, _ = _penclose(a2, x1, x2)
        if _qmin(l0, l1, l2, da, hi1) >= 0:
            continue
        xm = (x1 + x2) / 2
        for xs in (x1, xm, x2):
            if _qmin(_peval(a0, xs), _peval(a1, xs), _peval(a2, xs), da, hi1) < 0:
                return False, (xs, (da, hi1))
        if depth >= max_depth:
            return False, "undecided"
        stack.append((x1, xm, depth + 1))
        stack.append((xm, x2, depth + 1))
    return True, None


def rectangle_min_ok_cells(A0, A1c, A1x, w, law: Law, c, da, db, xa=Fr(0), xb=Fr(1, 2), margin=Fr(0)):
    """Second, independent exact decision of the same statement (slower, used as a
    control on small cases).  Decision of F(delta, x) >= margin on [da, db] x [xa, xb], where

        F = A0 + delta (A1c + A1x x) - w X(delta, x),   w >= 0,

    and X is ``excess``.  Returns (ok, worst_sample) where worst_sample is the
    smallest value met at the cell samples (exact, informative only).

    Method: for delta <= delta_e the numerator N = 2J (F - margin) is a quadratic in
    delta whose coefficients are polynomials in x; the minimum over delta is an endpoint
    value or (a0 - a1^2/(4 a2)); every sign change in x is a root of one of six
    polynomials, which are isolated exactly, and one rational point per cell decides
    the cell.  For delta >= delta_e, F is bilinear and its corners decide.
    """
    A0, A1c, A1x, w = Fr(A0) - Fr(margin), Fr(A1c), Fr(A1x), Fr(w)
    da, db, xa, xb = Fr(da), Fr(db), Fr(xa), Fr(xb)
    de = law.delta_e
    worst = None
    # region with X = 0
    lo2 = max(da, de)
    if lo2 <= db:
        for dd in (lo2, db):
            for xx in (xa, xb):
                v = A0 + dd * (A1c + A1x * xx)
                worst = v if worst is None or v < worst else worst
        if worst < 0:
            return False, worst
    hi1 = min(db, de)
    if da <= hi1:
        al = law.alpha
        Dp = [Fr(3), -(1 + 2 * c)]                       # D(x)
        Pp = _pmul([Fr(2), -2 * c], [Fr(1), Fr(-1)])     # P(x)
        A1 = [A1c, A1x]
        PmD = _padd(Pp, _pscale(Dp, -1))
        a0 = _pscale(Dp, 2 * al * A0)
        a1 = _padd(_pscale(_pmul(Dp, A1), 2 * al), _pscale(PmD, 2 * A0), _pscale(Pp, -w * de))
        a2 = _padd(_pscale(_pmul(PmD, A1), 2), _pscale(Pp, w))
        n1 = _padd(a0, _pscale(a1, da), _pscale(a2, da * da))
        n2 = _padd(a0, _pscale(a1, hi1), _pscale(a2, hi1 * hi1))
        q1 = _padd(a1, _pscale(a2, 2 * da))
        q2 = _padd(a1, _pscale(a2, 2 * hi1))
        disc = _padd(_pscale(_pmul(a2, a0), 4), _pscale(_pmul(a1, a1), -1))
        for xs in _cells([n1, n2, a2, q1, q2, disc], xa, xb):
            c0, c1, c2 = _peval(a0, xs), _peval(a1, xs), _peval(a2, xs)
            cands = [c0 + c1 * da + c2 * da * da, c0 + c1 * hi1 + c2 * hi1 * hi1]
            if c2 > 0:
                v = -c1 / (2 * c2)
                if da < v < hi1:
                    cands.append(c0 - c1 * c1 / (4 * c2))
            m = min(cands)
            # report in F units at this x: divide by 2 J at the minimising delta is not
            # needed for the sign; keep N's value (J > 0 on this region)
            worst = m if worst is None or m < worst else worst
            if m < 0:
                return False, m
    return True, worst


# ---------------------------------------------------------------- exact LP

def _solve_square(rows, rhs):
    """Exact Gaussian elimination; returns None if singular."""
    n = len(rows)
    M = [list(map(Fr, r)) + [Fr(b)] for r, b in zip(rows, rhs)]
    for col in range(n):
        piv = next((i for i in range(col, n) if M[i][col] != 0), None)
        if piv is None:
            return None
        M[col], M[piv] = M[piv], M[col]
        for i in range(n):
            if i != col and M[i][col] != 0:
                f = M[i][col] / M[col][col]
                M[i] = [a - f * b for a, b in zip(M[i], M[col])]
    return [M[i][n] / M[i][i] for i in range(n)]


def exact_lp_max(c, rows):
    """maximize c.z subject to a.z <= beta for every (a, beta) in rows, exactly.

    A float LP (HiGHS) proposes the active set; the optimum is then decided in exact
    rationals: a basis B with A_B z = beta_B, every row satisfied exactly, and dual
    weights y >= 0 with A_B^T y = c.  Returns (value, z, [(row index, weight)]).
    """
    from scipy.optimize import linprog
    k = len(c)
    A = np.array([[float(v) for v in a] for a, _ in rows])
    bvec = np.array([float(beta) for _, beta in rows])
    res = linprog(-np.array([float(v) for v in c]), A_ub=A, b_ub=bvec,
                  bounds=[(None, None)] * k, method="highs")
    if res.status != 0:
        raise RuntimeError(f"float LP status {res.status}: {res.message}")
    zf = res.x
    scale = np.maximum(1.0, np.abs(A).sum(axis=1))
    slack = (bvec - A @ zf) / scale
    order = list(np.argsort(slack))
    tried = set()
    for width in (k + 2, 8, 14, 24):
        cand = order[:width]
        for combo in itertools.combinations(cand, k):
            key = tuple(sorted(combo))
            if key in tried:
                continue
            tried.add(key)
            At = [[Fr(rows[i][0][j]) for i in combo] for j in range(k)]
            y = _solve_square(At, list(map(Fr, c)))
            if y is None or any(v < 0 for v in y):
                continue
            z = _solve_square([rows[i][0] for i in combo], [rows[i][1] for i in combo])
            if z is None:
                continue
            if any(sum(Fr(a_j) * z_j for a_j, z_j in zip(a, z)) > beta for a, beta in rows):
                continue
            val = sum(Fr(cj) * zj for cj, zj in zip(c, z))
            return val, z, [(i, yv) for i, yv in zip(combo, y) if yv != 0]
    raise RuntimeError("no exact optimal basis among the near-active rows")


def _affine(fn, k):
    """Coefficients (a, a0) of an affine function of k rationals: fn(z) = a.z + a0."""
    zero = [Fr(0)] * k
    a0 = fn(zero)
    a = []
    for j in range(k):
        e = list(zero)
        e[j] = Fr(1)
        a.append(fn(e) - a0)
    return a, a0


# ------------------------------------------------------------ system P

PAPER_GEOMETRY = (Fr(1, 6), Fr(5, 6), Fr(1, 8))   # (ell, M, b), lines 6860 to 6864


@dataclass
class SystemP:
    """The pointwise-numerator assembly, geometry z = (ell, M, b) free.

    frame "P0": hunt #134's system: endpoint on 0 <= delta <= 5/6 (the delta -> 0 end
                is the floor in the limit), M + ell <= 1, 2M >= 1 + 3 ell (total
                accounting of the row norm at d = 0, #134, inferred), 0 <= b and
                8b <= 3(M - 2 ell) (Gram), l_x > ell.
    frame "P1": the paper's side conditions as printed: endpoint on 1/50 <= delta <= 5/6,
                floor bin delta_0 = 1/50 with count 1 (line 15847), intermediate rows
                d <= 1/2 with R = 76/75 - 2 delta/3 for delta <= 5/6 (lines 16146 to 16165),
                prime supply ell/h > 7/37 and 5 ell > h (lines 16116 to 16126), small rows.
    frame "P2": P1 with every bin ceiling at delta <= 3/4 (bins of a step justified by
                beta_* <= 7/8, as Guo and Liu use them).
    """

    frame: str = "P0"
    law: Law = PAPER_LAW
    c: Fr = C_PAPER
    eta: Fr = Fr(0)        # improvement of the direct exponent l_x/2 + b/12

    k = 3

    @property
    def dmax(self) -> Fr:
        return Fr(3, 4) if self.frame == "P2" else Fr(5, 6)

    @property
    def dmin(self) -> Fr:
        return Fr(0) if self.frame == "P0" else Fr(1, 50)

    # geometry --------------------------------------------------------------
    @staticmethod
    def h(z):
        ell, M, b = z
        return 1 + ell - M / 2 + b / 2

    @staticmethod
    def l_y(z):
        return (z[1] + z[2]) / 2

    @staticmethod
    def l_x(z):
        return (z[1] - z[2]) / 2

    def target(self, z):
        """sigma_0 = 1 - h/6 + b/12 - eta = 5/6 + (M - 2 ell)/12 - eta."""
        ell, M, b = z
        return Fr(5, 6) + (M - 2 * ell) / 12 - self.eta

    def C0(self, z):
        """E(h) at delta = q = 0, R = 1 against the matched target (closed form)."""
        ell, M, b = z
        return Fr(1, 2) + ell / 2 - Fr(3, 4) * M + b / 6 + self.eta

    def E_general(self, z, d, delta, q, R, sigma0=None):
        """The paper's display (line 15729) with the geometry and sigma_0 left free."""
        ell, M, b = z
        if sigma0 is None:
            sigma0 = self.target(z)
        a = (1 + delta) / 2
        zc = Fr(17, 50)
        return (a - sigma0 + self.h(z) * (zc - Fr(1, 6)) - a * self.l_y(z) - (1 - a) * ell
                - (delta / 2 - q) * ell + d * (R + delta / 2 - zc))

    def negE(self, z, delta, x):
        """-E_* at d = h, q = x delta, R = 1 - delta + X (closed form of #134)."""
        ell, M, b = z
        X = excess(delta, x, self.law, self.c)
        return -self.C0(z) + delta * (ell + b) / 2 - ell * x * delta - self.h(z) * X

    # constraints ---------------------------------------------------------------
    def linear_constraints(self):
        """Named affine functions g with requirement g(z) >= 0 (strict ones flagged)."""
        cons = [
            ("dual length M + ell <= 1", lambda z: 1 - z[0] - z[1], False),
            ("row norm at d = 0: 2M >= 1 + 3 ell", lambda z: 2 * z[1] - 1 - 3 * z[0], False),
            ("b >= 0", lambda z: z[2], False),
            ("Gram: 8b <= 3(M - 2 ell)", lambda z: 3 * (z[1] - 2 * z[0]) - 8 * z[2], False),
            ("l_x > ell", lambda z: z[1] - z[2] - 2 * z[0], True),
        ]
        if self.frame in ("P1", "P2"):
            d0 = Fr(1, 50)
            dint = self.dmax
            cons += [
                ("floor bin delta_0 = 1/50",
                 lambda z: -(self.C0(z) + (1 + z[0] - z[1] / 2) * d0), False),
                ("intermediate rows at delta = 1/50",
                 lambda z: -(self.E_general(z, Fr(1, 2), d0, d0 / 2, Fr(76, 75) - Fr(2, 3) * d0)), False),
                (f"intermediate rows at delta = {dint}",
                 lambda z: -(self.E_general(z, Fr(1, 2), dint, dint / 2, Fr(76, 75) - Fr(2, 3) * dint)), False),
                ("supply: ell/h > 7/37", lambda z: 37 * z[0] - 7 * self.h(z), True),
                ("extension: 5 ell > h", lambda z: 5 * z[0] - self.h(z), True),
                ("small rows", lambda z: -(self.h(z) * (Fr(17, 50) - Fr(1, 6)) - self.l_y(z) / 2 + Fr(2, 100)), True),
            ]
        return cons

    def endpoint_regions(self):
        """(name, delta_lo, delta_hi) of the endpoint family."""
        return [("endpoint", self.dmin, self.dmax)]

    def endpoint_fn(self, region, delta, x):
        return lambda z: self.negE(z, delta, x)

    def rectangle_data(self, z, region):
        """(A0, A1c, A1x, w) with F = A0 + delta (A1c + A1x x) - w X = -E_*."""
        ell, M, b = z
        return -self.C0(z), (ell + b) / 2, -ell, self.h(z)

    # float evaluation for cut generation (measured) ------------------------------
    def F_float(self, z, region, D, X):
        ell, M, b = map(float, z)
        al, e0, c = float(self.law.alpha), float(self.law.e0), float(self.c)
        de = 3 * al + 2 * e0 - 2
        Dx = 3 - (1 + 2 * c) * X
        Px = (2 - 2 * c * X) * (1 - X)
        J = (al - D) * Dx + D * Px
        Xs = np.where(D < de, D * Px * (de - D) / (2 * J), 0.0)
        h = 1 + ell - M / 2 + b / 2
        C0 = 0.5 + ell / 2 - 0.75 * M + b / 6 + float(self.eta)
        return -C0 + D * (ell + b) / 2 - ell * X * D - h * Xs

    def objective(self):
        """maximize 2 ell - M  <=>  minimize the target."""
        return [Fr(2), Fr(-1), Fr(0)]

    def objective_to_target(self, val):
        return Fr(5, 6) - val / 12 - self.eta

    def shift(self, z, eps):
        """Move along the face M + ell = 1 towards smaller ell (restores the endpoint)."""
        return (z[0] - eps, z[1] + eps, z[2])

    def all_side_ok(self, z):
        return all((g(z) > 0) if strict else (g(z) >= 0) for _, g, strict in self.linear_constraints())


# ------------------------------------------------------------ system L

@dataclass
class SystemL:
    """Liu's refined comparison system (arXiv:2610.26835v1), z = (ell, b), M = 1 - ell.

    frame "L0": the endpoint E_{b,ell,kappa}(delta, x) <= -eta on 1/8 <= delta <= 3/4,
                0 <= x <= 1/2 (the system of Liu's optimality theorem; bins up to
                beta_* <= 7/8), with 0 <= b and ell <= 1/5.
    frame "L1": L0 with delta up to 5/6 (condition (3) as stated), the small-delta
                endpoint on 0 <= delta <= 1/8 (requires ell/h < 1/(6 kappa)), and the
                admissibility conditions (1), (2), (4) of Liu's Remark (lines 9010 to 9023)
                as side conditions.
    """

    frame: str = "L0"
    law: Law = PAPER_LAW
    kappa: Fr = Fr(3, 4)
    eta: Fr = Fr(0)

    k = 2

    @property
    def c(self) -> Fr:
        return 1 / (3 * self.kappa)

    @staticmethod
    def h(z):
        return (1 + z[1] + 3 * z[0]) / 2

    @staticmethod
    def l_y(z):
        return (1 + z[1] - z[0]) / 2

    @staticmethod
    def l_x(z):
        return (1 - z[1] - z[0]) / 2

    def target(self, z):
        return Fr(11, 12) - z[0] / 4 - self.eta

    def C0(self, z):
        return Fr(-1, 4) + z[1] / 6 + 5 * z[0] / 4

    def E(self, z, delta, x):
        """Liu's endpoint at d = h (line 8990), amplification law generalised, + eta."""
        ell, b = z
        X = excess(delta, x, self.law, self.c)
        h = self.h(z)
        return (self.C0(z) + delta / 2 + delta * x * (ell + self.c * (h / 4 - self.l_y(z) / 2))
                - Fr(3, 4) * h * (delta - X) + self.eta)

    def E_small(self, z, delta, x):
        """Liu's small-delta endpoint (line 8999), + eta; valid when ell/h < 1/(6 kappa)."""
        ell, b = z
        X = excess(delta, x, self.law, self.c)
        h = self.h(z)
        return (self.C0(z) + delta / 2 + ell * delta * x * (Fr(1, 2) + 2 * ell / h)
                - Fr(3, 4) * h * (delta - X) + self.eta)

    def linear_constraints(self):
        cons = [
            ("b >= 0", lambda z: z[1], False),
            ("ell <= 1/5", lambda z: Fr(1, 5) - z[0], False),
        ]
        if self.frame == "L1":
            k = self.kappa
            cons += [
                ("(1) b > 0", lambda z: z[1], True),
                ("(1) ell >= 1/6", lambda z: z[0] - Fr(1, 6), False),
                ("(1) B(ell) > 437/500", lambda z: Fr(11, 12) - z[0] / 4 - Fr(437, 500), True),
                ("(1) l_x > ell", lambda z: self.l_x(z) - z[0], True),
                ("(1) l_y - ell > 11b/6", lambda z: self.l_y(z) - z[0] - Fr(11, 6) * z[1], True),
                ("(2) 6 kappa ell > 3/4", lambda z: 6 * k * z[0] - Fr(3, 4), True),
                ("(2) ell/h < 1/(6 kappa)", lambda z: self.h(z) - 6 * k * z[0], True),
                ("(2) ell/h > 21/100", lambda z: 100 * z[0] - 21 * self.h(z), True),
                ("(2) h/2 < l_y", lambda z: self.l_y(z) - self.h(z) / 2, True),
                ("(2) l_y < 1/2", lambda z: Fr(1, 2) - self.l_y(z), True),
                ("(4) C0 + (1/2 + 3 ell/2)/50 < -1/100",
                 lambda z: Fr(-1, 100) - (self.C0(z) + self.eta + (Fr(1, 2) + Fr(3, 2) * z[0]) / 50), True),
                ("(4) 13h/75 - l_y/2 + 1/50 < -1/20",
                 lambda z: Fr(-1, 20) - (Fr(13, 75) * self.h(z) - self.l_y(z) / 2 + Fr(1, 50)), True),
                ("(4) C0 < -1/250", lambda z: Fr(-1, 250) - (self.C0(z) + self.eta), True),
            ]
        return cons

    def endpoint_regions(self):
        hi = Fr(5, 6) if self.frame == "L1" else Fr(3, 4)
        regs = [("endpoint", Fr(1, 8), hi)]
        if self.frame == "L1":
            regs.append(("small", Fr(0), Fr(1, 8)))
        return regs

    def endpoint_fn(self, region, delta, x):
        if region == "small":
            return lambda z: -self.E_small(z, delta, x)
        return lambda z: -self.E(z, delta, x)

    def rectangle_data(self, z, region):
        ell, b = z
        h = self.h(z)
        if region == "small":
            A1x = -ell * (Fr(1, 2) + 2 * ell / h)
        else:
            A1x = -(ell + self.c * (h / 4 - self.l_y(z) / 2))
        return -self.C0(z) - self.eta, -(Fr(1, 2) - Fr(3, 4) * h), A1x, Fr(3, 4) * h

    def F_float(self, z, region, D, X):
        ell, b = map(float, z)
        al, e0, c = float(self.law.alpha), float(self.law.e0), float(self.c)
        de = 3 * al + 2 * e0 - 2
        Dx = 3 - (1 + 2 * c) * X
        Px = (2 - 2 * c * X) * (1 - X)
        J = (al - D) * Dx + D * Px
        Xs = np.where(D < de, D * Px * (de - D) / (2 * J), 0.0)
        h = (1 + b + 3 * ell) / 2
        ly = (1 + b - ell) / 2
        C0 = -0.25 + b / 6 + 1.25 * ell
        if region == "small":
            mid = ell * X * (0.5 + 2 * ell / h)
        else:
            mid = X * (ell + c * (h / 4 - ly / 2))
        return -(C0 + D / 2 + D * mid - 0.75 * h * (D - Xs) + float(self.eta))

    def objective(self):
        return [Fr(1), Fr(0)]

    def objective_to_target(self, val):
        return Fr(11, 12) - val / 4 - self.eta

    def shift(self, z, eps):
        return (z[0] - eps, z[1])

    def admissibility(self, z) -> dict:
        """Liu's conditions (1), (2), (4) (lines 9010 to 9023), exact; eta added to the
        exponent conditions of (4)."""
        ell, b = z
        h, ly, lx = self.h(z), self.l_y(z), self.l_x(z)
        k = self.kappa
        C0 = self.C0(z) + self.eta
        A_sm = Fr(1, 2) + (ell / 2) * (Fr(1, 2) + 2 * ell / h) - h / 2
        B = self.target(z)
        return {
            "(1) b > 0": b > 0,
            "(1) 1/6 <= ell <= 1/5": Fr(1, 6) <= ell <= Fr(1, 5),
            "(1) 7497/10000 <= kappa <= 3/4": Fr(7497, 10000) <= k <= Fr(3, 4),
            "(1) B(ell) > 437/500": B > Fr(437, 500),
            "(1) l_x > ell": lx > ell,
            "(1) l_y - ell > 11b/6": ly - ell > Fr(11, 6) * b,
            "(2) 6 kappa ell > 3/4": 6 * k * ell > Fr(3, 4),
            "(2) ell/h < 1/(6 kappa)": ell / h < 1 / (6 * k),
            "(2) ell/h > 21/100": ell / h > Fr(21, 100),
            "(2) h/2 < l_y < 1/2": h / 2 < ly < Fr(1, 2),
            "(4) max{C0, C0 + A_sm/8} < -1/250": max(C0, C0 + A_sm / 8) < Fr(-1, 250),
            "(4) C0 + (1/2 + 3 ell/2)/50 < -1/100": C0 + (Fr(1, 2) + Fr(3, 2) * ell) / 50 < Fr(-1, 100),
            "(4) 13h/75 - l_y/2 + 1/50 < -1/20": Fr(13, 75) * h - ly / 2 + Fr(1, 50) < Fr(-1, 20),
        }

    def all_side_ok(self, z):
        ok = all((g(z) > 0) if strict else (g(z) >= 0) for _, g, strict in self.linear_constraints())
        if self.frame == "L1":
            ok = ok and all(self.admissibility(z).values())
        return ok


# ------------------------------------------------------- continuum checks

def feasible(system, z, margin=Fr(0)) -> tuple[bool, str]:
    """Exact decision: z satisfies every constraint of the system on the whole
    (delta, x) rectangle, with the endpoint margin given."""
    if not system.all_side_ok(z):
        bad = [name for name, g, strict in system.linear_constraints()
               if not ((g(z) > 0) if strict else (g(z) >= 0))]
        if isinstance(system, SystemL) and system.frame == "L1":
            bad += [k for k, v in system.admissibility(z).items() if not v]
        return False, "side: " + ", ".join(bad)
    if isinstance(system, SystemL) and system.frame == "L1":
        if not system.h(z) * 1 > 6 * system.kappa * z[0]:
            return False, "small-delta formula needs ell/h < 1/(6 kappa)"
    for name, lo, hi in system.endpoint_regions():
        A0, A1c, A1x, w = system.rectangle_data(z, name)
        law, c = system.law, system.c
        if isinstance(system, SystemP):
            A0 = A0  # eta already inside C0
        ok, _ = rectangle_min_ok(A0, A1c, A1x, w, law, c, lo, hi, margin=margin)
        if not ok:
            return False, f"{name} rectangle"
    return True, "ok"


def _most_violated(system, z, n_delta=700, n_x=41):
    """Float search for the smallest endpoint value at z (measured, cut generation)."""
    from scipy.optimize import minimize
    best = (math.inf, None, None, None)
    zf = tuple(float(v) for v in z)
    de = float(system.law.delta_e)
    for name, lo, hi in system.endpoint_regions():
        flo, fhi = float(lo), float(hi)
        ds = np.linspace(flo, fhi, n_delta)
        # geometric refinements next to the lower end and next to delta_e, where the
        # excess lives in a thin layer when alpha is small
        extra = [flo + (fhi - flo) * np.geomspace(1e-9, 1.0, 120)]
        if flo < de < fhi:
            extra.append(de - (de - flo) * np.geomspace(1e-9, 1.0, 120))
            extra.append(flo + de * np.geomspace(1e-9, 1.0, 120))
        ds = np.unique(np.clip(np.concatenate([ds] + extra), flo, fhi))
        xs = np.linspace(0.0, 0.5, n_x)
        Dg, Xg = np.meshgrid(ds, xs)
        F = system.F_float(zf, name, Dg, Xg)
        idx = np.argsort(F, axis=None)[:6]
        for flat in idx:
            i, j = np.unravel_index(flat, F.shape)
            x0 = np.array([Dg[i, j], Xg[i, j]])

            def fun(v, _name=name):
                return float(system.F_float(zf, _name, np.array(v[0]), np.array(v[1])))

            r = minimize(fun, x0, method="L-BFGS-B",
                         bounds=[(float(lo), float(hi)), (0.0, 0.5)])
            if r.fun < best[0]:
                best = (r.fun, name, r.x[0], r.x[1])
            if F[i, j] < best[0]:
                best = (F[i, j], name, Dg[i, j], Xg[i, j])
    return best


def _rat(v: float, lo: Fr, hi: Fr, den: int = 10 ** 12) -> Fr:
    r = Fr(v).limit_denominator(den)
    return min(max(r, lo), hi)


def initial_cuts(system):
    cuts = []
    for name, lo, hi in system.endpoint_regions():
        for i in range(0, 13):
            d = lo + (hi - lo) * Fr(i, 12)
            for x in (Fr(0), Fr(1, 4), Fr(1, 2)):
                cuts.append((name, d, x))
    return cuts


@dataclass
class Sandwich:
    lb: Fr                 # exact LP value on the cut set: a lower bound for the target
    ub: Fr                 # target of a geometry checked on the whole rectangle
    z_lb: tuple
    z_ub: tuple
    active: list = field(default_factory=list)
    cuts: list = field(default_factory=list)

    @property
    def width(self) -> Fr:
        return self.ub - self.lb


def sandwich(system, max_iter: int = 60, tol: float = 1e-14, extra_cuts=()) -> Sandwich:
    """Exact bracket of the best target of a system: cutting-plane exact LP (lower end)
    and an exactly checked geometry (upper end)."""
    cuts = initial_cuts(system) + list(extra_cuts)
    k = system.k
    for _ in range(max_iter):
        rows, names = [], []
        for name, g, _strict in system.linear_constraints():
            a, a0 = _affine(g, k)
            rows.append(([-v for v in a], a0))          # g >= 0  <=>  -a.z <= a0
            names.append(name)
        for reg, d, x in cuts:
            a, a0 = _affine(system.endpoint_fn(reg, d, x), k)
            rows.append(([-v for v in a], a0))
            names.append(f"{reg}@({d},{x})")
        val, z, active = exact_lp_max(system.objective(), rows)
        viol, reg, dv, xv = _most_violated(system, z)
        if viol >= -tol:
            break
        lo, hi = next((lo, hi) for n, lo, hi in system.endpoint_regions() if n == reg)
        cuts.append((reg, _rat(dv, lo, hi), _rat(xv, Fr(0), Fr(1, 2))))
    lb = system.objective_to_target(val)
    # upper end: round the LP optimum, then shift towards smaller ell until the exact
    # check on the whole rectangle passes
    zr = tuple(Fr(v).limit_denominator(10 ** 15) for v in z)
    eps = Fr(max(-viol, 0.0) * 8).limit_denominator(10 ** 18) + Fr(1, 10 ** 15)
    z_ub = None
    for _ in range(30):
        cand = tuple(Fr(v).limit_denominator(10 ** 16) for v in system.shift(zr, eps))
        ok, _why = feasible(system, cand)
        if ok:
            z_ub = cand
            break
        eps *= 4
    if z_ub is None:
        raise RuntimeError("could not find a checked geometry near the LP optimum")
    return Sandwich(lb, system.target(z_ub), tuple(z), tuple(z_ub),
                    [(names[i], w) for i, w in active], cuts)


# -------------------------------------------- regime A closed forms (system P)

@dataclass
class RegimeA:
    delta: Quad
    ell: Quad
    b: Quad
    target: Quad
    mu: Quad               # endpoint multiplier = shadow price of the endpoint
    d_eta: Quad            # d target / d eta (improvement of the direct exponent)
    d_alpha: Quad | None   # d target / d alpha along e0 = 1 - alpha
    d_theta: Quad | None   # d target / d theta along the threshold family
    notes: dict = field(default_factory=dict)


def _critical_P(law: Law, c):
    """Critical class of system P at x = 1/2: d(-E_*)/db = 0 <=> X(delta, 1/2) = delta - 1/3."""
    D, P = counts(Fr(1, 2), c)
    al, de = law.alpha, law.delta_e
    # delta P (de - delta) = 2 (delta - 1/3) ((al - delta) D + delta P)
    a = 3 * P - 2 * D
    bb = 2 * al * D + Fr(2, 3) * (D - P) - P * de
    cc = -Fr(2, 3) * al * D
    roots = [r for r in quad_roots(a, bb, cc) if Quad(Fr(1, 3)) < r < Quad(de)]
    assert len(roots) == 1, roots
    return roots[0], D, P


def regime_A_P(law: Law = PAPER_LAW, c=C_PAPER, eta=Fr(0)) -> RegimeA:
    """Closed form when only the endpoint at x = 1/2 binds (b interior, M + ell = 1)."""
    dlt, D, P = _critical_P(law, c)
    ell = (5 - 6 * dlt - 12 * eta) / (9 + 18 * dlt)
    T = Fr(11, 12) - ell / 4 - eta
    al, de = law.alpha, law.delta_e
    J = (al - dlt) * D + dlt * P
    X = dlt * P * (de - dlt) / (2 * J)
    # tangency in delta: dX/ddelta at x = 1/2
    num = P * (de - 2 * dlt) * J - dlt * P * (de - dlt) * (P - D)
    Xp = num / (2 * J * J)
    b = (1 + 3 * ell) * Xp / (1 - Xp)
    h = Fr(1, 2) + 3 * ell / 2 + b / 2
    mu = 1 / (3 + 6 * dlt)
    d_eta = mu - 1
    # dX/dalpha and dX/de0 at fixed delta
    dX_dal = dlt * P * (3 * J - (de - dlt) * D) / (2 * J * J)
    dX_de0 = dlt * P / J
    d_alpha = mu * h * (dX_dal - dX_de0)          # e0 = 1 - alpha
    d_theta = mu * h * Fr(5, 6) * dX_dal          # alpha = 5 theta / 6, e0 = 1/6
    notes = {
        "X_at_critical": X,
        "b_positive": b > 0,
        "gram_ok": 8 * b <= 3 * (1 - 3 * ell),
        "ell_le_one_fifth": ell <= Quad(Fr(1, 5)),
        "floor_slack": -(Fr(-1, 4) + 5 * ell / 4 + b / 6 + eta),   # -C0 on the face
    }
    return RegimeA(dlt, ell, b, T, mu, d_eta, d_alpha, d_theta, notes)


def alpha_needed_regime_A_P(level, c=C_PAPER) -> Fr:
    """Exact alpha (paper's law) at which the regime-A target of system P equals level.

    sigma = 11/12 - (5 - 6 d)/(36 (1 + 2 d)) gives d rationally, and the critical
    equation 48 d^2 - (90 alpha + 23) d + 37 alpha = 0 (at c = 4/9) is linear in alpha.
    Valid only where regime A holds (checked separately)."""
    level = Fr(level)
    k = 33 - 36 * level
    d = (5 - k) / (6 + 2 * k)
    D, P = counts(Fr(1, 2), c)
    # general: (3P - 2D) d^2 + (2 alpha D + 2(D - P)/3 - P(3 alpha + 2 e0 - 2)) d - 2 alpha D/3 = 0
    # with e0 = 1 - alpha: 3 alpha + 2 e0 - 2 = alpha
    # => alpha (2 D d - P d - 2 D/3) = -(3P - 2D) d^2 - 2 (D - P) d/3
    return (-(3 * P - 2 * D) * d * d - Fr(2, 3) * (D - P) * d) / (2 * D * d - P * d - Fr(2, 3) * D)


def theta_needed_regime_A_P(level, c=C_PAPER) -> Fr:
    """Exact raw-moment threshold theta (law alpha = 5 theta/6, e0 = 1/6) at which the
    regime-A target of system P equals level: the critical class is rational and the
    critical equation is linear in theta."""
    level = Fr(level)
    k = 33 - 36 * level
    d = (5 - k) / (6 + 2 * k)
    D, P = counts(Fr(1, 2), c)
    # d P (de - d) = 2 (d - 1/3) ((al - d) D + d P), al = 5 th/6, de = 5 th/2 - 5/3
    # theta-coefficient and constant of LHS - RHS
    lhs1, lhs0 = d * P * Fr(5, 2), d * P * (Fr(-5, 3) - d)
    rhs1, rhs0 = 2 * (d - Fr(1, 3)) * Fr(5, 6) * D, 2 * (d - Fr(1, 3)) * (-d * D + d * P)
    return (rhs0 - lhs0) / (lhs1 - rhs1)


def eta_needed_regime_A_P(level, law: Law = PAPER_LAW, c=C_PAPER) -> Quad:
    ra = regime_A_P(law, c)
    return (ra.target - Fr(level)) / (1 - ra.mu)


# -------------------------------------------- regime A closed forms (system L)

def _liu_parts(law: Law, kappa):
    c = 1 / (3 * Fr(kappa))
    D, P = counts(Fr(1, 2), c)
    return c, D, P


def _critical_L(law: Law, kappa):
    """Liu's critical class: dE/db = 0 at x = 1/2 <=> X = delta (1 + c/6) - 4/9."""
    c, D, P = _liu_parts(law, kappa)
    al, de = law.alpha, law.delta_e
    s = 1 + c / 6
    # delta P (de - delta) = 2 (s delta - 4/9) ((al - delta) D + delta P)
    a = -P - 2 * s * (P - D)
    bb = P * de - 2 * s * al * D + Fr(8, 9) * (P - D)
    cc = Fr(8, 9) * al * D
    roots = [r for r in quad_roots(a, bb, cc) if Quad(Fr(1, 8)) < r < Quad(de)]
    assert len(roots) == 1, roots
    return roots[0], c, D, P


def regime_A_L(law: Law = PAPER_LAW, kappa=Fr(3, 4), eta=Fr(0)) -> RegimeA:
    """Liu's tangent family at a fixed moment parameter kappa, amplification generalised.

    ell* = (5 - 6 d - 12 eta)/(9 + 6 d + 6 c d) at the critical class (b-free there)."""
    dlt, c, D, P = _critical_L(law, kappa)
    ell = (5 - 6 * dlt - 12 * eta) / (9 + 6 * dlt + 6 * c * dlt)
    T = Fr(11, 12) - ell / 4 - eta
    al, de = law.alpha, law.delta_e
    J = (al - dlt) * D + dlt * P
    num = P * (de - 2 * dlt) * J - dlt * P * (de - dlt) * (P - D)
    Xp = num / (2 * J * J)
    # dE/ddelta = 0 at x = 1/2:  1/2 + (1/2)(ell + c (5 ell - 1 - b)/8) - (3h/4)(1 - X') = 0
    # with h = (1 + b + 3 ell)/2  ->  linear in b
    # write E_delta = u0 + u1 b
    def Ed(bv):
        h = (1 + bv + 3 * ell) / 2
        return Fr(1, 2) + (ell + c * (5 * ell - 1 - bv) / 8) / 2 - Fr(3, 4) * h * (1 - Xp)
    u0 = Ed(Fr(0))
    u1 = Ed(Fr(1)) - u0
    b = -u0 / u1
    lam = Fr(3, 4) + dlt * (1 + c) / 2            # dE/dell at the critical class
    mu = 1 / (4 * lam)
    d_eta = mu - 1
    h = (1 + b + 3 * ell) / 2
    dX_dal = dlt * P * (3 * J - (de - dlt) * D) / (2 * J * J)
    dX_de0 = dlt * P / J
    d_alpha = mu * Fr(3, 4) * h * (dX_dal - dX_de0)
    d_theta = mu * Fr(3, 4) * h * Fr(5, 6) * dX_dal
    return RegimeA(dlt, ell, b, T, mu, d_eta, d_alpha, d_theta, {"lambda": lam})


def liu_ell_star_formula(delta, kappa):
    """Liu's own ell*(delta, kappa) (line 9696), for the reproduction check."""
    d, k = delta, kappa
    num = 324 * d * d * k * k - 72 * d * d * k + 3 * d * d - 684 * d * k * k + 126 * d * k - 5 * d + 450 * k * k - 60 * k
    den = 324 * d * d * k * k - 144 * d * d * k + 15 * d * d - 2340 * d * k * k + 450 * d * k - 25 * d + 2250 * k * k - 300 * k
    return num / den


def liu_cr(delta, kappa):
    d, k = delta, kappa
    return (3 - 324 * k * k) * d * d + (756 * k * k - 54 * k - 5) * d + 40 * k - 300 * k * k


# ------------------------------------------------ Liu's fixed point, exact

def _sym_liu_fixed_point_poly(law: Law, eta=Fr(0)):
    """Polynomial in kappa whose root is the fixed point kappa = 2 F(kappa) - 1 (sympy)."""
    d, k = sp.symbols("d k")
    al = sp.Rational(law.alpha.numerator, law.alpha.denominator)
    e0 = sp.Rational(law.e0.numerator, law.e0.denominator)
    et = sp.Rational(eta.numerator, eta.denominator)
    c = 1 / (3 * k)
    D = 3 - (1 + 2 * c) / 2
    P = (2 - c) / 2
    de = 3 * al + 2 * e0 - 2
    s = 1 + c / 6
    crit = sp.together(d * P * (de - d) - 2 * (s * d - sp.Rational(4, 9)) * ((al - d) * D + d * P))
    crit = sp.numer(crit)
    ell = (5 - 6 * d - 12 * et) / (9 + 6 * d + 6 * c * d)
    B = sp.Rational(11, 12) - ell / 4 - et
    fp = sp.numer(sp.together(B - (1 + k) / 2))
    res = sp.resultant(sp.Poly(sp.expand(crit), d), sp.Poly(sp.expand(fp), d))
    return sp.Poly(sp.factor(res), k)


def liu_tangent_mp(law: Law, kappa, eta=Fr(0), dps: int = 60) -> dict:
    """Liu's tangent family at a real kappa, in dps-digit arithmetic (the same closed
    form as ``regime_A_L``; used where kappa is irrational, e.g. the fixed point)."""
    import mpmath
    with mpmath.workdps(dps):
        F = lambda q: mpmath.mpf(q.numerator) / q.denominator if isinstance(q, Fr) else mpmath.mpf(q)
        k = kappa if not isinstance(kappa, Fr) else F(kappa)
        al, de, et = F(law.alpha), F(law.delta_e), F(eta)
        c = 1 / (3 * k)
        D = 3 - (1 + 2 * c) / 2
        P = (2 - c) / 2
        s = 1 + c / 6
        a = -P - 2 * s * (P - D)
        bb = P * de - 2 * s * al * D + mpmath.mpf(8) / 9 * (P - D)
        cc = mpmath.mpf(8) / 9 * al * D
        disc = bb * bb - 4 * a * cc
        roots = sorted([(-bb - mpmath.sqrt(disc)) / (2 * a), (-bb + mpmath.sqrt(disc)) / (2 * a)])
        dlt = [r for r in roots if mpmath.mpf(1) / 8 < r < de][0]
        ell = (5 - 6 * dlt - 12 * et) / (9 + 6 * dlt + 6 * c * dlt)
        T = mpmath.mpf(11) / 12 - ell / 4 - et
        J = (al - dlt) * D + dlt * P
        Xp = (P * (de - 2 * dlt) * J - dlt * P * (de - dlt) * (P - D)) / (2 * J * J)

        def Ed(bv):
            h = (1 + bv + 3 * ell) / 2
            return mpmath.mpf(1) / 2 + (ell + c * (5 * ell - 1 - bv) / 8) / 2 - mpmath.mpf(3) / 4 * h * (1 - Xp)
        u0 = Ed(0)
        u1 = Ed(1) - u0
        b = -u0 / u1
        lam = mpmath.mpf(3) / 4 + dlt * (1 + c) / 2
        mu = 1 / (4 * lam)
        h = (1 + b + 3 * ell) / 2
        dX_dal = dlt * P * (3 * J - (de - dlt) * D) / (2 * J * J)
        dX_de0 = dlt * P / J
        return {"delta": dlt, "ell": ell, "b": b, "target": T, "lambda": lam, "mu": mu,
                "d_eta": mu - 1, "d_alpha": mu * mpmath.mpf(3) / 4 * h * (dX_dal - dX_de0),
                "d_theta": mu * mpmath.mpf(3) / 4 * h * mpmath.mpf(5) / 6 * dX_dal, "h": h}


def liu_fixed_point(law: Law = PAPER_LAW, eta=Fr(0), digits: int = 40):
    """Fixed point B = F(2B - 1) of Liu's tangent family (the chain limit), exactly:
    the relevant real root of an explicit polynomial, isolated in a rational interval
    of width 10^-digits, then B = (1 + kappa)/2.  Returns (kappa_lo, kappa_hi, factor)."""
    import mpmath
    poly = _sym_liu_fixed_point_poly(law, eta)
    k = poly.gens[0]
    best = None
    for fac, _m in sp.factor_list(poly.as_expr())[1]:
        fp = sp.Poly(fac, k)
        if fp.degree() < 1:
            continue
        for (lo, hi), _mm in fp.intervals(eps=sp.Rational(1, 10 ** digits)):
            lo, hi = sp.Rational(lo), sp.Rational(hi)
            mid = (lo + hi) / 2
            if not (sp.Rational(7, 10) <= mid <= sp.Rational(8, 10)):
                continue
            with mpmath.workdps(digits + 20):
                kv = mpmath.mpf(int(sp.numer(mid))) / int(sp.denom(mid))
                try:
                    tv = liu_tangent_mp(law, kv, eta, dps=digits + 20)["target"]
                except IndexError:
                    continue
                if abs(tv - (1 + kv) / 2) < mpmath.mpf(10) ** (-digits + 5):
                    best = (Fr(int(sp.numer(lo)), int(sp.denom(lo))),
                            Fr(int(sp.numer(hi)), int(sp.denom(hi))), fp)
    if best is None:
        raise RuntimeError("no fixed point found")
    return best


def liu_fixed_point_price(law: Law = PAPER_LAW, eta=Fr(0)) -> dict:
    """B, and dB/dalpha, dB/deta, dB/dtheta at the fixed point with the feedback through
    kappa = 2B - 1: dB/dp = F_p/(1 - 2 F_kappa).  kappa is an exactly isolated root; the
    derivatives are the closed-form envelope expressions evaluated in 60-digit
    arithmetic, F_kappa by a central difference of the closed form (step 1e-25)."""
    import mpmath
    klo, khi, fac = liu_fixed_point(law, eta)
    with mpmath.workdps(60):
        kap = (mpmath.mpf(klo.numerator) / klo.denominator + mpmath.mpf(khi.numerator) / khi.denominator) / 2
        tg = liu_tangent_mp(law, kap, eta)
        step = mpmath.mpf(10) ** -25
        Fk = (liu_tangent_mp(law, kap + step, eta)["target"] - liu_tangent_mp(law, kap - step, eta)["target"]) / (2 * step)
        fb = 1 / (1 - 2 * Fk)
        return {
            "kappa": (klo, khi),
            "B": ((1 + klo) / 2, (1 + khi) / 2),
            "factor": fac,
            "F_kappa": Fk,
            "d_alpha": tg["d_alpha"] * fb,
            "d_eta": tg["d_eta"] * fb,
            "d_theta": tg["d_theta"] * fb,
            "tangent": tg,
        }


def alpha_needed_liu_fixed_point(level) -> Fr:
    """Exact alpha (paper's law) at which Liu's fixed point equals level, in regime A.

    At the fixed point kappa = 2 level - 1, ell = 4(11/12 - level); the critical class
    is then rational, and the critical equation is linear in alpha."""
    level = Fr(level)
    kappa = 2 * level - 1
    c = 1 / (3 * kappa)
    D, P = counts(Fr(1, 2), c)
    ell = 4 * (Fr(11, 12) - level)
    d = (5 - 9 * ell) / (6 * (1 + ell + c * ell))
    Y = d * (1 + c / 6) - Fr(4, 9)
    # (alpha - d) d P = 2 Y ((alpha - d) D + d P)  ->  (alpha - d)(d P - 2 Y D) = 2 Y d P
    return d + 2 * Y * d * P / (d * P - 2 * Y * D)


def eta_needed_liu_fixed_point(level, law: Law = PAPER_LAW) -> Quad:
    """Improvement eta of the direct exponent at which Liu's fixed point equals level
    (regime A): kappa = 2 level - 1, delta_c(kappa) does not involve eta, and
    11/12 - ell*/4 - eta = level is linear in eta."""
    level = Fr(level)
    kappa = 2 * level - 1
    dlt, c, D, P = _critical_L(law, kappa)
    # 11/12 - (5 - 6 d - 12 eta)/(4 (9 + 6 d + 6 c d)) - eta = level
    g = 4 * (9 + 6 * dlt + 6 * c * dlt)
    # (11/12 - level) g - (5 - 6 d) = eta (g - 12)
    return ((Fr(11, 12) - level) * g - (5 - 6 * dlt)) / (g - 12)


def theta_needed_liu_fixed_point(level) -> Fr:
    """Raw-moment threshold theta at which Liu's fixed point equals level (regime A)."""
    level = Fr(level)
    kappa = 2 * level - 1
    c = 1 / (3 * kappa)
    D, P = counts(Fr(1, 2), c)
    ell = 4 * (Fr(11, 12) - level)
    d = (5 - 9 * ell) / (6 * (1 + ell + c * ell))
    Y = d * (1 + c / 6) - Fr(4, 9)
    # d P (de - d) = 2 Y ((al - d) D + d P), al = 5 th/6, de = 5 th/2 - 5/3
    lhs1, lhs0 = d * P * Fr(5, 2), d * P * (Fr(-5, 3) - d)
    rhs1, rhs0 = 2 * Y * Fr(5, 6) * D, 2 * Y * (-d * D + d * P)
    return (rhs0 - lhs0) / (lhs1 - rhs1)


def theta_crossover_bisect(frame="P0", lo=Fr(889, 1000), hi=Fr(9, 10), width=Fr(1, 10 ** 8)):
    """Rational bracket for the threshold theta at which the best target of system P
    meets the trivial route 1/2 + 5 theta/12 (amplification at U = 1).  Below the
    bracket the trivial route is smaller, above it the assembly is (exact sandwiches)."""
    lo, hi = Fr(lo), Fr(hi)

    def side(th):
        s = sandwich(SystemP(frame, Law.threshold(th)))
        triv = trivial_route_abscissa(th)
        if s.lb > triv:
            return "trivial"
        if s.ub < triv:
            return "assembly"
        raise RuntimeError("sandwich straddles the trivial route")
    assert side(lo) == "trivial" and side(hi) == "assembly"
    while hi - lo > width:
        mid = Fr((lo + hi) / 2).limit_denominator(10 ** 12)
        if side(mid) == "trivial":
            lo = mid
        else:
            hi = mid
    return lo, hi


def alpha_needed_bisect(make_system, level, lo, hi, width=Fr(1, 10 ** 9)):
    """Rational bracket [a_lo, a_hi] for sup{alpha : best target <= level}, by bisection
    on exact sandwiches.  The best target is nondecreasing in alpha (the excess X grows
    with alpha at every bin, dX/dalpha = (delta P)^2/(2 J^2) > 0), so
    ub(a_lo) <= level < lb(a_hi) brackets the crossing."""
    level, lo, hi = Fr(level), Fr(lo), Fr(hi)
    s_lo, s_hi = sandwich(make_system(lo)), sandwich(make_system(hi))
    assert s_lo.ub <= level < s_hi.lb, (float(s_lo.ub), float(s_hi.lb))
    while hi - lo > width:
        mid = (lo + hi) / 2
        mid = Fr(mid).limit_denominator(10 ** 15) if (hi - lo) > Fr(1, 10 ** 12) else mid
        s = sandwich(make_system(mid))
        if s.ub <= level:
            lo, s_lo = mid, s
        elif s.lb > level:
            hi, s_hi = mid, s
        else:
            raise RuntimeError("sandwich straddles the level; tighten it")
    return lo, hi, s_lo, s_hi


def alpha_needed_liu_one_step(level, kappa=Fr(3, 4)) -> Fr:
    """Alpha at which one refined step at fixed kappa reaches level (regime A)."""
    level = Fr(level)
    c = 1 / (3 * Fr(kappa))
    D, P = counts(Fr(1, 2), c)
    ell = 4 * (Fr(11, 12) - level)
    d = (5 - 9 * ell) / (6 * (1 + ell + c * ell))
    Y = d * (1 + c / 6) - Fr(4, 9)
    return d + 2 * Y * d * P / (d * P - 2 * Y * D)


# ----------------------------------------------------------- Guo's 328/375

GUO_ELL, GUO_B = Fr(21, 125), Fr(11, 100)


def guo_E99(delta, x, ell=GUO_ELL, b=GUO_B):
    """Guo's endpoint (06_geometry line 15) with T replaced by T_99 (line 75)."""
    h = (1 + b + 3 * ell) / 2
    T = excess(delta, x, GUO_LAW, C_PAPER)
    return Fr(-1, 4) + b / 6 + 5 * ell / 4 - b * delta / 2 - ell * (Fr(1, 2) - x) * delta + h * T


def guo_identity_holds(points=None) -> bool:
    """20000(-108 J99 E99) equals Guo's printed polynomial (line 86 to 89), exactly."""
    D99 = lambda x: counts(x, C_PAPER)
    pts = points or [(Fr(i, 17), Fr(j, 9)) for i in range(0, 13) for j in range(0, 5)]
    for dl, x in pts:
        D, P = D99(x)
        J = (Fr(33, 40) - dl) * D + dl * P
        y = Fr(1, 2) - x
        lhs = 20000 * (-108 * J * guo_E99(dl, x)) if dl < GUO_LAW.delta_e else None
        rhs = (526080 * dl ** 2 - 406288 * dl + 79365
               + y * (1292640 * dl ** 2 - 603308 * dl + 72930)
               + y ** 2 * (920640 * dl ** 2 - 19144 * dl) + 322560 * y ** 3 * dl ** 2)
        if lhs is not None and lhs != rhs:
            return False
    return True


GUO_SQUARES = (
    (4 * 526080 * (79365 - 900) - 406288 ** 2, 45529856),
    (4 * 1292640 * 72930 - 603308 ** 2, 13108397936),
    (4 * 920640 * 100 - 19144 ** 2, 1763264),
)


def guo_bound_holds() -> bool:
    """E99 <= -7/42768 on 0 <= delta <= 3/4, 0 <= x <= 1/2 (Guo, line 98), decided
    exactly by the rectangle procedure."""
    h = (1 + GUO_B + 3 * GUO_ELL) / 2
    A0 = -(Fr(-1, 4) + GUO_B / 6 + 5 * GUO_ELL / 4)
    A1c = GUO_B / 2 + GUO_ELL / 2
    A1x = -GUO_ELL
    ok, _ = rectangle_min_ok(A0, A1c, A1x, h, GUO_LAW, C_PAPER, Fr(0), Fr(3, 4), margin=Fr(7, 42768))
    return ok


# ------------------------------------------------- loss-map support

def amplification_maxplus(r, h0) -> tuple[Fr, Fr]:
    """The amplification step as a max-plus LP in exponents (base D).

    Unknown: f(v) = log_D of the mean-square mass of the sixth-power-free rows of norm
    D^v.  Inputs used by the proof: for every ball radius D^h with h >= h0,
    max_v [f(v) + (h - v)/6] <= h (raw moment over the ball, each row counted once per
    sixth power a with q_{u a^6} <= D^h).  Output: f(u) at u = 1/r, in base U.
    Returns (dual bound from the single constraint h = h0, value of the primal
    configuration that puts all mass on the rows of norm D^u), both in base U."""
    r, h0 = Fr(r), Fr(h0)
    u = 1 / r
    dual = (Fr(5, 6) * h0 + u / 6) / u
    f_u = Fr(5, 6) * h0 + u / 6
    # primal check on a grid of ball radii h >= h0: f(u) + (h - u)/6 <= h
    for i in range(0, 41):
        hh = h0 + Fr(i, 10)
        assert f_u + (hh - u) / 6 <= hh
    return dual, f_u / u


def amplified_exponent(r, law: Law = PAPER_LAW) -> Fr:
    return law.e(r)


def trivial_route_abscissa(theta) -> Fr:
    """Zero-free abscissa from the raw moment alone, rows u = units (U = 1):
    sum |M_u(D)|^2 << H/P = H^(5/6) with H = D^theta gives
    sum mu(n) nu(n) W(q_n/D) << D^(1/2 + 5 theta/12), i.e. no zero right of
    1/2 + 5 theta/12 for any fixed L(s, nu) (inferred step: Mellin inversion)."""
    return Fr(1, 2) + Fr(5, 12) * Fr(theta)


# Eisenstein integers a + b w, w^2 = -1 - w ----------------------------------------

def _e_mul(x, y):
    a, b = x
    c, d = y
    return (a * c - b * d, a * d + b * c - b * d)


def _e_norm(x):
    a, b = x
    return a * a - a * b + b * b


def _e_pow(x, n):
    out = (1, 0)
    for _ in range(n):
        out = _e_mul(out, x)
    return out


UNITS = [(1, 0), (0, 1), (-1, -1), (-1, 0), (0, -1), (1, 1)]


def split_primes(limit: int):
    """Rational primes p = 1 mod 3 below limit with a root r of r^2 + r + 1 mod p:
    the residue map a + b w -> a + b r mod p is the map O -> O/pi for a prime pi of
    norm p dividing w - r."""
    out = []
    for p in range(7, limit):
        if p % 3 != 1 or any(p % q == 0 for q in range(2, int(p ** 0.5) + 1)):
            continue
        r = next(t for t in range(2, p) if (t * t + t + 1) % p == 0)
        out.append((p, r))
    return out


def sextic_symbol_trivial(x, p, r) -> bool:
    """(x / pi)_6 == 1 for the prime pi | (p, w - r), x prime to pi (exact)."""
    a, b = x
    v = (a + b * r) % p
    if v == 0:
        return True
    return pow(v, (p - 1) // 6, p) == 1


def sixth_powers_up_to(max_norm: int) -> set:
    """Every y^6 with y in Z[w], 0 < N(y^6) <= max_norm (exact)."""
    out = set()
    R = int(math.isqrt(4 * int(round(max_norm ** (1 / 6))) // 3 + 4)) + 3
    for a in range(-R, R + 1):
        for b in range(-R, R + 1):
            y = (a, b)
            if 0 < _e_norm(y) ** 6 <= max_norm:
                out.add(_e_pow(y, 6))
    return out


def invariance_group_check(max_norm: int = 5000, prime_limit: int = 3000) -> dict:
    """Exact enumeration of the multipliers that leave every row character unchanged.

    For every nonzero b in Z[w] with N(b) <= max_norm: if b is a sixth power, then
    (b/pi)_6 = 1 for every split prime pi below prime_limit not dividing b; if not,
    some such prime has (b/pi)_6 != 1.  So, in this range, the b with
    chi_n(u b) = chi_n(u) for all n prime to b are exactly the sixth powers, which is
    the amplifier set of line 12420 (units change chi_n(u) by a fixed character of n of
    bounded conductor, so they are absorbed in nu, not counted as amplifiers)."""
    primes = split_primes(prime_limit)
    sixth = sixth_powers_up_to(max_norm)
    total, n_sixth, sixth_bad, missing = 0, 0, [], []
    R = int(math.isqrt(4 * max_norm // 3)) + 2
    for a in range(-R, R + 1):
        for b in range(-R, R + 1):
            n = _e_norm((a, b))
            if n == 0 or n > max_norm:
                continue
            total += 1
            x = (a, b)
            if x in sixth:
                n_sixth += 1
                if not all(n % p == 0 or sextic_symbol_trivial(x, p, r) for p, r in primes):
                    sixth_bad.append(x)
                continue
            if not any(n % p != 0 and not sextic_symbol_trivial(x, p, r) for p, r in primes):
                missing.append(x)
    return {"elements": total, "sixth_powers": n_sixth, "sixth_power_with_nontrivial_symbol": sixth_bad,
            "non_sixth_power_without_witness": missing}


def ideal_count_ratio(P: int) -> Fr:
    """#{nonzero ideals of Z[w] prime to 6 with norm <= P} / P (exact count)."""
    R = int(math.isqrt(4 * P // 3)) + 2
    cnt = 0
    for a in range(-R, R + 1):
        for b in range(-R, R + 1):
            n = _e_norm((a, b))
            if 0 < n <= P and n % 2 != 0 and n % 3 != 0:
                cnt += 1
    return Fr(cnt, 6 * P)


def duality_lower_bound(K: int, D: int) -> tuple[int, int]:
    """Any inequality sum_{q_k <= K} |sum_n c_n chi_n(k)|^2 <= Delta sum |c_n|^2 valid
    for all c has Delta >= #columns: the row k = 1 has chi_n(1) = 1 on every column n,
    so c_n = 1 gives |sum_n 1|^2 = N^2 = N sum |c_n|^2 from that row alone.
    Returns (number of squarefree ideals prime to 6 with norm <= D, K) for a small
    case: Delta >= N there, and N > K once D is a little larger than K (exact count)."""
    R = int(math.isqrt(4 * D // 3)) + 2
    norms = []
    for a in range(-R, R + 1):
        for b in range(-R, R + 1):
            n = _e_norm((a, b))
            if 0 < n <= D and n % 2 and n % 3:
                norms.append((a, b))
    # squarefree as ideals: no prime ideal squared divides; test via norm squarefreeness
    # of the split part is not enough, so test divisibility by squares of elements
    ideals = {min(_e_mul(u, x) for u in UNITS) for x in norms}
    small = [y for y in ideals]
    sq = set()
    for y in small:
        if _e_norm(y) * _e_norm(y) <= D:
            sq.add(_e_pow(y, 2))
    def divides(y, x):
        # y | x in Z[w]: x * conj(y) / N(y) integral; conj(a + b w) = (a - b) - b w
        a, b = y
        cy = (a - b, -b)
        num = _e_mul(x, cy)
        ny = _e_norm(y)
        return num[0] % ny == 0 and num[1] % ny == 0
    sqf = [x for x in ideals if not any(_e_norm(s) > 1 and divides(s, x) for s in sq)]
    return len(sqf), K


# rivals ---------------------------------------------------------------------------

def rival_Wa_diagonal(a: float, Dmax: int = 20000) -> float:
    """Measured: (1/D) sum_{n <= D} |mu_a(n)|^2 for the coefficients mu_a of
    1/(zeta(s + a) zeta(s - a)), divided by D^(2a)/log D (bounded below means the
    rival's diagonal grows like D^(2a)/log D, so no mean value of diagonal size holds
    for it)."""
    mu = [0] * (Dmax + 1)
    mu[1] = 1
    primes = []
    is_comp = [False] * (Dmax + 1)
    for i in range(2, Dmax + 1):
        if not is_comp[i]:
            primes.append(i)
            for j in range(i * i, Dmax + 1, i):
                is_comp[j] = True
    mu_a = np.zeros(Dmax + 1)
    mu_a[1] = 1.0
    # multiplicative: mu_a(p) = -(p^a + p^-a), mu_a(p^2) = 1, mu_a(p^k) = 0 for k >= 3
    spf = list(range(Dmax + 1))
    for p in primes:
        for j in range(p, Dmax + 1, p):
            if spf[j] == j:
                spf[j] = p
    for n in range(2, Dmax + 1):
        p = spf[n]
        m, e = n, 0
        while m % p == 0:
            m //= p
            e += 1
        loc = {1: -(p ** a + p ** (-a)), 2: 1.0}.get(e, 0.0)
        mu_a[n] = mu_a[m] * loc
    D = Dmax
    diag = float(np.sum(mu_a[1:D + 1] ** 2)) / D
    return diag / (D ** (2 * a) / math.log(D))


def epstein_multiplicativity_defect():
    """Exact: the Epstein coefficients a(n) = r_Q(n)/2 of Q = x^2 + xy + 4y^2
    (discriminant -15) are not multiplicative: a(6) != a(2) a(3)."""
    from zeta.epstein import epstein_representation_count
    Q = (1, 1, 4)
    a = {n: Fr(epstein_representation_count(n, Q), 2) for n in (1, 2, 3, 6)}
    return a


# ------------------------------------------------------------------- report

LEVEL_RECORD = Fr(8748087, 10 ** 7)        # tracker record, FOLLOWUPS.md section 1
LEVEL_XU_SANG = Fr(8748867, 10 ** 7)
LEVEL_13_15 = Fr(13, 15)

#: the alpha grid of the price curve and the frames it is computed in
CURVE_ALPHAS = (Fr(5, 6), Fr(41, 50), Fr(4, 5), Fr(3, 4), Fr(2, 3), Fr(1, 2), Fr(1, 3), Fr(1, 100), Fr(0))
CURVE_FRAMES = ("P0", "P1", "P2")
THETA_GRID = (Fr(1), Fr(99, 100), Fr(19, 20), Fr(9, 10), Fr(5, 6), Fr(3, 4), Fr(2, 3))

#: brackets found by bisection on exact sandwiches (rebuilt by ``brackets()``)
P1_ALPHA_RECORD = (Fr(336749397, 419430400), Fr(2155196141, 2684354560))
THETA_CROSS_P0 = (Fr(1866221727, 2097152000), Fr(933110869, 1048576000))
THETA_CROSS_P2 = (Fr(7496246491, 8388608000), Fr(937030819, 1048576000))


def d10(x, places: int = 10) -> str:
    """Display: an exact number (Fr, Quad, mpf) rounded half-even to ``places`` decimals."""
    import mpmath
    from decimal import Decimal, ROUND_HALF_EVEN
    with mpmath.workdps(60):
        if isinstance(x, Quad):
            v = x.mp(60)
        elif isinstance(x, Fr):
            v = mpmath.mpf(x.numerator) / x.denominator
        else:
            v = mpmath.mpf(x)
        s = mpmath.nstr(v, 45, min_fixed=-100, max_fixed=100)
    return str(Decimal(s).quantize(Decimal(1).scaleb(-places), rounding=ROUND_HALF_EVEN))


def headline_numbers() -> dict:
    """Every closed-form number quoted on LOSS_MAP.md and guo_h11.md (fast)."""
    L = LEVEL_RECORD
    out = {}
    ra = regime_A_P()
    out.update({"P_T": ra.target, "P_delta": ra.delta, "P_ell": ra.ell, "P_b": ra.b, "P_mu": ra.mu,
                "P_d_alpha": ra.d_alpha, "P_d_eta": ra.d_eta, "P_d_theta": ra.d_theta})
    out["P_alpha_record"] = alpha_needed_regime_A_P(L)
    out["P_alpha_xu_sang"] = alpha_needed_regime_A_P(LEVEL_XU_SANG)
    out["P_eta_record"] = eta_needed_regime_A_P(L)
    out["P_theta_record"] = theta_needed_regime_A_P(L)
    out["P_ratio_eta_alpha"] = ra.d_eta / ra.d_alpha
    rg = regime_A_P(GUO_LAW)
    out.update({"P_guo_T": rg.target, "P_guo_ell": rg.ell, "P_guo_b": rg.b})
    fp = liu_fixed_point_price()
    tg = fp["tangent"]
    out.update({"L_kappa": fp["kappa"][0], "L_B": fp["B"][0], "L_F_kappa": fp["F_kappa"],
                "L_d_alpha": fp["d_alpha"], "L_d_eta": fp["d_eta"], "L_d_theta": fp["d_theta"],
                "L_delta": tg["delta"], "L_ell": tg["ell"], "L_b": tg["b"], "L_lambda": tg["lambda"],
                "L_mu": tg["mu"]})
    r1 = regime_A_L(PAPER_LAW, Fr(3, 4))
    out.update({"L1step_T": r1.target, "L1step_d_alpha": r1.d_alpha, "L1step_d_eta": r1.d_eta})
    out["L_alpha_record"] = alpha_needed_liu_fixed_point(L)
    out["L_kappa_record"] = 2 * L - 1
    out["L_alpha_record_7497"] = alpha_needed_liu_one_step(L, Fr(7497, 10000))
    out["L_alpha_record_3_4"] = alpha_needed_liu_one_step(L, Fr(3, 4))
    out["L_eta_record"] = eta_needed_liu_fixed_point(L)
    out["L_theta_record"] = theta_needed_liu_fixed_point(L)
    fg = liu_fixed_point_price(GUO_LAW)
    out["L_guo_B"] = fg["B"][0]
    out["L_guo_kappa"] = fg["kappa"][0]
    return out


def curve() -> dict:
    """The price curve: exact sandwiches of the best target, frames x alpha grid."""
    return {(fr, al): sandwich(SystemP(fr, Law.slope(al))) for fr in CURVE_FRAMES for al in CURVE_ALPHAS}


def theta_curve() -> dict:
    out = {}
    for th in THETA_GRID:
        out[("P0", th)] = sandwich(SystemP("P0", Law.threshold(th)))
        out[("P2", th)] = sandwich(SystemP("P2", Law.threshold(th)))
    return out


def brackets() -> dict:
    """Rebuild the bisection brackets quoted as constants above (slow)."""
    lo, hi, _, _ = alpha_needed_bisect(lambda a: SystemP("P1", Law.slope(a)), LEVEL_RECORD,
                                       Fr(4, 5), Fr(41, 50), width=Fr(1, 10 ** 10))
    return {"P1_alpha_record": (lo, hi), "theta_cross_P0": theta_crossover_bisect("P0"),
            "theta_cross_P2": theta_crossover_bisect("P2", lo=Fr(889, 1000), hi=Fr(95, 100))}


def report(verbose: bool = True) -> dict:
    out = {}
    raP = regime_A_P()
    out["P_regimeA"] = raP
    raL = liu_fixed_point_price()
    out["L_fixed"] = raL
    out["alpha_P_record"] = alpha_needed_regime_A_P(LEVEL_RECORD)
    out["alpha_L_record"] = alpha_needed_liu_fixed_point(LEVEL_RECORD)
    out["alpha_L1_record"] = alpha_needed_liu_one_step(LEVEL_RECORD)
    out["alpha_P_13_15"] = alpha_needed_regime_A_P(LEVEL_13_15)
    if verbose:
        print("system P (hunt #134), paper's inputs, regime A:")
        print(f"  target {raP.target} = {float(raP.target):.10f}")
        print(f"  d target/d alpha = {raP.d_alpha} = {float(raP.d_alpha):.10f}")
        print(f"  d target/d eta   = {float(raP.d_eta):.10f}, d target/d theta = {float(raP.d_theta):.10f}")
        print(f"  alpha for {LEVEL_RECORD} in regime A: {out['alpha_P_record']} = {float(out['alpha_P_record']):.10f}")
        print("system L (Liu), fixed point:")
        print(f"  B in [{float(raL['B'][0]):.15f}, {float(raL['B'][1]):.15f}]")
        print(f"  dB/dalpha = {float(raL['d_alpha']):.10f}, dB/deta = {float(raL['d_eta']):.10f},"
              f" dB/dtheta = {float(raL['d_theta']):.10f}")
        print(f"  alpha for {LEVEL_RECORD}: {out['alpha_L_record']} = {float(out['alpha_L_record']):.10f}")
    return out


def main(argv=None) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--sources", action="store_true", help="check source hashes and citations")
    args = ap.parse_args(argv)
    if args.sources:
        print("sources:", verify_sources())
        bad = verify_citations()
        print(f"citations: {len(CITATIONS) - len(bad)}/{len(CITATIONS)} on their stated line", bad or "")
    report()
    return 0


if __name__ == "__main__":
    sys.exit(main())

"""Seam (i): the finite grid in LAW D units against the paper's asymptotic count.

WHAT THIS MODULE IS FOR.  `identification_seam.py` closes seam (ii) - the
band dual's cap IS the hypothesis D >= theta * R0 - on explicit truncated
grids in LAW D units (grid Z, mean zero gap 2 pi, normalisation 2 pi A per
unit vector).  The source paper's count lives in DIFFERENT units (hat units,
`Ghat = G/(a L^2)`, grid step h = 2 pi / L in the ordinate, window support
[-L/2, L/2]) and is asymptotic in T with named error terms.  This module is
the conversion: the dictionary, its derivation, its numerical checks, the
full list of error terms the extra census term must survive, and the height
at which it survives them.

THE DICTIONARY, DERIVED (never asserted).  Both sides are the same Poisson
identity read at two grid steps.

  * Their window (Theorem D, paper 7.1: "writing phi^2(u) = v(u/L)") is
    phi_T(u) = sqrt(v(u/L)) on |u| <= L/2 with v = v*_lam(s) = cos(sqrt2 lam s).
    Ours is phi(t) = sqrt(cos(sqrt2 t)) on |t| <= 1/2.  So phi_T(u) = phi(u/L)
    at lam = 1, and phihat_T(tau) = L * phihat(tau L).
  * Hence the ONLY change of variable in the whole transfer is

        x = tau * L                  (ordinate scaled by L)

    under which their grid tau_k = T + k*2pi/L becomes x_k = x_0 + 2 pi k:
    grid step 2 pi in x, where ours is 1.  In the same variable the mean zero
    gap is 2 pi L / ell1 = 2 pi lam1, so lam1 = L/ell1 (not lam) is the
    density parameter - which is why their ratio constant is cRatio(lam1;...).
  * Poisson at grid step h (supp phi = [-1/2,1/2], so supp phi*phi = [-1,1],
    and the aliasing points +-2pi/h fall outside it for every h <= 2 pi):

        sum_k phihat(x - k h) phihat(x' - k h) = (2 pi / h) * Phi2(x - x'),

    so at h = 1 the norm is 2 pi A (LAW D, `law_d_incidence.lean`) and at
    h = 2 pi it is A.  Their normalisation is
    sum_k phihat_T(gamma - tau_k)^2 = L^2 * A = a L^2 with a = A.
  * Therefore **a = a*(lam) and A = a*(1)**: our A IS their a at lam = 1, and
    the NORMALISED objects agree with conversion factor exactly 1,

        <u_i, u_j> = Phi2(x_i - x_j)/A = omega(x_i - x_j)      (either grid)

    because the (2 pi / h) cancels between the inner product and the
    normalisation.  P, Q, Ahat = P + Q, R, tr(PQ), ||Q||_F^2, D and the pair
    slack are built from unit vectors only, so each carries factor 1.  Only
    the raw (unnormalised) Gram carries a L^2/(2 pi A) = L^2/(2 pi).

  * Consequence, and the cleanest way to state the transfer: since
    ||P||_F^2 = sum_on m^2 + R exactly,

        D = ||Ahat||_F^2 - sum_{rho on-line} m_rho^2,

    so the hypothesis D >= theta R0 with R0 = 2 c_u N is, in their objects,
    their units, and with no reference to our grid,

        ||Ahat||_F^2  >=  sum_{rho in S1 u S2} m_rho^2  +  2 theta c_u N(I').

THE ERROR LIST.  The composed inequality is the paper's own endgame
(`ThmD/Endgame.lean:thmD_abstract` through `ThmD/AssemblyD.lean:N0star_lower_c`)
with one extra additive term:

    N0*(T,2T) >= (2 - cinv(T)) N + 2 theta c_u N - err(T),
    err = 4 R1 + R2 + 3 NII + B(4 + 2 sqrt(cinv N + R2) + B) + |cinv - c_inf| N.

Every term is enumerated and sized in `error_budget`.  The one that dominates
is NOT calE: it is the window-moment drift |cinv(T) - 1/cStar(lam)|, whose
constants ARE explicit upstream (|a_D - a*| <= 4w/L, |b_D - b*| <= 4w/L,
|J_D - J*| <= 16w/L, `ThmD/Window.lean`), and whose coefficient 35.519106 is
derived term by term in `drift_coefficient`.

THE CROSSOVER, stated plainly.  2 theta c_u = 9.99e-6 is a fixed constant and
every error term is o(1), so the extra term survives the composition as an
asymptotic statement; it is not drowned.  But it becomes numerically
effective only above l = log(T/2pi) ~ 3.9e6, i.e. T ~ 10^(1.7e6).  The
crossover is finite and astronomically far outside any range where anything
is computed, and it scales like 1/improvement, so a 1e-5 improvement costs a
height exponential in 1e5.  `crossover_l` computes it; `crossover_sensitivity`
reports what the one existential constant still does to it.

Nothing here is evidence about RH, and no proportion is claimed.

Run ``.venv/bin/python hunts/frontier_math/asymptotic_transfer.py`` (~60 s).
"""

from __future__ import annotations

import math
import sys
from dataclasses import dataclass
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
from cg_transplant import bucket_floor, g_kernel  # noqa: E402
from identification_seam import TWO_PI, GridAssembly, phihat  # noqa: E402
from lp_certificate import EDGES, FLOOR_SCIPY  # noqa: E402
from paper_chain import A, PaperChain, phipap  # noqa: E402
from reconnect import H_PINNED, THETA_FULL_MT  # noqa: E402

S2 = math.sqrt(2.0)

#: ell1 - l = 2 log 2 - 1  (paper Notation: N(T,2T) = T ell1 / 2pi + O(l)).
ELL1_OFFSET = 2 * math.log(2.0) - 1.0

#: the retention and the census floor behind the candidate reading.
THETA = THETA_FULL_MT          # 0.995
C_U = FLOOR_SCIPY              # 5.021179065914518e-06 (one-sided)

#: the additive census term: R0 = 2 c_u N (one-sided floor -> ordered pairs).
IMPROVEMENT = 2.0 * THETA * C_U

#: the source's own explicit window-moment closeness constants
#: (ThmD/Window.lean aD_close / bD_close / jD_close), valid when 8w <= L.
MOMENT_CONST = {"a": 4.0, "b": 4.0, "J": 16.0}


# ---------------------------------------------------------------------------
# 1. the scale-free window objects of the source paper's 7.1
# ---------------------------------------------------------------------------


def theta_of(lam: float) -> float:
    """vartheta := lam / sqrt2  ([eq:vstar])."""
    return lam / S2


def v_star(s, lam: float = 1.0):
    """v*_lam(s) = cos(sqrt2 lam s) on [-1/2, 1/2]  ([eq:vstar])."""
    return np.cos(S2 * lam * np.asarray(s, float))


def a_star(lam: float) -> float:
    """a* = int v*  =  sin(vartheta)/vartheta."""
    th = theta_of(lam)
    return math.sin(th) / th


def b_star(lam: float) -> float:
    """b* = int v*^2  =  1/2 + sin(2 vartheta)/(4 vartheta)."""
    th = theta_of(lam)
    return 0.5 + math.sin(2 * th) / (4 * th)


def j_star(lam: float) -> float:
    """J* = int int |s-s'| v* v'  =  sin(2th)/(8 th^3) - cos(2th)/(4 th^2)."""
    th = theta_of(lam)
    return math.sin(2 * th) / (8 * th**3) - math.cos(2 * th) / (4 * th**2)


def moments_by_quadrature(lam: float, n: int = 4001) -> dict:
    """The same three moments by quadrature: the control on the closed forms."""
    s = np.linspace(-0.5, 0.5, n)
    v = v_star(s, lam)
    d = np.abs(s[:, None] - s[None, :])
    return {
        "a": float(np.trapezoid(v, s)),
        "b": float(np.trapezoid(v * v, s)),
        "J": float(np.trapezoid(np.trapezoid(d * np.outer(v, v), s, axis=1), s)),
    }


def c_star(lam: float) -> float:
    """c*_lam = sqrt2 sin(th)/(cos(th) + th sin(th))  ([eq:vstar])."""
    th = theta_of(lam)
    return S2 * math.sin(th) / (math.cos(th) + th * math.sin(th))


def c_ratio(lam1: float, a: float, b: float, J: float) -> float:
    """cRatio(lam1; a, b, J) = lam1 a^2 / (b + lam1^2 J)  ([eq:ratio-general])."""
    return lam1 * a * a / (b + lam1 * lam1 * J)


def HD(lam: float) -> float:
    """The Theorem-D Thm-A-line constant 2 - 1/c*_lam."""
    return 2.0 - 1.0 / c_star(lam)


def HD_slope(lam: float = 1.0, h: float = 1e-6) -> float:
    """dHD/dlam by central difference: the price of the lam < 1 requirement."""
    return (HD(lam + h) - HD(lam - h)) / (2 * h)


# ---------------------------------------------------------------------------
# 2. the unit dictionary: derived constants and their numerical checks
# ---------------------------------------------------------------------------


def poisson_constant(h: float, lam: float = 1.0) -> float:
    """(2 pi / h) * int phi^2: the squared norm of the evaluation vector.

    h = 1 (our grid) gives 2 pi A; h = 2 pi (their grid, read in x = tau L)
    gives A, and their own constant a L^2 is L^2 times that.  One formula,
    two readings - that is the whole unit seam.
    """
    return (TWO_PI / h) * a_star(lam)


def a_vs_A() -> dict:
    """Their a = L^-1 int phi_T^2 against our A = Phi2(0) = int phi^2.

    phi_T(u) = sqrt(v*(u/L)) gives int phi_T^2 = L int v* = L a*(lam), so
    a = a*(lam); at lam = 1 that is exactly our A.  Closed form and
    quadrature are both computed; the identity is the defect column.
    """
    q = moments_by_quadrature(1.0)
    return {
        "A_paper_chain": A,
        "a_star_1_closed": a_star(1.0),
        "a_star_1_quad": q["a"],
        "closed_vs_A": abs(a_star(1.0) - A),
        "quad_vs_A": abs(q["a"] - A),
        "formula": "a = a*(lam) = sin(lam/sqrt2)/(lam/sqrt2);  A = a*(1)",
    }


def moment_closed_forms_vs_quadrature(lams=(1.0, 0.99, 0.9)) -> list:
    """a*, b*, J* two ways, and cRatio at the starred moments against c*."""
    rows = []
    for lam in lams:
        q = moments_by_quadrature(lam)
        a, b, J = a_star(lam), b_star(lam), j_star(lam)
        rows.append({"lam": lam, "a": a, "b": b, "J": J,
                     "a_defect": abs(a - q["a"]), "b_defect": abs(b - q["b"]),
                     "J_defect": abs(J - q["J"]),
                     "cRatio": c_ratio(lam, a, b, J), "cStar": c_star(lam),
                     "c_defect": abs(c_ratio(lam, a, b, J) - c_star(lam))})
    return rows


def grid_sum_ladder(x: float = 0.31, xp: float = 2.0, phase: float = 0.37,
                    Ks=(100, 200, 400, 800)) -> list:
    """Norm and Gram on the PAPER grid (step 2 pi in x) up a truncation ladder.

    The closed-form normalisation A is used, never the truncated norm, so the
    residual IS the truncation defect and must fall like 1/K.
    """
    rows = []
    om = float(phipap(complex(x - xp, 0)).real / A)
    for K in Ks:
        n = np.arange(-K, K + 1, 1.0) * TWO_PI + phase
        v1 = phihat(x - n).real / math.sqrt(A)
        v2 = phihat(xp - n).real / math.sqrt(A)
        rows.append({"K": K, "span": K * TWO_PI,
                     "unit_defect": abs(float(v1 @ v1) - 1.0),
                     "gram": float(v1 @ v2), "omega": om,
                     "gram_defect": abs(float(v1 @ v2) - om)})
    return rows


def grid_step_invariance(x: float = 0.31, xp: float = 2.0,
                         spans=(600.0, 1200.0, 2400.0),
                         steps=(1.0, math.pi, TWO_PI)) -> list:
    """The normalised Gram is grid-step independent, up to truncation.

    This is what makes a finite-grid identity in LAW D units a statement
    about their matrices.  Each step gets the Poisson constant belonging to
    it; the residual spread must fall like 1/span for every step.
    """
    om = float(phipap(complex(x - xp, 0)).real / A)
    rows = []
    for span in spans:
        row = {"span": span, "omega": om}
        for h in steps:
            K = int(span / h)
            n = np.arange(-K, K + 1, 1.0) * h + 0.37
            norm = math.sqrt(poisson_constant(h))
            v1 = phihat(x - n).real / norm
            v2 = phihat(xp - n).real / norm
            row[f"h={h:.4f}"] = {"gram": float(v1 @ v2),
                                 "unit_defect": abs(float(v1 @ v1) - 1.0),
                                 "gram_defect": abs(float(v1 @ v2) - om)}
        row["worst_defect"] = max(v["gram_defect"] for k, v in row.items()
                                  if isinstance(v, dict))
        rows.append(row)
    return rows


class PaperGridAssembly:
    """`identification_seam.GridAssembly` rebuilt on the PAPER's grid.

    Same configuration, same kernel, different grid: step 2 pi in x = tau L
    (theirs) instead of 1 (ours), with the Poisson constant belonging to that
    step (a = A, i.e. a L^2 after undoing x = tau L) instead of 2 pi A.  Every
    reported quantity is a hat-unit one, so the two assemblies must agree term
    by term with conversion factor 1.
    """

    def __init__(self, xs, ms, pairs, span: float = 1200.0,
                 phase: float = 0.37, lam: float = 1.0):
        self.xs = np.asarray(xs, float)
        self.ms = np.asarray(ms, float)
        self.pairs = list(pairs)
        self.h = TWO_PI
        K = int(span / self.h)
        n = np.arange(-K, K + 1, 1.0) * self.h + phase
        norm = math.sqrt(poisson_constant(self.h, lam))
        self.U = (np.array([phihat(x - n).real for x in self.xs]) / norm
                  if len(self.xs) else np.zeros((0, len(n))))
        self.Vx, self.Vy = [], []
        for t, y in self.pairs:
            v = phihat(complex(t, y) - n) / norm
            self.Vx.append(v.real)
            self.Vy.append(v.imag)

    def R(self) -> float:
        G = self.U @ self.U.T
        M = np.outer(self.ms, self.ms) * G ** 2
        return float(M.sum() - np.trace(M))

    def trPQ(self) -> float:
        out = 0.0
        for x, yv in zip(self.Vx, self.Vy):
            a = self.U @ x
            b = self.U @ yv
            out += float((self.ms * 2 * (a * a - b * b)).sum())
        return out

    def fro2_Q(self) -> float:
        tot = 0.0
        for p in range(len(self.pairs)):
            for q in range(len(self.pairs)):
                x1, y1 = self.Vx[p], self.Vy[p]
                x2, y2 = self.Vx[q], self.Vy[q]
                tot += 4 * ((x1 @ x2) ** 2 - (x1 @ y2) ** 2
                            - (y1 @ x2) ** 2 + (y1 @ y2) ** 2)
        return tot

    def trP(self) -> float:
        return float((self.ms * np.einsum("ij,ij->i", self.U, self.U)).sum())

    def D(self) -> float:
        return self.R() + 2 * self.trPQ() + self.fro2_Q()

    def fro2_Ahat_minus_msq(self) -> float:
        """||Ahat||_F^2 - sum_on m^2, which is D by the exact identity."""
        P = (self.U * self.ms[:, None]).T @ self.U
        Q = np.zeros_like(P)
        for x, yv in zip(self.Vx, self.Vy):
            Q = Q + 2 * (np.outer(x, x) - np.outer(yv, yv))
        Ah = P + Q
        return float((Ah * Ah).sum() - (self.ms ** 2).sum())

    def identity_residual(self) -> float:
        """sum_i m_i^2 (||u_i||^4 - 1): ALL of the identity's finite-grid gap.

        ||P||_F^2 = sum_i m_i^2 G_ii^2 + R holds exactly; only ||u_i|| = 1
        is truncation-dependent, so this term accounts for the whole
        difference between D and ||Ahat||_F^2 - sum m^2, and it vanishes at
        the same 1/span rate as the unit-norm defect.
        """
        gii = np.einsum("ij,ij->i", self.U, self.U)
        return float((self.ms ** 2 * (gii ** 2 - 1.0)).sum())


def closed_form_reference(xs, ms, pairs) -> dict:
    """The three composition inputs in closed form, from the kernel alone.

    R    = sum_{i!=j} m_i m_j omega(x_i-x_j)^2
    trPQ = sum_i m_i W(x_i - t_p, y_p)                    (the chain's field)
    ||Q_p||_F^2 = 4 + 8 sigma^2 + 8 sigma^4 = 4 + slack(y)   (single pair;
        from <v,v> = 1 and <v,conj v> = Phi2(2iy)/A, i.e. xx = 1 + sigma^2,
        yy = sigma^2, xy = 0)
    Neither grid enters, so these are what BOTH assemblies must converge to.
    """
    chain = PaperChain()
    xs = np.asarray(xs, float)
    ms = np.asarray(ms, float)
    R = 0.0
    for i in range(len(xs)):
        for j in range(len(xs)):
            if i != j:
                om = float(phipap(complex(xs[i] - xs[j], 0)).real / A)
                R += ms[i] * ms[j] * om * om
    trPQ = 0.0
    for t, y in pairs:
        trPQ += float((ms * chain.W(xs - t, y)).sum())
    fro2 = sum(4.0 + chain.slack(y) for _, y in pairs) if len(pairs) == 1 else None
    return {"R": R, "trPQ": trPQ, "fro2_Q": fro2}


def roundtrip(spans=(600.0, 1200.0, 2400.0)) -> list:
    """The conversion factor, measured: our grid vs theirs vs the closed form.

    Factor 1 is a prediction of the dictionary, not an input to it, so the
    honest instrument is a ladder: both grids must approach the same
    kernel-only reference like 1/span, and their ratio must approach 1.
    """
    xs = [0.0, TWO_PI, 2 * TWO_PI]
    ms = [1, 2, 1]
    pairs = [(math.pi, 0.49)]
    ref = closed_form_reference(xs, ms, pairs)
    rows = []
    for span in spans:
        ours = GridAssembly(xs, ms, pairs, K=int(span))
        theirs = PaperGridAssembly(xs, ms, pairs, span=span)
        row = {"span": span, "N": float(sum(ms)), "trP_theirs": theirs.trP(),
               "D_ours": ours.D(), "D_theirs": theirs.D(),
               "D_identity_defect": abs(theirs.fro2_Ahat_minus_msq()
                                        - theirs.D()),
               "D_identity_explained": abs(theirs.fro2_Ahat_minus_msq()
                                           - theirs.D()
                                           - theirs.identity_residual())}
        for name, o, t, r in (("R", ours.R(), theirs.R(), ref["R"]),
                              ("trPQ", ours.trPQ(), theirs.trPQ(), ref["trPQ"]),
                              ("fro2_Q", ours.fro2_Q(), theirs.fro2_Q(),
                               ref["fro2_Q"])):
            row[name] = {"ours": o, "theirs": t, "ref": r,
                         "ratio": t / o, "rel_ours": abs(o / r - 1.0),
                         "rel_theirs": abs(t / r - 1.0)}
        row["D_ratio"] = theirs.D() / ours.D()
        rows.append(row)
    return rows


def wrong_normalisation_lesion(span: float = 1200.0) -> dict:
    """Lesion: carry OUR constant 2 pi A onto THEIR grid and watch it break.

    The planted fault is exactly the mistake this seam exists to prevent -
    reusing the LAW D normalisation across the change of variable without
    re-reading the Poisson constant at the new grid step.  It must show up as
    a clean factor 2 pi on the unit norm.
    """
    K = int(span / TWO_PI)
    n = np.arange(-K, K + 1, 1.0) * TWO_PI + 0.37
    raw = phihat(0.31 - n).real
    good = raw / math.sqrt(poisson_constant(TWO_PI))
    bad = raw / math.sqrt(poisson_constant(1.0))
    return {"good_unit_norm": float(good @ good),
            "lesioned_unit_norm": float(bad @ bad),
            "expected_lesion_ratio": 1.0 / TWO_PI,
            "measured_lesion_ratio": float(bad @ bad) / float(good @ good)}


# ---------------------------------------------------------------------------
# 3. the paper's parameters and their admissible ranges
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class PaperParams:
    """(lam, w) with the source's admissibility, plus the derived scalars.

    `Params.Valid` (Zeta23/Defs.lean): 0 < lam <= 1 and w >= 1.  The endgame
    `thmD_abstract` additionally takes lam < 1 STRICTLY, and the window-moment
    bounds need [eq:wrange] 8w <= L.  All three are checked here; none is
    invented.  Heights are carried as l = log(T/2pi), never as T.
    """

    lam: float
    w: float = 1.0

    def L(self, l: float) -> float:
        return self.lam * l

    def ell1(self, l: float) -> float:
        return l + ELL1_OFFSET

    def lam1(self, l: float) -> float:
        """lam1 = L/ell1: the DENSITY parameter (mean gap 2 pi lam1 in x)."""
        return self.L(l) / self.ell1(l)

    def valid(self, l: float) -> dict:
        return {"lam_pos": self.lam > 0.0, "lam_lt_one": self.lam < 1.0,
                "w_ge_one": self.w >= 1.0, "wrange": 8 * self.w <= self.L(l),
                "l_pos": l > 0.0}

    def is_valid(self, l: float) -> bool:
        return all(self.valid(l).values())

    def calE(self, l: float) -> float:
        """calE = w/L + (l^2 + X) log l /(T l) + T^(lam/2-1), in log space.

        With T = 2 pi e^l and X = e^(lam l): X/T = e^(-(1-lam) l)/(2 pi), so
        every term is evaluated without overflow at l ~ 1e6.
        """
        L = self.L(l)
        k = (1.0 - self.lam) * l
        mid = (math.log(l) / l) * (l * l * math.exp(-l) / TWO_PI
                                   + math.exp(-k) / TWO_PI)
        third = math.exp((self.lam / 2.0 - 1.0) * l) * TWO_PI ** (self.lam / 2.0 - 1.0)
        return self.w / L + mid + third

    def cinv_limit(self) -> float:
        return 1.0 / c_star(self.lam)

    def cinv_at(self, l: float) -> float:
        """1/cRatio at the starred moments and the finite-T lam1."""
        return 1.0 / c_ratio(self.lam1(l), a_star(self.lam), b_star(self.lam),
                             j_star(self.lam))

    def cinv_drift(self, l: float) -> float:
        """max |1/cRatio(lam1; a,b,J) - 1/c*(lam)| over the moment box.

        The box is the source's own: |a-a*| <= 4w/L, |b-b*| <= 4w/L,
        |J-J*| <= 16w/L, so this is the only o(1) term in the endgame whose
        constant is explicit rather than existential.
        """
        L = self.L(l)
        lam1 = self.lam1(l)
        a, b, J = a_star(self.lam), b_star(self.lam), j_star(self.lam)
        da, db, dJ = (MOMENT_CONST[key] * self.w / L for key in ("a", "b", "J"))
        target = 1.0 / c_star(self.lam)
        worst = 0.0
        for sa in (-1, 1):
            for sb in (-1, 1):
                for sj in (-1, 1):
                    worst = max(worst, abs(
                        1.0 / c_ratio(lam1, a + sa * da, b + sb * db, J + sj * dJ)
                        - target))
        return worst


def log10_T_of_l(l: float) -> float:
    """T = 2 pi e^l, reported as log10 T (the number does not fit a float)."""
    return (l + math.log(TWO_PI)) / math.log(10.0)


def log10_N_of_l(l: float) -> float:
    """N(T,2T) = T ell1 / 2 pi = e^l (l + 2 log 2 - 1), as log10."""
    return (l + math.log(l + ELL1_OFFSET)) / math.log(10.0)


# ---------------------------------------------------------------------------
# 4. the error budget
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class Term:
    name: str
    value: float          # size relative to N
    scaling: str          # its behaviour in T
    constant: str         # "explicit", or the name of the existential constant
    source: str


def error_budget(l: float, P: PaperParams, C: float = 1.0) -> list:
    """Every term the extra census term must survive, sized relative to N.

    `C` stands for the existential constants of `EvBound` (PrimeSideTemp:
    "exists C > 0, T0, forall T >= T0, |f| <= C g").  They are NOT recoverable
    from the formalisation, so the budget is a function of C and the
    crossover's dependence on C is reported separately.
    """
    lam, w = P.lam, P.w
    L, ell1 = P.L(l), P.ell1(l)
    calE, cinv, a = P.calE(l), P.cinv_at(l), a_star(lam)
    log_N = l + math.log(ell1)          # log N(T,2T)

    def _exp(z: float) -> float:        # underflow to 0, never overflow
        return math.exp(z) if z > -700.0 else 0.0

    # 4 R1 / N with R1 = C1 sqrt(X)/a
    r1 = 4.0 * C * _exp(lam * l / 2.0 - log_N) / a
    # R2 / N with R2 = C2 calE (cinv N)
    r2 = C * calE * cinv
    # 3 NII / N with NII <= CII sqrt(T) l
    nii = 3.0 * C * math.sqrt(TWO_PI) * l * _exp(l / 2.0 - log_N)
    # tail: B = theta0/(a L) with theta0 <= Ctheta l T^(lam/2-1)
    log_B = (math.log(C * l) + (lam / 2.0 - 1.0) * (l + math.log(TWO_PI))
             - math.log(a * L))
    tail = (_exp(log_B + math.log(4.0) - log_N)
            + 2.0 * _exp(log_B + 0.5 * math.log(cinv + r2) - 0.5 * log_N)
            + _exp(2.0 * log_B - log_N))
    # the constant drift |cinv(T) - 1/c*(lam)|  (explicit 4,4,16 w/L)
    drift = P.cinv_drift(l)
    # the price of lam < 1, measured against the paper's own headline HD(1)
    lam_gap = HD(1.0) - HD(lam)
    # our side: the census floor's 1/N edge effect on a finite window
    census_edge = _exp(-log_N)

    return [
        Term("R2 = C2 calE cinv N", r2,
             f"cinv*w/(lam l) = {cinv * w / L:.3e} plus O(log l e^-k/l)",
             "C2 (existential)", "TracesBoundsD.frhat"),
        Term("drift |cinv(T)-1/c*|", drift,
             f"35.519 w/L = {35.519106 * w / L:.3e}",
             "explicit (4,4,16 w/L)", "ThmD/Window aD/bD/jD_close"),
        Term("lam gap HD(1)-HD(lam)", lam_gap,
             f"HD'(1)(1-lam) = {HD_slope() * (1 - lam):.3e}",
             "explicit", "thmD_abstract requires lam < 1"),
        Term("4 R1 = 4 C1 sqrt(X)/a", r1, "T^(lam/2-1)/l",
             "C1 (existential)", "TracesBoundsD.tr1"),
        Term("3 NII (boundary)", nii, "l/sqrt(T)", "CII (existential)",
             "thmD_abstract hNII"),
        Term("tail B(4+2sqrt+B)", tail, "T^(lam/2-1)/sqrt(N)",
             "Ctheta (existential)", "Assembly/SeamMult, htheta0"),
        Term("census 1/N edge", census_edge, "1/N", "explicit",
             "closing_bookkeeping n-ladder"),
    ]


def drift_coefficient(lam: float = 1.0) -> dict:
    """The dominant term's constant, derived term by term rather than fitted.

    cinv = (b + lam1^2 J)/(lam1 a^2), and the source bounds the three moments
    by 4w/L, 4w/L, 16w/L.  With lam1 = L/ell1 = lam - lam(2log2-1)/ell1 the
    finite-T density parameter, the coefficient of w/L in the drift is

        4/(lam1 a^2) + 16 lam1/a^2 + 8 cinv/a + |dcinv/dlam1| (2 log 2 - 1),

    the last piece being the lam1-vs-lam offset; dcinv/dlam1 = (lam1^2 J - b)
    /(lam1^2 a^2) = -HD'(1) at lam = 1.  `error_budget`'s measured
    drift x L/w must converge to the total.
    """
    a, b, J = a_star(lam), b_star(lam), j_star(lam)
    cinv = 1.0 / c_star(lam)
    d_lam1 = (lam * lam * J - b) / (lam * lam * a * a)
    parts = {"from_b": MOMENT_CONST["b"] / (lam * a * a),
             "from_J": MOMENT_CONST["J"] * lam / (a * a),
             "from_a": MOMENT_CONST["a"] * 2 * cinv / a,
             "from_lam1_offset": abs(d_lam1) * ELL1_OFFSET,
             "dcinv_dlam1": d_lam1}
    parts["total"] = (parts["from_b"] + parts["from_J"] + parts["from_a"]
                      + parts["from_lam1_offset"])
    return parts


def budget_total(l: float, P: PaperParams, C: float = 1.0) -> float:
    return sum(t.value for t in error_budget(l, P, C))


def dominant_term(l: float, P: PaperParams, C: float = 1.0) -> Term:
    return max(error_budget(l, P, C), key=lambda t: t.value)


def budget_table(ls=(1e2, 1e3, 1e4, 1e6, 4e6), k: float = 1.5,
                 w: float = 1.0, C: float = 1.0) -> list:
    """The budget at representative admissible parameters, lam = 1 - k/l."""
    rows = []
    for l in ls:
        P = PaperParams(lam=1.0 - k / l, w=w)
        terms = error_budget(l, P, C)
        rows.append({"l": l, "log10_T": log10_T_of_l(l),
                     "log10_N": log10_N_of_l(l), "lam": P.lam,
                     "lam1": P.lam1(l), "calE": P.calE(l),
                     "valid": P.is_valid(l), "terms": terms,
                     "total": sum(t.value for t in terms),
                     "improvement": IMPROVEMENT})
    return rows


# ---------------------------------------------------------------------------
# 5. the crossover
# ---------------------------------------------------------------------------


def best_k(l: float, w: float = 1.0, C: float = 1.0, ks=None) -> tuple:
    """The lam < 1 minimising the budget at height l, written as k = (1-lam) l."""
    if ks is None:
        ks = np.linspace(0.05, 8.0, 160)
    best = None
    for k in ks:
        P = PaperParams(lam=1.0 - float(k) / l, w=w)
        if not P.is_valid(l):
            continue
        tot = budget_total(l, P, C)
        if best is None or tot < best[1]:
            best = (float(k), tot, P)
    return best


def crossover_l(C: float = 1.0, w: float = 1.0, lo: float = 1e2,
                hi: float = 1e10, tol: float = 1e-4) -> dict:
    """Least l with min_lam budget(l) < 2 theta c_u, by bisection in log l.

    The crossover is returned in l = log(T/2pi); T is reported as a power of
    ten because it does not fit a float.
    """
    def gap(x: float) -> float:
        return best_k(x, w, C)[1] - IMPROVEMENT

    if gap(hi) > 0:
        return {"exists": False, "C": C, "w": w, "searched_to": hi}
    while (hi - lo) / hi > tol:
        mid = math.sqrt(lo * hi)
        if gap(mid) > 0:
            lo = mid
        else:
            hi = mid
    k, tot, P = best_k(hi, w, C)
    return {"exists": True, "C": C, "w": w, "l": hi, "k": k, "lam": P.lam,
            "lam1": P.lam1(hi), "budget": tot, "improvement": IMPROVEMENT,
            "log10_T": log10_T_of_l(hi), "log10_N": log10_N_of_l(hi),
            "terms": error_budget(hi, P, C)}


def crossover_sensitivity(Cs=(1.0, 10.0, 100.0), w: float = 1.0) -> list:
    """How the crossover moves with the existential constant."""
    rows = []
    for C in Cs:
        r = crossover_l(C=C, w=w)
        rows.append({"C": C, "w": w, "exists": r["exists"], "l": r.get("l"),
                     "log10_T": r.get("log10_T")})
    return rows


def improvement_scaling(factors=(1.0, 10.0, 100.0)) -> list:
    """Crossover height against the SIZE of the improvement.

    The budget is ~ K/l with K ~ 38, so l_cross ~ K/improvement and T_cross is
    exponential in 1/improvement.  Measured here rather than asserted: the
    product l * improvement must come out roughly constant.
    """
    rows = []
    for f in factors:
        target = IMPROVEMENT * f
        lo, hi = 1e2, 1e11
        while (hi - lo) / hi > 1e-4:
            mid = math.sqrt(lo * hi)
            if best_k(mid)[1] - target > 0:
                lo = mid
            else:
                hi = mid
        rows.append({"improvement": target, "l": hi,
                     "log10_T": log10_T_of_l(hi),
                     "l_times_improvement": hi * target})
    return rows


# ---------------------------------------------------------------------------
# 6. the census kernel away from lam = 1
# ---------------------------------------------------------------------------


def _s(u):
    u = np.asarray(u, float)
    small = np.abs(u) < 1e-12
    us = np.where(small, 1.0, u)
    return np.where(small, 0.5, np.sin(us / 2) / us)


def g_lambda(u, lam: float = 1.0, lam1: float | None = None):
    """The mass kernel in mean-gap units at window lam and density lam1.

    In x = tau L units the mean gap is 2 pi lam1, and the incidence kernel is
    omega_lam = Phi2_lam / A_lam, so the gap-census kernel at gap u (measured
    in mean gaps) is

        g_{lam,lam1}(u) = [ vhat_lam(2 pi lam1 u) / vhat_lam(0) ]^2,
        vhat_lam(z) = s(z + sqrt2 lam) + s(z - sqrt2 lam),  s(w) = sin(w/2)/w.

    At lam = lam1 = 1 this must BE `cg_transplant.g_kernel`, which is the
    check that x = tau L with mean gap 2 pi lam1 is the right change of
    variable (`g_lambda_is_g_at_one`).
    """
    if lam1 is None:
        lam1 = lam
    z = 2 * np.pi * lam1 * np.asarray(u, float)
    num = _s(z + S2 * lam) + _s(z - S2 * lam)
    den = 2 * float(_s(np.array([S2 * lam]))[0])
    return (num / den) ** 2


def g_lambda_is_g_at_one(n: int = 20001) -> float:
    u = np.linspace(0.0, 6.0, n)
    return float(np.abs(g_lambda(u) - g_kernel(u)).max())


class LambdaGTable:
    """`reconnect.HardenedGTable`'s one-sided sampled minimum, at g_{lam,lam1}."""

    def __init__(self, lam: float = 1.0, lam1: float | None = None,
                 n: int = 600001, hi: float = 6.0):
        from scipy.optimize import brentq
        self.lam = lam
        self.lam1 = lam if lam1 is None else lam1
        self.x = np.linspace(0.0, hi, n)
        self.v = g_lambda(self.x, self.lam, self.lam1)

        def num(t):
            z = 2 * np.pi * self.lam1 * t
            return float(_s(np.array([z + S2 * self.lam]))[0]
                         + _s(np.array([z - S2 * self.lam]))[0])

        xs = np.linspace(0.5, hi, 1200)
        vs = np.array([num(t) for t in xs])
        self.roots = [brentq(num, xs[i], xs[i + 1])
                      for i in range(len(xs) - 1) if vs[i] * vs[i + 1] < 0]
        xf = np.linspace(0.0, hi, 4 * (n - 1) + 1)
        vf = g_lambda(xf, self.lam, self.lam1)
        self.gprime_max = 1.5 * float(np.abs(np.diff(vf) / np.diff(xf)).max())
        self.step = float(self.x[1] - self.x[0])

    def minimum(self, lo: float, hi: float) -> float:
        if any(lo <= r <= hi for r in self.roots):
            return 0.0
        i, j = np.searchsorted(self.x, [lo, hi])
        gm = float(self.v[max(i - 1, 0): j + 1].min())
        return max(0.0, gm - self.gprime_max * self.step)


def floor_at_lambda(lam: float = 1.0, lam1: float | None = None,
                    nu: float = H_PINNED, edges=EDGES, n: int = 600001):
    """The bucket floor c_u at the lam-deformed kernel, edges held fixed.

    Holding the edges at the lam = 1 optimum is one-sided (any admissible edge
    tuple gives a valid floor), so this under-reports c_u away from lam = 1 -
    the safe direction for a sensitivity statement.
    """
    table = LambdaGTable(lam, lam1, n=n)
    return bucket_floor(nu, *edges, table=table,
                        g=lambda u: g_lambda(u, lam, lam1))


def census_floor_lambda_sensitivity(deltas=(0.0, 1e-4, 1e-3)) -> list:
    """c_u against 1 - lam near 1, and the slope it implies."""
    rows, base = [], None
    for d in deltas:
        fl = floor_at_lambda(1.0 - d)
        if base is None:
            base = fl
        rows.append({"lam": 1.0 - d, "floor": fl,
                     "slope": ((fl - base) / (-d) if d else 0.0)})
    return rows


def census_floor_at_crossover(C: float = 1.0) -> dict:
    """c_u at the lam1 the crossover actually uses, against c_u(1).

    1 - lam1 = (1-lam) + (2 log 2 - 1)/l + O(1/l^2) is ~5e-7 there, so the
    kernel barely moves; the measurement says by how much and in which
    direction.
    """
    cr = crossover_l(C=C)
    if not cr["exists"]:
        return {"exists": False}
    lam, lam1 = cr["lam"], cr["lam1"]
    fl = floor_at_lambda(lam, lam1)
    base = floor_at_lambda(1.0)          # same instrument, same resolution
    return {"exists": True, "lam": lam, "lam1": lam1,
            "one_minus_lam1": 1.0 - lam1, "floor": fl, "floor_at_one": base,
            "pinned_reading": C_U, "instrument_vs_pinned": abs(base - C_U),
            "shift": fl - base, "relative": (fl - base) / base}


# ---------------------------------------------------------------------------
# 7. audit
# ---------------------------------------------------------------------------


def audit() -> None:
    print("= 1. the a-vs-A relation ((7.1) norm against the LAW D constant) =")
    r = a_vs_A()
    print(f"  {r['formula']}")
    print(f"  A (paper_chain)   = {r['A_paper_chain']:.16f}")
    print(f"  a*(1) closed form = {r['a_star_1_closed']:.16f}   "
          f"defect {r['closed_vs_A']:.2e}")
    print(f"  a*(1) quadrature  = {r['a_star_1_quad']:.16f}   "
          f"defect {r['quad_vs_A']:.2e}")
    for row in moment_closed_forms_vs_quadrature():
        print(f"  lam={row['lam']:.2f}: a*={row['a']:.10f} b*={row['b']:.10f} "
              f"J*={row['J']:.10f} (quad defects {row['a_defect']:.1e}/"
              f"{row['b_defect']:.1e}/{row['J_defect']:.1e})  "
              f"cRatio-vs-c* {row['c_defect']:.2e}")
    print(f"  HD(1) = {HD(1.0):.10f}  (source headline 0.6725007036...);  "
          f"HD'(1) = {HD_slope():.6f}")

    print("= 2. the Poisson constant at both grid steps =")
    for h, label in ((1.0, "ours, x-step 1"),
                     (TWO_PI, "theirs, x = tau L, x-step 2 pi")):
        print(f"  h = {h:.6f} ({label}): (2pi/h) int phi^2 = "
              f"{poisson_constant(h):.12f}")
    print(f"  their a L^2 = L^2 x {poisson_constant(TWO_PI):.12f};  "
          f"our 2 pi A = {poisson_constant(1.0):.12f};  raw-Gram factor "
          f"a L^2/(2 pi A) = L^2/(2 pi)")
    print("  truncation ladder on the paper grid (closed-form normalisation):")
    for row in grid_sum_ladder():
        print(f"    K={row['K']:4d} span={row['span']:7.0f}: "
              f"|u.u-1|={row['unit_defect']:.3e}  "
              f"gram-vs-omega={row['gram_defect']:.3e}")
    print("  grid-step invariance of the normalised Gram:")
    for row in grid_step_invariance():
        cells = "  ".join(f"h={h}: {row[h]['gram']:.8f}"
                          for h in row if h.startswith("h="))
        print(f"    span={row['span']:6.0f}  {cells}   worst defect vs omega "
              f"{row['worst_defect']:.2e}")

    print("= 3. round-trip: the composition inputs on both grids =")
    for row in roundtrip():
        print(f"  span={row['span']:6.0f}: "
              f"R {row['R']['ours']:.8f}/{row['R']['theirs']:.8f} "
              f"(ref {row['R']['ref']:.8f}, rel {row['R']['rel_ours']:.2e}/"
              f"{row['R']['rel_theirs']:.2e})")
        print(f"                trPQ {row['trPQ']['ours']:.6f}/"
              f"{row['trPQ']['theirs']:.6f} (rel {row['trPQ']['rel_theirs']:.2e})"
              f"   ||Q||^2 {row['fro2_Q']['ours']:.6f}/"
              f"{row['fro2_Q']['theirs']:.6f} "
              f"(rel {row['fro2_Q']['rel_theirs']:.2e})")
        print(f"                D ratio theirs/ours {row['D_ratio']:.8f};  "
              f"tr P = {row['trP_theirs']:.8f} (N = {row['N']:.0f});  "
              f"|D - (||Ahat||^2 - sum m^2)| = {row['D_identity_defect']:.2e} "
              f"(all of it sum m^2(||u||^4-1); unexplained "
              f"{row['D_identity_explained']:.1e})")
    les = wrong_normalisation_lesion()
    print(f"  LESION (LAW D constant on their grid): unit norm "
          f"{les['lesioned_unit_norm']:.6f} vs {les['good_unit_norm']:.6f}, "
          f"ratio {les['measured_lesion_ratio']:.8f} "
          f"(expected 1/2pi = {les['expected_lesion_ratio']:.8f})")

    print("= 4. the error budget at representative admissible parameters =")
    dc = drift_coefficient()
    print(f"  the dominant term's constant, derived: {dc['from_b']:.3f} (b) + "
          f"{dc['from_J']:.3f} (J) + {dc['from_a']:.3f} (a) + "
          f"{dc['from_lam1_offset']:.3f} (lam1 offset) = {dc['total']:.3f}")
    for l in (1e4, 1e6):
        P = PaperParams(lam=1.0 - 1.5 / l)
        print(f"    measured drift x L/w at l={l:.0e}: "
              f"{P.cinv_drift(l) * P.L(l) / P.w:.4f}")
    for row in budget_table():
        print(f"  l = {row['l']:.0e}  T = 10^{row['log10_T']:.4g}  "
              f"N = 10^{row['log10_N']:.4g}  lam = {row['lam']:.9f}  "
              f"lam1 = {row['lam1']:.9f}  admissible = {row['valid']}  "
              f"calE = {row['calE']:.4e}")
        for t in row["terms"]:
            print(f"      {t.name:24s} {t.value:.4e}   [{t.scaling}]  "
                  f"{t.constant}")
        verdict = ("IMPROVEMENT SURVIVES" if row["total"] < row["improvement"]
                   else "errors dominate")
        print(f"      {'TOTAL':24s} {row['total']:.4e}   vs 2*theta*c_u = "
              f"{row['improvement']:.4e}   {verdict}")

    print("= 5. the crossover =")
    cr = crossover_l()
    if cr["exists"]:
        print(f"  C = 1: crossover at l = {cr['l']:.4e}  "
              f"(T = 10^{cr['log10_T']:.5g}, N = 10^{cr['log10_N']:.5g}), "
              f"k = (1-lam) l = {cr['k']:.3f}, lam = {cr['lam']:.12f}")
        print(f"  budget there {cr['budget']:.4e} < improvement "
              f"{cr['improvement']:.4e}.  Dominant terms:")
        for t in sorted(cr["terms"], key=lambda t: -t.value)[:3]:
            print(f"      {t.name:24s} {t.value:.3e}  {t.constant}")
    else:
        print("  NO CROSSOVER in the searched range: the extra term would")
        print("  drown in the error terms at every feasible T.")
    print("  sensitivity to the existential EvBound constant:")
    for row in crossover_sensitivity():
        print(f"      C = {row['C']:6.1f}: l = {row['l']:.4e}  "
              f"T = 10^{row['log10_T']:.5g}")
    print("  crossover height against the size of the improvement:")
    for row in improvement_scaling():
        print(f"      improvement {row['improvement']:.3e}: l = {row['l']:.4e}"
              f"  (T = 10^{row['log10_T']:.5g}), l*improvement = "
              f"{row['l_times_improvement']:.3f}")

    print("= 6. the census kernel away from lam = 1 =")
    print(f"  g_lambda(1) vs cg_transplant.g_kernel: worst "
          f"{g_lambda_is_g_at_one():.2e}")
    for row in census_floor_lambda_sensitivity():
        tag = (f"  slope dc_u/dlam ~ {row['slope']:+.3e}" if row["slope"]
               else f"  (pinned reading {FLOOR_SCIPY:.6e})")
        print(f"  lam = {row['lam']:.4f}: floor = {row['floor']:.6e}{tag}")
    cf = census_floor_at_crossover()
    if cf["exists"]:
        print(f"  at the crossover lam1 = {cf['lam1']:.12f} "
              f"(1 - lam1 = {cf['one_minus_lam1']:.3e}): "
              f"c_u = {cf['floor']:.9e} against {cf['floor_at_one']:.9e} at "
              f"lam = 1, shift {cf['shift']:+.2e} ({cf['relative']:+.2e} "
              f"relative)")
        print(f"  (this instrument reproduces the pinned reading to "
              f"{cf['instrument_vs_pinned']:.1e}).  The shift raises the floor,")
        print("  so holding c_u at its lam = 1 value is the one-sided choice.")

    print("Scope: the dictionary is exact up to the measured 1/span truncation")
    print("of the grid instruments; the budget uses the source's own parameter")
    print("ranges and its own explicit moment constants, with the four EvBound")
    print("constants carried as C because the formalisation does not name them.")
    print("No proportion is claimed and nothing here is evidence about RH.")


if __name__ == "__main__":
    audit()

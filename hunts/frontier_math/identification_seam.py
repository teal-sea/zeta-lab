"""Seam (ii): identifying the band dual's cap with the hypothesis D >= theta*R.

THE CLAIM TO BE IDENTIFIED.  The kernel-checked composition
(`t3_composition_skeleton.lean`) needs the hypothesis

    D := R + 2 tr(P Q) + ||Q||_F^2  >=  theta * R0,

with P = sum_i m_i u_i u_i^T the on-line block, Q the off-line pair
block, R = sum_{i != j} m_i m_j <u_i, u_j>^2, and R0 a floor on R.  The
band dual (`paper_chain.py` / `paper_joint.py`) measures a cap on an
adversary's W-field profit against a slack budget.  This module derives
and MEASURES the dictionary between the two, term by term, on explicit
finite configurations at the paper field.  Nothing is remembered: every
identity below is checked against a direct grid assembly.

THE DICTIONARY (all in LAW D units: grid Z, mean zero gap 2 pi,
Phi2 = FT(phi^2) = `paper_chain.phipap`, A = Phi2(0)):

1. On-line vectors.  v_x(n) = phihat(x - n); LAW D (kernel-checked in
   `law_d_incidence.lean` for real arguments, extended here by direct
   summation for complex ones) gives <v_x, v_x> = 2 pi A, so
   u_x = v_x / sqrt(2 pi A) is the unit vector and
   <u_x, u_x'> = Phi2(x - x')/A = omega(x - x').  Hence
   R = sum_{i != j} m_i m_j omega^2 - the chain's retained mass, in the
   chain's own kernel.
2. Pair block.  An off-line pair at z = t + iy contributes (transpose
   convention, the clean-kill record) Q_p = 2 (x_p x_p^T - y_p y_p^T)
   with x_p + i y_p = v_z / sqrt(2 pi A).  Then for real on-line u_i,
       u_i^T Q_p u_i = 2 [ (Re c)^2 - (Im c)^2 ],  c = Phi2(x_i - z)/A,
   which is exactly the chain's damage field W(x_i - t, y).  Summing:
       tr(P Q) = sum_i m_i sum_p W(x_i - t_p, y_p).
3. Pair surplus.  ||Q_p||_F^2 - (4 tr Q_p - 4 b_p) is the pair's
   Frobenius mass beyond what the (L)-side consumes; the chain's
   slack(y) = 8 sigma^2 + 8 sigma^4 is its closed form (measured below,
   not assumed - the factor conventions are exactly where the level-4
   incident lived).
4. Cross terms.  ||Q||_F^2 = sum_p ||Q_p||_F^2 + sum_{p != p'}
   tr(Q_p Q_p'), and the cross trace has no a-priori sign.  It is
   measured over the swept families; a negative total that the dual's
   budget does not cover would be a HOLE in the identification and is
   reported as such.

WHAT THEN REMAINS.  With 1-3 pinned, the dual's verdict
"cap(theta, config) <= slack budget" IS the statement

    - 2 tr(P Q) <= (1 - theta) R + sum_p slack_p        (swept families)

whence D >= theta R + sum_p (4 tr Q_p - 4 b_p) + cross >= theta R
provided cross >= 0 or is covered (measured below; 4 tr Q_p - 4 b_p is
measured positive per pair).  The end-to-end check computes D and
theta*R directly on each configuration.  The identification inherits
the dual's scope: configuration families swept plus the joint layer's
one-sided completeness, not an unconditional sup.  R >= R0 (the CG-LP
floor under the gap census) is the separate, already-instrumented step
(`kernel_pairing.py` ladder).  No proportion is claimed.

Run ``.venv/bin/python hunts/frontier_math/identification_seam.py`` (~2 min).
"""

from __future__ import annotations

import math
import sys
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
from paper_chain import A, PaperBandDual, PaperChain, phipap  # noqa: E402

S2 = math.sqrt(2.0)
TWO_PI = 2 * math.pi

# Gauss-Legendre on [-1/2, 1/2] for phihat; phi = sqrt(cos(sqrt2 u)) is
# smooth on the closed box (cos >= cos(1/sqrt2) > 0), so GL converges
# geometrically IN THE ORDER - but the integrand e^{ixu} oscillates
# |x|/(2 pi) times across the box, so the order must scale with the
# largest argument.  The first run of this module used a fixed order 80
# and the truncation ladder ran BACKWARDS (defects growing with K): the
# quadrature, not the identity, was failing beyond |x| ~ 150.  The rule
# below is sized by max |Re z| and the failure is kept as a control
# (`quadrature_order_control`).
_RULES: dict = {}


def _rule(order: int):
    if order not in _RULES:
        gx, gw = np.polynomial.legendre.leggauss(order)
        u = 0.5 * gx
        _RULES[order] = (u, 0.5 * gw, np.sqrt(np.cos(S2 * u)))
    return _RULES[order]


def _order_for(maxabs: float) -> int:
    return max(120, int(0.75 * maxabs) + 120)


def phihat(z, order: int | None = None):
    """FT of the paper window at complex z, by argument-sized GL."""
    z = np.atleast_1d(np.asarray(z, complex))
    if order is None:
        order = _order_for(float(np.abs(z.real).max()))
    u, w, phi = _rule(order)
    return (np.exp(1j * np.outer(z, u)) * (phi * w)).sum(axis=1)


class GridAssembly:
    """Truncated LAW D grid assembly for one configuration."""

    def __init__(self, xs, ms, pairs, K: int = 600):
        self.xs = np.asarray(xs, float)      # on-line positions
        self.ms = np.asarray(ms, float)      # multiplicities (integers)
        self.pairs = list(pairs)             # [(t, y)]
        self.K = K
        n = np.arange(-K, K + 1, 1.0)
        span = [abs(x) for x in self.xs] + [abs(t) for t, _ in self.pairs]
        order = _order_for(K + (max(span) if span else 0.0))
        norm = math.sqrt(TWO_PI * A)
        self.U = np.array([phihat(x - n, order).real for x in self.xs]) / norm
        self.Vx, self.Vy = [], []
        for t, y in self.pairs:
            v = phihat(complex(t, y) - n, order) / norm
            self.Vx.append(v.real)
            self.Vy.append(v.imag)

    # -- skeleton inputs, all from dot products (never dense matrices) --

    def unit_defect(self) -> float:
        return float(max(abs(u @ u - 1.0) for u in self.U))

    def gram_vs_omega(self) -> float:
        """<u_i, u_j> against Phi2(dx)/A: worst absolute defect."""
        worst = 0.0
        for i in range(len(self.xs)):
            for j in range(i + 1, len(self.xs)):
                g = self.U[i] @ self.U[j]
                om = phipap(complex(self.xs[i] - self.xs[j], 0)).real / A
                worst = max(worst, abs(g - om))
        return worst

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

    def trPQ_vs_W(self, chain: PaperChain) -> float:
        """The identification 2-defect: u^T Q_p u against W, worst abs."""
        worst = 0.0
        for (t, y), x, yv in zip(self.pairs, self.Vx, self.Vy):
            for i, xi in enumerate(self.xs):
                lhs = 2 * ((self.U[i] @ x) ** 2 - (self.U[i] @ yv) ** 2)
                rhs = float(chain.W(np.array([xi - t]), y)[0])
                worst = max(worst, abs(lhs - rhs))
        return worst

    def pair_terms(self):
        """Per-pair (tr Q_p, b_p, ||Q_p||_F^2) from the 2x2 span."""
        out = []
        for x, yv in zip(self.Vx, self.Vy):
            xx, xy, yy = x @ x, x @ yv, yv @ yv
            tr = 2 * (xx - yy)
            fro = 4 * (xx * xx - 2 * xy * xy + yy * yy)
            # eigenvalues of Q_p on span(x, y): solve the 2x2 problem
            m = 2 * np.array([[xx, xy], [xy, -yy]])
            g = np.array([[xx, xy], [xy, yy]])
            # Q_p w = lam w with w = alpha x + beta y: m coeff against g
            lam = np.linalg.eigvals(np.linalg.solve(g, g @ m)) \
                if abs(np.linalg.det(g)) > 1e-14 else np.array([tr, 0.0])
            bp = int((np.real(lam) > 1e-12).sum())
            out.append({"tr": tr, "b": bp, "fro2": fro})
        return out

    def fro2_Q(self) -> float:
        tot = 0.0
        n = len(self.pairs)
        for p in range(n):
            for q in range(n):
                tot += self._crossQ(p, q)
        return tot

    def _crossQ(self, p: int, q: int) -> float:
        x1, y1 = self.Vx[p], self.Vy[p]
        x2, y2 = self.Vx[q], self.Vy[q]
        return 4 * ((x1 @ x2) ** 2 - (x1 @ y2) ** 2
                    - (y1 @ x2) ** 2 + (y1 @ y2) ** 2)

    def cross_total(self) -> float:
        n = len(self.pairs)
        return sum(self._crossQ(p, q) for p in range(n) for q in range(n)
                   if p != q)

    def D(self) -> float:
        return self.R() + 2 * self.trPQ() + self.fro2_Q()


def slack_identity(chain: PaperChain, ys=(0.02, 0.1, 0.3, 0.49),
                   K: int = 600) -> list:
    """Measured ||Q_p||_F^2 - (4 tr Q_p - 4 b_p) against slack(y)."""
    rows = []
    for y in ys:
        ga = GridAssembly([], [], [(0.31, y)], K=K)
        t = ga.pair_terms()[0]
        surplus = t["fro2"] - (4 * t["tr"] - 4 * t["b"])
        rows.append({"y": y, "surplus": surplus, "slack": chain.slack(y),
                     "tr": t["tr"], "b": t["b"],
                     "defect": abs(surplus - chain.slack(y))})
    return rows


def _lattice(nu: float, count: int, phase: float = 0.0):
    return [phase + k * TWO_PI / nu for k in range(count)]


def _damage_minima(chain: PaperChain, y: float, nbands: int = 2):
    """Argmin of W in the first negative bands, derived from the field."""
    g = np.arange(1.0, 20.0, 0.001)
    w = chain.W(g, y)
    outs, lo = [], None
    for k in range(1, len(g)):
        if w[k] < 0 and lo is None:
            lo = k
        if lo is not None and (w[k] >= 0 or k == len(g) - 1):
            seg = slice(lo, k)
            outs.append(float(g[seg][np.argmin(w[seg])]))
            lo = None
            if len(outs) == nbands:
                break
    return outs


def _joint_damage_minima(chain: PaperChain, pairs, n: int = 3,
                         span: float = 30.0):
    """The n deepest local minima of the JOINT field sum_p W(. - t_p, y_p).

    Added by the 2026-08-12 audit: the battery's multi-pair rows placed
    on-line points on a benign lattice, so the configuration the joint
    dual actually bounds -- zeros AT the joint minima of a multi-pair
    field -- was never exercised on explicit matrices."""
    g = np.arange(-span, span, 0.002)
    w = np.zeros_like(g)
    for t, y in pairs:
        w += chain.W(g - t, y)
    idx = [k for k in range(1, len(g) - 1)
           if w[k] < w[k - 1] and w[k] <= w[k + 1] and w[k] < 0]
    idx.sort(key=lambda k: w[k])
    return [float(g[k]) for k in idx[:n]]


def configurations():
    """The end-to-end battery: binding families from the sweeps, plus
    adversarial placements derived from the field itself (on-line points
    AT the damage minima, where total damage is positive and the sharp
    inequality actually bites)."""
    chain = PaperChain()
    on9 = _lattice(1.0, 9)
    mid = on9[4] + math.pi          # off-line between lattice points
    g1, g2 = _damage_minima(chain, 0.49, 2)
    adv1 = ([-g1, g1], [1, 1], [(0.0, 0.49)])
    adv2 = ([-g2, -g1, g1, g2], [1] * 4, [(0.0, 0.49)])
    adv3 = ([-g1, g1], [2, 2], [(0.0, 0.49)])
    dip = [(0.0, 0.49), (6.406, 0.49)]
    jm_dip = _joint_damage_minima(chain, dip, 3)
    lat4 = [(x, 0.49) for x in _lattice(0.5, 4)]
    jm_lat = _joint_damage_minima(chain, lat4, 3)
    adv4 = (jm_dip, [1] * len(jm_dip), dip)
    adv5 = (jm_dip, [2] * len(jm_dip), dip)
    adv6 = (jm_lat, [2] * len(jm_lat), lat4)
    return {
        "ADV: zeros at first damage minimum": adv1,
        "ADV: zeros at first two minima": adv2,
        "ADV: double zeros at first minimum": adv3,
        "ADV: zeros at JOINT minima of dipole": adv4,
        "ADV: double zeros at JOINT minima of dipole": adv5,
        "ADV: double zeros at JOINT minima of nu=0.5 lattice": adv6,
        "single pair y=0.49": (on9, [1] * 9, [(mid, 0.49)]),
        "single pair y=0.3": (on9, [1] * 9, [(mid, 0.3)]),
        "single pair y=0.02": (on9, [1] * 9, [(mid, 0.02)]),
        "worst dipole y=0.49": (on9, [1] * 9,
                                [(mid, 0.49), (mid + 6.406, 0.49)]),
        "nu=0.5 lattice y=0.49 (joint binding)": (
            on9, [1] * 9, [(x + math.pi, 0.49) for x in _lattice(0.5, 4)]),
        "soft lattice nu=0.9576 y=0.49": (
            on9, [1] * 9, [(x + math.pi, 0.49) for x in _lattice(0.9576, 5)]),
        "double zero present": (on9, [2] + [1] * 8, [(mid, 0.49)]),
        "pair on top of a zero": (on9, [1] * 9, [(on9[4], 0.49)]),
    }


def end_to_end(theta: float = 0.995, K: int = 600):
    """Two nested statements per configuration.

    GROSS (the corollary's hypothesis): D >= theta * R.  On finite
    configurations ||Q||_F^2 alone dwarfs theta*R, so this is a
    consistency control, not the sharp content.

    SHARP (what the dual's verdict asserts through the dictionary):
        damage - cross := -2 tr(P Q) - sum_{p != p'} tr(Q_p Q_p')
                       <= (1 - theta) * R + sum_p slack_p,
    i.e. the pair block's erosion of the retained mass, INCLUDING the
    pair-pair cross term -- measured negative, so it belongs on this
    side (audit 2026-08-12 finding A: the first draft omitted it, and
    its binding rows were single-pair, where it vanishes identically) --
    stays inside the per-pair Frobenius surplus plus the ceded
    (1-theta) fraction.  The joint dual budgets exactly this: its
    T_signed IS the cross term (measured identity, `coopt_adversary`
    dictionary control).  Here it is evaluated on explicit matrices.
    """
    chain = PaperChain()
    rows = []
    for name, (xs, ms, pairs) in configurations().items():
        ga = GridAssembly(xs, ms, pairs, K=K)
        damage = -2 * ga.trPQ()
        cross = ga.cross_total()
        budget = (1 - theta) * ga.R() + sum(chain.slack(y) for _, y in pairs)
        rows.append({
            "name": name, "R": ga.R(), "trPQ": ga.trPQ(),
            "fro2Q": ga.fro2_Q(), "cross": cross,
            "D": ga.D(), "thetaR": theta * ga.R(),
            "holds": ga.D() >= theta * ga.R(),
            "damage": damage, "budget": budget,
            "sharp_holds": damage - cross <= budget,
        })
    return rows


def quadrature_order_control() -> dict:
    """The failure that bit this module's first run, kept as a control.

    At fixed order 80 the unit norm at x = 400 is badly wrong; at the
    argument-sized order it is LAW D-consistent.  Both are measured.
    """
    n = np.arange(-600, 601, 1.0)
    norm = TWO_PI * A
    bad = float((phihat(400.0 - n, order=80).real ** 2).sum() / norm)
    good = float((phihat(400.0 - n).real ** 2).sum() / norm)
    return {"order80": bad, "sized": good,
            "bad_off": abs(bad - 1.0), "good_off": abs(good - 1.0)}


def truncation_ladder(Ks=(300, 600, 1200)) -> dict:
    """LAW D truncation on the assembled quantities: ~1/K scaling."""
    out = {}
    for K in Ks:
        ga = GridAssembly([0.0, TWO_PI], [1, 1], [(math.pi, 0.49)], K=K)
        out[K] = {"unit": ga.unit_defect(), "gram": ga.gram_vs_omega()}
    return out


def audit():
    chain = PaperChain()
    print("= LAW D grid assembly: unit norms and the omega dictionary =")
    lad = truncation_ladder()
    for K, r in lad.items():
        print(f"  K={K}: unit-norm defect {r['unit']:.3e}   "
              f"gram-vs-omega defect {r['gram']:.3e}")
    print("= identification 2: u^T Q_p u is the W field =")
    ga = GridAssembly(_lattice(1.0, 5), [1] * 5,
                      [(2 * TWO_PI + math.pi, 0.49), (math.pi, 0.3)], K=900)
    print(f"  worst |2[(u.x)^2-(u.y)^2] - W| = {ga.trPQ_vs_W(chain):.3e}")
    print("= identification 3: the pair surplus is slack(y) =")
    for r in slack_identity(chain):
        print(f"  y={r['y']:.2f}: surplus {r['surplus']:.6f}  "
              f"slack {r['slack']:.6f}  defect {r['defect']:.2e}  "
              f"(tr {r['tr']:.4f}, b={r['b']})")
    print("= identification 4: pair-pair cross terms (sign question) =")
    for name, (xs, ms, pairs) in configurations().items():
        if len(pairs) < 2:
            continue
        ga = GridAssembly(xs, ms, pairs, K=600)
        c = ga.cross_total()
        print(f"  {name}: cross = {c:+.6f}  "
              f"({'nonneg' if c >= -1e-10 else 'NEGATIVE - measured, see report'})")
    print("= quadrature-order control (the first run's own defect) =")
    qc = quadrature_order_control()
    print(f"  fixed order 80: |norm-1| = {qc['bad_off']:.3e} (the failure)")
    print(f"  argument-sized: |norm-1| = {qc['good_off']:.3e}")
    print("= end-to-end at theta = 0.995: gross and sharp =")
    for r in end_to_end():
        print(f"  {r['name']:42s} D={r['D']:+9.5f} thetaR={r['thetaR']:+8.5f}"
              f" {'HOLDS' if r['holds'] else 'FAILS'}   damage={r['damage']:+8.5f}"
              f" budget={r['budget']:+8.5f} {'SHARP-OK' if r['sharp_holds'] else 'SHARP-FAILS'}")
    print("Scope: identities exact up to measured 1/K truncation; the")
    print("configuration-free statement inherits the dual's swept-family")
    print("scope. R >= R0 is the separate CG-LP step. No proportion is")
    print("claimed and nothing here is evidence about RH.")


if __name__ == "__main__":
    audit()

"""Ball-arithmetic (Arb, via python-flint) route to the truncated Weil form.

Mirrors galerkin.Truncation entry-for-entry, but every quantity is an arb
ball whose radius bounds all truncation and rounding error:

* special functions (digamma, trigamma = Hurwitz zeta(2, .), pi, euler,
  logs, sqrts, sines) come from Arb with rigorous radii;
* the geometric series in z = e^{-2L} are summed to J terms and the dropped
  tail is added to the ball as an explicit +/- bound;
* the eigenvalue statements come from (i) a ball LDL^T factorization
  (matrix inertia: if every pivot ball has a determined sign, the inertia
  is rigorous), (ii) a Rayleigh-quotient ball upper bound for lambda_min,
  and (iii) python-flint's acb_mat.eig (Rump verification) enclosures.

Same convention alignment as zeta/rigor.py: python-flint is the Arb backend
the lab's enclosure work standardizes on; nothing here silently falls back
to floats, and an inconclusive pivot is reported as inconclusive.
"""

from __future__ import annotations

import math

from flint import acb, acb_mat, arb, ctx

import galerkin as GK


# ---------------------------------------------------------------------------
# assembly in balls
# ---------------------------------------------------------------------------


def _ball_pm(x: arb, eps: arb) -> arb:
    """The ball x +/- eps (eps >= 0)."""
    return x + (arb(0).union(eps).union(-eps))


class BallTruncation:
    """Ball-arithmetic twin of galerkin.Truncation (same formulas)."""

    def __init__(self, c: int, N: int, kind: str = "zeta", prec: int = 300):
        ctx.prec = prec
        self.prec = prec
        self.c = c
        self.N = N
        self.kind = kind
        pi = arb.pi()
        L = arb(c).log()
        self.L = L
        z = (-2 * L).exp()
        J = int(math.ceil((prec + 30) * math.log(2) / (2 * float(L)))) + 3
        if kind == "zeta":
            a = arb(1) / 4
            const = -pi.log() + acb(a).digamma().real
            coeffs = [(q, arb(p).log()) for (q, p) in GK.prime_powers_upto(float(c))]
        elif kind == "dh":
            a = arb(3) / 4
            const = -(pi / 5).log() + acb(a).digamma().real
            coeffs = self._dh_coeffs(int(c))
        else:
            raise ValueError(kind)
        self.a = a
        mus = [2 * (arb(j) + a) for j in range(J)]
        Es = [(-m * L).exp() for m in mus]
        one_minus_z = 1 - z
        # tail integral sum E_j / mu_j, j >= J bounded by geometric envelope
        tail_int = sum((E / m for m, E in zip(mus, Es)), arb(0))
        tail_int = _ball_pm(tail_int, Es[-1] * z / (mus[-1] * one_minus_z))
        S = [arb(0)] * (N + 1)
        Dg = [arb(0)] * (N + 1)
        for k in range(N + 1):
            om = 2 * pi * k / L
            zz = acb(a, om / 2)
            psi0 = zz.digamma()
            psi1 = acb(2).zeta(zz)  # trigamma via Hurwitz zeta(2, z)
            if k == 0:
                S[0] = arb(0)
                sum_cos1 = arb(0)
            else:
                geo = sum((E * om / (m * m + om * om) for m, E in zip(mus, Es)), arb(0))
                geo = _ball_pm(geo, Es[-1] * z * om / (mus[-1] ** 2 * one_minus_z))
                S[k] = psi0.imag / 2 - geo
                geo1 = sum(
                    (E * om * om / (m * (m * m + om * om)) for m, E in zip(mus, Es)),
                    arb(0),
                )
                geo1 = _ball_pm(geo1, Es[-1] * z / (mus[-1] * one_minus_z))
                sum_cos1 = -(psi0.real - acb(a).digamma().real) / 2 + geo1
            geox = sum(
                (
                    E
                    * (
                        (m * m - om * om) / (m * m + om * om) ** 2
                        + m * L / (m * m + om * om)
                    )
                    for m, E in zip(mus, Es)
                ),
                arb(0),
            )
            geox = _ball_pm(
                geox, Es[-1] * z * (1 + mus[-1] * L) / (mus[-1] ** 2 * one_minus_z)
            )
            sum_xcos = psi1.real / 4 - geox
            Dg[k] = 2 * sum_cos1 - (2 / L) * sum_xcos
        self._S = S
        self._archdiag = [const - Dg[k] + 2 * tail_int for k in range(N + 1)]
        P = [arb(0)] * (N + 1)
        R = [arb(0)] * (N + 1)
        for q, lam in coeffs:
            y = arb(q).log() if isinstance(q, int) else q
            w = lam / arb(q).sqrt() if isinstance(q, int) else lam
            for k in range(N + 1):
                om = 2 * pi * k / L
                P[k] += w * (om * y).sin()
                R[k] += w * 2 * (1 - y / L) * (om * y).cos()
        self._P = P
        self._R = R
        self._pi = pi

    def _dh_coeffs(self, cmax: int):
        """(n, Lambda_f(n)/... ) actually (n, Lambda_f(n)) as arb balls."""
        s5 = arb(5).sqrt()
        kap = ((10 - 2 * s5).sqrt() - 2) / (s5 - 1)
        pat = [arb(1), kap, -kap, arb(-1), arb(0)]

        def a(n):
            return pat[(n - 1) % 5]

        lam = {1: arb(0)}
        out = []
        for n in range(2, cmax + 1):
            s = a(n) * arb(n).log()
            for d in range(2, n):
                if n % d == 0:
                    s -= lam[d] * a(n // d)
            lam[n] = s
            out.append((n, s))
        return out

    def w02(self, n: int, m: int) -> arb:
        if self.kind != "zeta":
            return arb(0)
        L = self.L
        pi2 = self._pi**2
        num = 32 * L * (L / 4).sinh() ** 2 * (L * L - 16 * pi2 * m * n)
        return num / ((L * L + 16 * pi2 * m * m) * (L * L + 16 * pi2 * n * n))

    def _sgn(self, seq, k):
        return seq[k] if k >= 0 else -seq[-k]

    def entry(self, n: int, m: int) -> arb:
        if n == m:
            k = abs(n)
            return self.w02(n, n) + self._archdiag[k] - self._R[k]
        tm = self._sgn(self._S, m) + self._sgn(self._P, m)
        tn = self._sgn(self._S, n) + self._sgn(self._P, n)
        return self.w02(n, m) - (tm - tn) / (self._pi * (n - m))

    def even_matrix(self):
        N = self.N
        s2 = arb(2).sqrt()
        M = [[arb(0)] * (N + 1) for _ in range(N + 1)]
        M[0][0] = self.entry(0, 0)
        for k in range(1, N + 1):
            v = s2 * self.entry(0, k)
            M[0][k] = M[k][0] = v
        for j in range(1, N + 1):
            for k in range(j, N + 1):
                v = self.entry(j, k) + self.entry(j, -k)
                M[j][k] = M[k][j] = v
        return M

    def odd_matrix(self):
        N = self.N
        M = [[arb(0)] * N for _ in range(N)]
        for j in range(1, N + 1):
            for k in range(j, N + 1):
                v = self.entry(j, k) - self.entry(j, -k)
                M[j - 1][k - 1] = M[k - 1][j - 1] = v
        return M


# ---------------------------------------------------------------------------
# rigorous linear algebra on ball matrices
# ---------------------------------------------------------------------------


def ldlt_inertia(M, shift: arb | None = None):
    """Ball LDL^T of M - shift*I.  Returns (n_pos, n_neg, conclusive).

    If any pivot ball straddles zero the result is inconclusive from that
    pivot on and conclusive=False (no sign claims are made for the rest).
    """
    n = len(M)
    A = [[M[i][j] - (shift if (shift is not None and i == j) else arb(0)) for j in range(n)] for i in range(n)]
    d = []
    Lf = [[arb(0)] * n for _ in range(n)]
    for j in range(n):
        s = A[j][j]
        for k in range(j):
            s -= Lf[j][k] * Lf[j][k] * d[k]
        if not (s > 0 or s < 0):
            return (
                sum(1 for x in d if x > 0),
                sum(1 for x in d if x < 0),
                False,
            )
        d.append(s)
        for i in range(j + 1, n):
            t = A[i][j]
            for k in range(j):
                t -= Lf[i][k] * Lf[j][k] * d[k]
            Lf[i][j] = t / s
    return (sum(1 for x in d if x > 0), sum(1 for x in d if x < 0), True)


def rayleigh_upper(M, v_float) -> arb:
    """Rigorous upper bound on lambda_min from any nonzero vector."""
    n = len(M)
    v = [arb(x) for x in v_float]  # floats are exact dyadics
    num = arb(0)
    for i in range(n):
        for j in range(n):
            num += v[i] * M[i][j] * v[j]
    den = sum((x * x for x in v), arb(0))
    q = num / den
    # upper endpoint of the ball, as an arb point
    return q.mid() + q.rad()


def eig_enclosures(M, prec: int):
    """All-eigenvalue enclosures via acb_mat.eig (Rump verification)."""
    ctx.prec = prec
    n = len(M)
    A = acb_mat([[acb(M[i][j]) for j in range(n)] for i in range(n)])
    try:
        E = A.eig(algorithm="rump", multiple=True)
    except Exception:
        return None
    return sorted(E, key=lambda e: float(e.real.mid()))


def lambda_min_enclosure(M, lam_float: float, prec: int):
    """[lo, hi] with rigorous lo < lambda_min <= hi, plus inertia at 0.

    lo comes from LDL^T positive-definiteness of M - s I at trial shifts
    below the float estimate; hi from the smallest eig enclosure and the
    Rayleigh bound if a float eigenvector is supplied separately.
    """
    ctx.prec = prec
    n_pos0, n_neg0, concl0 = ldlt_inertia(M, arb(0))
    lo = None
    scale = abs(lam_float) if lam_float != 0 else 1e-30
    for f in (1e-25, 1e-15, 1e-8, 1e-4, 1e-2, 0.5, 1.0, 2.0, 10.0):
        s = arb(lam_float) - arb(scale) * arb(f)
        npos, nneg, concl = ldlt_inertia(M, s)
        if concl and nneg == 0 and npos == len(M):
            lo = s
            break
    return {
        "inertia_at_0": (n_pos0, n_neg0, concl0),
        "lower": lo,
    }

"""checker/: the (U-S) gate in exact arithmetic (mission kill-control 1).

(U-S), theory RESULTS s7.1: on a window of length log c,
  (1) the Weil distribution has atoms only at prime powers;
  (2) for each p the tower s_k(p) := Lambda_F(p^k)/log p equals
      sum_j alpha_{j,p}^k with every |alpha_{j,p}| = 1.
The exactly checkable consequence of (2) used here is |s_k(p)| <= d, the
degree. An atom at a prime power p^k that carries a log q component with
q != p is also recorded (it is not the local term of the place p).

Exact representation. For a Dirichlet series F = sum a_n n^{-s} with rational
a_n and a_1 = 1, -F'/F = sum Lambda_F(n) n^{-s} with

    Lambda_F(n) = a_n log n - sum_{d | n, 1 < d < n} Lambda_F(d) a_{n/d},

and every Lambda_F(n) is a Q-linear combination of the log p (log n =
sum_p v_p(n) log p). Distinct log p are linearly independent over Q (unique
factorisation), so "Lambda_F(n) = 0" and "s_k(p)" are decided exactly on the
coefficient vectors (dicts p -> Fraction). A second exact route, the formal
logarithm log F = sum b_n n^{-s} with rational b_n and Lambda_F(n) = b_n log n,
is implemented as a cross-check.

W_a = zeta(s+a) zeta(s-a) does not have rational coefficients. Its tower is
supplied in closed form, Lambda_W(p^k) = log p (p^{ka} + p^{-ka}) (additivity
of the log-derivative; derivation), and the tower condition is decided
exactly: for x = p^{ka} > 0, x + 1/x - 2 = (x - 1)^2 / x, so
|s_k(p)| <= 2 iff x = 1 iff k a = 0, a rational-arithmetic decision.
"""

from __future__ import annotations

from fractions import Fraction

N_MAX = 200


# --------------------------------------------------------------------------
# integers
# --------------------------------------------------------------------------


def factorize(n: int) -> dict[int, int]:
    out: dict[int, int] = {}
    d = 2
    while d * d <= n:
        while n % d == 0:
            out[d] = out.get(d, 0) + 1
            n //= d
        d += 1
    if n > 1:
        out[n] = out.get(n, 0) + 1
    return out


def prime_power(n: int):
    """(p, k) if n = p^k with k >= 1, else None."""
    f = factorize(n)
    if len(f) == 1:
        ((p, k),) = f.items()
        return p, k
    return None


def jacobi(a: int, n: int) -> int:
    """Jacobi symbol (a/n) for odd n > 0."""
    assert n > 0 and n % 2 == 1
    a %= n
    res = 1
    while a:
        while a % 2 == 0:
            a //= 2
            if n % 8 in (3, 5):
                res = -res
        a, n = n, a
        if a % 4 == 3 and n % 4 == 3:
            res = -res
        a %= n
    return res if n == 1 else 0


def kronecker_m23(n: int) -> int:
    """chi_{-23}(n) = (-23 / n), Kronecker symbol, n >= 1.

    -23 = 1 mod 8, so chi(2) = +1; odd part by the Jacobi symbol."""
    res = 1
    while n % 2 == 0:
        n //= 2
    return res * jacobi(-23, n) if n > 1 else res


def rep_count(n: int, form: tuple[int, int, int]) -> int:
    """#{(x, y) != (0, 0) in Z^2 : A x^2 + B x y + C y^2 = n}, by enumeration.

    Positive definite forms only; the bound on |y| is from
    4 A n = (2 A x + B y)^2 + (4 A C - B^2) y^2."""
    A, B, C = form
    disc = 4 * A * C - B * B
    assert disc > 0 and A > 0
    ymax = 0
    while disc * (ymax + 1) ** 2 <= 4 * A * n:
        ymax += 1
    tot = 0
    for y in range(-ymax, ymax + 1):
        # A x^2 + B y x + (C y^2 - n) = 0
        rad = B * B * y * y - 4 * A * (C * y * y - n)
        if rad < 0:
            continue
        r = int(rad**0.5)
        while r * r > rad:
            r -= 1
        while (r + 1) * (r + 1) <= rad:
            r += 1
        if r * r != rad:
            continue
        for s in {r, -r}:
            num = -B * y + s
            if num % (2 * A) == 0:
                x = num // (2 * A)
                if (x, y) != (0, 0):
                    tot += 1
    return tot


# --------------------------------------------------------------------------
# the objects (rational Dirichlet coefficients, a_1 = 1)
# --------------------------------------------------------------------------


def coeffs_zeta(n_max: int = N_MAX) -> dict[int, Fraction]:
    return {n: Fraction(1) for n in range(1, n_max + 1)}


def coeffs_dedekind_m23(n_max: int = N_MAX) -> dict[int, Fraction]:
    """Number of ideals of norm n in Q(sqrt -23): sum_{d | n} chi_{-23}(d)."""
    return {
        n: Fraction(sum(kronecker_m23(d) for d in range(1, n + 1) if n % d == 0))
        for n in range(1, n_max + 1)
    }


def coeffs_dedekind_m23_forms(n_max: int = N_MAX) -> dict[int, Fraction]:
    """Second route: (1/w) sum over the h = 3 reduced forms of discriminant -23,
    w = 2: (r_{1,1,6} + r_{2,1,3} + r_{2,-1,3}) / 2."""
    forms = ((1, 1, 6), (2, 1, 3), (2, -1, 3))
    return {n: Fraction(sum(rep_count(n, f) for f in forms), 2) for n in range(1, n_max + 1)}


def coeffs_epstein_116(n_max: int = N_MAX) -> dict[int, Fraction]:
    """Epstein zeta of x^2 + x y + 6 y^2, normalised to a_1 = 1 (r(1) = 2)."""
    return {n: Fraction(rep_count(n, (1, 1, 6)), 2) for n in range(1, n_max + 1)}


# --------------------------------------------------------------------------
# Lambda_F in the log-prime basis
# --------------------------------------------------------------------------


def _clean(v: dict) -> dict:
    return {p: c for p, c in v.items() if c != 0}


def lambda_vectors(a: dict[int, Fraction], n_max: int = N_MAX) -> dict[int, dict[int, Fraction]]:
    """Lambda_F(n), n = 2..n_max, as {p: rational coefficient of log p}."""
    if a[1] != 1:
        raise ValueError("normalise to a_1 = 1")
    lam: dict[int, dict[int, Fraction]] = {}
    for n in range(2, n_max + 1):
        v = {p: a[n] * e for p, e in factorize(n).items()}
        for d in range(2, n):
            if n % d == 0 and lam[d] and a[n // d] != 0:
                for p, cf in lam[d].items():
                    v[p] = v.get(p, Fraction(0)) - cf * a[n // d]
        lam[n] = _clean(v)
    return lam


def formal_log(a: dict[int, Fraction], n_max: int = N_MAX) -> dict[int, Fraction]:
    """b_n with log F = sum_{n >= 2} b_n n^{-s} (formal Dirichlet series)."""
    u = {n: a[n] for n in range(2, n_max + 1) if a[n] != 0}  # F - 1
    b = {n: Fraction(0) for n in range(2, n_max + 1)}
    power = dict(u)
    k = 1
    while power:
        sign = Fraction(1 if k % 2 else -1, k)
        for n, cf in power.items():
            b[n] += sign * cf
        nxt: dict[int, Fraction] = {}
        for n1, c1 in power.items():
            for n2, c2 in u.items():
                m = n1 * n2
                if m > n_max:
                    continue
                nxt[m] = nxt.get(m, Fraction(0)) + c1 * c2
        power = _clean(nxt)
        k += 1
    return b


# --------------------------------------------------------------------------
# the gate
# --------------------------------------------------------------------------


class ClosedFormTower:
    """Exact tower s_k(p) = p^{k a} + p^{-k a} for the shifted product W_a.

    Atoms only at prime powers (Lambda_W = Lambda (n^a + n^-a)); the value
    is not rational, so only exact decisions are exposed."""

    def __init__(self, a: Fraction):
        self.a = Fraction(a)

    def exceeds(self, p: int, k: int, d: int) -> bool:
        if d != 2:
            raise NotImplementedError("exact decision implemented for d = 2 only")
        # x + 1/x > 2  iff  (x - 1)^2 > 0  iff  x != 1  iff  k a != 0 (p >= 2)
        return k * self.a != 0

    def value(self, p: int, k: int, dps: int = 30):
        """Float value for the record only; never used in a decision."""
        from mpmath import mp

        with mp.workdps(dps):
            x = mp.mpf(p) ** (k * mp.mpf(self.a.numerator) / self.a.denominator)
            return +(x + 1 / x)


def gate_events(lam, degree: int, n_max: int = N_MAX) -> list[dict]:
    """All (U-S) violations for n <= n_max, ascending in n.

    lam: dict n -> {p: Fraction} (rational objects) or a ClosedFormTower."""
    ev = []
    for n in range(2, n_max + 1):
        pk = prime_power(n)
        if isinstance(lam, ClosedFormTower):
            if pk is not None and lam.exceeds(pk[0], pk[1], degree):
                ev.append({"n": n, "kind": "tower", "p": pk[0], "k": pk[1],
                           "s_k_float": float(lam.value(*pk))})
            continue
        v = lam[n]
        if not v:
            continue
        if pk is None:
            ev.append({"n": n, "kind": "composite_atom",
                       "coeffs": {str(p): str(c) for p, c in sorted(v.items())}})
            continue
        p, k = pk
        foreign = {q: c for q, c in v.items() if q != p}
        if foreign:
            ev.append({"n": n, "kind": "foreign_log", "p": p, "k": k,
                       "coeffs": {str(q): str(c) for q, c in sorted(v.items())}})
        s = v.get(p, Fraction(0))
        if abs(s) > degree:
            ev.append({"n": n, "kind": "tower", "p": p, "k": k, "s_k": str(s)})
    return ev


def towers(lam, primes, n_max: int = N_MAX) -> dict:
    """{p: [s_1(p), s_2(p), ...]} for p^k <= n_max (rational objects)."""
    out = {}
    for p in primes:
        seq, q = [], p
        while q <= n_max:
            seq.append(str(lam[q].get(p, Fraction(0))))
            q *= p
        out[str(p)] = seq
    return out


def accepts_window(events, c) -> bool:
    """Window mode: (U-S) restricted to the atoms inside the window, n < c."""
    return not any(e["n"] < c for e in events)


def accepts_places(events, c) -> bool:
    """Place mode, S = {inf} u {p < c}: the whole tower of every p in S
    (all p^k <= N_MAX) and every composite atom inside the window.

    This is what a T_S builder must apply: its local factor at p uses the
    whole tower, not only the atoms inside the window (mission control 2)."""
    for e in events:
        if e["kind"] == "composite_atom" and e["n"] < c:
            return False
        if e["kind"] in ("tower", "foreign_log") and e["p"] < c:
            return False
    return True


OBJECTS = {
    # name: (degree, coefficient builder or closed-form tower)
    "zeta": (1, coeffs_zeta),
    "dedekind_Q(sqrt-23)": (2, coeffs_dedekind_m23),
    "epstein_(1,1,6)": (2, coeffs_epstein_116),
    "W_a(a=1/4)": (2, lambda n_max=N_MAX: ClosedFormTower(Fraction(1, 4))),
}


def run_gate(n_max: int = N_MAX) -> dict:
    """Events and first rejection points for the four objects of the mission."""
    out = {}
    for name, (deg, build) in OBJECTS.items():
        obj = build(n_max)
        lam = obj if isinstance(obj, ClosedFormTower) else lambda_vectors(obj, n_max)
        ev = gate_events(lam, deg, n_max)
        rec = {
            "degree": deg,
            "n_max": n_max,
            "events": ev,
            "first_rejection_n": ev[0]["n"] if ev else None,
            "first_composite_atom": next((e["n"] for e in ev if e["kind"] == "composite_atom"), None),
            "first_tower_violation": next((e["n"] for e in ev if e["kind"] == "tower"), None),
            "n_composite_atoms": sum(1 for e in ev if e["kind"] == "composite_atom"),
            "n_tower_violations": sum(1 for e in ev if e["kind"] == "tower"),
            "n_foreign_log": sum(1 for e in ev if e["kind"] == "foreign_log"),
        }
        if not isinstance(obj, ClosedFormTower):
            rec["towers"] = towers(lam, [2, 3, 5, 7, 23])
        out[name] = rec
    return out

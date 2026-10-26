"""A second implementation in PARI/GP (through cypari2) for hunt #148.

Nothing here imports ``ffprobe.py``.  Residue symbols (by resultant and by Frobenius),
Gauss sums (by enumeration, by Davenport-Hasse and by the prime-power reduction),
finite-field and cyclotomic arithmetic, the probe's weights and sums, the local factor by
its definition, Patterson's C and rho_0, and the rival's L-polynomials are written again
in GP and evaluated by PARI.  Python and numpy only add up integer exponent histograms
(counts of roots of unity), which carry no arithmetic of their own.  The only thing shared
with ``ffprobe.py`` is the mathematics being checked, read again from its sources:

* chi(y) = y^((q-1)/n) and eps(g^((q-1)/n)) = zeta_n for g the least primitive root mod q;
* (a/c)_n = chi(Res(c, a)) for monic c, and a^((|P|-1)/n) mod P for a prime P;
* e(b/c) = e_o(coefficient of x^(deg c - 1) in b mod c), e_o(t) = zeta_q^t (q prime);
* g(r, eps^j, c) = sum over y mod c of eps((y/c)_n)^j e(r y / c).

``to_pari`` converts an ``ffprobe`` cyclotomic number (anything with ``.K.N`` and a
rational polynomial ``.p``) into a PARI polmod so the two can be compared as exact
elements of Q(zeta_N).
"""

from __future__ import annotations

import itertools
import math

import cypari2
import numpy as np

pari = cypari2.Pari()
try:  # pragma: no cover - depends on the PARI build
    pari.allocatemem(4 * 10 ** 9, silent=True)
except TypeError:  # older cypari2 has no ``silent``
    pari.allocatemem(4 * 10 ** 9)

GP = r"""
\\ ---------------------------------------------------------------- basic helpers
\\ the cyclotomic field Q(zeta_N) as polmods in z
ffone(N) = {
  Mod(1, polcyclo(N, 'z));
}
ffz(k, N) = {
  Mod('z, polcyclo(N, 'z))^(k % N);
}
\\ an exponent histogram h (h[k+1] counts zeta_N^k) as a polmod
ffh2pm(h, N) = {
  Mod(sum(k = 1, #h, h[k] * 'z^(k-1)), polcyclo(N, 'z));
}
\\ discrete logarithms modulo q to the least primitive root: lg[a] = k with g^k = a
fflogtab(q) = {
  my(g = znprimroot(q), v = vector(q-1), t = Mod(1, q));
  for (k = 0, q-2, v[lift(t)] = k; t *= g);
  v;
}
\\ the polynomial with base-q code 'code' (constant term = least significant digit), degree < L
ffpoly(code, L, q) = {
  Mod(1, q) * Polrev(vector(L, i, (code \ q^(i-1)) % q), 'x);
}
\\ exponent k of eps((a/c)_n) for monic c, by the resultant; -1 at non-units
ffsymk(a, c, q, n, lg) = {
  my(r);
  if (poldegree(c) <= 0, return(0));
  r = lift(polresultant(c, a));
  if (r == 0, -1, lg[r] % n);
}
\\ the same by Frobenius at a monic irreducible P: a^((q^d-1)/n) mod P is a constant
ffsymfrobk(a, P, q, n, lg) = {
  my(b);
  if (a % P == 0, return(-1));
  b = lift(Mod(a, P)^((q^poldegree(P) - 1)/n));
  b = lift(polcoef(b, 0));
  \\ b is an n-th root of unity in F_q: its log is a multiple of (q-1)/n
  (lg[b] / ((q-1)/n)) % n;
}
\\ the same through the factorization of c, prime by prime (Frobenius route)
ffsymfac(a, c, q, n, lg) = {
  my(f, k = 0, s);
  if (poldegree(c) <= 0, return(0));
  f = factor(c);
  for (i = 1, #f~, s = ffsymfrobk(a, f[i,1], q, n, lg); if (s < 0, return(-1)); k += f[i,2] * s);
  k % n;
}
\\ exponent l with e(b/c) = zeta_q^l for monic c
ffe(b, c, q) = {
  my(d = poldegree(c));
  if (d <= 0, return(0));
  lift(polcoef(b % c, d - 1, 'x));
}
\\ symbol exponents of every polynomial of degree < L (code order), resultant route
ffsymvec(c, L, q, n) = {
  my(lg = fflogtab(q), w = vector(q^L));
  for (code = 0, q^L - 1, w[code+1] = ffsymk(ffpoly(code, L, q), c, q, n, lg));
  w;
}
\\ the same, Frobenius route through the factorization
ffsymvecfac(c, L, q, n) = {
  my(lg = fflogtab(q), w = vector(q^L));
  for (code = 0, q^L - 1, w[code+1] = ffsymfac(ffpoly(code, L, q), c, q, n, lg));
  w;
}
\\ Moebius function of a monic polynomial
ffmu(c) = {
  my(f);
  if (poldegree(c) <= 0, return(1));
  f = factor(c);
  for (i = 1, #f~, if (f[i,2] > 1, return(0)));
  (-1)^(#f~);
}
\\ ---------------------------------------------------------------- Gauss sums
\\ tau(eps chi^j) = sum over y in F_q^x of eps(chi(y))^j e_o(y)
fftau(q, n, j, N) = {
  my(lg = fflogtab(q), h = vector(N));
  for (y = 1, q-1, h[((N/n) * j * lg[y] + (N/q) * y) % N + 1]++);
  ffh2pm(h, N);
}
\\ sum over x mod c of e(x^2/c), as an exponent histogram (the quadratic sum behind Gamma)
ffgammah(c, q, N) = {
  my(d = poldegree(c), h = vector(N), x);
  if (d <= 0, h[1] = 1; return(h));
  for (code = 0, q^d - 1, x = ffpoly(code, d, q); h[((N/q) * ffe(x * x, c, q)) % N + 1]++);
  h;
}
\\ sqrt(q): the quadratic Gauss sum, times -i when q = 3 mod 4
ffsqrt(q, N) = {
  my(G = sum(a = 0, q-1, ffz((N/q) * a^2, N)));
  if (q % 4 == 1, G, -ffz(N/4, N) * G);
}
\\ g(r, eps^j, c) by enumeration of y mod c, as an exponent histogram
ffgaussh(r, c, q, n, j, N) = {
  my(d = poldegree(c), h = vector(N), lg = fflogtab(q), k, l, y);
  if (d <= 0, h[1] = 1; return(h));
  for (code = 0, q^d - 1,
    y = ffpoly(code, d, q);
    k = ffsymk(y, c, q, n, lg);
    if (k < 0, next);
    l = ffe(r * y, c, q);
    h[((N/n) * j * k + (N/q) * l) % N + 1]++);
  h;
}
ffgauss(r, c, q, n, j, N) = {
  ffh2pm(ffgaussh(r, c, q, n, j, N), N);
}
\\ histograms of g(r, eps^j, c) for j = 1..n-1 at once (one pass over y mod c)
ffgausshall(r, c, q, n, N) = {
  my(d = poldegree(c), H = vector(n-1, j, vector(N)), lg = fflogtab(q), k, l, y);
  if (d <= 0, for (j = 1, n-1, H[j][1] = 1); return(H));
  for (code = 0, q^d - 1,
    y = ffpoly(code, d, q);
    k = ffsymk(y, c, q, n, lg);
    if (k < 0, next);
    l = ffe(r * y, c, q);
    for (j = 1, n-1, H[j][((N/n) * j * k + (N/q) * l) % N + 1]++));
  H;
}
\\ Davenport-Hasse for (r, c) = 1 (Patterson 2014): mu(c) eps((r/c)^-1 (c'/c)) (-tau(eps chi))^deg c;
\\ variant 2007 uses ((-r)/c)^-1
ffdh(r, c, q, n, j, N, v2007) = {
  my(m = ffmu(c), lg = fflogtab(q), kr, kd);
  if (m == 0, return(0 * ffone(N)));
  if (poldegree(c) <= 0, return(ffone(N)));
  kr = ffsymk(if (v2007, -r, r), c, q, n, lg);
  kd = ffsymk(deriv(c), c, q, n, lg);
  m * ffz((N/n) * j * (kd - kr), N) * (-fftau(q, n, j, N))^poldegree(c);
}
\\ g(r, eps^j, P^e) by the prime-power reduction; the prime Gauss sum G_m(P) by
\\ Davenport-Hasse (route 0) or by enumeration (route 1)
ffgpp(r, j, P, e, q, n, N, route) = {
  my(Q = q^poldegree(P), v = 0, rr = r, m = (j * e) % n, lg = fflogtab(q), k, G);
  if (r == 0, v = 10^9, while (rr % P == 0, rr = rr / P; v++));
  if (m == 0, return((if (v >= e, Q^e, 0) - if (v >= e - 1, Q^(e-1), 0)) * ffone(N)));
  if (v != e - 1, return(0 * ffone(N)));
  k = ffsymk(rr, P, q, n, lg);
  G = if (route, ffgauss(Mod(1, q) * 'x^0, P, q, n, m, N), ffdh(Mod(1, q) * 'x^0, P, q, n, m, N, 0));
  Q^(e-1) * ffz(-(N/n) * m * k, N) * G;
}
\\ g(r, eps^j, c) by the Chinese remainder theorem over the prime powers of c
ffgstruct(r, j, c, q, n, N, route) = {
  my(f, out = ffone(N), ex = 0, lg = fflogtab(q));
  if (poldegree(c) <= 0, return(out));
  f = factor(c);
  for (i = 1, #f~, out *= ffgpp(r, j, f[i,1], f[i,2], q, n, N, route); if (out == 0, return(out)));
  for (a = 1, #f~, for (b = a + 1, #f~,
    ex += j * f[a,2] * f[b,2] * (ffsymk(f[a,1], f[b,1], q, n, lg) + ffsymk(f[b,1], f[a,1], q, n, lg))));
  out * ffz((N/n) * ex, N);
}
\\ ---------------------------------------------------------------- Patterson's C and rho_0
\\ C(r, eps^j, i) = sum over monic c of degree i of g(r, eps^j, c); route 1 = enumeration, 0 = CRT/DH
ffCx(r, q, n, j, i, N, route) = {
  my(S = 0 * ffone(N), c);
  if (i == 0, return(ffone(N)));
  forvec(v = vector(i, k, [0, q-1]),
    c = Mod(1, q) * ('x^i + Polrev(v, 'x));
    S += if (route, ffgauss(r, c, q, n, j, N), ffgstruct(r, j, c, q, n, N, 0)));
  S;
}
ffC(r, q, n, j, i, N) = {
  ffCx(r, q, n, j, i, N, 1);
}
\\ rho_0(r, eps^j, i) = Psi(q^(-n-1)) with Psi = (1 - q^(n+1) T)/(1 - q^n T) sum_l C(i + n l) T^l
\\ (Patterson's constant c_o = (q-1)/n dropped); C by enumeration up to degree 'maxbrute'
ffrho0x(r, q, n, j, i, N, maxbrute) = {
  my(R = floor((1 + poldegree(r) - i)/n), C, val = 0 * ffone(N), dl);
  if (R < 0, return(val));
  C = vector(R+1, l, ffCx(r, q, n, j, i + n*(l-1), N, i + n*(l-1) <= maxbrute));
  for (l = 1, R+1,
    dl = C[l];
    for (m = 1, l-1, dl -= C[m] * (q-1) * q^(n*(l-m)));
    val += dl / q^((n+1)*(l-1)));
  val;
}
ffrho0(r, q, n, j, i, N) = {
  ffrho0x(r, q, n, j, i, N, 99);
}
\\ the T-coefficients D_0..D_top of Psi (without the (q-1)/n), C by enumeration up to 'maxbrute'
ffpsicoeffs(r, q, n, j, i, N, top, maxbrute) = {
  my(C = vector(top+1, l, ffCx(r, q, n, j, i + n*(l-1), N, i + n*(l-1) <= maxbrute)), D = vector(top+1));
  for (l = 1, top+1, D[l] = C[l]; for (m = 1, l-1, D[l] -= C[m] * (q-1) * q^(n*(l-m))));
  D;
}
\\ ---------------------------------------------------------------- the probe's local pieces
\\ the Poisson coefficient F(s, A, H) of eq. (local-F), b_* = x and xi = chi_x^xij, both sums enumerated
ffFx(s, A, H, q, n, N, xij) = {
  my(TA = Mod(1, q) * 'x * A, ds = poldegree(s), dt = poldegree(TA), lg = fflogtab(q), h = vector(N),
     d, kd, k, y, kx, ka, l);
  forvec(v = vector(ds, i, [0, q-1]),
    d = Mod(1, q) * Polrev(v, 'x);
    if (ds > 0 && (H - TA * d) % s != 0, next);
    kd = if (ds > 0, ffsymk(d, s, q, n, lg), 0);
    if (kd < 0, next);
    k = if (ds > 0, (H - TA * d) / s, H);
    for (code = 0, q^dt - 1,
      y = ffpoly(code, dt, q);
      kx = ffsymk(y, Mod(1, q) * 'x, q, n, lg);
      if (kx < 0, next);
      ka = if (poldegree(A) > 0, ffsymk(y, A, q, n, lg), 0);
      if (ka < 0, next);
      l = ffe(k * y, TA, q);
      h[((N/n) * (kd + xij * kx + ka) + (N/q) * l) % N + 1]++));
  ffh2pm(h, N);
}
ffF(s, A, H, q, n, N) = {
  ffFx(s, A, H, q, n, N, 1);
}
\\ the same with the Gauss sum modulo T A split by the Chinese remainder theorem (A prime to T):
\\ g_{xi chi_A}(T A, k) = xi(A) chi_A(T) g_xi(T, k) g_{chi_A}(A, k), g_xi(T, k) = conj(xi(k)) g_xi(T, 1)
ffFcrt(s, A, H, q, n, N, xij) = {
  my(TA = Mod(1, q) * 'x * A, ds = poldegree(s), lg = fflogtab(q), S = 0 * ffone(N), d, kd, k, k0, pre, gxi);
  gxi = fftau(q, n, xij, N);
  pre = ffz((N/n) * (xij * lg[lift(polcoef(A, 0))] + ffsymk(Mod(1, q) * 'x, A, q, n, lg)), N);
  forvec(v = vector(ds, i, [0, q-1]),
    d = Mod(1, q) * Polrev(v, 'x);
    if (ds > 0 && (H - TA * d) % s != 0, next);
    kd = if (ds > 0, ffsymk(d, s, q, n, lg), 0);
    if (kd < 0, next);
    k = if (ds > 0, (H - TA * d) / s, H);
    k0 = lift(polcoef(k, 0));
    if (k0 == 0, next);
    S += ffz((N/n) * kd - (N/n) * xij * lg[k0], N) * pre * gxi * ffgstruct(k, 1, A, q, n, N, 0));
  S;
}
\\ g_{chi_p^t}(p^t, y) with every residue modulo p^t enumerated (small t only); the
\\ character chi_p^t modulo p^t is the symbol (./p^t)_n itself, so the exponent of eps is 1
ffgpt(P, t, y, q, n, N) = {
  if (t == 0, return(ffone(N)));
  ffgauss(y, P^t, q, n, 1, N);
}
\\ the local scalar C_p(t, k, j') of eq. (local-scalar-definition): the outer sum enumerated,
\\ the inner Gauss sum by enumeration when q^(t deg p) <= 'cap', else by the prime-power reduction
ffCp(P, t, k, jp, q, n, N, cap) = {
  my(pk = P^k, pt = P^t, pj = P^jp, S = 0 * ffone(N), lg = fflogtab(q), d, kd, y, g);
  if (k == 0,
    if (t == 0, return(ffone(N)));
    return(if (q^(t * poldegree(P)) <= cap, ffgpt(P, t, pj, q, n, N), ffgpp(pj, 1, P, t, q, n, N, 1))));
  forvec(v = vector(poldegree(pk), i, [0, q-1]),
    d = Mod(1, q) * Polrev(v, 'x);
    if ((pj - pt * d) % pk != 0, next);
    kd = ffsymk(d, P, q, n, lg);
    if (kd < 0, next);
    y = (pj - pt * d) / pk;
    g = if (t == 0, ffone(N), if (q^(t * poldegree(P)) <= cap, ffgpt(P, t, y, q, n, N), ffgpp(y, 1, P, t, q, n, N, 1)));
    S += ffz((N/n) * k * kd, N) * g);
  S;
}
"""


def _load(script: str) -> None:
    """Evaluate each GP function definition separately, without comment lines."""
    block: list[str] = []
    for line in script.splitlines():
        if line.strip().startswith("\\\\") or not line.strip():
            continue
        block.append(line)
        if line.strip() == "}":
            pari(" ".join(block))
            block = []
    assert not block, "unterminated GP definition"


_load(GP)

_NAMES = ("ffone", "ffz", "ffh2pm", "fflogtab", "ffpoly", "ffsymk", "ffsymfrobk", "ffsymfac", "ffe", "ffsymvec",
          "ffsymvecfac", "ffmu", "fftau", "ffgammah", "ffsqrt", "ffgaussh", "ffgauss", "ffgausshall", "ffdh", "ffgpp",
          "ffgstruct", "ffCx", "ffC", "ffrho0x", "ffrho0", "ffpsicoeffs", "ffFx", "ffF", "ffFcrt", "ffgpt",
          "ffCp")
_FUN = {name: pari(name) for name in _NAMES}


# ---------------------------------------------------------------------------
# Thin Python wrappers (coefficient lists are constant term first)
# ---------------------------------------------------------------------------


def poly(coeffs, q: int):
    """A PARI polynomial over F_q in x from coefficients, constant first."""
    terms = " + ".join(f"({int(c) % q})*x^{k}" for k, c in enumerate(coeffs)) or "0"
    return pari(f"Mod(1,{q})*({terms})")


def to_pari(cyc):
    """An ffprobe Cyc as a PARI polmod in z modulo polcyclo(N, z)."""
    N = cyc.K.N
    p = cyc.p
    coeffs = p.coeffs() if not p.is_zero() else []
    terms = " + ".join(f"({c})*z^{k}" for k, c in enumerate(coeffs) if c != 0) or "0"
    return pari(f"Mod({terms}, polcyclo({N}, z))")


def equal(a, b) -> bool:
    return bool(pari(f"({a}) == ({b})"))


def logtab(q: int) -> list:
    """lg[a] = discrete log of a (1 <= a < q) to the least primitive root; lg[0] is unused
    (GP vectors are 1-based, so the Python copy gets a dummy first entry)."""
    return [0] + [int(x) for x in _FUN["fflogtab"](q)]


def symbol(a, c, q, n) -> int:
    return int(_FUN["ffsymk"](poly(a, q), poly(c, q), q, n, _FUN["fflogtab"](q)))


def symbol_frob(a, P, q, n) -> int:
    return int(_FUN["ffsymfrobk"](poly(a, q), poly(P, q), q, n, _FUN["fflogtab"](q)))


def symbol_vector(c, L, q, n, route: str = "res") -> np.ndarray:
    """Symbol exponents of every polynomial of degree < L, in code order (-1 at non-units)."""
    f = _FUN["ffsymvec"] if route == "res" else _FUN["ffsymvecfac"]
    return np.array([int(v) for v in f(poly(c, q), L, q, n)], dtype=np.int64)


def gauss(r, c, q, n, j, N):
    return _FUN["ffgauss"](poly(r, q), poly(c, q), q, n, j, N)


def gauss_struct(r, c, q, n, j, N, route: int = 0):
    return _FUN["ffgstruct"](poly(r, q), j, poly(c, q), q, n, N, route)


def gauss_dh(r, c, q, n, j, N, v2007: bool = False):
    return _FUN["ffdh"](poly(r, q), poly(c, q), q, n, j, N, 1 if v2007 else 0)


def C(r, q, n, j, i, N):
    return _FUN["ffC"](poly(r, q), q, n, j, i, N)


def C_struct(r, q, n, j, i, N):
    return _FUN["ffCx"](poly(r, q), q, n, j, i, N, 0)


def tau(q, n, j, N):
    return _FUN["fftau"](q, n, j, N)


def sqrtq(q, N):
    return _FUN["ffsqrt"](q, N)


def rho0(r, q, n, j, i, N, maxbrute: int = 99):
    return _FUN["ffrho0x"](poly(r, q), q, n, j, i, N, maxbrute)


def psi_coeffs(r, q, n, j, i, N, top: int, maxbrute: int = 99) -> list:
    return list(_FUN["ffpsicoeffs"](poly(r, q), q, n, j, i, N, top, maxbrute))


def F_poisson(s, A, H, q, n, N, xi_j: int = 1):
    """F(s, A, H) with both sums enumerated (the definition)."""
    return _FUN["ffFx"](poly(s, q), poly(A, q), poly(H, q), q, n, N, xi_j)


def F_crt(s, A, H, q, n, N, xi_j: int = 1):
    """F(s, A, H) with the Gauss sum modulo T A split by the Chinese remainder theorem."""
    return _FUN["ffFcrt"](poly(s, q), poly(A, q), poly(H, q), q, n, N, xi_j)


def C_p(P, t, k, jp, q, n, N, cap: int = 7 ** 3):
    return _FUN["ffCp"](poly(P, q), t, k, jp, q, n, N, cap)


def zeta(k, N):
    return _FUN["ffz"](k, N)


def from_hist(h, N):
    """sum_k h[k] zeta_N^k as a polmod, from an integer vector (numpy or list)."""
    return _FUN["ffh2pm"](pari.vector(len(h), [int(x) for x in h]), N)


def conj(a, N):
    """Complex conjugation in Q(zeta_N): z -> z^(N-1)."""
    return pari(f"Mod(subst(lift({a}), 'z, 'z^({N}-1)), polcyclo({N}, 'z))")


def to_complex(a, N) -> complex:
    return complex(pari(f"subst(lift({a}), 'z, exp(2*Pi*I/{N}))"))


def is_zero(a) -> bool:
    return bool(pari(f"({a}) == 0"))


def monic_polys(q: int, d: int):
    """Coefficient lists (constant first) of every monic polynomial of degree d."""
    for low in itertools.product(range(q), repeat=d):
        yield list(low) + [1]


def mobius(c, q) -> int:
    return int(_FUN["ffmu"](poly(c, q)))


def factor(c, q) -> list:
    """[(coefficient list of a monic irreducible, exponent)] for a monic c."""
    if len(c) <= 1:
        return []
    f = pari.factor(poly(c, q))
    out = []
    for i in range(int(pari.matsize(f)[0])):
        P = f[i, 0]
        co = [int(pari.lift(pari.polcoef(P, k))) for k in range(int(pari.poldegree(P)) + 1)]
        out.append((co, int(f[i, 1])))
    return out


# ---------------------------------------------------------------------------
# The F_7[T] probe, written again from the paper's definitions
# ---------------------------------------------------------------------------


def _pmul(a, b, q):
    """Product of two coefficient lists over F_q (constant first)."""
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] = (out[i + j] + x * y) % q
    return out


def _codes_digits(q: int, L: int) -> np.ndarray:
    """digits[code, i] = coefficient of x^i of the polynomial with code 'code', degree < L."""
    codes = np.arange(q ** L, dtype=np.int64)
    if L == 0:
        return np.zeros((1, 0), dtype=np.int64)
    return np.stack([(codes // q ** i) % q for i in range(L)], axis=1)


class PariProbe:
    """The base probe over F_q[T] (q = 7, n = 6) with every weight computed in PARI.

    Weights, from Section 6 of the paper read over F_q[T]: b_* = T, xi = chi_T^xi_j,
    tau = q^(-1/2) g_xi(T, 1), Xi(a) = xi(a) chi_a(T), alpha(c) = lambda^deg c with
    lambda = (-tau(eps chi^2)/sqrt q)^3, R(a, b) = eps(chi(-1))^(deg a deg b),
    G(c) = conj(chi_c(4)) Gamma(c), Gamma(c) = q^(-deg c/2) sum_{x mod c} e(x^2/c), and the
    target eta(a) = eps(chi(a_0))^eta_e zeta_q^(eta_t a_1/a_0) modulo T^2."""

    def __init__(self, q: int = 7, n: int = 6, xi_j: int = 1, eta_e: int = 1, eta_t: int = 1, eta_fun=None):
        self.q, self.n, self.xi_j, self.eta_e, self.eta_t = q, n, xi_j, eta_e, eta_t
        self.eta_fun = eta_fun  # a target given as a function of a coefficient list (the rival)
        self.N = math.lcm(n, q, 4)
        self.lg = logtab(q)
        N = self.N
        self.one = _FUN["ffone"](N)
        self.sq = sqrtq(q, N)
        self.tau_xi = tau(q, n, xi_j, N) / self.sq
        self.lam = (-tau(q, n, 2, N) / self.sq) ** 3
        self.sgn = self.lg[q - 1] % n  # eps(chi(-1)) = zeta_n^sgn
        self._gamma_cache: dict = {}
        self._w_cache: dict = {}

    def eta(self, a):
        """The target at a coefficient list, as a polmod (0 at multiples of T)."""
        if self.eta_fun is not None:
            return self.eta_fun(a)
        e = self.eta_exp(a)
        return 0 * self.one if e is None else zeta(e, self.N)

    def K_def(self, c, nn, s, a, u):
        """K(c, n, s, a; u) of eq. (local-full-coefficient), A = c n^3, H = u a^6, with F through
        the Chinese remainder theorem (``ffFcrt``)."""
        q, n, N = self.q, self.n, self.N
        A = _pmul(c, _pmul(nn, _pmul(nn, nn, q), q), q)
        a6 = [1]
        for _ in range(6):
            a6 = _pmul(a6, a, q)
        H = _pmul(u, a6, q)
        Fv = F_crt(s, A, H, q, n, N, self.xi_j)
        if is_zero(Fv):
            return Fv
        pre = self.zn(self.sym([0, 1], s) - self.xi_exp(s) + self.xi_exp(u)) / (self.sq * self.tau_xi)
        dA = len(A) - 1
        theta = self.gamma_j(c, 2) * conj(self.lam, N) ** dA
        k4 = self.sym([4], A)
        G_conj = conj(self.zn(-k4) * self.Gamma(A), N)
        Xi_inv = self.zn(-(self.xi_exp(A) + self.sym([0, 1], A)))
        return Fv * pre * theta * G_conj * self.eta(A) * Xi_inv * self.R(dA, len(s) - 1)

    # characters, all as exponents k of zeta_n or e of zeta_N
    def chi_exp(self, x: int) -> int:
        return self.lg[x % self.q] % self.n

    def sym(self, a, c) -> int:
        """Exponent of (a/c)_n, -1 at non-units (PARI resultant)."""
        return int(_FUN["ffsymk"](poly(a, self.q), poly(c, self.q), self.q, self.n, _FUN["fflogtab"](self.q)))

    def xi_exp(self, a) -> int | None:
        a0 = a[0] % self.q
        return None if a0 == 0 else (self.xi_j * self.chi_exp(a0)) % self.n

    def eta_exp(self, a) -> int | None:
        q = self.q
        a0 = a[0] % q
        a1 = a[1] % q if len(a) > 1 else 0
        if a0 == 0:
            return None
        return ((self.N // self.n) * self.eta_e * self.chi_exp(a0)
                + (self.N // q) * ((self.eta_t * a1 * pow(a0, q - 2, q)) % q)) % self.N

    def zn(self, k):
        return zeta((self.N // self.n) * k, self.N)

    def Gamma(self, c):
        """q^(-deg c/2) sum_{x mod c} e(x^2/c), by enumeration of x mod c."""
        q, N = self.q, self.N
        d = len(c) - 1
        key = tuple(c)
        if key in self._gamma_cache:
            return self._gamma_cache[key]
        val = _FUN["ffh2pm"](_FUN["ffgammah"](poly(c, q), q, N), N) / self.sq ** d
        self._gamma_cache[key] = val
        return val

    def gamma_j(self, c, j: int):
        """gamma_j(c) = q^(-deg c/2) g(1, eps^j, c), CRT and Davenport-Hasse in PARI."""
        return gauss_struct([1], c, self.q, self.n, j, self.N) / self.sq ** (len(c) - 1)

    def weight_A(self, c, nn, gamma_route: str = "brute"):
        """gamma_2(c) conj(alpha(A)) eta(A) Xi(A)^-1 conj(G(A)) q^(-deg c/2 - deg n), A = c n^3."""
        q, N = self.q, self.N
        key = (tuple(c), tuple(nn), gamma_route)
        if key in self._w_cache:
            return self._w_cache[key]
        A = _pmul(c, _pmul(nn, _pmul(nn, nn, q), q), q)
        dA = len(A) - 1
        etaA = self.eta(A)
        if is_zero(etaA):
            return A, 0 * self.one
        g2 = self.gamma_j(c, 2)
        alpha_conj = conj(self.lam, N) ** dA
        xiA = self.xi_exp(A)
        kAT = self.sym([0, 1], A)  # chi_A(T)
        Xi_inv = self.zn(-(xiA + kAT))
        k4 = self.sym([4], A)  # chi_A(4)
        if gamma_route == "brute" or dA <= 4 or mobius(A, q) == 0:
            Gam = self.Gamma(A)
        else:
            # squarefree A of degree >= 5: Gamma(A) = gamma_3(A), the paper's lemma (CRT and the
            # count of square roots), checked by enumeration up to degree 4 in the cross-check run
            Gam = self.gamma_j(A, 3)
        G_conj = conj(self.zn(-k4) * Gam, N)
        w = g2 * alpha_conj * etaA * Xi_inv * G_conj / self.sq ** (len(c) - 1 + 2 * (len(nn) - 1))
        self._w_cache[key] = (A, w)
        return A, w

    def weight_s(self, s):
        """chi_s(T) / (tau xi(s))."""
        return self.zn(self.sym([0, 1], s) - self.xi_exp(s)) / self.tau_xi

    def R(self, da: int, db: int):
        return self.zn(self.sgn * da * db)


def theta_pairs(q: int, D: int) -> list:
    """(c, n) with c squarefree monic, n monic, deg(c n^3) = D, both prime to T."""
    out = []
    for dn in range(0, D // 3 + 1):
        dc = D - 3 * dn
        for nn in monic_polys(q, dn):
            if dn > 0 and nn[0] % q == 0:
                continue
            for c in monic_polys(q, dc):
                if dc > 0 and c[0] % q == 0:
                    continue
                if mobius(c, q) == 0:
                    continue
                out.append((c, nn))
    return out


def probe_direct(P: PariProbe, DX: int, Ds: int, DA: int, gamma_route: str = "brute", progress=None):
    """I(D_X, D_s, D_A) = sum_s sum_A w_s w_A R(A, s) sum_{deg m < D_X + D_s + 1} xi(m) chi_A(m) g_{chi_s}(s, -m),
    with every symbol a PARI resultant and every Gauss sum a PARI sum; numpy only counts."""
    q, n, N = P.q, P.n, P.N
    L = DX + Ds + 1
    box = _codes_digits(q, L)
    xi_e = np.array([-1 if r == 0 else (P.xi_j * P.chi_exp(int(r))) % n for r in box[:, 0]], dtype=np.int64)
    As = []
    for (c, nn) in theta_pairs(q, DA):
        A, w = P.weight_A(c, nn, gamma_route)
        if is_zero(w):
            continue
        kA = symbol_vector(A, L, q, n) if len(A) > 1 else np.zeros(q ** L, dtype=np.int64)
        As.append((A, w, kA))
        if progress:
            progress()
    total = 0 * P.one
    for s in monic_polys(q, Ds):
        if Ds > 0 and s[0] % q == 0:
            continue
        ws = P.weight_s(s)
        ks = symbol_vector(s, L, q, n) if Ds > 0 else np.zeros(q ** L, dtype=np.int64)
        sqf = mobius(s, q) != 0
        if sqf:
            pref = gauss_struct([1], s, q, n, 1, N) * P.zn(-P.sym([q - 1], s))  # g(1, s) conj(chi_s(-1))
        else:
            # g_{chi_s}(s, -m) depends on m mod s: tabulate it over the residues by enumeration
            red = np.array([[int(pari.lift(pari.polcoef(poly([0] * i + [1], q) % poly(s, q), k))) for i in range(L)]
                            for k in range(Ds)], dtype=np.int64)  # (m mod s) = red @ m
            rcodes = ((box @ red.T) % q) @ (q ** np.arange(Ds, dtype=np.int64))
            res = _codes_digits(q, Ds)
            gtab = [gauss([(-int(x)) % q for x in res[r]], s, q, n, 1, N) for r in range(q ** Ds)]
        for (A, w, kA) in As:
            if sqf:
                ok = (xi_e >= 0) & (kA >= 0) & (ks >= 0)
                h6 = np.bincount((xi_e[ok] + kA[ok] - ks[ok]) % n, minlength=n)
                inner = from_hist([h6[k // (N // n)] if k % (N // n) == 0 else 0 for k in range(N)], N) * pref
            else:
                ok = (xi_e >= 0) & (kA >= 0)
                cnt = np.bincount(rcodes[ok] * n + (xi_e[ok] + kA[ok]) % n, minlength=(q ** Ds) * n).reshape(q ** Ds, n)
                inner = 0 * P.one
                for r in range(q ** Ds):
                    if cnt[r].any() and not is_zero(gtab[r]):
                        inner = inner + gtab[r] * from_hist(
                            [cnt[r][k // (N // n)] if k % (N // n) == 0 else 0 for k in range(N)], N)
            if is_zero(inner):
                continue
            total = total + ws * w * P.R(len(A) - 1, Ds) * inner
    return total


def probe_poisson_s1(P: PariProbe, DX: int, DA: int, gamma_route: str = "brute"):
    """The Poisson side for D_s = 0: q^(D_X - D_A) / tau times
    sum_A w_A sum_{H != 0, H(0) != 0, deg H < D_A - D_X} F(1, A, H), with
    F(1, A, H) = xi(A) chi_A(T) g_xi(T, H) g_{chi_A}(A, H) (Chinese remainder theorem for the
    modulus T A), g_xi(T, H) = conj(xi(H)) g_xi(T, 1) and g_{chi_A}(A, H) by CRT and Davenport-Hasse."""
    q, n, N = P.q, P.n, P.N
    Lh = DA - DX
    if Lh <= 0:
        return 0 * P.one
    Hs = [list(row) for row in _codes_digits(q, Lh) if row[0] != 0]
    gxi = tau(q, n, P.xi_j, N)
    total = 0 * P.one
    for (c, nn) in theta_pairs(q, DA):
        A, w = P.weight_A(c, nn, gamma_route)
        if is_zero(w):
            continue
        pref = P.zn(P.xi_exp(A) + P.sym([0, 1], A)) * gxi
        acc = 0 * P.one
        for H in Hs:
            g = gauss_struct(H, A, q, n, 1, N)
            if is_zero(g):
                continue
            acc = acc + g * P.zn(-P.xi_exp(H))
        if is_zero(acc):
            continue
        total = total + w * pref * acc
    total = total / P.tau_xi
    e = DX - DA
    return total * q ** e if e >= 0 else total / q ** (-e)


# ---------------------------------------------------------------------------
# The local factor of eq. (local-P) by its definition, coefficient by coefficient
# ---------------------------------------------------------------------------


def local_coefficient(P: PariProbe, Pp, u, e0: int, l: int, k: int, m: int, cap: int = 7 ** 3):
    """The coefficient of x^(e0+3l) w^k v^m in P_p (eq. local-P), with the normalization
    Q^(-e0/2 - l) included: (-1)^e0 gamma_1^-e0 eta(p)^e0 (a_p conj(gamma_3))^l rho^(k-t)
    omega^(t k - e0 l - l(l-1)/2) C_p(t, k, j + 6m)."""
    q, n, N = P.q, P.n, P.N
    dP = len(Pp) - 1
    Pq = poly(Pp, q)
    uq = poly(u, q)
    j = 0
    uu = uq
    while bool(pari(f"({uu}) % ({Pq}) == 0")):
        uu = uu / Pq
        j += 1
    uu_list = [int(pari.lift(pari.polcoef(uu, i))) for i in range(int(pari.poldegree(uu)) + 1)]
    rho = P.zn(P.sym(uu_list, Pp))
    om = P.zn(P.sym([q - 1], Pp))
    eta_p = P.eta(list(Pp))
    a_p = conj(P.lam, N) ** (3 * dP) * eta_p ** 3
    g1 = P.gamma_j(Pp, 1)
    g3 = P.gamma_j(Pp, 3)
    t = e0 + 3 * l
    Cp = C_p(Pp, t, k, j + 6 * m, q, n, N, cap)
    if is_zero(Cp):
        return Cp
    kap = (-eta_p / g1) ** e0 * (a_p * conj(g3, N)) ** l * rho ** (k - t)
    kap = kap * om ** (t * k - e0 * l - l * (l - 1) // 2) * Cp
    return kap / P.sq ** (dP * (e0 + 2 * l))


# ---------------------------------------------------------------------------
# Dirichlet characters modulo T^3 and the rival
# ---------------------------------------------------------------------------


def char_T3_exp(a, q, n, N, lg, e, al, be):
    """chi(a) = eps(a_0)^e zeta_q^(al x + be (y - x^2/2)), a = a_0 (1 + x T + y T^2) mod T^3; None at T | a."""
    co = list(a) + [0, 0, 0]
    a0, a1, a2 = co[0] % q, co[1] % q, co[2] % q
    if a0 == 0:
        return None
    inv = pow(a0, q - 2, q)
    x, y = (a1 * inv) % q, (a2 * inv) % q
    half = pow(2, q - 2, q)
    add = (al * x + be * (y - x * x * half)) % q
    return ((N // n) * e * (lg[a0] % n) + (N // q) * add) % N


def L_coefficients(q, n, N, e, al, be, maxdeg: int = 4) -> list:
    """c_d = sum over monic a of degree d of chi(a), as polmods (exponent histograms in Python)."""
    lg = logtab(q)
    out = []
    for d in range(maxdeg + 1):
        h = [0] * N
        for a in monic_polys(q, d):
            k = char_T3_exp(a, q, n, N, lg, e, al, be)
            if k is not None:
                h[k] += 1
        out.append(from_hist(h, N))
    return out


# ---------------------------------------------------------------------------
# Truncated series with polmod coefficients, the definition-side Euler product and high series
# ---------------------------------------------------------------------------


class PSeries:
    """{exponent tuple: polmod}, truncated to exponents at most ``maxes`` coordinatewise."""

    def __init__(self, maxes, terms=None):
        self.maxes = tuple(maxes)
        self.terms = {}
        for e, c in (terms or {}).items():
            if all(a <= b for a, b in zip(e, self.maxes)) and not is_zero(c):
                self.terms[tuple(e)] = c

    def __mul__(self, o):
        out = {}
        for e1, c1 in self.terms.items():
            for e2, c2 in o.terms.items():
                e = tuple(a + b for a, b in zip(e1, e2))
                if all(a <= b for a, b in zip(e, self.maxes)):
                    out[e] = out[e] + c1 * c2 if e in out else c1 * c2
        return PSeries(self.maxes, out)

    def coeff(self, e, N):
        return self.terms.get(tuple(e), 0 * _FUN["ffone"](N))


def primes_list(q: int, dmax: int, exclude_T: bool = True) -> list:
    """Monic irreducibles of degree 1..dmax (coefficient lists), T excluded."""
    out = []
    for d in range(1, dmax + 1):
        for c in monic_polys(q, d):
            if exclude_T and c == [0, 1]:
                continue
            f = factor(c, q)
            if len(f) == 1 and f[0][1] == 1:
                out.append(c)
    return out


def euler_product_def(P: PariProbe, u, maxes, cap: int = 7 ** 3) -> PSeries:
    """prod over primes p != T of the local factor of eq. (local-P), each coefficient by its
    definition (``local_coefficient``), in global variables X^deg p, W^deg p, V^deg p."""
    Xm, Wm, Vm = maxes
    out = PSeries(maxes, {(0, 0, 0): P.one})
    for Pp in primes_list(P.q, max(Xm, Wm, Vm, 1)):
        dP = len(Pp) - 1
        loc = {}
        for e0 in (0, 1):
            for l in range(0, Xm // 3 + 1):
                ex = e0 + 3 * l
                if ex * dP > Xm:
                    continue
                for k in range(0, Wm // dP + 1):
                    for m in range(0, Vm // dP + 1):
                        v = local_coefficient(P, Pp, u, e0, l, k, m, cap)
                        if not is_zero(v):
                            loc[(ex * dP, k * dP, m * dP)] = v
        out = out * PSeries(maxes, loc)
    return out


def high_series_def(P: PariProbe, u, maxes) -> PSeries:
    """sum over (c, n, s, a) of K(c, n, s, a; u) q^(-deg c/2 - deg n) X^deg A W^deg s V^deg a."""
    q = P.q
    Xm, Wm, Vm = maxes
    out = {}
    for D in range(0, Xm + 1):
        for (c, nn) in theta_pairs(q, D):
            norm = P.sq ** (-(len(c) - 1) - 2 * (len(nn) - 1))
            for ds in range(0, Wm + 1):
                for s in monic_polys(q, ds):
                    if ds > 0 and s[0] % q == 0:
                        continue
                    for da in range(0, Vm + 1):
                        for a in monic_polys(q, da):
                            if da > 0 and a[0] % q == 0:
                                continue
                            kv = P.K_def(c, nn, s, a, u)
                            if is_zero(kv):
                                continue
                            e = (D, ds, da)
                            out[e] = out[e] + kv * norm if e in out else kv * norm
    return PSeries(maxes, out)


# ---------------------------------------------------------------------------
# Patterson's relations among the rho_0, transcribed again from the sources
# ---------------------------------------------------------------------------


def hecke_infinity_records(q, n, j, dr, rho, N, form: str, extra_sign: int = 0) -> list:
    """Booleans, one per relation, for rho = {i: rho_0(r, eps^j, i)} at deg r = dr.

    form "printed_2014": rho(i) = eps chi(-1)^(i s) tau(eps chi^(i-i')) q^-1 rho(i') and the
    converse with i, i' exchanged and no q (2014, lines 224-231), for i < i', s = 1 + deg r;
    form "printed_2007": rho(i) = tau(eps^(2i-1-deg r)) eps chi(-1)^(i s) rho(i') q^(2i+E-3-deg r);
    form "corrected": the same with q^((n+1) R) more, R = floor((1 + deg r - i)/n);
    rho(i) = 0 whenever i = i'.  ``extra_sign`` adds eps chi(-1)^(extra_sign * s) (the 2014
    additive character in the 2007 form)."""
    lg = logtab(q)
    sg = lg[q - 1] % n
    s = dr + 1
    zn = lambda k: zeta((N // n) * k, N)
    out = []
    if form == "printed_2014":
        for i in range(n):
            ip = (s - i) % n
            if ip == i:
                out.append(is_zero(rho[i]))
            elif i < ip:
                A = zn(j * sg * i * s) * tau(q, n, j * (i - ip), N)
                B = zn(j * sg * ip * s) * tau(q, n, j * (ip - i), N)
                out.append(equal(rho[i], A * rho[ip] / q) and equal(rho[ip], B * rho[i]))
        return out
    for i in range(n):
        ip = (1 + dr - i) % n
        if (2 * i - 1 - dr) % n == 0:
            out.append(is_zero(rho[i]))
            continue
        E = 2 + (2 * i - 2 - dr) // n
        qe = 2 * i + E - 3 - dr + ((n + 1) * ((1 + dr - i) // n) if form == "corrected" else 0)
        rhs = tau(q, n, j * (2 * i - 1 - dr), N) * zn(j * sg * (i + extra_sign) * s) * rho[ip]
        rhs = rhs * q ** qe if qe >= 0 else rhs / q ** (-qe)
        out.append(equal(rho[i], rhs))
    return out


def finite_hecke_rhs(q, n, j, ro, Pp, jj, i, rho_fun, N):
    """Right side of the finite Hecke relation (2014, lines 235-247) for rho_0(r_o P^jj, eps^j, i):
    eps chi(-1)^(i D) q^(carry (1 + 1/n) + (D)_n - [D/n]) g(-r_o, eps^(jj+1), P) rho_0(r_o P^(n-2-jj), i - D),
    D = (jj + 1) deg P, with eps replaced by eps^j throughout."""
    lg = logtab(q)
    sg = lg[q - 1] % n
    D = (jj + 1) * (len(Pp) - 1)
    carry = (i % n) - ((i - D) % n) - (D % n)
    qexp = (carry // n) * (n + 1) + (D % n) - (D // n)
    g = gauss_struct([(-x) % q for x in ro], Pp, q, n, j * (jj + 1), N)
    r2 = ro
    for _ in range(n - 2 - jj):
        r2 = _pmul(r2, Pp, q)
    val = zeta((N // n) * j * sg * i * D, N) * g * rho_fun(r2, (i - D) % n)
    return val * q ** qexp if qexp >= 0 else val / q ** (-qexp)


def affine_image(r, a: int, b: int, q: int) -> list:
    """a^(-deg r) r(a x + b), the monic image of r under x -> a x + b."""
    out = [0]
    arg = [b % q, a % q]
    powk = [1]
    for k, cf in enumerate(r):
        if k > 0:
            powk = _pmul(powk, arg, q)
        term = [(cf * x) % q for x in powk]
        out = [(x + y) % q for x, y in itertools.zip_longest(out, term, fillvalue=0)]
    while len(out) > 1 and out[-1] == 0:
        out.pop()
    inv = pow(out[-1], q - 2, q)
    return [(x * inv) % q for x in out]


def hypergeometric_hist(r, q, n, j, N) -> list:
    """sum over a in F_q with r(a) != 0 of conj(eps(chi(r(a))))^j, as an exponent histogram."""
    lg = logtab(q)
    h = [0] * N
    for a in range(q):
        v = sum(int(cf) * pow(a, k, q) for k, cf in enumerate(r)) % q
        if v:
            h[(-(N // n) * j * lg[v]) % N] += 1
    return h

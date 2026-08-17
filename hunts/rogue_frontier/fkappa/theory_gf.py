"""Collapsed master formula for the corrected C_{kappa,i}.

Implements, in exact rational arithmetic, the operator-resolvent collapse of
the grand composition sum over Bian's corrected constants (derivation in
theory_notes.md, checkpoint 1):

    C_{kappa,i} = 2^{i-1} [X^{i-1}] S(X) / i!            (i >= 3),
    S(X) = - (1 + D_u)^{-1} g |_{s=0},

where g and D_u are built from the y-side closed form

    F = -(Dm + D2)/(1+A) + Cq B/(1+A)^2

(all ingredients Bell-polynomial expressions in the z-side power sums
s_r = sum mu_r(z_j), marks m_r = mu_r(z_marked), letters
mu_r(z) = (-1)^{r-1}(r-1)!(1-(z+1)^{-r}), jet coefficients
e(r,n) = (-1)^{r+n}(r+n-1)!).

Everything is graded: ring elements are {(X-order n, s-monomial): Fraction}
with X truncated at Nmax and s-degree <= X-order automatically.

Usage:
  .venv/bin/python hunts/rogue_frontier/fkappa/theory_gf.py --kappa 2 --nmax 20
      computes the row and validates against coefficients.json (corrected).
  --nmax beyond 20 extends the row (no reference values there; prints them).
  --json FILE  dump the row as exact rationals.
"""

import argparse
import json
import os
import sys
from fractions import Fraction
from math import comb, factorial

HERE = os.path.dirname(os.path.abspath(__file__))


# ---------------- graded ring: Q[s_1..s_R][[X]] / X^{Nmax+1} ---------------
# element: dict {(n, mono): Fraction}, mono = tuple of R exponents.

def rz():
    return {}


def radd(A, B):
    out = dict(A)
    for k, c in B.items():
        v = out.get(k, 0) + c
        if v:
            out[k] = v
        else:
            out.pop(k, None)
    return out


def rscale(A, c):
    if not c:
        return {}
    return {k: v * c for k, v in A.items()}


def rmul(A, B, nmax):
    out = {}
    for (n1, m1), c1 in A.items():
        for (n2, m2), c2 in B.items():
            n = n1 + n2
            if n > nmax:
                continue
            m = tuple(a + b for a, b in zip(m1, m2))
            k = (n, m)
            v = out.get(k, 0) + c1 * c2
            if v:
                out[k] = v
            else:
                out.pop(k, None)
    return out


def rconst(c, R):
    return {(0, (0,) * R): Fraction(c)} if c else {}


def rvar(r, R, xord=0, c=1):
    """the variable s_r (1-based) at X-order xord."""
    mono = tuple(1 if i == r - 1 else 0 for i in range(R))
    return {(xord, mono): Fraction(c)}


def rinv_one_plus(A, R, nmax):
    """(1 + A)^{-1} for A with min X-order >= 1 (X-adic geometric series)."""
    out = rconst(1, R)
    term = rconst(1, R)
    for _ in range(nmax):
        term = rscale(rmul(term, A, nmax), -1)
        if not term:
            break
        out = radd(out, term)
    return out


# ---------------- the model ----------------------------------------------

def build(kappa, nmax, verbose=False):
    R = kappa + 1                       # s_1 .. s_{kappa+1}
    marks = list(range(2, kappa + 3))   # m_2 .. m_{kappa+2}

    def e(r, n):
        return Fraction((-1) ** (r + n) * factorial(r + n - 1))

    # Bell polynomials Bell_a(s_1..s_a), a = 0..kappa
    Bell = [rconst(1, R)]
    for a in range(1, kappa + 1):
        acc = rz()
        for j in range(a):
            acc = radd(acc, rscale(rmul(Bell[j], rvar(a - j, R), nmax),
                                   comb(a - 1, j)))
        Bell.append(acc)

    # A, Cq (mark-free); B, D2, Dm (linear in marks: dict mark_index -> elem)
    A = rz()
    Cq = rz()
    B = {r: rz() for r in marks}
    D2 = {r: rz() for r in marks}
    Dm = {r: rz() for r in marks}
    for a in range(1, kappa + 1):
        # A += X^a Bell_a
        A = radd(A, {(n + a, m): c for (n, m), c in Bell[a].items()})
        for r in range(1, a + 1):
            co = comb(a, r)
            piece = {(n + a, m): c * co for (n, m), c in Bell[a - r].items()}
            Cq = radd(Cq, rmul(piece, rvar(r + 1, R), nmax))
            B[r + 1] = radd(B[r + 1], piece)
            D2[r + 2] = radd(D2[r + 2], piece)
        for r in range(1, a):
            for rp in range(1, a - r + 1):
                co = Fraction(factorial(a),
                              factorial(r) * factorial(rp)
                              * factorial(a - r - rp))
                piece = {(n + a, m): c * co
                         for (n, m), c in Bell[a - r - rp].items()}
                Dm[rp + 1] = radd(Dm[rp + 1],
                                  rmul(piece, rvar(r + 1, R), nmax))

    inv = rinv_one_plus(A, R, nmax)
    inv2 = rmul(inv, inv, nmax)
    CqInv2 = rmul(Cq, inv2, nmax)

    # F_r, coefficient of mark m_r
    F = {}
    for r in marks:
        t1 = rscale(rmul(radd(Dm[r], D2[r]), inv, nmax), -1)
        t2 = rmul(CqInv2, B[r], nmax)
        F[r] = radd(t1, t2)

    # jets: jet_r(eps) = sum_{n>=1} e(r,n) eps^n / n!, truncated at eps^kappa
    # jetpow[r][t] = coefficients (list over eps-order 0..kappa) of jet_r^t
    maxr = kappa + 2
    jet = {r: [Fraction(0)] + [e(r, n) / factorial(n)
                               for n in range(1, kappa + 1)]
           for r in range(1, maxr + 1)}

    def eps_mul(u, v):
        w = [Fraction(0)] * (kappa + 1)
        for i, ci in enumerate(u):
            if not ci:
                continue
            for j, cj in enumerate(v):
                if i + j <= kappa and cj:
                    w[i + j] += ci * cj
        return w

    jetpow = {}
    for r in range(1, maxr + 1):
        pows = [[Fraction(1)] + [Fraction(0)] * kappa]
        for _t in range(1, kappa + 1):
            pows.append(eps_mul(pows[-1], jet[r]))
        jetpow[r] = pows

    def substitute(H):
        """H(s + jet(eps)), truncated at eps^kappa.
        Returns list over eps-order 0..kappa of ring elements."""
        out = [rz() for _ in range(kappa + 1)]
        for (n, mono), c in H.items():
            # product over r of (s_r + jet_r)^{mono_r}
            cur = [(0, [Fraction(1)] + [Fraction(0)] * kappa, mono)]
            # walk variables one at a time
            acc = {((0,) * R): [Fraction(1)] + [Fraction(0)] * kappa}
            for ridx in range(R):
                mr = mono[ridx]
                if mr == 0:
                    continue
                nxt = {}
                for base_mono, epsvec in acc.items():
                    for t in range(0, min(mr, kappa) + 1):
                        if t and all(x == 0 for x in jetpow[ridx + 1][t]):
                            continue
                        newvec = epsvec if t == 0 else eps_mul(
                            epsvec, jetpow[ridx + 1][t])
                        if t and all(x == 0 for x in newvec):
                            continue
                        bm = list(base_mono)
                        bm[ridx] = mr - t
                        bm = tuple(bm)
                        co = comb(mr, t)
                        if bm in nxt:
                            nxt[bm] = [a + co * b for a, b in
                                       zip(nxt[bm], newvec)]
                        else:
                            nxt[bm] = [co * b for b in newvec]
                acc = nxt
            for bm, epsvec in acc.items():
                for eo, ec in enumerate(epsvec):
                    if ec:
                        k = (n, bm)
                        v = out[eo].get(k, 0) + c * ec
                        if v:
                            out[eo][k] = v
                        else:
                            out[eo].pop(k, None)
        return out

    def D_u(H):
        """unmarked-block operator: sum_n X^n n! [eps^n] H(s+jet)."""
        sub = substitute(H)
        out = rz()
        for n in range(1, kappa + 1):
            fn = factorial(n)
            for (xo, m), c in sub[n].items():
                if xo + n > nmax:
                    continue
                k = (xo + n, m)
                v = out.get(k, 0) + fn * c
                if v:
                    out[k] = v
                else:
                    out.pop(k, None)
        return out

    # g = D_M (sum_r F_r m_r) |_{m=0}
    #   = sum_n X^n n! [eps^n] sum_r F_r(s+jet(eps)) * jetm_r(eps)
    # jetm_r(eps) = jet_r(eps) (same letters, r in marks)
    g = rz()
    for r in marks:
        sub = substitute(F[r])
        # multiply (over eps) by jet_r, then extract
        for n in range(1, kappa + 1):
            fn = factorial(n)
            for a in range(0, n):
                jc = jet[r][n - a] if 1 <= n - a <= kappa else Fraction(0)
                if not jc:
                    continue
                for (xo, m), c in sub[a].items():
                    if xo + n > nmax:
                        continue
                    k = (xo + n, m)
                    v = g.get(k, 0) + fn * jc * c
                    if v:
                        g[k] = v
                    else:
                        g.pop(k, None)

    # resolvent: S = - sum_j (-1)^j D_u^j g |_{s=0}
    zero_mono = (0,) * R
    Scoef = [Fraction(0)] * (nmax + 1)
    h = g
    j = 0
    while h:
        sgn = -1 if j % 2 == 0 else 1   # -(-1)^j
        for (xo, m), c in h.items():
            if m == zero_mono:
                Scoef[xo] += sgn * c
        # prune: s-degree must be consumable by remaining X-orders
        h = {k: c for k, c in h.items() if sum(k[1]) <= nmax - k[0]}
        h = D_u(h)
        j += 1
        if verbose and j % 5 == 0:
            print(f"  resolvent depth {j}, terms {len(h)}", file=sys.stderr)

    # assemble the row
    row = {1: Fraction(1), 2: Fraction(-4)}
    for i in range(3, nmax + 2):
        n = i - 1
        if n <= nmax:
            row[i] = Fraction(2 ** (i - 1)) * Scoef[n] / factorial(i)
    return row


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--kappa", type=int, default=2)
    ap.add_argument("--nmax", type=int, default=19,
                    help="X-truncation; row computed through i = nmax+1")
    ap.add_argument("--json", default=None)
    ap.add_argument("--verbose", action="store_true")
    args = ap.parse_args()

    row = build(args.kappa, args.nmax, verbose=args.verbose)

    ref = {}
    path = os.path.join(HERE, "coefficients.json")
    if os.path.exists(path):
        data = json.load(open(path))
        ref = {int(i): Fraction(v) for i, v in
               data["corrected"]["rows"].get(str(args.kappa), {}).items()}

    print(f"kappa = {args.kappa}, row through i = {args.nmax + 1}")
    bad = 0
    for i in sorted(row):
        r = row[i]
        if i in ref:
            mark = "ok" if r == ref[i] else f"MISMATCH ref {ref[i]}"
            bad += r != ref[i]
        else:
            mark = "(new)"
        print(f"  C_{{{args.kappa},{i}}} = {r}   {mark}")
    if ref:
        print("VALIDATION:", "all reference values reproduced"
              if not bad else f"{bad} MISMATCHES")
    if args.json:
        with open(args.json, "w") as f:
            json.dump({str(i): str(v) for i, v in row.items()}, f, indent=1)
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())

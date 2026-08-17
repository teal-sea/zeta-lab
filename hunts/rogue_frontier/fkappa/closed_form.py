"""A closed generating identity for the corrected constants C(v,w).

Derivation sketch (all on the squarefree support, which carries the main
term; Lemma 8 of the thesis supplies the only asymptotic input):

1. From g_j = zeta^{(j)}/zeta and Taylor, sum_j g_j(s) y^j / j! =
   zeta(s+y)/zeta(s), so on squarefree n:
       sum_j b_j(n) y^j / j!  =  prod_{p | n} (e^{-y log p} - 1).

2. B((v_1..v_l), n) = b_{v_1} * ... * (b_{v_l} log)(n): on squarefree n
   the convolution distributes the primes of n over l blocks (empty
   blocks contribute 0 automatically since b_j(1) = 0), and the final
   log(d_l) is produced by a marker e^{lambda s} on the primes of block l,
   differentiated at lambda = 0.

3. Lemma 8 in integral form: for a monomial prod s_i^{h_i} of the slice
   polynomial, sum_{p_1<...<p_m, prod p <= x} prod log^{h_i} p_i
   ~ x L^{H-1} / (m! (H-1)!) * prod (h_i - 1)!  with
   prod (h_i-1)! = int_{(0,inf)^m} prod s^{h_i - 1} e^{-sum s} ds.
   The m-sum with 1/m! exponentiates the single-prime integral, and the
   per-prime integral is Frullani:
       int_0^inf (e^{-as}-1)(e^{-bs}-1) e^{-cs} ds/s
         = log[ (a+c)(b+c) / (c(a+b+c)) ].

Result: with variables y_1..y_l (v-blocks), z_1..z_k (w-blocks), markers
lambda (v-block l), mu (w-block k), and c_{jj'} = t - lambda*[j=l]
- mu*[j'=k],

    Phi = prod_{j=1..l} prod_{j'=1..k}
          (y_j + c_{jj'})(z_{j'} + c_{jj'}) /
          ( c_{jj'} (y_j + z_{j'} + c_{jj'}) ),

    C(v,w) = (prod_j v_j!)(prod_j w_j!) / (|v|+|w|+1)!
             * [coeff of prod y_j^{v_j} prod z_{j'}^{w_{j'}}]
               d/dlambda d/dmu Phi |_{lambda=mu=0, t=1}.

(The engine/thesis sign convention, with (-1)^{|v|+|w|} folded into
C(v,w), comes out automatically from the (e^{-ys}-1) factors.)

For single components (l = k = 1) this collapses to
Phi = 1 + yz/(c(y+z+c)) and yields the closed form

    C((a),(b)) = (-1)^{a+b} a b / (a+b-1).

This script verifies both statements against the independent symbolic
route of validate_pairs.true_C (and hence, transitively, against the
corrected engine).

Run:  .venv/bin/python hunts/rogue_frontier/fkappa/closed_form.py
"""

import sys
import os
from fractions import Fraction
from math import factorial as fact

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from validate_pairs import true_C

# ---- truncated multivariate polynomial arithmetic over Q ----------------
# monomial: tuple of exponents over variables (y_1..y_l, z_1..z_k, lam, mu)
# truncation: y_j <= v_j, z_j <= w_j, lam <= 1, mu <= 1.


class TPoly:
    def __init__(self, caps, d=None):
        self.caps = caps
        self.d = d or {}

    @classmethod
    def const(cls, caps, c):
        return cls(caps, {tuple(0 for _ in caps): Fraction(c)})

    @classmethod
    def var(cls, caps, idx, c=1):
        mono = tuple(1 if i == idx else 0 for i in range(len(caps)))
        return cls(caps, {mono: Fraction(c)})

    def add(self, other):
        d = dict(self.d)
        for m, c in other.d.items():
            d[m] = d.get(m, Fraction(0)) + c
            if not d[m]:
                del d[m]
        return TPoly(self.caps, d)

    def mul(self, other):
        caps = self.caps
        d = {}
        for m1, c1 in self.d.items():
            for m2, c2 in other.d.items():
                m = tuple(a + b for a, b in zip(m1, m2))
                if any(e > cap for e, cap in zip(m, caps)):
                    continue
                d[m] = d.get(m, Fraction(0)) + c1 * c2
        return TPoly(caps, {m: c for m, c in d.items() if c})

    def inv(self):
        """1/self, assuming constant term 1 + u with u nilpotent under
        truncation: geometric series."""
        caps = self.caps
        zero = tuple(0 for _ in caps)
        c0 = self.d.get(zero, Fraction(0))
        assert c0 != 0
        u = TPoly(caps, {m: -c / c0 for m, c in self.d.items() if m != zero})
        out = TPoly.const(caps, 1)
        term = TPoly.const(caps, 1)
        for _ in range(sum(caps)):
            term = term.mul(u)
            if not term.d:
                break
            out = out.add(term)
        return TPoly(caps, {m: c / c0 for m, c in out.d.items()})


def C_closed(v, w):
    """Evaluate the generating identity for C(v,w) by truncated series."""
    l, k = len(v), len(w)
    caps = list(v) + list(w) + [1, 1]   # y-caps, z-caps, lam, mu
    caps = tuple(caps)
    LAM, MU = len(v) + len(w), len(v) + len(w) + 1
    Phi = TPoly.const(caps, 1)
    one = TPoly.const(caps, 1)
    for j in range(l):
        for jp in range(k):
            # c = 1 - lam*[j=l-1] - mu*[jp=k-1]   (t = 1)
            c = TPoly.const(caps, 1)
            if j == l - 1:
                c = c.add(TPoly.var(caps, LAM, -1))
            if jp == k - 1:
                c = c.add(TPoly.var(caps, MU, -1))
            y = TPoly.var(caps, j)
            z = TPoly.var(caps, l + jp)
            num = y.add(c).mul(z.add(c))
            den = c.mul(y.add(z).add(c))
            Phi = Phi.mul(num).mul(den.inv())
    # coefficient of prod y^{v} z^{w} lam^1 mu^1
    target = tuple(list(v) + list(w) + [1, 1])
    coeff = Phi.d.get(target, Fraction(0))
    pref = 1
    for x in list(v) + list(w):
        pref *= fact(x)
    return coeff * Fraction(pref, fact(sum(v) + sum(w) + 1))


def main():
    print("single-component closed form C((a),(b)) = (-1)^(a+b) ab/(a+b-1),")
    print("checked against the generating identity and the independent "
          "symbolic route:")
    ok = True
    for a in range(1, 6):
        for b in range(1, a + 1):
            cf = C_closed((a,), (b,))
            pred = Fraction((-1) ** (a + b) * a * b, a + b - 1)
            tc = true_C((a,), (b,))
            good = cf == pred == tc
            ok &= good
            if not good:
                print(f"  ({a},{b}): identity {cf}, formula {pred}, "
                      f"symbolic {tc}  MISMATCH")
    print("  all a,b <= 5 agree" if ok else "  MISMATCHES above")

    print("\nmulti-component pairs, generating identity vs symbolic route:")
    battery = [
        ((1, 1), (1, 1)), ((2, 1), (3,)), ((1, 2), (3,)),
        ((2,), (1, 1)), ((3,), (1, 1, 1)), ((2, 1), (2, 1)),
        ((2, 2), (2,)), ((2, 1), (1, 1, 1)), ((3, 1), (2, 2)),
        ((3, 2), (2, 2, 1)), ((4, 1), (3, 2)), ((1, 1, 1, 1), (2, 2)),
    ]
    allok = True
    for v, w in battery:
        cf = C_closed(v, w)
        tc = true_C(v, w)
        mark = "ok" if cf == tc else "MISMATCH"
        allok &= cf == tc
        print(f"  C({v},{w}): identity {cf}, symbolic {tc}   {mark}")
    print("\nresult:", "generating identity confirmed on all tested pairs"
          if ok and allok else "MISMATCHES FOUND")
    return 0 if (ok and allok) else 1


if __name__ == "__main__":
    sys.exit(main())

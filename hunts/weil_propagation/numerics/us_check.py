"""Theory C4 prerequisite (U-S), checked from coefficients, exactly.

Theory RESULTS s7.1 (branch teal-sea/weil-propagation-theory, commit
8188609): the step that Dedekind zeta_{Q(sqrt -23)} passes and Epstein
(1,1,6) fails is
  (1) atoms only at prime powers: Lambda(n) = 0 unless n = p^k;
  (2) unitary local roots, with the checkable consequence
      |s_k(p)| <= d, s_k(p) = Lambda(p^k) / log p, d the degree (2 here).
Claimed: Dedekind passes both; Epstein fails (1) at n = 6 and (2) at n = 8.

Exact arithmetic: a_n = r(n) / r(1) is rational, log n = sum_p e_p log p,
so the recursion a_n log n = sum_{d | n} Lambda(d) a_{n/d} keeps every
Lambda(n) a rational combination of log p over primes p | n. "Lambda(n) = 0"
is then an exact statement (all rational coefficients zero), and
s_k(p) is the rational coefficient of log p in Lambda(p^k) (the other
coefficients must vanish; that is checked too). Representation counts from
zeta.epstein.epstein_representation_count (integers).

Writes us_check.json. Usage: us_check.py [nmax]   (default 200)
"""

from __future__ import annotations

import os
import sys
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import wp_common as W  # noqa: E402
from sympy import factorint  # noqa: E402
from zeta.epstein import epstein_representation_count as rep  # noqa: E402

NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 200
OUT = os.path.join(W.HERE, "us_check.json")
DEGREE = 2


def counts(kind: str, n: int) -> int:
    if kind == "epstein_1_1_6":
        return rep(n, (1, 1, 6))
    return W.dedekind_m23_count(n)


def log_vec(n: int) -> dict:
    return {p: Fraction(e) for p, e in factorint(n).items()}


def add(u: dict, v: dict, s: Fraction) -> dict:
    out = dict(u)
    for p, x in v.items():
        out[p] = out.get(p, Fraction(0)) + s * x
        if out[p] == 0:
            del out[p]
    return out


def lambdas(kind: str, nmax: int) -> dict:
    r1 = counts(kind, 1)
    a = {n: Fraction(counts(kind, n), r1) for n in range(1, nmax + 1)}
    lam = {1: {}}
    for n in range(2, nmax + 1):
        v = {p: a[n] * e for p, e in log_vec(n).items() if a[n] != 0}
        for d in range(2, n):
            if n % d == 0 and a[n // d] != 0:
                v = add(v, lam[d], -a[n // d])
        lam[n] = v
    return lam


def check(kind: str) -> dict:
    lam = lambdas(kind, NMAX)
    composite_atoms, tower, off_basis = [], {}, []
    for n in range(2, NMAX + 1):
        f = factorint(n)
        if len(f) > 1:
            if lam[n]:
                composite_atoms.append(n)
            continue
        (p, k), = f.items()
        extra = {q: x for q, x in lam[n].items() if q != p}
        if extra:
            off_basis.append(n)
        s = lam[n].get(p, Fraction(0))
        tower.setdefault(p, {})[k] = s
    violations = sorted(
        (p ** k, p, k, str(s)) for p, ks in tower.items() for k, s in ks.items() if abs(s) > DEGREE
    )
    return {
        "nmax": NMAX,
        "composite_atoms": composite_atoms,
        "first_composite_atom": composite_atoms[0] if composite_atoms else None,
        "prime_power_atoms_off_log_p": off_basis,
        "tower_violations_abs_s_gt_d": [list(v) for v in violations],
        "first_tower_violation": list(violations[0]) if violations else None,
        "towers_small_p": {str(p): {str(k): str(s) for k, s in sorted(tower[p].items())} for p in sorted(tower) if p <= 23},
        "passes_1_atoms_only_at_prime_powers": not composite_atoms,
        "passes_2_abs_s_le_d": not violations and not off_basis,
    }


def main():
    d = {"meta": {"note": __doc__.split("\n\n")[0], "degree": DEGREE}}
    for kind in ("dedekind_Q_sqrt_m23", "epstein_1_1_6"):
        d[kind] = check(kind)
        r = d[kind]
        print(kind, "(1)", r["passes_1_atoms_only_at_prime_powers"], "first composite atom", r["first_composite_atom"],
              "| (2)", r["passes_2_abs_s_le_d"], "first |s|>d", r["first_tower_violation"], flush=True)
        print("   towers p<=13:", {p: t for p, t in r["towers_small_p"].items() if int(p) <= 13})
        print("   composite atoms <= 60:", [n for n in r["composite_atoms"] if n <= 60])
    W.save(OUT, d)


if __name__ == "__main__":
    main()

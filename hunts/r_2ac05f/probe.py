"""Adjudicate the two conflicting kappa=2 form-factor tables.

Two directories in this laboratory carry a table of the same quantity, the
regular coefficients C_{2,i} of Bian's pair-correlation form factor for the
zeros of xi'' , and they disagree from i = 2 onward:

    hunts/higher_xi/C2_EXACT.json        1, -8, 24, -32, 64/3, ...
    hunts/rogue_frontier/fkappa/         1, -4,  4, -16, 52/3, ...
        (branch, commit 360c545, "corrected" mode, rows["2"])

This probe recomputes the row from the analytic identity, in code written
for this adjudication and importing neither hunt.  It is a third opinion,
not a rerun of either side.

THE DERIVATION
--------------
Write P = xi'/xi.  Then xi^(kappa) = Q_kappa(P) xi with

    Q_0 = 1,        Q_{kappa+1} = D Q_kappa + P Q_kappa,      D = d/ds,

so that, since log xi^(kappa) = log Q_kappa + log xi,

    R_kappa := xi^(kappa+1) / xi^(kappa) = P + D log Q_kappa.

Near the critical line and up to terms lower by a power of the height,
P = L + g with L = (1/2) log(T / 2 pi) treated as a constant and
g = zeta'/zeta.  Put x = 1/L and Qhat_kappa = Q_kappa / L^kappa.  Dividing
the recursion by L^{kappa+1} gives a recursion with no L in it at all:

    Qhat_0 = 1,     Qhat_{kappa+1} = x D Qhat_kappa + (1 + g x) Qhat_kappa,

and D log Q_kappa = D Qhat_kappa / Qhat_kappa, so

    R_kappa = L + g + D Qhat_kappa / Qhat_kappa =: L + sum_{j>=0} q_j x^j.

Sanity: Qhat_1 = 1 + g x and Qhat_2 = 1 + 2 g x + (g' + g^2) x^2, which is
the object hunts/higher_xi/C2_PROVENANCE.md writes down by hand.

THE ARITHMETIC ALGEBRA
----------------------
Each q_j is a finite combination of Dirichlet convolutions of the series
A_b(s) = sum_n Lambda(n) log^b(n) n^{-s}.  Represent the convolution
A_{b_1} * ... * A_{b_r} by the multiset word (b_1, ..., b_r).  Then

    g = -A_0                       -> the word (0,) with coefficient -1,
    product = concatenation of words,
    D (b_1,...,b_r) = - sum_j (b_1,...,b_j + 1,...,b_r)

because differentiating n^{-s} pulls down -log n = -(log n_1 + ... ).

THE PAIRING
-----------
The form factor's regular part is a mean square of these words,

    C_{kappa,i} = 2^{i-1} sum_{p+q=i-1} <q_p, q_q>,

with the basis pairing recorded in hunts/higher_xi/C2_EXACT.json,

    <(b_1..b_r),(d_1..d_r)> = sum_{sigma in S_r} prod_j (b_j+d_sigma(j)+1)!
                              / (2r + sum b + sum d - 1)!,

and zero on words of unequal length.  This pairing is the one ingredient
taken from a disputant rather than rederived here.  It is *kappa-independent*
by construction: it knows only about products of Lambda's, and nothing about
which derivative of xi produced them.  It is therefore fully calibrated by
the kappa = 1 row, which the literature fixes independently: Farmer and Gonek
(arXiv:0803.0425) give, for the zeros of xi',

    F_1 = |a| - 4 a^2 + sum_{k>=1} ((k-1)!/(2k)!) (2|a|)^{2k+1},

i.e. eleven exact rationals with four forced zeros among them.  A pairing
that is wrong cannot reproduce that row, and both disputants agree on it.

Nothing here is evidence for or against the Riemann hypothesis (docs/08).
"""

from __future__ import annotations

import json
from collections import defaultdict
from fractions import Fraction as F
from itertools import permutations
from math import factorial
from pathlib import Path

# --------------------------------------------------------------------------
# formal Dirichlet algebra on words


Series = dict  # word (tuple of ints, sorted) -> Fraction


def _add(target: Series, word: tuple[int, ...], coeff: F) -> None:
    key = tuple(sorted(word))
    new = target.get(key, F(0)) + coeff
    if new:
        target[key] = new
    else:
        target.pop(key, None)


def mul(a: Series, b: Series) -> Series:
    out: Series = {}
    for wa, ca in a.items():
        for wb, cb in b.items():
            _add(out, wa + wb, ca * cb)
    return out


def add(a: Series, b: Series) -> Series:
    out = dict(a)
    for w, c in b.items():
        _add(out, w, c)
    return out


def scale(a: Series, k: F) -> Series:
    return {w: c * k for w, c in a.items() if c * k}


def deriv(a: Series) -> Series:
    """d/ds, acting on a Dirichlet series written in the word basis."""
    out: Series = {}
    for word, coeff in a.items():
        for j in range(len(word)):
            bumped = word[:j] + (word[j] + 1,) + word[j + 1 :]
            _add(out, bumped, -coeff)
    return out


ONE: Series = {(): F(1)}          # the Dirichlet identity
G: Series = {(0,): F(-1)}         # g = zeta'/zeta = -A_0


# --------------------------------------------------------------------------
# power series in x = 1/L whose coefficients are Series


Poly = list  # index j -> Series, the coefficient of x^j


def p_mul(a: Poly, b: Poly, order: int) -> Poly:
    out = [dict() for _ in range(order + 1)]
    for i, ai in enumerate(a):
        if i > order or not ai:
            continue
        for j, bj in enumerate(b):
            if i + j > order or not bj:
                continue
            out[i + j] = add(out[i + j], mul(ai, bj))
    return out


def p_deriv(a: Poly) -> Poly:
    return [deriv(c) for c in a]


def p_shift(a: Poly, order: int) -> Poly:
    """multiply by x"""
    return ([dict()] + list(a))[: order + 1]


def p_inverse(a: Poly, order: int) -> Poly:
    """Formal inverse; requires the x^0 coefficient to be the identity."""
    assert a[0] == ONE, a[0]
    out = [dict() for _ in range(order + 1)]
    out[0] = ONE
    for n in range(1, order + 1):
        acc: Series = {}
        for k in range(1, n + 1):
            if a[k]:
                acc = add(acc, mul(a[k], out[n - k]))
        out[n] = scale(acc, F(-1))
    return out


def qhat(kappa: int, order: int) -> Poly:
    """Qhat_kappa = Q_kappa / L^kappa as a power series in x = 1/L."""
    q: Poly = [dict() for _ in range(order + 1)]
    q[0] = ONE
    one_plus_gx: Poly = [dict() for _ in range(order + 1)]
    one_plus_gx[0] = ONE
    one_plus_gx[1] = G
    for _ in range(kappa):
        q = [
            add(u, v)
            for u, v in zip(
                p_shift(p_deriv(q), order), p_mul(one_plus_gx, q, order)
            )
        ]
    return q


def dirichlet_coefficients(kappa: int, order: int) -> dict[int, Series]:
    """q_j in R_kappa = L + sum_j q_j x^j."""
    # one extra order internally: D Qhat / Qhat loses nothing, but the
    # product truncation is cleaner with slack.
    work = order + 2
    q = qhat(kappa, work)
    logderiv = p_mul(p_deriv(q), p_inverse(q, work), work)
    out = {j: dict(logderiv[j]) for j in range(order + 1)}
    out[0] = add(out[0], G)
    return out


# --------------------------------------------------------------------------
# the pairing


def pair_words(left: tuple[int, ...], right: tuple[int, ...]) -> F:
    if len(left) != len(right):
        return F(0)
    r = len(left)
    denom = factorial(2 * r + sum(left) + sum(right) - 1)
    total = 0
    for sigma in permutations(right):
        prod = 1
        for b, d in zip(left, sigma):
            prod *= factorial(b + d + 1)
        total += prod
    return F(total, denom)


_PAIR_CACHE: dict[tuple, F] = {}


def pair(a: Series, b: Series) -> F:
    total = F(0)
    for wa, ca in a.items():
        for wb, cb in b.items():
            if len(wa) != len(wb):
                continue
            key = (wa, wb)
            if key not in _PAIR_CACHE:
                _PAIR_CACHE[key] = pair_words(wa, wb)
            total += ca * cb * _PAIR_CACHE[key]
    return total


def form_factor(kappa: int, max_index: int) -> dict[int, F]:
    q = dirichlet_coefficients(kappa, max_index)
    out: dict[int, F] = {}
    for i in range(1, max_index + 1):
        total = F(0)
        for p in range(i):
            total += pair(q[p], q[i - 1 - p])
        out[i] = F(2) ** (i - 1) * total
    return out


# --------------------------------------------------------------------------
# the two disputed tables, and the external control


def farmer_gonek_row(max_index: int) -> dict[int, F]:
    """|a| - 4a^2 + sum_k ((k-1)!/(2k)!) (2|a|)^{2k+1}."""
    row = {i: F(0) for i in range(1, max_index + 1)}
    row[1] = F(1)
    if max_index >= 2:
        row[2] = F(-4)
    k = 1
    while 2 * k + 1 <= max_index:
        row[2 * k + 1] += F(factorial(k - 1), factorial(2 * k)) * F(2) ** (2 * k + 1)
        k += 1
    return row


HIGHER_XI_C2 = [
    "1", "-8", "24", "-32", "64/3", "-64/3", "1216/45", "-256/15",
    "1088/63", "-11776/945", "42496/4725",
]

FKAPPA_C2_CORRECTED = [
    "1", "-4", "4", "-16", "52/3", "16/3", "208/45", "-64/15",
    "-40/63", "-32/945", "3424/4725",
]

BIAN_FIGURE_10_1_KAPPA_2 = [
    "1", "-4", "4", "-16", "28", "16", "544/45", "-512/45",
    "-104/63", "-416/945", "6688/1575",
]


def main() -> None:
    n = 11
    control = form_factor(1, n)
    expected = farmer_gonek_row(n)
    control_ok = control == expected

    derived2 = form_factor(2, n)
    higher = {i: F(s) for i, s in enumerate(HIGHER_XI_C2, start=1)}
    fkappa = {i: F(s) for i, s in enumerate(FKAPPA_C2_CORRECTED, start=1)}
    figure = {i: F(s) for i, s in enumerate(BIAN_FIGURE_10_1_KAPPA_2, start=1)}

    # The load-bearing structural fact: the x^1 coefficient of Qhat_kappa.
    lead = {k: qhat(k, 2)[1] for k in (1, 2, 3)}

    print("kappa = 1 control against Farmer-Gonek:", "PASS" if control_ok else "FAIL")
    for i in range(1, n + 1):
        print(f"  i={i:2d}  derived {str(control[i]):>12}  FG {str(expected[i]):>12}")
    print()
    print("kappa = 2:")
    print(f"{'i':>3} {'this probe':>14} {'higher_xi':>14} {'fkappa corr':>14} {'Bian fig':>14}")
    for i in range(1, n + 1):
        print(
            f"{i:>3} {str(derived2[i]):>14} {str(higher[i]):>14} "
            f"{str(fkappa[i]):>14} {str(figure[i]):>14}"
        )
    print()
    print("Qhat_kappa x^1 coefficient (the multiplicity that decides i=2):")
    for k, series in lead.items():
        print(f"  kappa={k}: {series}   (kappa * g)")

    results = {
        "schema": 1,
        "question": "which kappa=2 form-factor table is right, higher_xi's or fkappa's",
        "method": "independent recomputation of R_kappa = P + D log Q_kappa "
                  "in a formal Dirichlet word algebra; pairing calibrated on "
                  "the Farmer-Gonek kappa=1 row",
        "external_control": {
            "row": "kappa = 1, Farmer-Gonek arXiv:0803.0425 closed form",
            "indices_checked": n,
            "passes": control_ok,
            "derived": [str(control[i]) for i in range(1, n + 1)],
            "expected": [str(expected[i]) for i in range(1, n + 1)],
        },
        "kappa_2": {
            "this_probe": [str(derived2[i]) for i in range(1, n + 1)],
            "higher_xi_C2_EXACT": HIGHER_XI_C2,
            "fkappa_corrected_row_2": FKAPPA_C2_CORRECTED,
            "bian_figure_10_1_row_2": BIAN_FIGURE_10_1_KAPPA_2,
            "agrees_with_higher_xi": derived2 == higher,
            "agrees_with_fkappa": derived2 == fkappa,
            "first_disagreement_with_fkappa": next(
                (i for i in range(1, n + 1) if derived2[i] != fkappa[i]), None
            ),
        },
        "multiplicity_witness": {
            "statement": "the x^1 coefficient of Qhat_kappa is kappa*g, so the "
                         "first arithmetic coefficient q_1 of R_kappa is "
                         "kappa * (Lambda log), and C_{kappa,2} = -4 kappa",
            "qhat_x1": {str(k): {str(w): str(c) for w, c in s.items()}
                        for k, s in lead.items()},
            "C_kappa_2_derived": {
                str(k): str(form_factor(k, 2)[2]) for k in (1, 2, 3)
            },
        },
        "verdict": (
            "higher_xi" if derived2 == higher
            else "fkappa" if derived2 == fkappa
            else "neither"
        ),
    }
    out = Path(__file__).with_name("results.json")
    out.write_text(json.dumps(results, indent=2) + "\n")
    print(f"\nwrote {out}")


if __name__ == "__main__":
    main()

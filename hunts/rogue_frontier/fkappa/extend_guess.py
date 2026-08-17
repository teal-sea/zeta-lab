"""Structure guessing on the extended corrected sequences (task d).

Searches for linear recurrences with polynomial coefficients over exact
rationals,

    sum_{j=0}^{R} p_j(n) a_{n+j} = 0,   deg p_j <= D,   R <= 6, D <= 6,

on the machinery-only subsequence i >= 5 of the corrected kappa = 2 row
and the corrected stable diagonal, and on transformed sequences:
a_i * i!, a_i / i!, a_i * 2^i, a_i / 2^i, a_i * (2i+1)!!/4^i, the odd and
even subsequences, and the partial-sum sequence.

Discipline: a candidate recurrence is fitted WITHOUT the last computed
term, must then verify on every fitted term with at least SURPLUS spare
equations, and must predict the held-out last term exactly. Only
candidates passing all three are reported as found.

Run:  .venv/bin/python hunts/rogue_frontier/fkappa/extend_guess.py
"""

import json
import os
import sys
from fractions import Fraction
from math import factorial as fact

import sympy as sp

HERE = os.path.dirname(os.path.abspath(__file__))

SURPLUS = 3
RMAX = 6
DMAX = 6


def load_sequences():
    with open(os.path.join(HERE, "coefficients.json")) as f:
        base = json.load(f)["corrected"]
    ext = {}
    p = os.path.join(HERE, "coefficients_ext.json")
    if os.path.exists(p):
        with open(p) as f:
            ext = json.load(f).get("corrected", {})
    row2 = dict(base["rows"]["2"])
    row2.update(ext.get("rows", {}).get("2", {}))
    diag = dict(base["diagonal"])
    diag.update(ext.get("diagonal", {}))
    out = {}
    for name, d in (("kappa2", row2), ("diagonal", diag)):
        keys = sorted(int(k) for k in d)
        out[name] = [(k, Fraction(d[str(k)])) for k in keys if k >= 5]
    return out


def dfact(n):
    """(n)!! for odd n."""
    r = 1
    while n > 1:
        r *= n
        n -= 2
    return r


def transforms(pairs):
    """Named transformed (index, value) sequences from (i, a_i) pairs."""
    yield "raw", pairs
    yield "a*i!", [(i, a * fact(i)) for i, a in pairs]
    yield "a/i!", [(i, a / fact(i)) for i, a in pairs]
    yield "a*2^i", [(i, a * 2 ** i) for i, a in pairs]
    yield "a/2^i", [(i, a / Fraction(2 ** i)) for i, a in pairs]
    yield "a*(2i+1)!!/4^i", [(i, a * dfact(2 * i + 1) / Fraction(4 ** i))
                             for i, a in pairs]
    odd = [(j, a) for j, (i, a) in enumerate(p for p in pairs
                                             if p[0] % 2 == 1)]
    even = [(j, a) for j, (i, a) in enumerate(p for p in pairs
                                              if p[0] % 2 == 0)]
    yield "odd-sub", odd
    yield "even-sub", even
    ps = []
    s = Fraction(0)
    for i, a in pairs:
        s += a
        ps.append((i, s))
    yield "partial-sums", ps


def prec_search(vals, idxs, rmax=RMAX, dmax=DMAX, surplus=SURPLUS):
    """Exact P-recursive search with the given surplus; returns
    (R, D, polys) for the first (lowest R, then D) verified fit on the
    FULL data passed in, else None."""
    N = len(vals)
    n = sp.symbols("n")
    for r in range(1, rmax + 1):
        for d in range(0, dmax + 1):
            nunk = (r + 1) * (d + 1)
            neq = N - r
            if neq < nunk + surplus:
                continue
            rows = []
            for e in range(neq):
                nn = idxs[e]
                row = []
                for j in range(r + 1):
                    for t in range(d + 1):
                        row.append(sp.Integer(nn) ** t
                                   * sp.Rational(vals[e + j].numerator,
                                                 vals[e + j].denominator))
                rows.append(row)
            M = sp.Matrix(rows)
            null = M.nullspace()
            if not null:
                continue
            vec = null[0]
            den = sp.lcm([sp.fraction(sp.nsimplify(x))[1] for x in vec])
            vec = [sp.nsimplify(x * den) for x in vec]
            polys = []
            for j in range(r + 1):
                p = sp.expand(sum(vec[j * (d + 1) + t] * n ** t
                                  for t in range(d + 1)))
                polys.append(p)
            if all(p == 0 for p in polys):
                continue
            return r, d, polys
    return None


def verify(polys, r, vals, idxs):
    """Check sum_j p_j(n) a_{n+j} = 0 on every window of the data."""
    n = sp.symbols("n")
    for e in range(len(vals) - r):
        nn = idxs[e]
        s = sum(polys[j].subs(n, nn)
                * sp.Rational(vals[e + j].numerator,
                              vals[e + j].denominator)
                for j in range(r + 1))
        if sp.simplify(s) != 0:
            return False
    return True


def predict_last(polys, r, vals, idxs):
    """Predict vals[-1] from the previous r terms via the recurrence;
    returns (ok, predicted or reason)."""
    n = sp.symbols("n")
    nn = idxs[-1 - r]
    lead = polys[r].subs(n, nn)
    if lead == 0:
        return False, "leading polynomial vanishes at prediction point"
    s = sum(polys[j].subs(n, nn)
            * sp.Rational(vals[-1 - r + j].numerator,
                          vals[-1 - r + j].denominator)
            for j in range(r))
    pred = sp.Rational(sp.simplify(-s / lead))
    ok = pred == sp.Rational(vals[-1].numerator, vals[-1].denominator)
    return ok, pred


def hunt(name, pairs, report):
    """Full discipline: fit without last term, verify, predict."""
    for tname, tp in transforms(pairs):
        if len(tp) < 8:
            report.append(f"  {name}/{tname}: too few terms "
                          f"({len(tp)}), skipped")
            continue
        idxs = [i for i, a in tp]
        vals = [a for i, a in tp]
        found = prec_search(vals[:-1], idxs[:-1], surplus=SURPLUS)
        if not found:
            report.append(f"  {name}/{tname}: no recurrence "
                      f"(R<={RMAX}, D<={DMAX}, surplus>={SURPLUS}, "
                      f"N={len(tp) - 1} fit terms)")
            continue
        r, d, polys = found
        okv = verify(polys, r, vals[:-1], idxs[:-1])
        okp, pred = predict_last(polys, r, vals, idxs)
        status = ("FOUND AND CONFIRMED" if (okv and okp is True)
                  else "REJECTED (failed "
                       + ("verification" if not okv else "prediction")
                       + ")")
        report.append(f"  {name}/{tname}: candidate order {r} degree {d} "
                      f"-> {status}")
        if okv and okp is True:
            for j, p in enumerate(polys):
                report.append(f"      p_{j}(n) = {p}")
        elif okv and okp is not True:
            report.append(f"      predicted {pred}, actual {vals[-1]}")


def main():
    global SURPLUS
    if len(sys.argv) > 1 and sys.argv[1].startswith("--surplus="):
        SURPLUS = int(sys.argv[1].split("=")[1])
        print(f"(surplus requirement lowered to {SURPLUS}; a fit passing "
              f"only the held-out prediction is weaker evidence)")
    seqs = load_sequences()
    report = []
    for name, pairs in seqs.items():
        imax = max(i for i, a in pairs)
        report.append(f"{name} (machinery terms 5 <= i <= {imax}, "
                      f"{len(pairs)} terms):")
        hunt(name, pairs, report)
    text = "\n".join(report)
    print(text)
    return text


if __name__ == "__main__":
    main()

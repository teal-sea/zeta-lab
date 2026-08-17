"""Structure analysis of the extended C_{kappa,i} tables (task 4).

Reads coefficients.json (written by bian_engine.py --extend) and reports:

(a) the kappa = 1 row against the Farmer-Gonek closed form
    |a| - 4a^2 + sum_k ((k-1)!/(2k)!) (2|a|)^{2k+1};

(b) for each stable diagonal (published i.e. skip/figure, and corrected):
    - the sequence, numerators/denominators factored,
    - successive ratios and |C_i|^{1/i} growth,
    - sympy find_linear_recurrence attempts on the raw sequence and on
      several factorial normalizations,
    - OEIS-ready query strings for the numerator sequences;

(c) the same recurrence attempts for the kappa = 2 row.

Run:  .venv/bin/python hunts/rogue_frontier/fkappa/analyze.py
"""

import json
import os
import sys
from fractions import Fraction
from math import factorial as fact

import sympy as sp

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from bian_engine import farmer_gonek_row, load_ckpt


def load():
    return load_ckpt()


def frac(s):
    return Fraction(s)


def seq_from(d):
    keys = sorted(int(k) for k in d)
    return [frac(d[str(k)]) for k in keys], keys


def fg_check(rows, imax):
    fg = farmer_gonek_row(imax)
    ok = all(frac(rows["1"][str(i)]) == fg[i]
             for i in range(1, imax + 1) if str(i) in rows["1"])
    return ok


def describe(name, seq, keys):
    print(f"\n--- {name} ---")
    for i, c in zip(keys, seq):
        num, den = c.numerator, c.denominator
        fn = sp.factorint(abs(num)) if num else {}
        fd = sp.factorint(den)
        fns = "*".join(f"{p}^{e}" if e > 1 else str(p)
                       for p, e in sorted(fn.items())) or "1"
        fds = "*".join(f"{p}^{e}" if e > 1 else str(p)
                       for p, e in sorted(fd.items())) or "1"
        sgn = "-" if num < 0 else " "
        print(f"  i={i:2d}  {str(c):>40s}   |num|={fns}  den={fds}{sgn}")
    print("  ratios C_{i+1}/C_i:",
          ", ".join(f"{float(seq[j+1]/seq[j]):.4f}" if seq[j] else "inf"
                    for j in range(len(seq) - 1)))
    print("  |C_i|^(1/i):",
          ", ".join(f"{float(abs(seq[j]))**(1.0/keys[j]):.4f}"
                    for j in range(len(seq)) if seq[j]))


def cfinite(vals):
    """Exact constant-coefficient linear recurrence search.
    Returns (order, coeffs) with x_n = sum_j coeffs[j] x_{n-1-j}, verified
    on all data with at least 3 surplus equations, else None."""
    N = len(vals)
    for d in range(1, (N - 3) // 2 + 1):
        A = sp.Matrix([[vals[n - 1 - j] for j in range(d)]
                       for n in range(d, 2 * d)])
        b = sp.Matrix([vals[n] for n in range(d, 2 * d)])
        try:
            sol = A.solve(b)
        except Exception:
            continue
        good = all(
            sum(sol[j] * vals[n - 1 - j] for j in range(d)) == vals[n]
            for n in range(d, N))
        if good and N - 2 * d >= 3:
            return d, list(sol)
    return None


def precursive(vals, keys, rmax=3, smax=3):
    """Exact P-recursive search: sum_{j=0}^r p_j(n) x_{n+j} = 0 with
    deg p_j <= s, verified on all data with >= 3 surplus equations."""
    N = len(vals)
    n = sp.symbols("n")
    for r in range(1, rmax + 1):
        for s in range(0, smax + 1):
            nunk = (r + 1) * (s + 1)
            neq = N - r
            if neq < nunk + 3:
                continue
            rows = []
            for idx in range(neq):
                nn = keys[idx]
                row = []
                for j in range(r + 1):
                    for t in range(s + 1):
                        row.append(sp.Integer(nn) ** t * vals[idx + j])
                rows.append(row)
            M = sp.Matrix(rows)
            null = M.nullspace()
            if not null:
                continue
            vec = null[0]
            polys = []
            for j in range(r + 1):
                p = sum(vec[j * (s + 1) + t] * n ** t
                        for t in range(s + 1))
                polys.append(sp.factor(sp.simplify(p)))
            if all(p == 0 for p in polys):
                continue
            return r, s, polys, len(null)
    return None


def try_recurrences(name, seq, keys):
    """Exact recurrence search on the sequence and on normalizations.
    Fits use only i >= 3 (i = 1, 2 are the special analytic constants)."""
    print(f"\n  recurrence attempts for {name} (using i >= 3):")
    pairs = [(i, c) for i, c in zip(keys, seq) if i >= 3]
    norms = {
        "raw": lambda i, c: c,
        "c*i!": lambda i, c: c * fact(i),
        "c*i!/2^i": lambda i, c: c * fact(i) / Fraction(2 ** i),
        "c*(2i)!/(4^i i!)": lambda i, c: c * fact(2 * i) //
            (Fraction(4 ** i) * fact(i)),
    }
    found = False
    for label, f in norms.items():
        vals = [sp.Rational(f(i, c).numerator, f(i, c).denominator)
                for i, c in pairs]
        kk = [i for i, c in pairs]
        cf = cfinite(vals)
        if cf:
            print(f"    {label}: C-finite order {cf[0]}: {cf[1]}")
            found = True
            continue
        pr = precursive(vals, kk)
        if pr:
            r, s, polys, dim = pr
            print(f"    {label}: P-recursive order {r}, degree {s} "
                  f"(nullspace dim {dim}):")
            for j, p in enumerate(polys):
                print(f"        p_{j}(n) = {p}")
            found = True
    if not found:
        print("    none found (C-finite to order ~N/2; P-recursive to "
              "order 3, degree 3)")


def oeis_queries(name, seq, keys):
    nums = [abs(c.numerator) for c in seq]
    dens = [c.denominator for c in seq]
    print(f"  OEIS query ({name} numerators): "
          + ",".join(str(n) for n in nums[:12]))
    print(f"  OEIS query ({name} denominators): "
          + ",".join(str(n) for n in dens[:12]))


def main():
    data = load()
    for mode in ("skip", "corrected"):
        if mode not in data:
            continue
        d = data[mode]
        imax = max(int(k) for k in d["diagonal"])
        print(f"\n================ mode: {mode} (i up to {imax}) "
              f"================")
        ok = fg_check(d["rows"], imax)
        print(f"(a) kappa=1 row == Farmer-Gonek closed form for "
              f"i <= {imax}: {ok}")
        if mode == "skip":
            ok2 = fg_check(d["rows_figure"], imax)
            print(f"    (figure assembly kappa=1 row too: {ok2})")

        which = ("diagonal_figure" if mode == "skip" else "diagonal")
        label = ("published stable diagonal (figure assembly, skip)"
                 if mode == "skip"
                 else "corrected stable diagonal (eq 10.1, corrected)")
        seq, keys = seq_from(d[which])
        describe(label, seq, keys)
        try_recurrences(label, seq, keys)
        oeis_queries(label, seq, keys)

        # kappa = 2 row
        rowsrc = d["rows_figure"] if mode == "skip" else d["rows"]
        if "2" in rowsrc:
            seq2, keys2 = seq_from(rowsrc["2"])
            describe(f"kappa=2 row ({mode})", seq2, keys2)
            try_recurrences(f"kappa=2 row ({mode})", seq2, keys2)
            oeis_queries(f"kappa=2 row ({mode})", seq2, keys2)


if __name__ == "__main__":
    main()

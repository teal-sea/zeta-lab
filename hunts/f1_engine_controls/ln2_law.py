"""The ln 2 degeneracy in `ontology/04_transcendental_matrix.py`, as a law.

`docs/15` §4 reports that the antisymmetric prime-graph matrix has a
degenerate eigenvalue locked onto `ln 2`, and its Reality Check answers that
this is a truncation artifact "caused by primes near the boundary cutoff N
(specifically with multiplicity `pi(N/2) - pi(N/3) - 1`)".  The artifact
reading is right.  The formula is the special case of a wider law, and it
stops holding at `N = 338`.

**The mechanism.**  Write `M` for the matrix: nodes `1..N`, and for every
node `u` and prime `p` with `u p <= N` an edge carrying `M[u, up] = +ln p`
and `M[up, u] = -ln p`.  Call `u` a *dead end* when `2u <= N < 3u`.  Two
facts follow immediately from that inequality: an edge above `u` needs a
prime `p <= N/u < 3`, so the only one is `u -> 2u` with weight `ln 2`, and an
edge above `2u` needs `p <= N/(2u) < 3/2`, so there is none.  Every dead end
therefore carries a private `ln 2` rung at the top of the graph.

Let `D` be the dead ends and put

    v = sum_{u in D} c_u (e_u + i e_{2u}).

On the support the eigen-relation is automatic for any coefficients `c`:
`(M v)_u = ln 2 * (i c_u) = i ln 2 * v_u`, and
`(M v)_{2u} = -ln 2 * c_u = i ln 2 * (i c_u) = i ln 2 * v_{2u}`.

Off the support it is not.  A node `w = u / q`, for `q` a prime dividing `u`,
receives `ln q * c_u`, and `v_w = 0` there, so the whole sum reaching `w` must
vanish.  (The doubled node `2u / q = 2w` receives `i` times the same sum, so
it repeats the condition rather than adding one.)  Collect those conditions
as the *hub incidence matrix* `C`, rows indexed by the hubs `w`, columns by
`D`, with `C[w, u] = ln q` whenever `w = u / q`.  Then

    multiplicity of the eigenvalue i ln 2  =  dim ker C  =  |D| - rank C.

**Why the quoted formula usually works.**  A prime `p` in `D` has the single
hub `1`, contributing the row `(ln p)_p`.  If every dead end were prime the
rank would be `1` and the multiplicity `|D| - 1 = pi(N/2) - pi(N/3) - 1`,
which is the quoted formula.  A composite dead end normally brings hubs of
its own that pin its coefficient to zero, so it changes neither side.  What
breaks the formula is a *closed* pattern among the composite dead ends: at
`N = 338` the semiprimes `121, 143, 169` over the prime pair `{11, 13}` share
the hubs `11` and `13` between them, three columns against two rows, and one
extra mode survives.  From there on the quoted formula undercounts.

Nothing here is modified in `ontology/`: the prototype is imported by path
and read.

Run:  .venv/bin/python hunts/f1_engine_controls/ln2_law.py --max-n 400
"""

from __future__ import annotations

import argparse
import importlib.util
import json
import math
from pathlib import Path

import numpy as np
from mpmath import mp
from sympy import primefactors, primepi

_REPO_ROOT = Path(__file__).resolve().parents[2]
_PROTOTYPE = _REPO_ROOT / "ontology" / "04_transcendental_matrix.py"

#: The eigenvalue under study, as a float.  The measured cluster sits within
#: ~1e-15 of it, which is why the default tolerance can be this tight.
LN2 = math.log(2)

#: First N at which the multiplicity quoted in `docs/15` departs from the
#: measured one.  Pinned by tests/test_f1_engine_controls.py.
FIRST_DEPARTURE = 338


def load_prototype():
    """Import `ontology/04_transcendental_matrix.py` by path, unmodified.

    Its stem is not a valid Python identifier, so it cannot be imported by
    name; the same dodge `tests/test_rogue_lab_controls.py` uses.
    """
    spec = importlib.util.spec_from_file_location("f1_prototype_04", _PROTOTYPE)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def dead_end_nodes(n_max: int) -> list[int]:
    """The `u` with `2u <= N < 3u`: nodes whose only edge upward is `x2`."""
    return [u for u in range(1, n_max + 1) if 2 * u <= n_max < 3 * u]


def hub_incidence(n_max: int) -> tuple[list[list[float]], list[int], list[int]]:
    """`(C, dead_ends, hubs)`: the conditions the `ln 2` modes must satisfy.

    `C[i][j] = ln q` when `hubs[i] = dead_ends[j] / q` for a prime `q`.  A
    dead end divisible by `q^2` reaches the same hub twice and the weights
    add, which is why the entry accumulates rather than assigns.
    """
    ends = dead_end_nodes(n_max)
    column = {u: j for j, u in enumerate(ends)}
    rows: dict[int, list[float]] = {}
    for u in ends:
        for q in primefactors(u):
            row = rows.setdefault(u // q, [0.0] * len(ends))
            row[column[u]] += math.log(q)
    hubs = sorted(rows)
    return [rows[w] for w in hubs], ends, hubs


def _rank(matrix: list[list[float]], dps: int = 40) -> int:
    """Rank by Gaussian elimination at `dps` digits.

    The entries are logarithms of primes, so there is no exact rational
    arithmetic to fall back on and a rank is a numerical judgment either way.
    Doing the elimination at 40 digits and calling anything below 1e-25 zero
    puts about twenty-five orders of magnitude between the decision and
    double-precision round-off, and `rank_agrees_with_numpy` checks the two
    routes against each other.
    """
    if not matrix:
        return 0
    with mp.workdps(dps):
        rows = [[mp.mpf(x) for x in row] for row in matrix]
        n_cols = len(rows[0])
        pivot_row = 0
        zero = mp.mpf("1e-25")
        for col in range(n_cols):
            best = max(range(pivot_row, len(rows)), key=lambda i: abs(rows[i][col]), default=None)
            if best is None or abs(rows[best][col]) < zero:
                continue
            rows[pivot_row], rows[best] = rows[best], rows[pivot_row]
            pivot = rows[pivot_row][col]
            for i in range(pivot_row + 1, len(rows)):
                factor = rows[i][col] / pivot
                if factor != 0:
                    rows[i] = [a - factor * b for a, b in zip(rows[i], rows[pivot_row])]
            pivot_row += 1
            if pivot_row == len(rows):
                break
        return pivot_row


def rank_agrees_with_numpy(n_max: int) -> bool:
    """True when the high-precision rank matches double-precision LAPACK."""
    matrix, _, _ = hub_incidence(n_max)
    if not matrix:
        return True
    return _rank(matrix) == int(np.linalg.matrix_rank(np.array(matrix), tol=1e-9))


def predicted_multiplicity(n_max: int) -> int:
    """`|D| - rank C`: the law derived in the module docstring."""
    matrix, ends, _ = hub_incidence(n_max)
    return len(ends) - _rank(matrix)


def measured_multiplicity(n_max: int, tol: float = 1e-9) -> int:
    """Eigenvalues of the built matrix within `tol` of `i ln 2`, counted once
    per conjugate pair (the positive imaginary parts only)."""
    matrix = load_prototype().build_antisymmetric_matrix(n_max)
    gammas = np.imag(np.linalg.eigvals(matrix))
    return int(np.sum(np.abs(gammas[gammas > 1e-9] - LN2) < tol))


def quoted_multiplicity(n_max: int) -> int:
    """`pi(N/2) - pi(N/3) - 1`, the formula recorded in `docs/15`.

    Returns a negative count for small `N`, which is one way of noticing that
    it was never meant as a definition.
    """
    return int(primepi(n_max // 2) - primepi(n_max // 3) - 1)


def scan(n_values: list[int]) -> list[dict]:
    """Measured, derived and quoted multiplicity at each `N`."""
    out = []
    for n_max in n_values:
        measured = measured_multiplicity(n_max)
        predicted = predicted_multiplicity(n_max)
        quoted = quoted_multiplicity(n_max)
        out.append(
            {
                "N": n_max,
                "measured": measured,
                "law_dim_ker_C": predicted,
                "docs15_formula": quoted,
                "law_agrees": measured == predicted,
                "docs15_agrees": measured == quoted,
                "n_dead_ends": len(dead_end_nodes(n_max)),
            }
        )
    return out


def first_departure(lo: int = 10, hi: int = 400) -> int | None:
    """Smallest `N >= lo` where the quoted formula misses the law, ignoring
    the small-`N` range in which the formula returns a negative count."""
    for n_max in range(lo, hi + 1):
        quoted = quoted_multiplicity(n_max)
        if quoted >= 0 and predicted_multiplicity(n_max) != quoted:
            return n_max
    return None


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--max-n", type=int, default=400)
    parser.add_argument("--step", type=int, default=10)
    parser.add_argument("--json", type=Path, default=None)
    args = parser.parse_args()

    rows = scan(list(range(30, args.max_n + 1, args.step)))
    print(f"{'N':>5} {'measured':>9} {'|D| - rank C':>13} {'docs/15':>8}")
    for row in rows:
        flag = "" if row["docs15_agrees"] else "   <- docs/15 undercounts"
        assert row["law_agrees"], f"the law failed at N={row['N']}"
        print(
            f"{row['N']:>5} {row['measured']:>9} {row['law_dim_ker_C']:>13} "
            f"{row['docs15_formula']:>8}{flag}"
        )
    departure = first_departure()
    print(f"\nfirst departure of the docs/15 formula: N = {departure}")
    print(f"law held at every N scanned: {all(r['law_agrees'] for r in rows)}")
    if args.json:
        args.json.write_text(
            json.dumps({"rows": rows, "first_departure": departure}, indent=2),
            encoding="utf-8",
        )
        print(f"wrote {args.json}")


if __name__ == "__main__":
    main()

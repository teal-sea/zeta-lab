"""Generate the two Lean certificates for DESIGN-kernel-negative-cell from Arb.

    .venv/bin/python hunts/weil_dh_line/gen_cert_lean.py

Rebuilds the band-64 even Davenport-Heilbronn Gram matrix in Arb (256 bits) at
two windows, takes the exact dyadic midpoints, scales them to integers, and
writes:

- `Cert65.lean`: the cell at c = 1541/50 (30.82), all 65 modes, with the
  rounded bottom eigenvector of the midpoint matrix;
- `Cert2x2.lean`: the principal block at modes (54, 55) at c = 55, a pipeline
  smoke test far from the 30.6 to 30.8 threshold;
- `cert_data.json`: the data both files carry, the entry-radius bounds, and the
  SHA-256 of each Lean file.

Each Lean file states, for its integer matrix `B = L * mid(M)` and vector `u`,
that `u^T B u < 0` and that `eDen * u^T B u + eNum * L * u^T u < 0`, where
`eNum / eDen` is the largest row sum of the entry radii. Both are proved by
`decide +kernel`. That margin is what makes `u^T G u < 0` for every symmetric
`G` within the radii of `mid(M)`: for such `G`,
`|u^T (G - mid M) u| <= sum_ij |u_i| |u_j| r_ij <= (max_i sum_j r_ij) u^T u`.
That inequality and the Arb enclosure of the true DH Gram entries are not
formalized; they are checked in exact rational arithmetic by
`test_cert_lean.py`. Uses only core Lean, so each file elaborates in seconds.
"""
from __future__ import annotations

import hashlib
import json
import os
import sys
from fractions import Fraction
from math import gcd

import mpmath as mp

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
NUM = os.path.join(ROOT, "hunts", "weil_propagation", "numerics")
WT = os.path.join(ROOT, "hunts", "rogue_frontier", "weil_trunc")
for _p in (NUM, WT, ROOT):
    if _p not in sys.path:
        sys.path.insert(0, _p)

from flint import arb_mat, ctx  # noqa: E402

import enclosures as EN  # noqa: E402
import wp_common as W  # noqa: E402

PREC = 256
N = 64
CELL_C = Fraction(1541, 50)
SMOKE_C = Fraction(55)
SMOKE_MODES = (54, 55)
U_DIGITS = 40          # the cell vector: bottom eigenvector rounded at 40 decimal places


def _dyadic(x) -> Fraction:
    m, e = x.man_exp()
    return Fraction(int(m)) * Fraction(2) ** int(e)


def gram(c: Fraction):
    """Midpoints and radius upper bounds of the even band-N DH Gram at window c."""
    ctx.prec = PREC
    bt = EN.BallTruncation(W.cq(c), N, kind="dh", prec=PREC)
    M = arb_mat(bt.even_matrix())
    n = M.nrows()
    mid = [[_dyadic(M[i, j].mid()) for j in range(n)] for i in range(n)]
    rad = [[_dyadic(M[i, j].rad()) for j in range(n)] for i in range(n)]
    return mid, rad


def _scale(mid):
    L = 1
    for row in mid:
        for x in row:
            L = L * x.denominator // gcd(L, x.denominator)
    B = [[int(x * L) for x in row] for row in mid]
    assert all(Fraction(B[i][j], L) == mid[i][j] for i in range(len(B)) for j in range(len(B)))
    return B, L


def qf(B, u) -> int:
    return sum(u[i] * sum(B[i][j] * u[j] for j in range(len(u))) for i in range(len(u)))


def cell():
    mid, rad = gram(CELL_C)
    B, L = _scale(mid)
    n = len(B)
    with mp.workdps(120):
        Am = mp.matrix(n, n)
        for i in range(n):
            for j in range(n):
                Am[i, j] = mp.mpf(mid[i][j].numerator) / mid[i][j].denominator
        E, V = mp.eigsy(Am)
        k = min(range(n), key=lambda i: E[i])
        u = [int(mp.nint(V[i, k] * 10 ** U_DIGITS)) for i in range(n)]
    e = max(sum(row) for row in rad)
    return {"name": "cell", "c": str(CELL_C), "N": N, "modes": list(range(n)), "L": L,
            "B": B, "u": u, "e": e}


def smoke():
    mid, rad = gram(SMOKE_C)
    i, j = SMOKE_MODES
    block = [[mid[i][i], mid[i][j]], [mid[j][i], mid[j][j]]]
    B, L = _scale(block)
    u = [B[1][1], -B[0][1]]                      # w = (d, -b): the form is d (a d - b^2)
    rb = [[rad[i][i], rad[i][j]], [rad[j][i], rad[j][j]]]
    e = max(sum(row) for row in rb)
    return {"name": "smoke_2x2", "c": str(SMOKE_C), "N": N, "modes": list(SMOKE_MODES), "L": L,
            "B": B, "u": u, "e": e}


def _lean_list(xs) -> str:
    return "[" + ", ".join(str(x) for x in xs) + "]"


def lean_file(cert, ns: str, doc: str) -> str:
    rows = ",\n    ".join(_lean_list(r) for r in cert["B"])
    n = len(cert["u"])
    e = cert["e"]
    return f'''/-
{doc}
-/
module

@[expose] public section

namespace ZetaLab.{ns}

/-- Dot product of two integer lists. -/
def dot (x y : List Int) : Int := (List.zipWith (· * ·) x y).foldl (· + ·) 0

/-- The quadratic form `u^T B u`, with `B` given by its rows. -/
def qf (B : List (List Int)) (u : List Int) : Int := dot u (B.map (fun row => dot row u))

/-- `L` times the exact Arb midpoints of the Gram entries (`L = {cert["L"]}`). -/
def B : List (List Int) :=
  [{rows}]

/-- The test vector. -/
def u : List Int := {_lean_list(cert["u"])}

/-- An upper bound for the largest row sum of the Arb entry radii, `eNum / eDen`. -/
def eNum : Int := {e.numerator}
def eDen : Int := {e.denominator}
def L : Int := {cert["L"]}

/-- `B` is a symmetric `{n} x {n}` array and `u` has `{n}` entries. -/
def shapeOK : Bool :=
  B.length == {n} && B.all (fun row => row.length == {n}) && u.length == {n} &&
    (List.range {n}).all (fun i => (List.range {n}).all (fun j =>
      (B.getD i []).getD j 0 == (B.getD j []).getD i 0))

theorem shape_ok : shapeOK = true := by decide +kernel

/-- The integer quadratic form of the midpoint matrix is negative at `u`. -/
theorem qf_neg : qf B u < 0 := by decide +kernel

/-- The margin: `u^T mid(M) u / u^T u + eNum / eDen < 0`, cleared of denominators. -/
theorem margin_neg : eDen * qf B u + eNum * L * dot u u < 0 := by decide +kernel

#print axioms shape_ok
#print axioms qf_neg
#print axioms margin_neg

end ZetaLab.{ns}
'''


CELL_DOC = """Kernel check of the algebraic step for the Davenport-Heilbronn negative cell
at window c = 1541/50 (30.82), band N = 64, even sector, 65 modes
(`hunts/weil_dh_line/DESIGN-kernel-negative-cell.md`). Generated by
`gen_cert_lean.py`; data and hashes in `cert_data.json`.

What is proved, by kernel evaluation (`decide +kernel`): for the integer matrix
`B = L * mid(M)`, where `mid(M)` are the exact dyadic midpoints of the Arb
enclosures of the Gram entries, and the listed vector `u`, `u^T B u < 0`, and
`u^T mid(M) u / u^T u + e < 0` with `e` an upper bound for the largest row sum
of the entry radii.

What is not proved here: that the true DH Gram entries lie in those Arb balls
(hardened, Arb), and the elementary inequality that turns the margin into
`u^T G u < 0` for every symmetric `G` within the radii (stated in
`gen_cert_lean.py`, checked in exact rationals by `test_cert_lean.py`). The
composite statement about the DH band form is therefore hardened, not
kernel-checked. This is the cell at c = 30.82 for N = 64 only; the cell at
c >= 30.617188 rests on N = 256 and on a nesting argument
(`hunts/weil_propagation/numerics/RESULTS.md` section 3.2), neither of which
this file touches."""

SMOKE_DOC = """Pipeline smoke test for the Davenport-Heilbronn certificate route: the
principal 2 x 2 block at modes (54, 55) of the band N = 64 even DH Gram at
window c = 55. Generated by `gen_cert_lean.py`; data in `cert_data.json`.

With `w = (d, -b)` the block's form is `d (a d - b^2)`, negative here. At c = 55
the form's lowest eigenvalue is far below zero; this is far from the 30.6 to 30.8
threshold and says nothing about the cell. It exercises the same generator,
data path and kernel check as `Cert65.lean` at a size that checks in seconds.
The same scope applies: the Arb enclosure and the perturbation inequality are
not formalized here."""


def main() -> dict:
    out = {}
    for cert, fname, ns, doc in ((cell(), "Cert65.lean", "DHCell65", CELL_DOC),
                                 (smoke(), "Cert2x2.lean", "DHSmoke2x2", SMOKE_DOC)):
        text = lean_file(cert, ns, doc)
        path = os.path.join(HERE, fname)
        with open(path, "w") as f:
            f.write(text)
        q = qf(cert["B"], cert["u"])
        uu = sum(x * x for x in cert["u"])
        e = cert["e"]
        out[cert["name"]] = {
            "lean": fname, "lean_sha256": hashlib.sha256(text.encode()).hexdigest(),
            "c": cert["c"], "N": cert["N"], "modes": cert["modes"],
            "L": str(cert["L"]), "u": [str(x) for x in cert["u"]],
            "e_num": str(e.numerator), "e_den": str(e.denominator), "e_float": float(e),
            "qf": str(q), "rayleigh_float": float(Fraction(q, cert["L"] * uu)),
            "margin_float": float(Fraction(q, cert["L"] * uu) + e),
        }
    with open(os.path.join(HERE, "cert_data.json"), "w") as f:
        json.dump(out, f, indent=1)
        f.write("\n")
    print(json.dumps({k: {kk: v[kk] for kk in ("rayleigh_float", "e_float", "margin_float")}
                      for k, v in out.items()}, indent=1))
    return out


if __name__ == "__main__":
    main()

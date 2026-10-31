"""The Lean certificates against Arb, in exact rational arithmetic.

`Cert65.lean` and `Cert2x2.lean` are checked by Lean's kernel in CI
(`full.yml`, "the DH negative-cell certificates"). These tests check what the
Lean does not: that the committed files are exactly what `gen_cert_lean.py`
writes from a fresh Arb build, and that the margin they prove does carry over to
every symmetric matrix inside the Arb balls.
"""

from __future__ import annotations

import hashlib
import json
import re
import sys
from fractions import Fraction
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
DATA = json.loads((HERE / "cert_data.json").read_text())

sys.path.insert(0, str(HERE))
import gen_cert_lean as gen  # noqa: E402  (a failed import must fail, not skip)


def _parse(text: str) -> dict:
    rows = dict(re.findall(r"def row(\d+) : List Int := \[([^\]]*)\]", text))
    B = [[int(x) for x in rows[str(i)].split(",")] for i in range(len(rows))]
    u = [int(x) for x in re.search(r"def u : List Int := \[([^\]]*)\]", text).group(1).split(",")]
    num = lambda name: int(re.search(rf"def {name} : Int := (-?\d+)", text).group(1))  # noqa: E731
    return {"B": B, "u": u, "eNum": num("eNum"), "eDen": num("eDen"), "L": num("L")}


def _qf(B, u):
    return sum(u[i] * sum(B[i][j] * u[j] for j in range(len(u))) for i in range(len(u)))


@pytest.fixture(scope="module")
def built():
    return {"cell": gen.cell(), "smoke_2x2": gen.smoke()}


@pytest.mark.parametrize("name,fname,ns,doc", [
    ("cell", "Cert65.lean", "DHCell65", "CELL_DOC"),
    ("smoke_2x2", "Cert2x2.lean", "DHSmoke2x2", "SMOKE_DOC"),
])
def test_the_committed_lean_is_what_arb_gives(built, name, fname, ns, doc):
    text = gen.lean_file(built[name], ns, getattr(gen, doc))
    committed = (HERE / fname).read_text()
    assert text == committed, f"{fname} differs from a fresh Arb build"
    assert hashlib.sha256(committed.encode()).hexdigest() == DATA[name]["lean_sha256"]


@pytest.mark.parametrize("name,fname", [("cell", "Cert65.lean"), ("smoke_2x2", "Cert2x2.lean")])
def test_the_margin_carries_to_every_matrix_in_the_balls(built, name, fname):
    """The kernel proves `eDen * u^T B u + eNum * L * u^T u < 0`. For symmetric G with
    |G_ij - mid_ij| <= r_ij, |u^T (G - mid) u| <= sum |u_i| |u_j| r_ij <= (max_i sum_j r_ij) u^T u,
    using |u_i u_j| <= (u_i^2 + u_j^2) / 2 and the symmetry of r. Checked here exactly, and at the
    worst-case G that pushes every entry to the edge of its ball against u."""
    d = _parse((HERE / fname).read_text())
    B, u, L = d["B"], d["u"], d["L"]
    n = len(u)
    assert all(B[i][j] == B[j][i] for i in range(n) for j in range(n))
    e = Fraction(d["eNum"], d["eDen"])
    assert e == built[name]["e"]
    uu = sum(x * x for x in u)
    q = _qf(B, u)
    assert q < 0 and d["eDen"] * q + d["eNum"] * L * uu < 0
    mid, rad = gen.gram(Fraction(built[name]["c"]))
    idx = built[name]["modes"]
    worst = sum(abs(u[a]) * abs(u[b]) * rad[i][j] for a, i in enumerate(idx) for b, j in enumerate(idx))
    assert worst <= e * uu
    assert Fraction(q, L) + worst < 0         # u^T G u < 0 for the worst G in the balls


def test_the_cell_is_the_recorded_one():
    c = DATA["cell"]
    assert (c["c"], c["N"], len(c["u"])) == ("1541/50", 64, 65)
    assert -4.85e-32 < c["rayleigh_float"] < -4.83e-32 and 5.4e-73 < c["e_float"] < 5.5e-73


def test_a_planted_digit_in_the_lean_data_is_caught(built):
    text = (HERE / "Cert65.lean").read_text()
    d = _parse(text)
    i, j = 5, 9
    old = str(d["B"][i][j])
    new = old[:-1] + str((int(old[-1]) + 1) % 10)
    head, tail = text.split("def row5 : List Int :=", 1)
    faulted = head + "def row5 : List Int :=" + tail.replace(old, new, 1)
    f = _parse(faulted)
    assert f["B"] != d["B"]
    assert not all(f["B"][a][b] == f["B"][b][a] for a in range(65) for b in range(65)) or \
        f["B"] != built["cell"]["B"]

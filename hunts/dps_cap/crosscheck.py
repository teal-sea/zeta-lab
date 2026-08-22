"""A second route to the same magnitude, not using epstein_completed's answer.

For a negative fundamental discriminant D the class forms partition the
representation counts:

    sum_{Q in Cl(D)} r_Q(n) = w * sum_{d | n} chi_D(d),          w = #units

so, since ``d = |D|/4`` is the same for every class,

    sum_{Q} Lambda_Q(s) = (sqrt(d)/pi)^s Gamma(s) * w * zeta(s) L(s, chi_D).

For D = -23: h = 3, w = 2, classes (1,1,6), (2,1,3), (2,-1,3), the last two
inverse to each other so their Epstein zetas coincide. The right-hand side is
built here from mpmath's ``zeta`` and Hurwitz zeta alone -- no code from
``zeta/epstein.py`` touches it -- so agreement is a check on the left-hand
side's scale at exactly the point under test, at each precision.

Run from the repository root; see the interpreter note in ``probe.py``.
"""

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
# portability fix on landing, 2026-08-21: this line hardcoded an
# absolute path into the author's home directory, which
# tests/test_repo_hygiene.py rejects. ROOT is already the repo root,
# so this resolves to the same directory on the machine that wrote it
# and works anywhere else.
for _sp in (ROOT / ".venv" / "lib").glob("python*/site-packages"):
    sys.path.append(str(_sp))

from mpmath import mp, mpc  # noqa: E402

from zeta.epstein import epstein_completed, epstein_reduced_forms  # noqa: E402

DISC = -23
UNITS = 2
S_RE, S_IM = "0.8", "85.7"
PRECISIONS = (20, 60)

#: quadratic residues mod 23, so chi_{-23}(n) = Legendre(n | 23) since -23 = 1 mod 4
_QR23 = {(a * a) % 23 for a in range(1, 23)}


def chi(a: int) -> int:
    a %= 23
    if a == 0:
        return 0
    return 1 if a in _QR23 else -1


def dirichlet_L(s):
    """L(s, chi_{-23}) through Hurwitz zeta values, at the working precision."""
    return mp.power(23, -s) * mp.fsum(
        chi(a) * mp.zeta(s, mp.mpf(a) / 23) for a in range(1, 23)
    )


def main() -> None:
    forms = epstein_reduced_forms(DISC)
    print("classes:", forms)
    rows = []
    for dps in PRECISIONS:
        with mp.workdps(dps + 15):
            s = mpc(S_RE, S_IM)
            d = mp.mpf(-DISC) / 4
            rhs = (
                mp.power(mp.sqrt(d) / mp.pi, s)
                * mp.gamma(s)
                * UNITS
                * mp.zeta(s)
                * dirichlet_L(s)
            )
        lhs = mp.fsum(epstein_completed(s, f, dps=dps) for f in forms)
        with mp.workdps(dps + 15):
            rel = abs(lhs - rhs) / abs(rhs)
            rows.append(
                {
                    "dps": dps,
                    "lhs_sum_over_classes": mp.nstr(abs(lhs), 12),
                    "rhs_zeta_times_L": mp.nstr(abs(rhs), 12),
                    "relative_defect": mp.nstr(rel, 6),
                }
            )
        print(
            f"dps={dps:>4}  |sum_Q Lambda_Q| = {rows[-1]['lhs_sum_over_classes']:<18}"
            f"  |RHS| = {rows[-1]['rhs_zeta_times_L']:<18}"
            f"  rel. defect = {rows[-1]['relative_defect']}"
        )

    (Path(__file__).parent / "crosscheck.json").write_text(
        json.dumps(
            {
                "identity": "sum_Q Lambda_Q(s) = (sqrt(d)/pi)^s Gamma(s) * w * zeta(s) L(s, chi_D)",
                "discriminant": DISC,
                "classes": [list(f) for f in forms],
                "point": f"{S_RE}+{S_IM}i",
                "rows": rows,
            },
            indent=2,
        )
        + "\n"
    )


if __name__ == "__main__":
    main()

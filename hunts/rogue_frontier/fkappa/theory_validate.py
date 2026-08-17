"""Validation battery for the theory work (theory_notes.md).

(a) single-component closed form C((a),(b)) = (-1)^{a+b} ab/(a+b-1),
    a,b <= 6, generating identity vs independent symbolic route;
(b) twelve multi-component corrected C(v,w), generating identity vs
    symbolic route;
(c) the collapsed master formula rows (theory_gf.build) against
    coefficients.json corrected rows for kappa = 2 and 3, i = 3..20,
    and the partial sums of the bound quantity.

Run:  .venv/bin/python hunts/rogue_frontier/fkappa/theory_validate.py
"""

import json
import os
import sys
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

from closed_form import C_closed            # noqa: E402
from validate_pairs import true_C           # noqa: E402
from theory_gf import build                 # noqa: E402


def main():
    failures = 0

    print("(a) singles a,b <= 6: identity vs (-1)^(a+b)ab/(a+b-1) vs symbolic")
    for a in range(1, 7):
        for b in range(1, a + 1):
            cf = C_closed((a,), (b,))
            pred = Fraction((-1) ** (a + b) * a * b, a + b - 1)
            tc = true_C((a,), (b,))
            ok = cf == pred == tc
            failures += not ok
            if not ok or (a, b) in ((6, 6), (6, 1)):
                print(f"    ({a},{b}): {cf} vs {pred} vs {tc} "
                      f"{'ok' if ok else 'FAIL'}")
    print("    all 21 pairs ok" if not failures else f"    {failures} FAIL")

    print("(b) multi-component pairs: identity vs symbolic")
    battery = [
        ((1, 1), (1, 1)), ((2, 1), (3,)), ((1, 2), (3,)),
        ((2,), (1, 1)), ((3,), (1, 1, 1)), ((2, 1), (2, 1)),
        ((2, 2), (2,)), ((2, 1), (1, 1, 1)), ((3, 1), (2, 2)),
        ((3, 2), (2, 2, 1)), ((4, 1), (3, 2)), ((1, 1, 1, 1), (2, 2)),
    ]
    nb = 0
    for v, w in battery:
        cf, tc = C_closed(v, w), true_C(v, w)
        ok = cf == tc
        nb += not ok
        print(f"    C({v},{w}) = {cf}   {'ok' if ok else f'FAIL vs {tc}'}")
    failures += nb
    print(f"    {len(battery) - nb}/{len(battery)} ok")

    print("(c) collapsed master formula vs corrected rows, i = 3..20")
    data = json.load(open(os.path.join(HERE, "coefficients.json")))
    for kappa in (2, 3):
        row = build(kappa, 19)
        ref = {int(i): Fraction(vv) for i, vv in
               data["corrected"]["rows"][str(kappa)].items()}
        bad = [i for i in range(3, 21) if row[i] != ref[i]]
        failures += len(bad)
        print(f"    kappa={kappa}: "
              + ("18/18 ok" if not bad else f"FAIL at {bad}"))
        S = Fraction(0)
        for i in sorted(ref):
            S += ref[i] * Fraction(1, (i + 1) * (i + 2))
        print(f"      bound at I=20: {float(1 - 2 * S):+.6f}")

    print("RESULT:", "ALL VALIDATIONS PASS" if not failures
          else f"{failures} FAILURES")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())

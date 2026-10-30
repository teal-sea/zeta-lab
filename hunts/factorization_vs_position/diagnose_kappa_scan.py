"""Reproduce the kappa-scan diagnosis without changing detector.py or family.py.

The commit that opened this note named no path. This file is that diagnostic.
It imports ``detector.py`` and ``family.py`` unchanged and prints the three
checks in ``DIAGNOSIS.md``: the real-part ratio, the kappa = 0 coefficients,
and the residue table at the two ends of the family.

    python hunts/factorization_vs_position/diagnose_kappa_scan.py
    python hunts/factorization_vs_position/diagnose_kappa_scan.py --ratios-only
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

# The hunt directory is not a package. Import its modules by path, as the
# experiment scripts do, and leave them unmodified.
_HERE = Path(__file__).resolve().parent
if str(_HERE) not in sys.path:
    sys.path.insert(0, str(_HERE))

from mpmath import mp  # noqa: E402

from detector import generalized_offline_residue  # noqa: E402
from family import (  # noqa: E402
    Z_kappa,
    f_kappa_coefficients,
    find_online_zeros_kappa,
)
from zeta.epstein import KAPPA_REF  # noqa: E402
from zeta.factorization import factorization_defect, log_derivative_coefficients  # noqa: E402

_HEIGHTS = (4.0, 12.3, 30.3, 50.0, 77.7)
_C_GRID = (20, 40, 60, 80, 86, 90, 95)
_T_MAX = 110.0
_N_MAX = 2000
_KAPPA_ENDS = (0.0, 1.0)


def dh_archimedean_bracket(r):
    return mp.re(mp.digamma(mp.mpf(3) / 4 + mp.mpc(0, 1) * r / 2)) + mp.log(5 / mp.pi)


def print_ratios(dps: int = 25) -> None:
    """The scanner returns Re(phase * f_kappa). Print that real part's ratio."""
    kappa_dh = mp.mpf(KAPPA_REF)
    print(f"KAPPA_REF = {KAPPA_REF}")
    print("t        Z(kappa=0)     Z(1)/Z(0)          1+KAPPA_REF")
    for t in _HEIGHTS:
        z0 = Z_kappa(t, 0.0, dps=dps)
        z1 = Z_kappa(t, 1.0, dps=dps)
        ratio = z1 / z0
        expected = 1 + float(kappa_dh)
        print(f"{t:7.1f}  {z0:14.8g}  {ratio:.16f}  {expected:.16f}")
    print(
        "The scanner's output is (1 + KAPPA_REF*kappa) times the kappa = 0 "
        "output. KAPPA_REF begins 0.284079. The factor is positive for kappa "
        "in [0, 1], so sign changes cannot depend on kappa."
    )


def print_coefficients() -> None:
    coeffs = f_kappa_coefficients(0.0, 12)
    print("n        " + " ".join(f"{n:2d}" for n in range(1, 13)))
    shown = []
    for n in range(1, 13):
        value = coeffs[n]
        shown.append(" 0" if abs(value) < 1e-12 else f"{value:+.0f}")
    print("f_0(n)  " + " ".join(shown))


def print_residue_table() -> None:
    for kappa in _KAPPA_ENDS:
        coeffs = f_kappa_coefficients(kappa, _N_MAX)
        defect = factorization_defect(coeffs, _N_MAX)
        zeros = find_online_zeros_kappa(kappa, t_max=_T_MAX, dps=15, step=0.1)
        b = [float(x) for x in log_derivative_coefficients(coeffs, _N_MAX)]
        print(f"kappa = {kappa:.1f}   defect = {float(defect):.4f}   online zeros = {len(zeros)}")
        print(f"{'c':>5} {'arith':>12} {'zeroside':>12} {'residue':>12}")
        for c in _C_GRID:
            row = generalized_offline_residue(
                c=float(c),
                b=b,
                archimedean_bracket_fn=dh_archimedean_bracket,
                online_zeros=zeros,
                has_pole=False,
                a=0.25,
                n_max=_N_MAX,
            )
            print(
                f"{row['c']:5.0f} {row['arithmetic']:12.4f} "
                f"{row['online_zeros']:12.4f} {row['residue']:12.4f}"
            )
        print()


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Reproduce the kappa-scan diagnosis from detector.py and family.py."
    )
    parser.add_argument(
        "--ratios-only",
        action="store_true",
        help="print the proportionality check and skip the residue table",
    )
    args = parser.parse_args(argv)
    print_ratios()
    print()
    print_coefficients()
    if not args.ratios_only:
        print()
        print_residue_table()
    return 0


if __name__ == "__main__":
    sys.exit(main())

"""Independent rival calculations for the de_branges mechanism.

The Hermite-Biehler defect is evaluated directly from public completed
functions.  No module from the mechanism or another hunt is imported.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from mpmath import mp

from zeta.core import xi
from zeta.epstein import (
    OFFLINE_ZERO_IM,
    OFFLINE_ZERO_RE,
    completed_dh,
    epstein_completed,
    shifted_completed,
)

FORM_116 = (1, 1, 6)
GAMMA_1 = "14.1347251417346937904572519836"
EPSTEIN_ZERO = ("0.9532604748", "16.2902157204")
SHIFT_DELTA = "0.1"


def completed(kind: str, s, dps: int = 55):
    if kind == "zeta":
        return xi(s, dps=dps)
    if kind == "dh":
        return completed_dh(s, dps=dps)
    if kind == "epstein":
        return epstein_completed(s, FORM_116, dps=dps)
    if kind == "wa":
        return shifted_completed(s, mp.mpf(1) / 4, dps=dps)
    if kind == "zeta_shift":
        return xi(s - mp.mpf(SHIFT_DELTA), dps=dps)
    raise ValueError(kind)


def hb_defect(kind: str, h, x, y, dps: int = 50):
    """Return log|E_h(conj z)| minus log|E_h(z)| for z=x+iy."""
    with mp.workdps(dps):
        h, x, y = mp.mpf(h), mp.mpf(x), mp.mpf(y)
        lower = mp.mpc(mp.mpf(1) / 2 + h - y, -x)
        upper = mp.mpc(mp.mpf(1) / 2 + h + y, -x)
        return mp.log(abs(completed(kind, lower, dps + 5))) - mp.log(
            abs(completed(kind, upper, dps + 5))
        )


def symmetry_defects(kind: str, dps: int = 50) -> dict:
    with mp.workdps(dps):
        s = mp.mpc("0.37", "7.25")
        value = completed(kind, s, dps + 5)
        fixed = completed(kind, 1 - s, dps + 5)
        result = {"fixed_half": mp.nstr(abs(value - fixed), 14)}
        if kind == "zeta_shift":
            delta = mp.mpf(SHIFT_DELTA)
            actual = completed(kind, 1 + 2 * delta - s, dps + 5)
            result["actual_center_0_6"] = mp.nstr(abs(value - actual), 14)
        return result


def rival_cell(kind: str, h_failure, h_control, x, beta, y="0.05") -> dict:
    with mp.workdps(50):
        zero = mp.mpc(beta, x)
        return {
            "h_failure": mp.nstr(mp.mpf(h_failure), 12),
            "h_control": mp.nstr(mp.mpf(h_control), 12),
            "x": mp.nstr(mp.mpf(x), 18),
            "y": mp.nstr(mp.mpf(y), 12),
            "failure_defect": mp.nstr(hb_defect(kind, h_failure, x, y), 20),
            "control_defect": mp.nstr(hb_defect(kind, h_control, x, y), 20),
            "zero_real_part": mp.nstr(mp.mpf(beta), 18),
            "zero_residual": mp.nstr(abs(completed(kind, zero, 55)), 14),
            "symmetry_defects": symmetry_defects(kind),
        }


def report() -> dict:
    with mp.workdps(50):
        return {
            "parameters": {"shift_delta": "0.1", "defect_y": "0.05", "dps": 50},
            "zeta_control": {
                "h": "0.1",
                "x": mp.nstr(mp.mpf(GAMMA_1), 18),
                "defect": mp.nstr(hb_defect("zeta", "0.1", GAMMA_1, "0.05"), 20),
            },
            "rivals": {
                "davenport_heilbronn": rival_cell(
                    "dh", "0.25", "0.375", OFFLINE_ZERO_IM, OFFLINE_ZERO_RE
                ),
                "epstein_1_1_6": rival_cell(
                    "epstein", "0.375", "0.5", EPSTEIN_ZERO[1], EPSTEIN_ZERO[0]
                ),
                "W_1_4": rival_cell("wa", "0.2", "0.3", GAMMA_1, "0.75"),
                "zeta_shift_delta_0_1": rival_cell(
                    "zeta_shift", "0.05", "0.15", GAMMA_1, "0.6"
                ),
            },
        }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", type=Path)
    args = parser.parse_args()
    payload = report()
    rendered = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    if args.write:
        args.write.write_text(rendered, encoding="utf-8")
    print(rendered, end="")


if __name__ == "__main__":
    main()

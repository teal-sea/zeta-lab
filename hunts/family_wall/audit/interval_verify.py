#!/usr/bin/env python3
"""Directed interval checks for reported witness values.

Every printed gap is interpreted as the exact decimal rational shown in the
JSON input.  mpmath's interval context then encloses all transcendental and
arithmetic rounding error.  This certifies the safe direction needed here:
the displayed upper endpoint really is an upper bound for W at that witness.
"""

from __future__ import annotations

import argparse
import decimal
import json
from pathlib import Path

import mpmath as mp


def endpoint(value, upper: bool, decimal_places: int = 30) -> str:
    """Format an interval endpoint with decimal-directed rounding."""
    raw = value._mpi_[1 if upper else 0]
    exact_binary = mp.mpf(raw)
    with decimal.localcontext() as context:
        context.prec = 200
        as_decimal = decimal.Decimal(mp.nstr(exact_binary, 150))
        quantum = decimal.Decimal(1).scaleb(-decimal_places)
        mode = decimal.ROUND_CEILING if upper else decimal.ROUND_FLOOR
        return format(as_decimal.quantize(quantum, rounding=mode), "f")


def iv_weight(x):
    iv = mp.iv
    q = 1 / iv.sqrt(2)

    def sinc(z):
        if 0 in z:
            raise ValueError("interval straddles removable sinc singularity")
        return iv.sin(z) / z

    kval = (sinc(q - iv.pi * x) + sinc(q + iv.pi * x)) / 2
    kzero = sinc(q)
    return (kval / kzero) ** 2


def verify_record(record: dict) -> dict:
    iv = mp.iv
    decimal_gaps = record.get("gaps_decimal") or [repr(x) for x in record["gaps"]]
    gaps = [iv.mpf(x) for x in decimal_gaps]
    n = len(gaps) + 1
    total = sum(gaps, iv.mpf(0))
    energy = iv.mpf(0)
    for s in range(1, n):
        coefficient = iv.mpf(2) / (n - s)
        for i in range(n - s):
            energy += coefficient * iv_weight(sum(gaps[i : i + s], iv.mpf(0)))

    q = 1 / iv.sqrt(2)
    h = iv.mpf(3) / 2 - q / iv.tan(q)
    cap = (n - 1) / h
    bound = h * (1 + energy)
    return {
        "n": n,
        "sum_lower": endpoint(total, False),
        "sum_upper": endpoint(total, True),
        "cap_lower": endpoint(cap, False),
        "cap_upper": endpoint(cap, True),
        "sum_cap_accepted": total.b <= cap.a,
        "W_lower": endpoint(energy, False),
        "W_upper": endpoint(energy, True),
        "bound_lower": endpoint(bound, False),
        "bound_upper": endpoint(bound, True),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("inputs", nargs="+", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--dps", type=int, default=80)
    args = parser.parse_args()
    mp.iv.dps = args.dps
    mp.mp.dps = args.dps + 30

    records = []
    for path in args.inputs:
        payload = json.loads(path.read_text())
        if "results" in payload:
            records.extend(payload["results"])
        elif "result" in payload and payload["result"].get("cap") is not None:
            records.append(payload["result"])
    verified = [verify_record(record) for record in sorted(records, key=lambda r: r["n"])]
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps({"interval_dps": args.dps, "results": verified}, indent=2) + "\n")
    print(json.dumps(verified, indent=2))


if __name__ == "__main__":
    main()

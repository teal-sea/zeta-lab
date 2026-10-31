"""The pre-registered two-radii rule: runs A and B must intersect at every n.

Reads ``artifacts/big/lambda_A.txt`` and ``lambda_B.txt`` (rigorous ``arb``
strings, one per n), checks each file's SHA-256 against its production
summary, and checks that the two balls overlap at every common n.  Writes
``artifacts/two_radii.json``.

Usage: .venv/bin/python hunts/li_dh_onset_hardened/compare.py
Nothing here is evidence about the Riemann Hypothesis.
"""

from __future__ import annotations

import hashlib
import json
import os
import sys

from flint import arb

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from balls import HERE, prec_guard  # noqa: E402

ART = os.path.join(HERE, "artifacts")


def load(tag: str) -> tuple[list, str]:
    summary = json.load(open(os.path.join(ART, f"production_{tag}.json")))
    path = os.path.join(HERE, summary["table"]["path"])
    raw = open(path, "rb").read()
    sha = hashlib.sha256(raw).hexdigest()
    if sha != summary["table"]["sha256"]:
        raise SystemExit(f"{tag}: table hash does not match its summary")
    with prec_guard(256):
        vals = [arb(line.split(" ", 1)[1].strip()) for line in raw.decode().splitlines()]
    return vals, sha


def main() -> None:
    a, sha_a = load("A")
    b, sha_b = load("B")
    n = min(len(a), len(b))
    disjoint, worst = [], 0.0
    with prec_guard(256):
        for i in range(n):
            if not a[i].overlaps(b[i]):
                disjoint.append(i + 1)
            worst = max(worst, float(abs(a[i].mid() - b[i].mid()).mid()))
    out = {"n_common": n, "sha256_A": sha_a, "sha256_B": sha_b,
           "disjoint_count": len(disjoint), "disjoint_first": disjoint[:50],
           "max_midpoint_difference": worst, "rule_holds": not disjoint}
    print(json.dumps(out, indent=1))
    with open(os.path.join(ART, "two_radii.json"), "w") as fh:
        json.dump(out, fh, indent=1)


if __name__ == "__main__":
    main()

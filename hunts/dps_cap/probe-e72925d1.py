"""One number at two precisions: |Lambda_Q(0.8 + 85.7i)| for Q = (2, 1, 3).

The question is what ``dps=min(dps, 20)`` costs in the rival interfaces of
``zeta/epstein.py`` (``epstein_interface``, ``count_zeros_box`` branch), by
evaluating the same completed Epstein zeta at the capped precision and at a
precision well above it.

Run from the repository root.  The worktree this was written in carried no
``.venv`` of its own, so the interpreter path is bootstrapped explicitly
below; delete the two ``sys.path`` lines and use ``.venv/bin/python`` in a
normal clone.
"""

import json
import sys
import time
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

from zeta.epstein import epstein_completed  # noqa: E402

FORM = (2, 1, 3)
S_RE, S_IM = "0.8", "85.7"
PRECISIONS = (20, 60, 100)


def main() -> None:
    rows = []
    for dps in PRECISIONS:
        with mp.workdps(dps + 25):
            s = mpc(S_RE, S_IM)
        t0 = time.perf_counter()
        value = epstein_completed(s, FORM, dps=dps)
        elapsed = time.perf_counter() - t0
        with mp.workdps(dps + 10):
            magnitude = abs(value)
            rows.append(
                {
                    "dps": dps,
                    "abs": mp.nstr(magnitude, min(dps, 25)),
                    "log10_abs": float(mp.log10(magnitude)),
                    "re": mp.nstr(mp.re(value), min(dps, 25)),
                    "im": mp.nstr(mp.im(value), min(dps, 25)),
                    "seconds": round(elapsed, 3),
                }
            )
        print(
            f"dps={dps:>4}  |Lambda_Q| = {rows[-1]['abs']:<30}"
            f"  log10 = {rows[-1]['log10_abs']:+.3f}  ({elapsed:.2f}s)"
        )

    out = {
        "point": f"{S_RE}+{S_IM}i",
        "form": list(FORM),
        "function": "zeta.epstein.epstein_completed",
        "cap_under_test": "dps=min(dps, 20) in epstein_interface.count_zeros_box",
        "rows": rows,
    }
    (Path(__file__).parent / "results.json").write_text(json.dumps(out, indent=2) + "\n")


if __name__ == "__main__":
    main()

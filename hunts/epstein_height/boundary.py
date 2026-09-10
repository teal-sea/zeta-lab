"""Cells inside the transition band, where the law is actually making a prediction.

The first surface was a rectangular grid, and most of its cells are pinned at
the oracle's ceiling or flat at zero: only twelve of ninety-eight sat in the
band where the predicted correct-digit count is strictly between the two, so
only twelve tested anything.  This run puts the precisions where the law says
the transition is, at a spread of target margins, so the residual is measured
on cells chosen to be informative rather than on whatever the grid happened to
hit.

Choosing cells from the prediction is legitimate for measuring the residual of
a law and would not be legitimate for deciding whether there is an effect at
all.  The rectangular grid already answered that question, and this run does
not revisit it.
"""
from __future__ import annotations

import json
from pathlib import Path

import law
import probe

ART = Path(__file__).resolve().parent / "artifacts"
MARGINS = (1, 3, 6, 10, 14)


def main() -> None:
    rows = []
    for form in [(1, 1, 4), (2, 1, 3)]:
        for t in (40.0, 60.0, 80.0, 100.0, 120.0):
            dpss = sorted({law.required_dps(5.0, t, m) for m in MARGINS})
            rows += probe.surface(form, [t], dpss, sigma=5.0, qmax=20000)
    (ART / "boundary.json").write_text(json.dumps(rows, indent=1), encoding="utf-8")
    print(f"-> {ART / 'boundary.json'} ({len(rows)} cells)")


if __name__ == "__main__":
    main()

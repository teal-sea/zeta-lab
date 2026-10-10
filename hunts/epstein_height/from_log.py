"""Rebuild surface.json from surface.log, and refuse when that would lose data.

**This file was written on a false premise and is kept with the premise
corrected, because deleting it would delete the record of the mistake.** It was
written mid-run, when the log ended partway through the third form and
`surface.json` did not yet exist, and its docstring said the run had been
"stopped by its own wall clock". The run then finished. `surface.log` carries all
120 cells, 40 per form for three forms, and ends with the probe's own success
line; `surface.json` is the probe's full-precision output, later merged with 38
boundary cells.

So a rebuild from the log is now a downgrade: the log's printed fields are
rounded and the JSON's are not, and the log has no boundary cells in it. The
module therefore **refuses** when the existing JSON has at least as many rows,
and says why. An independent audit found this; it had not fired because nobody
re-ran it after the probe finished.
"""
from __future__ import annotations

import json
import re
from pathlib import Path

ART = Path(__file__).resolve().parent / "artifacts"
LINE = re.compile(
    r"form=\((?P<form>[^)]*)\) t=\s*(?P<t>[\d.]+) dps=\s*(?P<dps>\d+) "
    r"rel_err=\s*(?P<err>[\d.eE+-]+) correct_digits=\s*(?P<cd>[\d.]+)")


def main() -> None:
    rows = []
    for line in (ART / "surface.log").read_text(encoding="utf-8").splitlines():
        m = LINE.search(line)
        if not m:
            continue
        rows.append({
            "form": [int(v) for v in m.group("form").split(",")],
            "sigma": 5.0,
            "t": float(m.group("t")),
            "dps": int(m.group("dps")),
            "relative_error": float(m.group("err")),
            "correct_digits": float(m.group("cd")),
        })
    dest = ART / "surface.json"
    if dest.exists():
        existing = json.loads(dest.read_text(encoding="utf-8"))
        if len(existing) >= len(rows):
            print(f"REFUSED: {dest.name} already holds {len(existing)} rows against "
                  f"{len(rows)} parseable from the log, and the log's fields are "
                  f"rounded where the JSON's are not. Nothing written.")
            return
    dest.write_text(json.dumps(rows, indent=1), encoding="utf-8")
    from collections import Counter
    c = Counter(tuple(r["form"]) for r in rows)
    print(f"{len(rows)} cells recovered; per form " + ", ".join(
        f"{k}:{v}" for k, v in c.items()))


if __name__ == "__main__":
    main()

"""Rebuild surface.json from surface.log.

The probe writes its JSON at the end, and the run that produced this surface
was stopped by its own wall clock partway through the third form.  Rather than
discard two complete forms, the printed lines are parsed back: they carry every
field the fit uses, and the log is the same object the JSON would have held.
Recorded here rather than done by hand, so the reconstruction is reproducible
and so it is obvious that the third form is partial.
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
    (ART / "surface.json").write_text(json.dumps(rows, indent=1), encoding="utf-8")
    from collections import Counter
    c = Counter(tuple(r["form"]) for r in rows)
    print(f"{len(rows)} cells recovered; per form " + ", ".join(
        f"{k}:{v}" for k, v in c.items()))


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Write report.py's rendered tables into PILOT.md and OWNER_MEMO.md between their markers.

Each `<!-- table:NAME -->` ... `<!-- /table:NAME -->` pair is replaced by the table
`report.markdown_tables(pilot.json)[NAME]`; nothing else in either document is touched.
The hunt test checks the same equality, so a document edited by hand drifts red.

Run: .venv/bin/python hunts/rung3_ball_production/render_docs.py
"""
from __future__ import annotations

import importlib.util
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent


def _report():
    spec = importlib.util.spec_from_file_location("rung3_ball_production_report",
                                                  HERE / "report.py")
    assert spec is not None and spec.loader is not None
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def render(text: str, tables: dict[str, str]) -> str:
    def sub(m: re.Match) -> str:
        name = m.group(1)
        if name not in tables:
            raise SystemExit(f"no rendered table named {name!r}")
        body = tables[name].strip("\n").rstrip()     # keep a nested block's indentation
        return f"<!-- table:{name} -->\n{body}\n<!-- /table:{name} -->"
    return re.sub(r"<!-- table:([a-z_]+) -->.*?<!-- /table:\1 -->", sub, text, flags=re.S)


def main() -> None:
    tables = _report().markdown_tables(json.loads((HERE / "pilot.json").read_text()))
    for doc in ("PILOT.md", "OWNER_MEMO.md"):
        path = HERE / doc
        path.write_text(render(path.read_text(), tables))
        print(f"rendered {doc}")


if __name__ == "__main__":
    main()

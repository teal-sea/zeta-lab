"""Hunt #148: render section 2 of VERIFICATION.md from results_second.json.

Every leaf of the cross-check output that pairs a count of checks with a count that held
(``checked``/``compared``/``moduli`` against ``agree``/``hold``/``all_routes_agree``/...)
becomes one row, as do boolean leaves and mismatch counts.  A row whose held count falls
short of its checked count, a false boolean or a nonzero mismatch count is marked ``short``:
whether that is a documented erratum (a misprinted formula the hunt recorded) or a failure to
reproduce is said in the prose under the table, not decided here.

    .venv/bin/python hunts/ff_probe/render_verification.py          # rewrite the table
    .venv/bin/python hunts/ff_probe/render_verification.py --check  # non-zero if stale
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
BEGIN = "<!-- results-table: begin (render_verification.py) -->"
END = "<!-- results-table: end -->"
TOTALS = ("checked", "compared", "moduli")
HELD = ("agree", "hold", "all_routes_agree", "vanish_above_R", "pari_crt_eq_pari_definition",
        "pari_definition_eq_ffprobe_factorization", "equal")
# A boolean or an [a, b] pair is a check only if its name says it compares; other booleans
# (``zero``, ``any_disc_zero``) are findings, listed but never marked short.
CHECK_WORDS = ("eq", "equal", "agree", "hold", "is_", "vanish", "same")


def is_check(name: str) -> bool:
    return any(w in name.lower() for w in CHECK_WORDS)


def rows(node, path=()):
    """Yield (path, held, total, ok) for every comparable leaf group."""
    if isinstance(node, dict):
        total_key = next((k for k in TOTALS if isinstance(node.get(k), int)), None)
        if total_key is not None:
            total = node[total_key]
            for k in HELD:
                if isinstance(node.get(k), int) and not isinstance(node.get(k), bool):
                    yield path + (k,), node[k], total, node[k] == total
            mm = node.get("mismatches")
            if isinstance(mm, int):
                yield path + ("mismatches",), mm, total, mm == 0
        for k in sorted(node):
            v = node[k]
            if k in TOTALS or k in HELD or k == "seconds":
                continue
            if k == "mismatches" and isinstance(v, int):
                continue
            if isinstance(v, bool):
                yield path + (k,), v, None, v or not is_check(k)
            elif (isinstance(v, list) and len(v) == 2 and is_check(k)
                  and all(isinstance(x, int) and not isinstance(x, bool) for x in v)):
                yield path + (k,), v[0], v[1], v[0] == v[1]
            elif isinstance(v, (dict, list)):
                yield from rows(v, path + (k,))
            elif isinstance(v, int) and path and path[-1] == "mismatches":
                yield path + (k,), v, 0, v == 0
    elif isinstance(node, list):
        for i, v in enumerate(node):
            if isinstance(v, (dict, list)):
                yield from rows(v, path + (str(i),))


def render(results: dict) -> str:
    out = ["| item | check | held / checked | |", "|---|---|---|---|"]
    n = short = 0
    for item in sorted(results):
        for path, held, total, ok in rows(results[item]):
            n += 1
            short += not ok
            where = ".".join(path) or "(item)"
            if total is None:
                val = "true" if held else "false"
            elif path[-1] == "mismatches" or (len(path) > 1 and path[-2] == "mismatches"):
                val = f"{held:,} mismatches" + (f" in {total:,}" if total else "")
            else:
                val = f"{held:,} / {total:,}"
            out.append(f"| `{item}` | `{where}` | {val} | {'' if ok else 'short'} |")
    secs = sum(float(v.get("seconds", 0)) for v in results.values() if isinstance(v, dict))
    out.append("")
    out.append(f"{len(results)} items, {n} rows, {short} marked short; {secs:,.1f} s of item time in total.")
    return "\n".join(out)


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--results", default=str(HERE / "results_second.json"))
    args = ap.parse_args(argv)
    table = render(json.loads(Path(args.results).read_text()))
    doc = HERE / "VERIFICATION.md"
    text = doc.read_text()
    a, b = text.index(BEGIN) + len(BEGIN), text.index(END)
    new = text[:a] + "\n" + table + "\n" + text[b:]
    if args.check:
        if new != text:
            print("VERIFICATION.md section 2 is stale; rerun render_verification.py", file=sys.stderr)
            return 1
        return 0
    doc.write_text(new)
    return 0


if __name__ == "__main__":
    sys.exit(main())

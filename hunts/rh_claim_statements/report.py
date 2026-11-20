"""Print the tables of RESULTS.md from claims.json and results.json.

    .venv/bin/python -m hunts.rh_claim_statements.report            # markdown to stdout

The numbers in RESULTS.md sections 2 to 5 are this script's output, not typed.
"""
from __future__ import annotations

import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
GRADE = {"complete_cover": "complete cover", "exact_finite": "exact, finite", "measured_range": "measured on a range"}


def _num(x, digits=4):
    if isinstance(x, bool) or x is None:
        return "-"
    if isinstance(x, (list, tuple)) and len(x) == 2 and all(isinstance(v, (int, float)) for v in x):
        return f"[{_num(x[0], digits)}, {_num(x[1], digits)}]"
    if isinstance(x, int):
        return str(x)
    if isinstance(x, float):
        if x == 0:
            return "0"
        return f"{x:.{digits}g}"
    return str(x)


def slack_value(r):
    """A single number for sorting: how far the stated constant is from the tightest one the test accepts."""
    s = r.get("slack")
    if isinstance(s, list):
        return float(s[0])
    if isinstance(s, (int, float)):
        return float(s)
    return None


def main():
    led = json.loads((HERE / "claims.json").read_text(encoding="utf-8"))
    res = json.loads((HERE / "results.json").read_text(encoding="utf-8"))
    claims = {c["id"]: c for c in led["claims"]}
    recs = res["claims"]
    print("| id | statement (archive name) | where | grade | cases | margin | slack | mutants rejected |")
    print("|---|---|---|---|---|---|---|---|")
    for r in recs:
        c = claims[r["id"]]
        where = c["path"].split("/")[-1] + ":" + str(c["line"])
        muts = r["mutants"]
        print(f"| {r['id']} | `{c['name']}` | {where} | {GRADE.get(r['grade'], 'FAILED' if r['holds'] is False else 'undecided')} | "
              f"{r['cases']} | {_num(r.get('margin'))} | {_num(r.get('slack'))} | {sum(m['rejected'] for m in muts)}/{len(muts)} |")
    print()
    s = res["summary"]
    print("Counts by grade:", ", ".join(f"{GRADE[g]}: {n}" for g, n in s["by_grade"].items()),
          f"(total {s['hold']} of {s['claims']} hold; failed: {s['fail'] or 'none'}; undecided: {s['undecided'] or 'none'}).")
    print(f"Mutants: {s['mutants_rejected']} of {s['mutants']} rejected. Run time {s['seconds']} s on one core.")
    print()
    print("By topic and grade:")
    topics = {}
    for r in recs:
        topics.setdefault(claims[r["id"]]["topic"], {}).setdefault(r["grade"], []).append(r["id"])
    for t, d in topics.items():
        print(f"- {t}: " + "; ".join(f"{GRADE[g]} {len(v)}" for g, v in d.items()))
    print()
    print("Sharpness, as recorded in the ledger and measured by the run:")
    for r in recs:
        c = claims[r["id"]]
        print(f"- {r['id']} `{c['name']}`: {c['sharpness']}. Tightest: {json.dumps(r.get('tightest'), ensure_ascii=False)[:160]}; "
              f"sharp constant {_num(r.get('sharp_constant'), 7)}; tested range: {r.get('tested_range', 'the whole stated domain')}.")
    if "decoys" in res:
        print()
        print("Decoys:")
        for k, d in res["decoys"].items():
            body = {kk: vv for kk, vv in d.items() if kk not in ("reading",)}
            print(f"- {k}: {json.dumps(body, ensure_ascii=False)[:700]}")


if __name__ == "__main__":
    main()

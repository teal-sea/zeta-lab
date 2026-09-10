"""A second, disjoint blind sample, for validating the repaired classifier.

The first sample of thirty rows was used to find two structural defects in
`classify.py`, so the agreement figure recomputed against it after the repair is
fitted, not measured.  This draws a fresh stratified sample from the rows the
first one did not touch, so a second blind audit is an independent test of
`classify2.py` rather than a re-run of the exam it was tuned on.

Stratification is against the repaired classifier's own strict labels, half
positive and half negative, so agreement is not inflated by an unbalanced draw.
The key is written to a path outside the repository.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ART = HERE / "artifacts"
N_PER_ARM = 15


def main() -> None:
    out_key = Path(sys.argv[1]) if len(sys.argv) > 1 else ART / "audit_key2_sample.json"
    rows = json.loads((ART / "classified2.json").read_text(encoding="utf-8"))
    already = {r["commit"] for r in
               json.loads((ART / "audit_sample.json").read_text(encoding="utf-8"))}

    events = [(r["directory"], e) for r in rows for e in r["events"]
              if e["sha"][:12] not in already]
    pos = sorted([x for x in events if x[1]["strict"]], key=lambda x: x[1]["sha"])
    neg = sorted([x for x in events if not x[1]["strict"]], key=lambda x: x[1]["sha"])

    def stride(xs, n):
        if len(xs) <= n:
            return xs
        step = len(xs) / n
        return [xs[int(i * step)] for i in range(n)]

    sample = stride(pos, N_PER_ARM) + stride(neg, N_PER_ARM)
    sample.sort(key=lambda x: x[1]["sha"])

    import classify as C
    out, key = [], {}
    for i, (d, e) in enumerate(sample):
        diffs = "".join(C._diff_of(e["sha"], p) for p in e["claim_files_touched"])
        out.append({
            "row_id": i, "hunt_directory": d, "commit": e["sha"][:12],
            "date": e["date"], "subject": e["subject"],
            "files_touched": e["claim_files_touched"],
            "diff_first_8000_chars": diffs[:8000],
        })
        key[str(i)] = {"strict": e["strict"], "medium": e["medium"], "loose": e["loose"]}

    (ART / "audit_sample2.json").write_text(json.dumps(out, indent=1), encoding="utf-8")
    out_key.write_text(json.dumps(key, indent=1), encoding="utf-8")
    print(f"fresh rows {len(out)} (positives {sum(1 for k in key.values() if k['strict'])}), "
          f"disjoint from the first {len(already)}; key -> {out_key}")


if __name__ == "__main__":
    main()

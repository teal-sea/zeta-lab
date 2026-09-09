"""Emit a blind audit sample: N classified events with their evidence, and
the classifier's verdict withheld.

The sample is deterministic (a fixed stride over the event list sorted by
sha) so it can be regenerated and disputed, and it is stratified: half the
rows are events the classifier called corrections at the strict level, half
are events it called clean.  A sample drawn only from the positives measures
precision and calls it accuracy.
"""
from __future__ import annotations

import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ART = HERE / "artifacts"
N_PER_ARM = 15


def main() -> None:
    rows = json.loads((ART / "classified.json").read_text(encoding="utf-8"))
    events = [(r["directory"], e) for r in rows for e in r["events"]]
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
    out = []
    for i, (d, e) in enumerate(sample):
        diffs = "".join(C._diff_of(e["sha"], p) for p in e["claim_files_touched"])
        out.append({
            "row_id": i,
            "hunt_directory": d,
            "commit": e["sha"][:12],
            "date": e["date"],
            "subject": e["subject"],
            "files_touched": e["claim_files_touched"],
            "diff_first_8000_chars": diffs[:8000],
        })
    (ART / "audit_sample.json").write_text(json.dumps(out, indent=1), encoding="utf-8")
    key = {str(i): {"strict": e["strict"], "medium": e["medium"], "loose": e["loose"]}
           for i, (_, e) in enumerate(sample)}
    (ART / "audit_key.json").write_text(json.dumps(key, indent=1), encoding="utf-8")
    print(f"sample rows {len(out)}  (positives {len(stride(pos, N_PER_ARM))}, "
          f"negatives {len(stride(neg, N_PER_ARM))})  -> audit_sample.json (key withheld)")


if __name__ == "__main__":
    main()

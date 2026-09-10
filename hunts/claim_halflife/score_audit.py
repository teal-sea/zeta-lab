"""Score the blind audit against the key that was withheld from it.

The auditor was given 30 rows of commit subject, file list and diff, and asked
one question per row.  It was told not to read the classifier, and the key was
moved out of the repository before the audit ran so that reading it was not
possible from the tree.

What this measures is agreement, not truth.  Where the two disagree, one of
them is wrong and the disagreement says which rows to look at; it does not say
which side is right.  Those rows are listed so a third reader can settle them.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ART = HERE / "artifacts"


def main() -> None:
    key = json.loads(Path(sys.argv[1]).read_text(encoding="utf-8"))
    audit = json.loads(Path(sys.argv[2]).read_text(encoding="utf-8"))
    sample = {r["row_id"]: r for r in
              json.loads((ART / "audit_sample.json").read_text(encoding="utf-8"))}

    tp = tn = fp = fn = 0
    disagreements = []
    for row in audit["rows"]:
        i = row["row_id"]
        k = key[str(i)]["strict"]
        a = row["is_revision"]
        if a and k:
            tp += 1
        elif not a and not k:
            tn += 1
        elif a and not k:
            fn += 1          # the classifier said no, the human-style audit said yes
            disagreements.append(("classifier-missed", i, row))
        else:
            fp += 1          # the classifier said yes, the audit said no
            disagreements.append(("classifier-overcalled", i, row))

    n = tp + tn + fp + fn
    agree = tp + tn
    prec = tp / (tp + fp) if tp + fp else None
    rec = tp / (tp + fn) if tp + fn else None
    out = {
        "n": n, "agreement": agree / n,
        "classifier_positive_audit_positive": tp,
        "classifier_negative_audit_negative": tn,
        "classifier_positive_audit_negative": fp,
        "classifier_negative_audit_positive": fn,
        "classifier_precision_against_audit": prec,
        "classifier_recall_against_audit": rec,
        "disagreements": [
            {"kind": k, "row_id": i, "commit": sample[i]["commit"],
             "hunt": sample[i]["hunt_directory"], "subject": sample[i]["subject"],
             "auditor_said": r["is_revision"], "auditor_confidence": r["confidence"],
             "auditor_why": r["why"]}
            for k, i, r in disagreements],
        "auditor_rubric_notes": audit.get("rubric_notes"),
        "auditor_expected_disagreements": audit.get("disagreements_expected"),
    }
    (ART / "audit_score.json").write_text(json.dumps(out, indent=1), encoding="utf-8")
    print(f"rows scored {n}")
    print(f"agreement {agree}/{n} = {100*agree/n:.1f}%")
    print(f"  both say revision      {tp}")
    print(f"  both say not           {tn}")
    print(f"  classifier over-called {fp}")
    print(f"  classifier missed      {fn}")
    if prec is not None:
        print(f"classifier precision against the audit {prec:.2f}, recall {rec:.2f}")
    print()
    for d in out["disagreements"]:
        print(f"  [{d['kind']}] row {d['row_id']} {d['commit']} {d['hunt']}")
        print(f"      {d['subject'][:100]}")
        print(f"      auditor ({d['auditor_confidence']}): {d['auditor_why'][:190]}")


if __name__ == "__main__":
    main()

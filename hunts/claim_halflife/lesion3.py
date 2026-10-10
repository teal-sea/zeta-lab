"""Rung A0: does the test read ANY of the artifacts it names?

`lesion2.py` mutated the first artifact each test names.  Twenty of its
twenty-six targets name more than one, up to thirty-seven, so "the test did not
notice" could always have meant "the test reads a different file of that hunt".
That is a fault in the instrument, not a finding about the tree, and reporting
the earlier number as a coverage figure would have been wrong.

This rung removes it.  Every artifact the test names, from that hunt, is
mutated at once: every numeric leaf scaled by 1.1.  A test that stays green
under that is not reading any number of that hunt's, which is the statement the
earlier rung was reaching for.

The null rung is unchanged and mandatory.  A target whose test goes red on a
byte-identical rewrite is not excluded here: it is recorded as **byte-pinned**,
which is the strongest guard available and the opposite of a failure.  All
three such targets were checked and each test does compute a hash of the file.
"""
from __future__ import annotations

import json
import re
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
ART = HERE / "artifacts"
PY = str(REPO / ".venv" / "bin" / "python")

import lesion2 as L2  # mutate / leaves / run_test / snapshot / restore
import lesion as L1   # artifacts_read_by


def main() -> None:
    classified = json.loads((ART / "classified.json").read_text(encoding="utf-8"))
    targets = [(r["directory"], t) for r in classified for t in r["pinned_by"]]

    results = []
    for hunt, test in targets:
        arts = L1.artifacts_read_by(test, hunt)
        arts = [a for a in arts if L2.leaves(a) > 0]
        if not arts:
            results.append({"hunt": hunt, "test": test, "outcome": "no-mutable-artifact",
                            "n_artifacts": 0})
            print(f"{hunt:22s} {test:42s} no artifact of this hunt has a mutable number")
            continue
        for a in arts:
            L2.snapshot(a)

        # null rung over all of them at once
        for a in arts:
            if a.suffix == ".json":
                L2.null_rewrite(a)
        null_green = L2.run_test(test)
        for a in arts:
            L2.restore(a)
        if not null_green:
            results.append({"hunt": hunt, "test": test, "outcome": "byte-pinned",
                            "n_artifacts": len(arts),
                            "artifacts": [str(a.relative_to(REPO)) for a in arts]})
            print(f"{hunt:22s} {test:42s} BYTE-PINNED over {len(arts)} artifact(s)")
            continue

        n_mut = 0
        for a in arts:
            if L2.mutate(a, 0.10, None) is not None:
                n_mut += 1
        red = not L2.run_test(test)
        for a in arts:
            L2.restore(a)
        results.append({"hunt": hunt, "test": test,
                        "outcome": "reads-numbers" if red else "reads-no-numbers",
                        "n_artifacts": len(arts), "n_mutated": n_mut,
                        "total_leaves": sum(L2.leaves(a) for a in arts),
                        "artifacts": [str(a.relative_to(REPO)) for a in arts]})
        print(f"{hunt:22s} {test:42s} {results[-1]['outcome']:16s} "
              f"({n_mut} artifact(s), {results[-1]['total_leaves']} leaves)", flush=True)

    (ART / "lesion3.json").write_text(json.dumps(results, indent=1), encoding="utf-8")
    from collections import Counter
    c = Counter(r["outcome"] for r in results)
    scored = c["reads-numbers"] + c["reads-no-numbers"] + c["byte-pinned"]
    defended = c["reads-numbers"] + c["byte-pinned"]
    print()
    print(f"targets {len(results)}   scored {scored}   "
          f"defending at least one number {defended}   "
          f"reading none {c['reads-no-numbers']}   "
          f"no mutable artifact {c['no-mutable-artifact']}")


if __name__ == "__main__":
    main()

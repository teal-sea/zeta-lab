"""Compare re-run stage blocks with the committed results, field by field.

Used by ``.github/workflows/dh-floor-rerun.yml`` for the 2026-10-19 correction
(NOTES.md, "Correction"), for this hunt and for ``hunts/jensen_clock``.  Every
leaf of a committed block is compared with the re-run as stored (strings and
floats exactly, so "identical" means to the last printed digit); the only keys
skipped are wall-clock timings.  A stage whose re-run file or block is absent
is reported as missing and makes the exit code non-zero: an absent re-run is
not an unchanged one.

    python hunts/flow_repair/compare_rerun.py --out report.json \\
        --stage LABEL COMMITTED.json KEY RERUN.json KEY  [--stage ...]

KEY may be dotted (``survey_2_3.pair2``) to reach into a block.
"""

from __future__ import annotations

import argparse
import json
import os
import sys

#: wall-clock fields, the only ones a faithful re-run may change
TIMING_KEYS = {"seconds", "seconds_total"}


def dig(blob, key):
    for part in key.split("."):
        if not isinstance(blob, dict) or part not in blob:
            return None
        blob = blob[part]
    return blob


def walk(old, new, path, rec):
    if isinstance(old, dict) and isinstance(new, dict):
        for k in sorted(set(old) | set(new)):
            if k in TIMING_KEYS:
                continue
            sub = f"{path}.{k}"
            if k not in new:
                rec["missing"].append(sub)
            elif k not in old:
                rec["added"].append(sub)
            else:
                walk(old[k], new[k], sub, rec)
        return
    if isinstance(old, list) and isinstance(new, list) and len(old) == len(new):
        for i, (a, b) in enumerate(zip(old, new)):
            walk(a, b, f"{path}.{i}", rec)
        return
    rec["fields_compared"] += 1
    if old == new:
        rec["identical"] += 1
    else:
        rec["changed"].append({"path": path, "committed": old, "rerun": new})


def compare(label, committed_path, committed_key, rerun_path, rerun_key):
    rec = {"committed": f"{committed_path}:{committed_key}",
           "rerun": f"{os.path.basename(rerun_path)}:{rerun_key}",
           "fields_compared": 0, "identical": 0,
           "changed": [], "missing": [], "added": []}
    with open(committed_path, encoding="utf-8") as fh:
        old = dig(json.load(fh), committed_key)
    if old is None:
        raise SystemExit(f"{label}: committed block {committed_key} not found")
    new = None
    if os.path.exists(rerun_path):
        with open(rerun_path, encoding="utf-8") as fh:
            new = dig(json.load(fh), rerun_key)
    if new is None:
        rec["missing"].append(f"{label} (no re-run block)")
        return rec
    walk(old, new, label, rec)
    return rec


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--out", required=True)
    ap.add_argument("--stage", nargs=5, action="append", required=True,
                    metavar=("LABEL", "COMMITTED", "KEY", "RERUN", "RKEY"))
    ap.add_argument("--note", default="")
    args = ap.parse_args()
    import mpmath

    report = {
        "omega_dh_cutoff": "relative",
        "note": args.note,
        "mpmath": mpmath.__version__,
        "commit": os.environ.get("GITHUB_SHA", ""),
        "run": (f"{os.environ['GITHUB_SERVER_URL']}/{os.environ['GITHUB_REPOSITORY']}"
                f"/actions/runs/{os.environ['GITHUB_RUN_ID']}"
                if os.environ.get("GITHUB_RUN_ID") else ""),
        "stages": {},
    }
    for label, cpath, ckey, rpath, rkey in args.stage:
        report["stages"][label] = compare(label, cpath, ckey, rpath, rkey)
    st = report["stages"].values()
    report["totals"] = {
        "stages": len(report["stages"]),
        "fields_compared": sum(s["fields_compared"] for s in st),
        "identical": sum(s["identical"] for s in st),
        "changed": sum(len(s["changed"]) for s in st),
        "missing": sum(len(s["missing"]) for s in st),
        "added": sum(len(s["added"]) for s in st),
    }
    with open(args.out, "w", encoding="utf-8") as fh:
        json.dump(report, fh, indent=1, sort_keys=True)
        fh.write("\n")

    t = report["totals"]
    lines = [f"### {args.out}",
             f"{t['stages']} stages, {t['fields_compared']} fields compared: "
             f"{t['identical']} identical, {t['changed']} changed, "
             f"{t['missing']} missing, {t['added']} added", ""]
    for label, s in report["stages"].items():
        lines.append(f"- {label}: {s['fields_compared']} fields, {len(s['changed'])} changed, "
                     f"{len(s['missing'])} missing")
        for c in s["changed"]:
            lines.append(f"  - CHANGED {c['path']}: {c['committed']} -> {c['rerun']}")
        for m in s["missing"]:
            lines.append(f"  - MISSING {m}")
    text = "\n".join(lines)
    print(text)
    if os.environ.get("GITHUB_STEP_SUMMARY"):
        with open(os.environ["GITHUB_STEP_SUMMARY"], "a", encoding="utf-8") as fh:
            fh.write(text + "\n\n")
    if t["fields_compared"] == 0:
        print("nothing was compared", file=sys.stderr)
        return 1
    return 1 if t["missing"] else 0


if __name__ == "__main__":
    sys.exit(main())

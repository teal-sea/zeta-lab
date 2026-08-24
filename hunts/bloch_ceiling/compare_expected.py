"""Compare every printed statistic against the archive's expected output.

Reads the archive's expected-output/verification.md and reference-run logs
(paths via BLOCH_SRC, see fetch_upstream.sh), the Modal record
artifacts/modal-reproduce.json (quick programs, sector shards, control), and
prints one line per statistic: expected, observed, match.  Exit status is the
number of mismatches.

    source <(hunts/bloch_ceiling/fetch_upstream.sh)
    python hunts/bloch_ceiling/compare_expected.py
"""
from __future__ import annotations

import glob
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
SRC = os.environ.get("BLOCH_SRC", os.path.join(HERE, "..", "..", ".upstream", "bloch",
                                               "zenodo-bloch-computations", "src"))
ARCHIVE = os.path.normpath(os.path.join(SRC, ".."))
REC = json.load(open(os.path.join(HERE, "artifacts", "modal-reproduce.json"), encoding="utf-8"))
quick = REC["quick/quick.json"]

# (label, regex over the log, log key) -> expected value from verification.md
FIXED = [
    ("fine (A) |a_3| <=", r"\(A\)\s+\|a_3\| <= \[([0-9.]+)", "fixed_fine", "3.28877762819"),
    ("fine (B) Phi(-1,0) gain", r"\(B\)\s+Phi\(-1,0\) >= sqrt3/4 \+ \[([0-9.]+)", "fixed_fine", "0.0149407644273"),
    ("fine (C) gain", r"\(C\)\s+B >= sqrt3/4 \+ \[([0-9.]+)", "fixed_fine", "0.0114402996202"),
    ("fine (C) B >=", r"\n\s+= \[([0-9.]+) \+/-", "fixed_fine", "0.444453001512"),
    ("fine displayed-minorant margin", r"validity margin \(must be <= 0\): \[(-[0-9.e-]+)", "fixed_fine", "-5.756091347e-8"),
    ("fine min R", r"min_theta R\(theta\) >= \[([0-9.]+)", "fixed_fine", "0.41491575"),
    ("fine PASS line", r"(PASS: all assertions applicable to the fine certificate verified)", "fixed_fine", "PASS: all assertions applicable to the fine certificate verified"),
    ("coarse (A) |a_3| <=", r"\(A\)\s+\|a_3\| <= \[([0-9.]+)", "fixed_coarse", "3.29102479849"),
    ("coarse (B) Phi(-1,0) gain", r"\(B\)\s+Phi\(-1,0\) >= sqrt3/4 \+ \[([0-9.]+)", "fixed_coarse", "0.0150346379669"),
    ("coarse (C) gain", r"\(C\)\s+B >= sqrt3/4 \+ \[([0-9.]+)", "fixed_coarse", "0.0113729923988"),
    ("coarse (C) B >=", r"\n\s+= \[([0-9.]+) \+/-", "fixed_coarse", "0.444385694291"),
    ("coarse min R", r"min_theta R\(theta\) >= \[([0-9.]+)", "fixed_coarse", "0.41480041"),
    ("coarse PASS line", r"(PASS: all assertions applicable to the coarse certificate verified)", "fixed_coarse", "PASS: all assertions applicable to the coarse certificate verified"),
    ("ceiling witness gain", r"Phi_even - sqrt\(3\)/4 <= \[([0-9.]+)", "fixed_ceiling", "0.01519720970909415"),
    ("ceiling PASS line", r"(PASS: the fixed-radius approach is rigorously capped below \+0.0152)", "fixed_ceiling", "PASS: the fixed-radius approach is rigorously capped below +0.0152"),
    ("uniform positivity margin", r"uniform positivity margin: \+([0-9.]+)", "verify_mesh20", "0.000936855231"),
    ("near moment slope margin", r"near moment slope margin: \[([0-9.]+)", "verify_mesh20", "0.0331790701855"),
    ("near centre |c| <=", r"near centre: \|c\| <= \[([0-9.]+)", "verify_mesh20", "0.136904745959"),
    ("near centre min R", r"< min R \[([0-9.]+)", "verify_mesh20", "0.436558987993"),
    ("near moment gain", r"near moment gain: \[([0-9.]+)", "verify_mesh20", "0.0153040536989472"),
    ("20x20 mesh away minimum", r"away minimum: \(([0-9.]+)", "verify_mesh20", "0.015866072532"),
    ("MESH RESULT", r"MESH RESULT: gain=([0-9.]+); PASS > 0.0153", "verify_mesh20", "0.015304053699"),
]

mismatches = 0
print("== quick programs (Modal container) against expected-output/verification.md and VARIABLE_RADIUS_FINDINGS.md")
for label, rx, key, expected in FIXED:
    m = re.search(rx, quick[key]["log"])
    obs = m.group(1) if m else None
    ok = obs is not None and (obs == expected or obs.startswith(expected) or expected.startswith(obs))
    if not ok and obs is not None:
        try:  # the findings file quotes some values rounded to 12 places
            digits = len(expected.split(".")[1]) if "." in expected else 0
            ok = abs(float(obs) - float(expected)) <= 0.5 * 10 ** (-digits)
        except ValueError:
            ok = False
    mismatches += 0 if ok else 1
    print(f"{'MATCH   ' if ok else 'MISMATCH'} {label}: expected {expected}, observed {obs}")

# reference-run sector counts from the logs
print("\n== away sectors: reference log vs Modal (author's branch_verify, 40x40 grid, 8 shards)")
ref = {}
for path in glob.glob(os.path.join(ARCHIVE, "reference-run", "logs", "*.log")):
    text = open(path, encoding="utf-8").read()
    for m in re.finditer(r"sector\s+(\d+): PASS > 0.0153; cert\w+_boxes=(\d+), open=(\d+); elapsed=([0-9:.]+)", text):
        ref[int(m.group(1))] = {"boxes": int(m.group(2)), "elapsed": m.group(4)}
    m = re.search(r"sector\s+(\d+): reference antipodal gain=([0-9.]+)", text)
    if m:
        ref.setdefault(int(m.group(1)), {})["antipodal"] = m.group(2)
per = REC.get("_per_sector", {})
shards = [v for k, v in REC.items() if k.startswith("repro/") and "shard" in v]
total_ref = total_obs = 0
for j in range(24):
    s = per.get(str(j)) or per.get(j)
    mine = [v for v in shards if v["sector"] == j]
    anti = {f"{v['reference_antipodal_gain']:.12f}" for v in mine}
    obs = s["terminal_boxes"] if s else None
    exp = ref.get(j, {}).get("boxes")
    ok = obs is not None and exp is not None and obs == exp and (s["cells"] == 1600) and s["incomplete_cells"] == 0
    mismatches += 0 if ok else 1
    if exp:
        total_ref += exp
    if obs:
        total_obs += obs
    print(f"{'MATCH   ' if ok else 'MISMATCH'} sector {j:2d}: reference {exp} boxes ({ref.get(j, {}).get('elapsed')}), "
          f"observed {obs} over {s['cells'] if s else 0}/1600 cells in {s['shards'] if s else 0} shards, incomplete cells {s['incomplete_cells'] if s else '?'}, "
          f"antipodal ref {ref.get(j, {}).get('antipodal')} obs {sorted(anti)}, wall max {s['wall_max'] if s else '?'}s")
print(f"total terminal boxes: reference {total_ref} (paper: 11443518), observed {total_obs}")

print("\n== control: sector 4 with the README's default --max-boxes 200000")
ctl = REC.get("control-default-cap/sector_04.json")
if ctl:
    print(json.dumps({k: ctl.get(k) for k in ("status", "status_line", "final_line", "max_open", "terminal_boxes", "open_at_end", "current_gain_at_stop", "wall_seconds", "command")}, indent=1))
else:
    print("not yet recorded")
print(f"\nmismatches: {mismatches}")
sys.exit(mismatches)

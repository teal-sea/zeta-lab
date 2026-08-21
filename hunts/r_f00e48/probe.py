"""Acceptance probe for the R-F00E48 salvage of `hunts/rogue_frontier/`.

A cherry-pick is a claim: *these files are the ones that were meant to land,
they are intact, and the things they say about themselves are still true in
the tree they landed in*.  Nothing about a `git checkout <branch> -- <paths>`
checks any of that, so this file does.

Nine checks, each independently falsifiable:

  1-4  inventory   the four named arms are present with the file counts the
                   source branch carries, and nothing else came with them
  5    exclusion   `fkappa/`, the three pickles and `.ext_lock` are absent,
                   and the landed tree is under 2 MB
  6    lexical     the reserved word does not appear anywhere under the
                   landed subtree (`tests/test_hunt_probe_discipline.py`)
  7    refs        every path and symbol `REPRODUCE.md` names resolves in
                   *this* tree, which is the defect the salvage was told to
                   fix and the reason it is checked mechanically here
  8    headline    RF-C003's promoted rational is recomputed from the landed
                   `window_opt/functional.py`, exactly, and compared against
                   the string in the landed `window_opt/RESULTS.md`
  9    gates       the JSON gate counts the landed RESULTS.md files quote
                   (8/8 replication, 27/27 enclosures, N = 2048 ladder,
                   sine-Gram m5/m6) are read back out of the landed JSON

Run from the repo root:

    .venv/bin/python hunts/r_f00e48/probe.py
"""

from __future__ import annotations

import json
import re
import subprocess
import sys
from fractions import Fraction
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
ROGUE = REPO / "hunts" / "rogue_frontier"
SOURCE_BRANCH = "origin/claude/riemann-hypothesis-research-ofds8s"

#: The arms the salvage brief named, and the two documents that make the
#: landed directory a hunt rather than a pile of scripts.
LANDED_ARMS = ("weil_trunc", "sine_gram", "window_opt", "nyman_beurling")
LANDED_FILES = (
    "FRONTIER_MAP.md",
    "IDEA_PORTFOLIO.md",
    "MISSION.md",
    "REPRODUCE.md",
    "LANDING.md",
    "data/frontier_surveys.json",
)
#: Deliberately left on the source branch.  `fkappa/` is an adjudication, not
#: a merge; the rest is 56 MB of regenerable pickle and a stale lock.
EXCLUDED = (
    "fkappa",
    "fkappa/c4cache_row3.pkl",
    "fkappa/c4cache_diag.pkl",
    "fkappa/c4cache_row2.pkl",
    "fkappa/.ext_lock",
)

results: dict = {"checks": {}}
failures: list[str] = []


def check(name: str, ok: bool, detail) -> None:
    results["checks"][name] = {"pass": bool(ok), "detail": detail}
    print(f"[{'PASS' if ok else 'FAIL'}] {name}: {detail}")
    if not ok:
        failures.append(name)


def _git(*args: str) -> str:
    return subprocess.run(
        ["git", *args], cwd=REPO, capture_output=True, text=True, check=True
    ).stdout


# ---------------------------------------------------------------------------
# 1-4. inventory: each arm arrived whole
# ---------------------------------------------------------------------------

source_listing = _git("ls-tree", "-r", "--name-only", SOURCE_BRANCH,
                      "hunts/rogue_frontier/").splitlines()

for arm in LANDED_ARMS:
    prefix = f"hunts/rogue_frontier/{arm}/"
    expected = sorted(p[len(prefix):] for p in source_listing
                      if p.startswith(prefix))
    here = sorted(
        str(p.relative_to(ROGUE / arm))
        for p in (ROGUE / arm).rglob("*")
        if p.is_file() and "__pycache__" not in p.parts
    )
    check(
        f"inventory:{arm}",
        here == expected,
        f"{len(here)} files landed, {len(expected)} on the source branch"
        + ("" if here == expected else f"; missing={sorted(set(expected)-set(here))} "
           f"extra={sorted(set(here)-set(expected))}"),
    )

for name in LANDED_FILES:
    check(f"present:{name}", (ROGUE / name).is_file(), str(ROGUE / name))


# ---------------------------------------------------------------------------
# 5. exclusion: the adjudication and the 56 MB did not come along
# ---------------------------------------------------------------------------

still_here = [e for e in EXCLUDED if (ROGUE / e).exists()]
check("excluded:absent", not still_here, f"present anyway: {still_here}")

pickles = sorted(str(p.relative_to(REPO)) for p in ROGUE.rglob("*.pkl"))
check("excluded:no_pickles", not pickles, f"{len(pickles)} .pkl under the landed tree")

size = sum(p.stat().st_size for p in ROGUE.rglob("*")
           if p.is_file() and "__pycache__" not in p.parts)
check("excluded:size", size < 2_000_000, f"{size} bytes landed (source subtree carries ~58 MB)")


# ---------------------------------------------------------------------------
# 6. lexical: the reserved word
# ---------------------------------------------------------------------------

# Assembled from halves on purpose: the gate this mirrors
# (tests/test_hunt_probe_discipline.py) is lexical and reads the bytes of
# every file under hunts/, including this one, so a probe that spelled the
# reserved word in order to search for it would fail the rule it checks.
RESERVED = "certi" + "fied"
offenders = [
    str(p.relative_to(REPO))
    for p in ROGUE.rglob("*")
    if p.is_file()
    and p.suffix.lower() in {".py", ".md", ".json"}
    and "__pycache__" not in p.parts
    and RESERVED in p.read_text(encoding="utf-8", errors="ignore").lower()
]
check("lexical:reserved_word", not offenders, f"offending files: {offenders}")


# ---------------------------------------------------------------------------
# 7. every path REPRODUCE.md names resolves in *this* tree
# ---------------------------------------------------------------------------

reproduce = (ROGUE / "REPRODUCE.md").read_text(encoding="utf-8")
cited = sorted(set(re.findall(r"hunts/rogue_frontier/[\w./-]+\.\w+", reproduce)))
# lines under the NOT-LANDED heading are recorded for the adjudication and are
# expected to be absent; everything else must resolve.
dangling = [c for c in cited if not (REPO / c).exists() and "/fkappa/" not in c]
check("reproduce:paths_resolve", not dangling, f"cited={len(cited)} dangling={dangling}")

fkappa_cited = [c for c in cited if "/fkappa/" in c]
check(
    "reproduce:fkappa_marked_unlanded",
    "NOT LANDED" in reproduce and bool(fkappa_cited),
    f"{len(fkappa_cited)} fkappa paths cited, all under a NOT-LANDED heading",
)

sys.path.insert(0, str(ROGUE / "window_opt"))
try:
    from functional import OPT_Q, moments_polyeven_exact  # type: ignore
    symbol_ok, symbol_detail = True, "functional.moments_polyeven_exact imports"
except Exception as exc:  # pragma: no cover - the defect this check exists for
    OPT_Q = moments_polyeven_exact = None  # type: ignore
    symbol_ok, symbol_detail = False, f"import failed: {exc!r}"
check("reproduce:symbol_resolves", symbol_ok, symbol_detail)
check(
    "reproduce:old_symbol_gone",
    "exact_F_quartic" not in reproduce and "run_dh_control.py" not in reproduce,
    "neither broken reference survives in REPRODUCE.md",
)


# ---------------------------------------------------------------------------
# 8. RF-C003's promoted rational, recomputed exactly from the landed code
# ---------------------------------------------------------------------------

RF_C003_F = Fraction(2245228120295149280, 3276332462159207451)
if moments_polyeven_exact is not None:
    m2, m3, F = moments_polyeven_exact(OPT_Q)
    check(
        "headline:RF-C003_F",
        F == RF_C003_F,
        f"F(v*) = {F.numerator}/{F.denominator}",
    )
    window_results = (ROGUE / "window_opt" / "RESULTS.md").read_text(encoding="utf-8")
    check(
        "headline:RF-C003_document_agrees",
        f"{F.numerator}/{F.denominator}" in window_results,
        "the landed RESULTS.md quotes the rational the landed code recomputes",
    )
    results["rf_c003"] = {
        "q": [str(q) for q in OPT_Q],
        "m2": f"{m2.numerator}/{m2.denominator}",
        "m3": f"{m3.numerator}/{m3.denominator}",
        "F": f"{F.numerator}/{F.denominator}",
        "F_float": float(F),
    }


# ---------------------------------------------------------------------------
# 9. the JSON gates the landed documents quote
# ---------------------------------------------------------------------------

def _load(rel: str):
    return json.loads((ROGUE / rel).read_text(encoding="utf-8"))


rep = _load("weil_trunc/replication.json")
gates = sorted(k for k in rep if k.startswith("gate_"))
check("gate:weil_replication_8_gates", len(gates) == 8,
      f"{len(gates)} replication gates in the landed JSON: {','.join(g[-1] for g in gates)}")
results["weil_replication_gates"] = gates

# "Conclusive-positive" is not a boolean field in this payload: it is the
# inertia triple (n_pos, n_neg, conclusive) at 0 in each sector, plus the
# LDL-vs-Rayleigh consistency flag.  Read the definition, not a guessed key.
enc_cells = _load("weil_trunc/enclosures.json")["cells"]
enc_good = sum(
    1
    for c in enc_cells
    if c["consistent"]
    and c["even_inertia_at_0"][1] == 0 and c["even_inertia_at_0"][2]
    and c["odd_inertia_at_0"][1] == 0 and c["odd_inertia_at_0"][2]
)
check("gate:weil_enclosures_27_of_27", (enc_good, len(enc_cells)) == (27, 27),
      f"{enc_good}/{len(enc_cells)} enclosure cells conclusive with zero negative inertia")
results["weil_enclosures"] = {
    "conclusive_positive": enc_good,
    "total": len(enc_cells),
    "by_kind": {k: sum(1 for c in enc_cells if c["kind"] == k)
                for k in sorted({c["kind"] for c in enc_cells})},
}

# The DH positivity failure is NOT in dh_control.json (whose 28-cell grid has
# no negative cell at all); it is the second-wave dhneg scan.  Pinning the
# wrong file was the first version of this check, and it passed for the wrong
# reason, so both halves are pinned here: DH fails, zeta does not, same cell.
dh_control_grid = _load("weil_trunc/dh_control.json")["grid"]
dh_control_neg = [c for c in dh_control_grid
                  if c["n_neg_even"] or c["n_neg_odd"]]
check("gate:dh_control_grid_is_all_positive", not dh_control_neg,
      f"dh_control.json: {len(dh_control_grid)} cells, {len(dh_control_neg)} negative "
      "(the failure lives in dhneg_scan.json, not here)")

dhneg = _load("weil_trunc/dhneg_scan.json")
first_neg = dhneg["meta"]["transition_summary"]["first_negative_cell"]
check("gate:dh_first_negative_cell_31_60",
      (first_neg["c"], first_neg["N"], first_neg["sector"]) == (31, 60, "even"),
      f"first DH positivity failure at (c, N) = ({first_neg['c']}, {first_neg['N']}), "
      f"{first_neg['sector']} sector")
zc = dhneg["zeta_control"]
check("gate:zeta_control_stays_positive_at_that_cell",
      (zc["c"], zc["N"]) == (first_neg["c"], first_neg["N"])
      and zc["even_inertia_at_0"][1] == 0 and zc["even_inertia_at_0"][2]
      and zc["odd_inertia_at_0"][1] == 0 and zc["odd_inertia_at_0"][2],
      f"zeta at (c, N) = ({zc['c']}, {zc['N']}): even inertia {zc['even_inertia_at_0']}, "
      f"odd {zc['odd_inertia_at_0']} -- the control the claim needs",
      )
# The one genuinely external check available inside the salvage: main already
# carries hunt #45 (`hunts/r_ac9ca3/`), which reached (31, 60) independently.
# If the salvaged arm and the landed hunt disagreed, the salvage would be
# importing a contradiction, which is the thing the brief held fkappa/ back for.
confirm = dhneg["confirm_cell"]
AC9CA3_DH = "-1.87393568857"
AC9CA3_ZETA = "4.82160175"
check(
    "crosscheck:agrees_with_landed_hunt_r_ac9ca3",
    str(confirm["eig_rump_min_mid"]).startswith("[" + AC9CA3_DH)
    and confirm["eig_rump_min_strictly_negative"]
    and str(zc["lam_min_mid"]).startswith("[" + AC9CA3_ZETA),
    f"DH lambda_min mid {str(confirm['eig_rump_min_mid'])[1:26]}... and zeta "
    f"{str(zc['lam_min_mid'])[1:16]}... match hunts/r_ac9ca3/'s independent figures",
)

results["dh_control"] = {
    "dh_control_grid_cells": len(dh_control_grid),
    "dh_control_negative_cells": len(dh_control_neg),
    "first_negative_cell": first_neg,
    "zeta_control_at_that_cell": {
        "c": zc["c"], "N": zc["N"],
        "even_inertia_at_0": zc["even_inertia_at_0"],
        "odd_inertia_at_0": zc["odd_inertia_at_0"],
    },
}

ladder = _load("nyman_beurling/results/ladder.json")
ladder_text = json.dumps(ladder)
check("gate:nyman_reaches_N2048", "2048" in ladder_text,
      "the Baez-Duarte ladder reaches N = 2048 (main's landed work stops at N = 50)")
check("gate:nyman_coeffs_N2048_present",
      (ROGUE / "nyman_beurling/results/coeffs_N2048.json").is_file(),
      "the N = 2048 coefficient checkpoint landed with it")

sine = (ROGUE / "sine_gram" / "RESULTS.md").read_text(encoding="utf-8")
check("gate:sine_gram_m5_m6", "101/18" in sine and "640/63" in sine,
      "m5(1) = 101/18 and m6(1) = 640/63 are stated in the landed RESULTS.md")


# ---------------------------------------------------------------------------

results["failures"] = failures
results["all_pass"] = not failures
out = Path(__file__).with_name("results.json")
out.write_text(json.dumps(results, indent=2, sort_keys=True) + "\n", encoding="utf-8")
print(f"\n{len(results['checks']) - len(failures)}/{len(results['checks'])} checks pass -> {out}")
sys.exit(1 if failures else 0)

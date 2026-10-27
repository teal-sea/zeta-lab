"""Evaluate the merged [10^4, 10^5] census against its PREREG, RESULTS.md section 8.12.

Hunt #119, unit 3 (2026-10-26). Every threshold below is the one written in
section 8.12 before any census data existed (commit ac11243af); this module
applies them and does not choose them.

Input: `census_runs/full_r1/census_1e5.json` (the merge job's output) plus the
committed `census_1e4.json`, `census_deep4_1e5.json` and `twosided.json`.
Output: `census_runs/full_r1/evaluation.json`.

Grade of every verdict: *measured* (float screen, ODE landings).

Run:  .venv/bin/python hunts/lambda_dh_exact/evaluate_census.py
"""
from __future__ import annotations

import json
import math
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)

RUN = os.environ.get("LDH_CENSUS_RUN") or os.path.join(HERE, "census_runs", os.environ.get("LDH_CENSUS_ATTEMPT", "full_r1"))
FLOOR = 0.05765184034869543
BAND = 0.0004
M2, M3 = 0.05767, 0.05586          # per-decade maxima as registered (section 8.8)
M2_EXACT_GAMMA, M3_EXACT_GAMMA = 240.4047, 2442.5303
P8_WIDEN = 0.15
KC_UNACCOUNTED = 0.10
KD_RTOL = 1e-6
KE_CORE_HOURS = 30.0
TWO_SIDED_IN_SAMPLE = 0.112
TWO_SIDED_EXPECT = 0.160


def load(path):
    with open(path) as fh:
        return json.load(fh)


def two_sided_ratio(row) -> dict:
    import census_1e4 as cz
    import twosided as ts
    g, y0 = row["gamma"], row["y0"]
    h = ts.h_mean(g)
    reals = cz.line_zeros(g - 4 * h, g + 4 * h)
    d_l = g - max(x for x in reals if x < g)
    d_r = min(x for x in reals if x > g) - g
    gate = abs(min(d_l, d_r) / h - row["gap_ratio_d_over_h"])
    t2 = ts.t_star_two(y0, d_l, d_r, h)
    return {"gamma": g, "ratio": row["landing_ode"] / t2, "gate_defect": gate,
            "d_L_over_h": d_l / h, "d_R_over_h": d_r / h}


def main() -> None:
    merged = load(os.path.join(RUN, "census_1e5.json"))
    rows = merged["rows"]
    shards = merged["shards"]
    # KNOWN LIMITS (recorded 2026-10-26 in review, RESULTS.md section 8.16;
    # logic deliberately unchanged, so the recorded evaluations reproduce):
    # 1. Only rows with a landing enter `landed`, and the floor verdict reads
    #    `landed` alone.  A row whose accounting closed but whose ODE made no
    #    crossing by t_end (census_1e4.py: landing_ode None) is dropped here,
    #    and no kill condition requires n_landed == n_rows, although such a
    #    row is exactly a landing later than 1.25 y0^2/2.
    # 2. Flagged windows the guarded locate could not place (`unlocated`) are
    #    reported beside K-c but enter no kill condition and no verdict.
    # Neither occurred in attempt 2 (170 of 170 landed, 0 unlocated); both
    # are pinned by test_known_limit_evaluation_drops_unlanded_and_unlocated.
    landed = [r for r in rows if r["landing_ode"] is not None]
    low = load(os.path.join(HERE, "census_1e4.json"))["rows"]
    deep = load(os.path.join(HERE, "census_deep4_1e5.json"))["rows"]
    ins = {round(r["gamma"], 2) for r in load(os.path.join(HERE, "twosided.json"))["rows"]}

    out = {"what": "evaluation of the [1e4, 1e5] census against RESULTS.md section 8.12",
           "plan_sha256": merged["plan_sha256"], "n_shards": len(shards),
           "n_rows": len(rows), "n_landed": len(landed)}

    # K-b: every shard present with a complete screen (merge refuses otherwise; re-checked)
    out["K_b_ok"] = (len(shards) == 36 and all(s["screen_complete"] for s in shards)
                     and sorted(s["shard"] for s in shards) == list(range(36)))
    # K-c: unaccounted fraction
    n_unacc = sum(not r["accounting_ok"] for r in rows)
    out["n_unaccounted"] = n_unacc
    out["unaccounted_fraction"] = n_unacc / len(rows) if rows else None
    out["unaccounted_gammas"] = [round(r["gamma"], 2) for r in rows if not r["accounting_ok"]]
    out["K_c_ok"] = out["unaccounted_fraction"] is not None and out["unaccounted_fraction"] <= KC_UNACCOUNTED
    # reported beside K-c, not inside it (8.12's text is unchanged): flagged windows whose
    # zero the guarded locate could not place, roots the guard refused and relocated, and
    # windows whose accounting closed only on the 0.5005 fallback (attempt 2 onward)
    out["n_unlocated_windows"] = sum(s.get("n_unlocated", 0) for s in shards)
    out["n_relocated_by_guard"] = sum(s.get("n_relocated_by_guard", 0) for s in shards)
    out["n_accounting_fallback"] = sum("accounting_fallback" in r for r in rows)
    # K-d: replication of the eight targeted landings
    rep = []
    for d in deep:
        if d["landing_ode"] is None:
            continue
        m = [r for r in rows if abs(r["gamma"] - d["gamma"]) < 1e-3]
        new = m[0]["landing_ode"] if m else None
        rep.append({"gamma": round(d["gamma"], 2), "recorded": d["landing_ode"], "census": new,
                    "rel": abs(new / d["landing_ode"] - 1) if new else None})
    out["K_d_replication"] = rep
    out["K_d_ok"] = len(rep) == 8 and all(x["rel"] is not None and x["rel"] <= KD_RTOL for x in rep)
    # K-e: actual core-hours
    cpu = sum(sum(s["cpu_seconds"].values()) for s in shards)
    out["core_hours"] = cpu / 3600
    out["K_e_ok"] = out["core_hours"] <= KE_CORE_HOURS
    out["peak_rss_gb_max"] = max(s["peak_rss"]["peak_gb"] for s in shards)
    valid = out["K_b_ok"] and out["K_d_ok"] and out["K_e_ok"]
    out["census_valid"] = valid

    # 1. the floor in this decade
    m4row = max(landed, key=lambda r: r["landing_ode"])
    m4 = m4row["landing_ode"]
    out["m4"] = m4
    out["m4_at"] = {"gamma": m4row["gamma"], "y0": m4row["y0"]}
    beats = [r for r in landed if r["landing_ode"] > FLOOR * (1 + BAND)]
    out["floor_beaten_by"] = [round(r["gamma"], 2) for r in beats]
    out["verdict_floor"] = ("not made (K-c)" if not out["K_c_ok"] else
                            ("raised" if beats else "no pair with y0 > 0.3396 in [1e4, 1e5] beats it"))
    # 2. KC4: fires iff m4 > m3
    out["verdict_KC4"] = "fires" if m4 > M3 else "does not fire up to 1e5"
    out["m4_gt_m2"] = m4 > M2
    # 3. P5 up to 1e5: argmax over every measured landing below 1e5 in this hunt
    allrows = [r for r in low if r["landing_ode"] is not None] + landed
    best = max(allrows, key=lambda r: r["landing_ode"])
    p5 = 1e3 <= best["gamma"] <= 1e5 and 0.40 <= best["y0"] <= 0.52
    out["P5_argmax"] = {"gamma": best["gamma"], "y0": best["y0"], "landing": best["landing_ode"]}
    out["verdict_P5"] = "holds up to 1e5" if p5 else "refuted up to 1e5"
    # 4. P8
    later = [r for r in landed if r["later_than_naive"]]
    out["P8_count"] = len(later)
    out["P8_rate"] = len(later) / len(landed)
    out["verdict_P8"] = ("observed" if later else "not observed") + (
        "; rate above 15 percent widens P1" if out["P8_rate"] > P8_WIDEN else "")
    # 5. two-sided, out of sample
    oos = [r for r in landed if round(r["gamma"], 2) not in ins and r["accounting_ok"]]
    ts_rows = [two_sided_ratio(r) for r in oos]
    rms = math.sqrt(sum((x["ratio"] - 1) ** 2 for x in ts_rows) / len(ts_rows))
    out["two_sided_oos"] = {"n": len(ts_rows), "rms": rms,
                            "max_gate_defect": max(x["gate_defect"] for x in ts_rows),
                            "n_in_band": sum(0.85 <= x["ratio"] <= 1.25 for x in ts_rows),
                            "min_ratio": min(x["ratio"] for x in ts_rows),
                            "max_ratio": max(x["ratio"] for x in ts_rows)}
    out["verdict_two_sided_oos"] = ("expectation met (rms < 0.160)" if rms < TWO_SIDED_EXPECT
                                    else "expectation failed (rms >= 0.160): section 8.11's reading undone")
    out["two_sided_oos_rows"] = ts_rows
    # section 8.12: K-b voids decade-wide statements, K-d voids the census, K-e stops it
    if not valid:
        why = ", ".join(k for k in ("K_b_ok", "K_d_ok", "K_e_ok") if not out[k])
        for k in ("verdict_floor", "verdict_KC4", "verdict_P5", "verdict_P8", "verdict_two_sided_oos"):
            out[k] = f"void ({why} failed); computed value kept for the record: {out[k]}"
    with open(os.path.join(RUN, "evaluation.json"), "w") as fh:
        json.dump(out, fh, indent=1)
    print(json.dumps({k: v for k, v in out.items() if k not in ("two_sided_oos_rows", "K_d_replication")},
                     indent=1))


if __name__ == "__main__":
    main()

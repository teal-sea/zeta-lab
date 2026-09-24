"""Phase 3 (checker/): snapshot two_adic/'s T_S for zeta, then R_S = Q - T_S.

two_adic/ builds T_S = T_inf + Delta_T as a float64 array (Delta_T measured
grade, error band a few 1e-3). This script snapshots it once per unit into
checker_ts_snapshot.json and writes the analysis to checker_ts_cells.json.

Fail closed. The snapshot is keyed to checker_glue.ts_key(): a digest of the
HEAD blobs of every T_S input (non-test .py under two_adic/ and kernel/,
kernel/*.json). Building refuses while any input is dirty in the working
tree, and the key is re-read before every unit: a digest change or a dirty
input stops the run. The 22:37 orphan (bare python3, keyed to HEAD while
ta_prolate.py was modified) is the failure this closes.

Route. One unit is one call of two_adic/'s ta_prolate.delta_T_cells for
(nvec, S, N) with all three cells, composed exactly as
ta_ts.KernelProvider.delta_T / T_S_matrix compose it:
T_S = provider.T_inf_matrix(c, N, dps) + (dT + dT^*)/2 real. The Mellin
transforms (the cost) do not depend on c, so one call serves the three
cells. test_checker_ts.py compares one unit with a live T_S_matrix call.

Units (per (nvec, S, N), all cells):
  converged rows (two_adic/ INTERFACE.md): (80, 1200, 8), (120, 1600, 16),
    (200, 2400, 32);
  mode-count response at N = 16: (80, 1600, 16) against (120, 1600, 16);
  quadrature response at N = 16: (120, 1200, 16) against (120, 1600, 16);
  same-settings P3: (80, 1200, 16) (N = 8 must be its central block);
  float64 floor of dps: the N = 8 unit also stores T_inf at dps 60.
The phase 1 dps 40 / 60 response cannot bite on a float64 Delta_T (it only
changes which kernel/ JSON supplies T_inf before rounding to float64); the
mode-count and quadrature responses replace it as the tolerance source.

    PYTHONPATH=$PWD <venv python> .../run_checker_ts.py --routed <hash> [--units 0,2] [--analyse <probe commit>]
"""

from __future__ import annotations

import argparse
import json
import os
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)

import numpy as np  # noqa: E402
from mpmath import mp  # noqa: E402

import checker_glue as GLUE  # noqa: E402
import checker_props as CP  # noqa: E402
import checker_q as CQ  # noqa: E402

CELLS = ["2.2", "2.5", "2.9"]
SETTINGS = GLUE.TS_SETTINGS
UNITS = [  # (nvec, S, N, role)
    (80, 1200, 8, "converged"),
    (120, 1600, 16, "converged"),
    (200, 2400, 32, "converged"),
    (80, 1600, 16, "mode_count_response"),
    (120, 1200, 16, "quadrature_response"),
    (80, 1200, 16, "same_settings_P3"),
    # added after the first analysis: 80 -> 120 modes moved T_S by up to 7.8e-2,
    # 90-96 % of it at |n| >= 12, so the converged rows are tested against MORE
    # modes (the response of a row to refinement, not of a coarser row)
    (160, 1600, 16, "mode_count_up"),
]
# Not run locally: (240, 2400, 32) at Kmax 14 was stopped at 16 min wall
# (9.2 min CPU, load average 8 to 9 on the shared laptop), against an estimate
# of 320 s. It is a CI proposal (RESULTS.md s7). N = 32 carries the N = 16
# refinement response of the same cell as a stated proxy.
CI_UNITS = [(240, 2400, 32, "mode_count_up")]
# 2026-09-24: the cloud container stands in for the CI job (operator: no
# GitHub Actions). CI_UNITS follow UNITS in the index space, so --units 7
# builds (240, 2400, 32).
ALL_UNITS = UNITS + CI_UNITS
SNAP = GLUE.TS_SNAPSHOT
OUT = os.path.join(HERE, "checker_ts_cells.json")


def unit_key(c, N, dps, nv, S):
    return f"{c}|{int(N)}|{int(dps)}|{int(nv)}|{int(S)}"


def _guard(digest0=None):
    digest, dirty = GLUE.ts_key()
    if dirty:
        raise SystemExit("refused: T_S inputs dirty in the working tree:\n  " + "\n  ".join(dirty))
    if digest0 is not None and digest != digest0:
        raise SystemExit(f"stopped: T_S input digest moved {digest0[:12]} -> {digest[:12]} during the run")
    return digest


def build_unit(nv, S, N, dps_list=(40,)):
    """{key: rows} for the three cells, composed as KernelProvider does."""
    ta_ts, _ = GLUE._ta()
    TP = GLUE._import(GLUE.TWO_ADIC, "ta_prolate")
    prov = ta_ts.KernelProvider(nv, S)
    pm = TP.ProlateModes(nvec=nv, dps=20)
    out, diag = TP.delta_T_cells(pm, CELLS, N, S=float(S), alpha=1.0)
    rows = {}
    for c in CELLS:
        dT = out[c][0]
        dT = ((dT + dT.conj().T) / 2).real
        for dps in dps_list:
            T = prov.T_inf_matrix(c, N, dps) + dT
            rows[unit_key(c, N, dps, nv, S)] = [[float(x) for x in r] for r in T]
    return rows, diag


def snapshot(routed, only=None):
    digest = _guard()
    head = GLUE._git("rev-parse", "HEAD").strip()
    meta = {"ts_inputs_digest": digest, "head_at_start": head, "routed_two_adic": routed,
            "python": sys.executable, "numpy": np.__version__,
            "route": "ta_prolate.delta_T_cells(ProlateModes(nvec, dps=20), cells, N, S, alpha=1) "
                     "+ KernelProvider(nvec, S).T_inf_matrix(c, N, dps), as ta_ts.T_S_matrix composes"}
    snap = {"meta": meta, "T_S": {}, "units": {}}
    if os.path.exists(SNAP):
        with open(SNAP) as fh:
            old = json.load(fh)
        if old["meta"].get("ts_inputs_digest") == digest:
            snap = old  # resume: same inputs
            snap["meta"]["routed_two_adic"] = routed
    for i, (nv, S, N, role) in enumerate(ALL_UNITS):
        if (only is None and i >= len(UNITS)) or (only is not None and i not in only):
            continue
        ukey = f"{nv}|{S}|{N}"
        if ukey in snap["units"]:
            continue
        _guard(digest)
        t = time.time()
        rows, diag = build_unit(nv, S, N, dps_list=(40, 60) if N == 8 else (40,))
        _guard(digest)  # inputs unchanged across the build
        stray = GLUE.loaded_inputs_outside_key()
        if stray:
            raise SystemExit("refused: T_S loaded modules outside the key: " + ", ".join(stray))
        snap["T_S"].update(rows)
        snap["units"][ukey] = {"role": role, "seconds": round(time.time() - t, 1),
                               "kmax": GLUE._import(GLUE.TWO_ADIC, "ta_prolate").kmax_for(nv),
                               "diag": diag}
        with open(SNAP, "w") as fh:  # checkpoint per unit
            json.dump(snap, fh)
        print(ukey, role, snap["units"][ukey]["seconds"], "s", flush=True)
    print("snapshot units:", sorted(snap["units"]), flush=True)
    return snap


# ----------------------------------------------------------------- analysis


def to_np(M):
    return np.array([[complex(M[i, j]) for j in range(M.cols)] for i in range(M.rows)])


def spec_norm(A):
    return float(np.linalg.norm(A, 2))


def probes(routed):
    """two_adic/'s Gram probe per converged row, read from ta_ts_prolate.json
    at the routed commit (git show), never from a working-tree copy."""
    rel = f"{GLUE.C4S2}/two_adic/ta_ts_prolate.json"
    rows = json.loads(GLUE._git("show", f"{routed}:{rel}"))["rows"]
    out = {}
    for c in CELLS:
        for N, (nv, S) in SETTINGS.items():
            hit = [r for r in rows if int(r["nvec"]) == nv and float(r["S"]) == S
                   and int(r["N"]) == N and float(r["c"]) == float(c)]
            if len(hit) != 1:
                raise KeyError(f"two_adic/ probe row (nvec={nv}, S={S}, N={N}, c={c}) at {routed}: {len(hit)} hits")
            out[(c, N)] = float(hit[0]["gram_sensitivity"])
    return out


def analyse(snap, probe_commit):
    T = {k: np.array(v) for k, v in snap["T_S"].items()}
    pr = probes(probe_commit)
    ta_ts, _ = GLUE._ta()
    out = {"meta": dict(snap["meta"], units=snap["units"], probe_commit=probe_commit,
                        band_rule="band(c, N) = max(two_adic/'s Gram probe for the delivered row, the "
                                  "refinement response ||T_S(more modes) - T_S(row)||_2, the quadrature "
                                  "response ||T_S(120, 1600) - T_S(120, 1200)||_2 at N = 16). Refinement: "
                                  "N = 8 row (80, 1200) against the central block of (160, 1600, 16); "
                                  "N = 16 row (120, 1600) against (160, 1600); N = 32 row: its own refinement "
                                  "(240, 2400) is a CI proposal, the N = 16 refinement response of the "
                                  "same cell is carried as a stated proxy. Weyl: no eigenvalue of R_S moves more than ||dT||_2 between "
                                  "the two builds. A refinement response indicates, it does not bound, the "
                                  "truncation error. band_cell(c) = max over N, used only where one threshold "
                                  "is needed across N (the monotonicity check).",
                        eig_route="numpy eigvalsh on float64 R = Q - T_S, Q rounded from dps 40; "
                                  "the rounding (1e-16 relative) is 13 orders below the band"),
           "cells": {}}
    for c in CELLS:
        Qfull = CQ.Q_matrix(c, 32, 40)
        rec = {}
        t8 = T[unit_key(c, 8, 40, 80, 1200)]
        t16 = T[unit_key(c, 16, 40, 120, 1600)]
        t32 = T[unit_key(c, 32, 40, 200, 2400)]
        u16 = T[unit_key(c, 16, 40, 160, 1600)]
        quad = spec_norm(t16 - T[unit_key(c, 16, 40, 120, 1200)])
        refine = {8: spec_norm(t8 - u16[8:25, 8:25]), 16: spec_norm(u16 - t16)}
        rec["quadrature_response_N16"] = quad
        rec["refinement_response"] = {"8": refine[8], "16": refine[16], "32": None}
        refine[32] = refine[16]  # proxy, kept for s7.3; the real 240-mode response is in door_N32_200_vs_240
        u32_key = unit_key(c, 32, 40, 240, 2400)
        has32 = u32_key in T  # (240, 2400, 32): CI_UNITS, built on the cloud container 2026-09-24
        # the coarser direction: two_adic/ lists (80, 1200) as converged at N = 16 too
        rec["mode_response_80_to_120_N16"] = spec_norm(t16 - T[unit_key(c, 16, 40, 80, 1600)])
        rec["mode_response_80_to_120_N16_central_N8"] = spec_norm((t16 - T[unit_key(c, 16, 40, 80, 1600)])[8:25, 8:25])
        rec["mode_response_120_to_160_N16"] = refine[16]
        rec["combined_response_N16_80_1200"] = spec_norm(t16 - T[unit_key(c, 16, 40, 80, 1200)])
        rec["P3_same_settings_defect"] = float(np.abs(t8 - T[unit_key(c, 16, 40, 80, 1200)][8:25, 8:25]).max())
        rec["P3_converged_rows_defect_norm"] = spec_norm(t8 - t16[8:25, 8:25])
        rec["P3_converged_rows_defect"] = float(np.abs(t8 - t16[8:25, 8:25]).max())
        rec["dps60_float64_floor_N8"] = float(np.abs(t8 - T[unit_key(c, 8, 60, 80, 1200)]).max())
        bands = {}
        for N, (nv, S) in SETTINGS.items():
            bands[N] = max(pr[(c, N)], refine[N], quad)
        rec["band_cell"] = max(bands.values())
        for N, (nv, S) in SETTINGS.items():
            TS = T[unit_key(c, N, 40, nv, S)]
            band = bands[N]
            Q = to_np(CQ.central_block(Qfull, N) if N < 32 else Qfull).real
            Tinf = ta_ts.KernelProvider(nv, S).T_inf_matrix(c, N, 40)
            R = Q - TS
            bases = CP.class_bases(c, N, 40)
            e_inf = np.linalg.eigvalsh(Q - Tinf)
            r = {"probe": pr[(c, N)], "refinement_response": refine[N] if N < 32 else None,
                 "refinement_proxy": refine[N] if N == 32 else None, "band": band,
                 "T_S_herm_defect": float(np.abs(TS - TS.T).max()),
                 "T_S_low3": [float(x) for x in np.linalg.eigvalsh(TS)[:3]],
                 "Q_low3": [float(x) for x in np.linalg.eigvalsh(Q)[:3]],
                 "R_inf_full": {"low3": [float(x) for x in e_inf[:3]],
                                "n_minus": int((e_inf < -band).sum()), "n_undecided": int((abs(e_inf) <= band).sum())}}
            w, V = np.linalg.eigh(R)
            nn = np.arange(-N, N + 1)
            top = (V[np.abs(nn) > N // 2, :] ** 2).sum(0)
            r["full_negatives_top_half_weight"] = [float(x) for x in top[w < -band]]
            r["full_n_minus_top_half"] = int(((w < -band) & (top > 0.5)).sum())
            for cls in ("full", "minus", "minus_zero"):
                B = to_np(bases[cls])
                e = np.linalg.eigvalsh(B.conj().T @ R @ B)
                neg, und, pos = CQ.inertia(list(e), band)
                r[cls] = {"low3": [float(x) for x in e[:3]], "n_minus": neg, "n_undecided": und,
                          "n_plus": pos, "undecided": [float(x) for x in e if abs(x) <= band],
                          "n_minus_at_band_cell": int((e < -rec["band_cell"]).sum()),
                          "dim": int(e.size)}
            # discriminator (2): R_S compressed to the resolved coordinates |n| <= N/2
            half = np.abs(nn) <= N // 2
            eh = np.linalg.eigvalsh(R[np.ix_(half, half)])
            r["resolved_half"] = {"dim": int(half.sum()), "low3": [float(x) for x in eh[:3]],
                                  "n_minus": int((eh < -band).sum()), "n_undecided": int((abs(eh) <= band).sum())}
            rec[str(N)] = r
        # discriminator (1): N = 16 at S = 1600, 80 / 120 / 160 modes, one threshold (band(c, 16));
        # and the N = 8 central blocks of the same three builds, at band(c, 8)
        Q16 = to_np(CQ.central_block(Qfull, 16)).real
        disc = {}
        for nv in (80, 120, 160):
            R16 = Q16 - T[unit_key(c, 16, 40, nv, 1600)]
            e16 = np.linalg.eigvalsh(R16)
            e8 = np.linalg.eigvalsh(R16[8:25, 8:25])
            k16 = int((e16 < -bands[16]).sum())
            disc[str(nv)] = {"N16_low3": [float(x) for x in e16[:3]],
                             "N16_n_minus": k16,
                             "N16_last_two_counted": [float(x) for x in e16[max(0, k16 - 2):k16]],
                             "N16_n_minus_at_band_cell": int((e16 < -rec["band_cell"]).sum()),
                             "N8_block_low3": [float(x) for x in e8[:3]],
                             "N8_block_n_minus": int((e8 < -bands[8]).sum())}
        # |n| <= 16 of the N = 32 row at band(c, 16): the same coordinates and threshold
        # as the full N = 16 builds above, at the best resolution held (200, 2400)
        R32 = to_np(Qfull).real - T[unit_key(c, 32, 40, 200, 2400)]
        e = np.linalg.eigvalsh(R32[16:49, 16:49])
        k = int((e < -bands[16]).sum())
        disc["200_N32_on_n_le_16"] = {"low3": [float(x) for x in e[:3]], "n_minus_at_band16": k,
                                      "last_two_counted": [float(x) for x in e[max(0, k - 2):k]]}
        rec["modes_N16_S1600"] = disc
        if has32:
            # RESULTS s7.6, the door: the N = 32 row (200 modes) against 240 modes.
            # Weyl: no eigenvalue of R_S moves more than weyl_response between the
            # two builds. Counted at two thresholds: the s7.3 band (N = 16 proxy)
            # and the band with the real N = 32 refinement response in it.
            Q32 = to_np(Qfull).real
            nn = np.arange(-32, 33)
            dT32 = T[u32_key] - t32
            resp = spec_norm(dT32)
            hi = np.abs(nn) > 16
            thr = {"band_s73": bands[32], "band_real": max(pr[(c, 32)], resp, quad)}
            door = {"weyl_response": resp, "weyl_response_central_N16": spec_norm(dT32[np.ix_(~hi, ~hi)]),
                    "weyl_response_top_half": spec_norm(dT32[np.ix_(hi, hi)]), **thr}
            for nv in (200, 240):
                w, V = np.linalg.eigh(Q32 - T[unit_key(c, 32, 40, nv, 2400)])
                top = (V[np.abs(nn) > 16, :] ** 2).sum(0)
                d = {"low3": [float(x) for x in w[:3]]}
                for name, b in thr.items():
                    neg = w < -b
                    d[name] = {"n_minus": int(neg.sum()), "n_minus_top_half": int((neg & (top > 0.5)).sum()),
                               "n_minus_resolved_half": int((neg & (top <= 0.5)).sum()),
                               "n_undecided": int((abs(w) <= b).sum()),
                               "negatives": [float(x) for x in w[neg]],
                               "top_half_negatives": [float(x) for x in w[neg & (top > 0.5)]]}
                door[str(nv)] = d
            rec["door_N32_200_vs_240"] = door
        out["cells"][c] = rec
        print(c, "analysed", flush=True)
    with open(OUT, "w") as fh:
        json.dump(out, fh, indent=1)
    return out


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--routed", required=True, help="two_adic/ commit routed by the coordinator")
    ap.add_argument("--units", default=None, help="comma-separated indices into UNITS (run in pieces)")
    ap.add_argument("--analyse", default=None, metavar="PROBE_COMMIT",
                    help="analyse after the snapshot step, reading two_adic/'s probe at this commit")
    a = ap.parse_args()
    only = None if a.units is None else {int(x) for x in a.units.split(",")}
    s = snapshot(a.routed, only)
    if a.analyse:
        analyse(s, a.analyse)

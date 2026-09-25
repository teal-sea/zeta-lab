"""Phase 3 (checker/): snapshot two_adic/'s T_S for zeta, then R_S = Q - T_S.

two_adic/ builds T_S = T_inf + Delta_T as a float64 array (Delta_T measured
grade, error band a few 1e-3). This script snapshots it once per unit into
checker_ts_snapshot.json and writes the analysis to checker_ts_cells.json.

Fail closed. The snapshot is keyed to checker_glue.ts_key(): a digest of the
HEAD blobs of every T_S input (the import closure of two_adic/ta_ts.py, found
by a static scan, plus kernel/cells_dps40.json and cells_dps60.json; until
2026-09-24 every non-test .py under two_adic/ and kernel/, and kernel/*.json).
Building refuses while any input is dirty in the working
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
    PYTHONPATH=$PWD <venv python> .../run_checker_ts.py --rebuild-rho [--timed-out 364|3060|32] --analyse c3dca00
(--merge-modal, the first follow-up's merge into the old-route snapshot, is at 3dc0a74.)
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
# of 320 s. It ran on Modal on 2026-09-24 (MODAL_UNITS below, merge_modal at 3dc0a74);
# until then N = 32 carried the N = 16 refinement response as a stated proxy.
CI_UNITS = [(240, 2400, 32, "mode_count_up")]
SNAP = GLUE.TS_SNAPSHOT
OUT = os.path.join(HERE, "checker_ts_cells.json")

# Follow-up of 2026-09-24: modal/ ran CI_UNITS and two_adic/'s default rule at
# N = 32 on Modal (build_unit, tree 284eff6, same T_S input digest). merge_modal
# copies those rows into the snapshot, read-only on modal/out, each unit marked
# with its source file and platform. The laptop 200|2400|32 rows are kept; the
# Modal builds of that unit are read from modal/out by the platform check only.
MODAL_OUT = os.path.abspath(os.path.join(HERE, "..", "modal", "out"))
MODAL_UNITS = [  # (nvec, S as passed, file, role); S is keyed as int(S)
    (240, 2400, "checker_240_2400_32.json", "mode_count_up (CI_UNITS)"),
    (280, 2266.1020257693895, "checker_280_2266_32.json", "default rule at c = 2.9"),
    (319, 2633.163333456407, "checker_319_2633_32.json", "default rule at c = 2.5"),
    (364, 3060.0807085398565, "checker_364_3060_32.json", "default rule at c = 2.2"),
]
MODAL_PLATFORM_ROWS = {"200_modal": "checker_200_2400_32.json",
                       "200_modal_sandybridge": "checker_200_2400_32_sandybridge.json"}
DEFAULT_ROW = {"2.2": 364, "2.5": 319, "2.9": 280}  # two_adic/'s rule nvec = int(8N/L) + 40

# Follow-up 2 of 2026-09-24 (RESULTS s7.8): two_adic/ c3dca00 evaluates rho by a QR
# of the Gram factor, T_S's input digest moved 1dcab230 -> b2e7787b, and modal/
# rebuilt all eleven units into modal/out_rho (tree e2b46a5). rebuild_rho builds
# a new snapshot from those files only; the old snapshot (old route, laptop rows
# plus the first Modal merge) stays in git history at 3dc0a74 (last written
# 8d66d09), and so do merge_modal and the s7.7 analysis (modes_n32 there).
MODAL_OUT_RHO = os.path.abspath(os.path.join(HERE, "..", "modal", "out_rho"))
RHO_ROUTED = "c3dca00"  # two_adic/ commit where rho changed and ta_ts_prolate.json was regenerated
OLD_ROUTE_COMMIT = "3dc0a74"  # the old snapshot and cells JSON, last written 8d66d09
RHO_UNITS = [(nv, S, N, role) for nv, S, N, role in UNITS] + [
    (nv, S, 32, role) for nv, S, _, role in MODAL_UNITS]
RHO_LOCAL_CALIBRATION = "local_checker_80_1200_8.json"
# The s7.8 reading (committed 49db49f, before any eigenvalue of a rebuilt row):
REFINED = {c: (240, DEFAULT_ROW[c]) for c in CELLS}  # clause 2
GATE_COND_F = 1e14  # clause 4: two_adic/ s10.4, "a row above about 1e14" is past A2's stopping point
A2_LAST_CLEAN = 6.7e11  # A2: rho off by 1.4e-5 at cond(F) = 6.7e11 (and 6.5e-2 at 3.8e14)
A3_DRIFT = 3.2e-12  # clause 10: two_adic/ A3, the QR route's largest change at (200, 2400), N = 32


def rho_file(nv, S, N):
    return f"checker_{int(nv)}_{int(S)}_{int(N)}.json"


def cond_F(diag):
    return max(float(diag["cond_Fz"]), float(diag["cond_Fb"]))


def p2_bin(low, band0):
    """s7.8 clause 7: the falsifier's bins, fixed before the run."""
    if low >= -band0:
        return "pass"
    if low >= -0.1:
        return "fails at order 1e-2"
    if low >= -1:
        return "fails at order 1e-1"
    return "fails at order 1 or more"


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
    for i, (nv, S, N, role) in enumerate(UNITS):
        if only is not None and i not in only:
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


def modal_unit(fname, nv, S, digest):
    """One modal/out checker file, checked before it may enter the snapshot:
    status ok, the in-container guard clean before and after, the same T_S
    input digest as here, exactly the unit and rows build_unit writes."""
    import hashlib

    path = os.path.join(MODAL_OUT, fname)
    with open(path, "rb") as fh:
        raw = fh.read()
    d = json.loads(raw)
    m = d["meta"]
    ukey = f"{nv}|{int(S)}|32"
    keys = {unit_key(c, 32, 40, nv, S) for c in CELLS}
    problems = []
    if m.get("status") != "ok":
        problems.append(f"status {m.get('status')}")
    if not (m["guard_before"]["ok"] and m["guard_after"]["ok"]):
        problems.append("in-container guard not clean")
    if not (m["ts_inputs_digest"] == m["guard_before"]["ts_inputs_digest"]
            == m["guard_after"]["ts_inputs_digest"] == digest):
        problems.append(f"digest {m['ts_inputs_digest'][:12]} != {digest[:12]}")
    if set(d["units"]) != {ukey} or set(d["T_S"]) != keys:
        problems.append(f"units {sorted(d['units'])}, rows {sorted(d['T_S'])}")
    if any(np.array(d["T_S"][k]).shape != (65, 65) for k in keys & set(d["T_S"])):
        problems.append("row shape")
    if problems:
        raise SystemExit(f"refused: {fname}: " + "; ".join(problems))
    u = dict(d["units"][ukey])
    u["source"] = {
        "file": f"{GLUE.C4S2}/modal/out/{fname}", "sha256": hashlib.sha256(raw).hexdigest(),
        "platform": m["machine"]["platform"], "python": m["machine"]["python"],
        "blas_core": m.get("blas_core"), "numpy": m["versions"]["numpy"],
        "tree_commit": m["tree_commit"], "ts_inputs_digest": m["ts_inputs_digest"],
        "weyl_bound": m["calibration"]["weyl_bound"],
        "arithmetic_floor_bound": m["calibration"]["arithmetic_floor_bound"]}
    return ukey, u, {k: d["T_S"][k] for k in keys}


def rho_unit(fname, nv, S, N, digest):
    """One modal/out_rho checker file, checked before it may enter the snapshot:
    status ok, the in-container guard clean before and after, the same T_S input
    digest as here, the calibration passed, exactly the unit, S and rows
    build_unit writes (dps 40 and 60 at N = 8, dps 40 otherwise), each row
    (2N + 1) square."""
    import hashlib

    path = os.path.join(MODAL_OUT_RHO, fname)
    with open(path, "rb") as fh:
        raw = fh.read()
    d = json.loads(raw)
    m = d["meta"]
    ukey = f"{nv}|{int(S)}|{int(N)}"
    dps_list = (40, 60) if int(N) == 8 else (40,)
    keys = {unit_key(c, N, dps, nv, S) for c in CELLS for dps in dps_list}
    problems = []
    if m.get("status") != "ok":
        problems.append(f"status {m.get('status')}")
    if not (m["guard_before"]["ok"] and m["guard_after"]["ok"]):
        problems.append("in-container guard not clean")
    if not (m["ts_inputs_digest"] == m["guard_before"]["ts_inputs_digest"]
            == m["guard_after"]["ts_inputs_digest"] == digest):
        problems.append(f"digest {m['ts_inputs_digest'][:12]} != {digest[:12]}")
    if not m.get("calibration", {}).get("passed"):
        problems.append("calibration not passed")
    if set(d["units"]) != {ukey} or set(d["T_S"]) != keys:
        problems.append(f"units {sorted(d['units'])}, rows {sorted(d['T_S'])}")
    elif float(d["units"][ukey].get("S_exact", S)) != float(S):
        problems.append(f"S {d['units'][ukey].get('S_exact')} != {S}")
    n = 2 * int(N) + 1
    if any(np.array(d["T_S"][k]).shape != (n, n) for k in keys & set(d["T_S"])):
        problems.append("row shape")
    if problems:
        raise SystemExit(f"refused: {fname}: " + "; ".join(problems))
    u = dict(d["units"][ukey])
    cal = m["calibration"]
    u["source"] = {
        "file": f"{GLUE.C4S2}/modal/out_rho/{fname}", "sha256": hashlib.sha256(raw).hexdigest(),
        "platform": m["machine"]["platform"], "python": m["machine"]["python"],
        "blas_core": m.get("blas_core"), "numpy": m["versions"]["numpy"],
        "tree_commit": m["tree_commit"], "ts_inputs_digest": m["ts_inputs_digest"],
        "child_wall_seconds": m.get("child_wall_seconds"), "wall_seconds": m.get("wall_seconds"),
        "calibration": {"unit": cal["unit"], "threshold": cal["threshold"], "max": cal["max"],
                        "passed": cal["passed"]}}
    return ukey, u, {k: d["T_S"][k] for k in keys}


def rebuild_rho(timed_out=()):
    """The snapshot under the QR route, from modal/out_rho only (s7.8). Refuses
    on a dirty or moved T_S input and on any file rho_unit refuses. Resumes a
    snapshot already built from out_rho under the same digest; a unit already
    in it must be bitwise equal. Units not yet landed are listed as pending,
    units modal/RUNS.md s7.6 records as timed out are passed in and listed."""
    digest = _guard()
    snap = None
    if os.path.exists(SNAP):
        with open(SNAP) as fh:
            old = json.load(fh)
        if old["meta"].get("ts_inputs_digest") == digest and old["meta"].get("source") == "modal/out_rho":
            snap = old
    if snap is None:
        snap = {"meta": {}, "T_S": {}, "units": {}}
    pending, trees = [], set()
    for nv, S, N, role in RHO_UNITS:
        ukey = f"{nv}|{int(S)}|{int(N)}"
        if not os.path.exists(os.path.join(MODAL_OUT_RHO, rho_file(nv, S, N))):
            if ukey not in timed_out:
                pending.append(ukey)
            continue
        ukey, u, rows = rho_unit(rho_file(nv, S, N), nv, S, N, digest)
        u["role"] = role
        for k, v in rows.items():
            if k in snap["T_S"] and snap["T_S"][k] != v:
                raise SystemExit(f"refused: {k} already in the snapshot with other values")
        snap["T_S"].update(rows)
        snap["units"][ukey] = u
        trees.add(u["source"]["tree_commit"])
    if len(trees) > 1:
        raise SystemExit(f"refused: units built from different trees {sorted(trees)}")
    snap["meta"] = {
        "ts_inputs_digest": digest, "source": "modal/out_rho", "date": "2026-09-24",
        "built_tree": trees.pop() if trees else None, "routed_two_adic": RHO_ROUTED,
        "head_at_rebuild": GLUE._git("rev-parse", "HEAD").strip(),
        "python": sys.executable, "numpy": np.__version__,
        "pending": pending, "timed_out": sorted(timed_out),
        "old_route": f"{OLD_ROUTE_COMMIT} (snapshot last written 8d66d09, digest 1dcab230, rho by np.linalg.inv)",
        "route": "run_checker_ts.build_unit(nvec, S, N, dps_list) on Modal, rho by QR of the Gram factor; "
                 "every row a Modal build (Linux x86_64 gVisor, Python 3.12, OpenBLAS), one route, one platform"}
    _guard(digest)
    with open(SNAP, "w") as fh:
        json.dump(snap, fh)
    print("rebuilt units:", ", ".join(sorted(snap["units"])), "| pending:", ", ".join(pending) or "none",
          flush=True)
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


def modes_n32(c, snap, T, Q, t32, u16, band0, proxy, n16, old_band32):
    """RESULTS s7.8: the N = 32 builds under the QR route, read by the reading
    committed in 49db49f before any eigenvalue of a rebuilt row. Returns the
    record and band(c, 32). The s7.7 version (old route, band from the
    240-mode row alone, platform check on three builds of one unit) is at
    3dc0a74."""
    nn = np.arange(-32, 33)
    builds = {"200": t32}
    for nv, S, _, _ in MODAL_UNITS:
        k = unit_key(c, 32, 40, nv, S)
        if k in T:
            builds[str(nv)] = T[k]
    ukeys = {"200": "200|2400|32", **{str(nv): f"{nv}|{int(S)}|32" for nv, S, _, _ in MODAL_UNITS}}
    diag = {name: snap["units"][ukeys[name]]["diag"] for name in builds}
    cF = {name: cond_F(diag[name]) for name in builds}
    ts_low = {name: float(np.linalg.eigvalsh(TS)[0]) for name, TS in builds.items()}
    resp = {name: spec_norm(TS - t32) for name, TS in builds.items()}
    # clauses 2 to 5: refined rows of the cell, the determinacy gate, P2 at band_0
    verdict = {}
    for nv in REFINED[c]:
        name = str(nv)
        if name not in builds:
            verdict[name] = {"admitted": False, "reason": "absent (timed out or not landed)"}
        elif cF[name] >= GATE_COND_F:
            verdict[name] = {"admitted": False, "reason": "past the determinacy gate (cond_F >= 1e14)"}
        elif ts_low[name] < -band0:
            verdict[name] = {"admitted": False, "reason": "fails P2 at band_0"}
        else:
            verdict[name] = {"admitted": True, "reason": None}
    admitted = [n for n, v in verdict.items() if v["admitted"]]
    # clause 6: the largest measured response among the admitted refined rows
    band = max([band0] + [resp[n] for n in admitted])
    refinement = max([resp[n] for n in admitted]) if admitted else None
    # clause 8: the criterion's referent, the 200-mode row's top-half negatives at the proxy band
    w200, V200 = np.linalg.eigh(Q - t32)
    top200 = (V200[np.abs(nn) > 16, :] ** 2).sum(0)
    depths = w200[(w200 < -proxy) & (top200 > 0.5)]
    # NOT part of the reading (added after the numbers, labelled as such in s7.8): the band
    # s7.7's rule would give, the 240-mode response alone, to show what the default-rule
    # row's response does to the count
    band240 = max(band0, resp["240"]) if "240" in admitted else band0
    out = {"band": band, "band_0": band0, "band_proxy": proxy, "old_band_32": old_band32,
           "sensitivity_band_240_only": band240,
           "refinement_response": refinement, "admitted": admitted, "n_minus_N16": n16,
           "cond_F_200": cF["200"], "top_half_depths_200_at_proxy_band": [float(x) for x in depths],
           "builds": {}}
    for name, TS in builds.items():
        flag = A3_DRIFT * max(1.0, cF[name] / cF["200"])  # clause 10, an estimate above the 200-mode row
        w, V = np.linalg.eigh(Q - TS)
        top = (V[np.abs(nn) > 16, :] ** 2).sum(0)
        k = int((w < -band).sum())
        dT = resp[name]
        wd, Vd = np.linalg.eigh(TS - t32)
        vd = Vd[:, np.argmax(np.abs(wd))]
        out["builds"][name] = {
            "cond_Fz": float(diag[name]["cond_Fz"]), "cond_Fb": float(diag[name]["cond_Fb"]),
            "cond_Gb": float(diag[name]["cond_Gb"]), "cond_F": cF[name],
            "past_gate": bool(cF[name] >= GATE_COND_F),
            "beyond_A2_last_clean": bool(A2_LAST_CLEAN < cF[name] < GATE_COND_F),
            "T_S_low": ts_low[name], "P2_bin": p2_bin(ts_low[name], band0),
            "P2_bin_at_old_band": p2_bin(ts_low[name], old_band32),
            "dT_vs_200": dT, "dT_vs_200_N8_block": spec_norm((TS - t32)[24:41, 24:41]),
            "dT_top_eigvec_weight_on_n_gt_16": float((vd[np.abs(nn) > 16] ** 2).sum()) if dT > 0 else None,
            "N16_block_vs_160_1600": spec_norm(TS[16:49, 16:49] - u16),
            "n_minus": k, "n_minus_top_half": int(((w < -band) & (top > 0.5)).sum()),
            "low3": [float(x) for x in w[:3]], "last_two_counted": [float(x) for x in w[max(0, k - 2):k]],
            "first_not_counted": float(w[k]), "min_gap_to_band": float(np.abs(w + band).min()),
            "platform_flag": flag, "n_flagged": int((np.abs(w + band) <= flag).sum()),
            "n_minus_range": [int((w < -band - flag).sum()), int((w < -band + flag).sum())],
            "n_minus_at_proxy_band": int((w < -proxy).sum()),
            "sensitivity_n_minus_at_band_240_only": int((w < -band240).sum()),
            "n_minus_top_half_at_proxy_band": int(((w < -proxy) & (top > 0.5)).sum()),
            "top_half_depths_exceeded_by_dT": int((np.abs(depths) < dT).sum()),
            "n_kept_by_weyl": int((w200 < -band - dT).sum())}
    # clause 9: per admitted refined row, then the cell
    for name, v in verdict.items():
        if v["admitted"]:
            lo, hi = out["builds"][name]["n_minus_range"]
            v["label"] = "survives" if lo > n16 else ("falls" if hi <= n16 else "undecided")
        else:
            v["label"] = "not admitted"
    labels = {verdict[n]["label"] for n in admitted}
    if not admitted:
        cell = "undecided, no admitted refinement"
    elif labels == {"survives"}:
        cell = "survives"
    elif labels == {"falls"}:
        cell = "falls"
    else:
        cell = "split"
    out["s7_6_verdict"] = verdict
    out["cell_verdict"] = cell
    return out, band, refinement


def old_route_cells():
    """The cells JSON of the old route (rho by np.linalg.inv), from git history."""
    return json.loads(GLUE._git("show", f"{OLD_ROUTE_COMMIT}:{GLUE.C4S2}/checker/checker_ts_cells.json"))


def _eig_change(a, b):
    """Largest change between two lists of eigenvalues of equal length, else None."""
    if a is None or b is None or len(a) != len(b):
        return None
    return max((abs(x - y) for x, y in zip(a, b)), default=0.0)


def vs_old(rec, old):
    """s7.8 clause 11: N = 8 and 16 against the old route (3dc0a74). Counts
    compared exactly; bands, probes and listed eigenvalues by largest change."""
    out = {}
    for N in ("8", "16"):
        a, b = rec[N], old[N]
        counts = lambda x: [x["full_n_minus_top_half"], x["resolved_half"]["n_minus"],  # noqa: E731
                            x["resolved_half"]["n_undecided"], x["R_inf_full"]["n_minus"]] + [
            x[cls][k] for cls in ("full", "minus", "minus_zero") for k in ("n_minus", "n_undecided", "n_plus")]
        ch = [_eig_change(a[cls]["low3"], b[cls]["low3"]) for cls in ("full", "minus", "minus_zero")]
        ch += [_eig_change(a[cls]["undecided"], b[cls]["undecided"]) for cls in ("full", "minus", "minus_zero")]
        ch += [_eig_change(a["resolved_half"]["low3"], b["resolved_half"]["low3"]),
               _eig_change(a["T_S_low3"], b["T_S_low3"])]
        out[N] = {"counts_equal": counts(a) == counts(b), "counts_new": counts(a), "counts_old": counts(b),
                  "band_change": abs(a["band"] - b["band"]), "probe_change": abs(a["probe"] - b["probe"]),
                  "max_eig_change": max(x for x in ch if x is not None),
                  "undecided_lengths_equal": all(len(a[cls]["undecided"]) == len(b[cls]["undecided"])
                                                 for cls in ("full", "minus", "minus_zero"))}
    m_new, m_old = rec["modes_N16_S1600"], old["modes_N16_S1600"]
    keys = ("80", "120", "160", "80_S1200")
    out["modes_N16_S1600"] = {
        "counts_equal": all([m_new[k][f] for f in ("N16_n_minus", "N16_n_minus_top_half", "N8_block_n_minus")]
                            == [m_old[k][f] for f in ("N16_n_minus", "N16_n_minus_top_half", "N8_block_n_minus")]
                            for k in keys),
        "max_eig_change": max(max(_eig_change(m_new[k]["N16_low3"], m_old[k]["N16_low3"]),
                                  _eig_change(m_new[k]["N8_block_low3"], m_old[k]["N8_block_low3"])) for k in keys)}
    for k in ("quadrature_response_N16", "mode_response_80_to_120_N16", "mode_response_120_to_160_N16",
              "P3_converged_rows_defect_norm"):
        out[k + "_change"] = abs(rec[k] - old[k])
    return out


def analyse(snap, probe_commit):
    T = {k: np.array(v) for k, v in snap["T_S"].items()}
    pr = probes(probe_commit)
    ta_ts, _ = GLUE._ta()
    OLD = old_route_cells()["cells"]
    with open(os.path.join(MODAL_OUT_RHO, RHO_LOCAL_CALIBRATION)) as fh:
        loc = json.load(fh)["T_S"]
    platform_n8 = max(float(np.abs(np.array(v) - T[k]).max()) for k, v in loc.items())
    missing32 = [f"{nv}|{int(S)}|32" for nv, S, _, _ in MODAL_UNITS if f"{nv}|{int(S)}|32" not in snap["units"]]
    pending32 = [u for u in missing32 if u in snap["meta"].get("pending", [])]
    out = {"meta": dict(snap["meta"], units=snap["units"], probe_commit=probe_commit,
                        reading_commit="49db49f", platform_N8_local_vs_modal=platform_n8,
                        n32_pending=pending32,
                        band_rule="band(c, N) = max(two_adic/'s Gram probe for the delivered row, the "
                                  "refinement response, the quadrature response ||T_S(120, 1600) - "
                                  "T_S(120, 1200)||_2 at N = 16). Refinement: N = 8 row (80, 1200) against "
                                  "the central block of (160, 1600, 16); N = 16 row (120, 1600) against "
                                  "(160, 1600); N = 32 row (200, 2400): the largest ||T_S(X) - T_S(200, 2400)||_2 "
                                  "over the admitted refined rows X of the cell ((240, 2400) and the cell's "
                                  "default-rule row; admitted = max(cond_Fz, cond_Fb) < 1e14 and no eigenvalue "
                                  "of T_S(X) below -band_0, band_0 = max(probe, quadrature)), s7.8, read in "
                                  "49db49f before any eigenvalue. A refinement response indicates, it does not "
                                  "bound, the truncation error. band_cell(c) = max over N, used only where one "
                                  "threshold is needed across N (the monotonicity check).",
                        eig_route="numpy eigvalsh on float64 R = Q - T_S, Q rounded from dps 40; "
                                  "the rounding (1e-16 relative) is 13 orders below the band"),
           "cells": {}}
    for c in CELLS:
        Qfull = CQ.Q_matrix(c, 32, 40)
        Q32 = to_np(Qfull).real
        rec = {}
        t8 = T[unit_key(c, 8, 40, 80, 1200)]
        t16 = T[unit_key(c, 16, 40, 120, 1600)]
        t32 = T[unit_key(c, 32, 40, 200, 2400)]
        u16 = T[unit_key(c, 16, 40, 160, 1600)]
        quad = spec_norm(t16 - T[unit_key(c, 16, 40, 120, 1200)])
        refine = {8: spec_norm(t8 - u16[8:25, 8:25]), 16: spec_norm(u16 - t16)}
        rec["quadrature_response_N16"] = quad
        rec["mode_response_80_to_120_N16"] = spec_norm(t16 - T[unit_key(c, 16, 40, 80, 1600)])
        rec["mode_response_80_to_120_N16_central_N8"] = spec_norm((t16 - T[unit_key(c, 16, 40, 80, 1600)])[8:25, 8:25])
        rec["mode_response_120_to_160_N16"] = refine[16]
        rec["mode_response_120_to_160_N16_central_N8"] = spec_norm((u16 - t16)[8:25, 8:25])
        rec["combined_response_N16_80_1200"] = spec_norm(t16 - T[unit_key(c, 16, 40, 80, 1200)])
        rec["P3_same_settings_defect"] = float(np.abs(t8 - T[unit_key(c, 16, 40, 80, 1200)][8:25, 8:25]).max())
        rec["P3_converged_rows_defect_norm"] = spec_norm(t8 - t16[8:25, 8:25])
        rec["P3_converged_rows_defect"] = float(np.abs(t8 - t16[8:25, 8:25]).max())
        rec["dps60_float64_floor_N8"] = float(np.abs(t8 - T[unit_key(c, 8, 60, 80, 1200)]).max())
        bands = {8: max(pr[(c, 8)], refine[8], quad), 16: max(pr[(c, 16)], refine[16], quad)}
        band0 = max(pr[(c, 32)], quad)
        proxy = max(pr[(c, 32)], refine[16], quad)
        rec["band_32_proxy"] = proxy
        rec["band_0_32"] = band0
        # N = 32 is analysed once the cell's refined rows are in (landed, or recorded as timed out);
        # the grade is final only when all eleven are (s7.8 clause 12)
        cell_pending = [u for u in pending32 if int(u.split("|")[0]) in REFINED[c]]
        ready32 = not cell_pending
        rec["refinement_response"] = {"8": refine[8], "16": refine[16], "32": None}
        order = (8, 16, 32) if ready32 else (8, 16)
        for N in order:
            nv, S = SETTINGS[N]
            TS = T[unit_key(c, N, 40, nv, S)]
            if N == 32:
                m32, bands[32], refine[32] = modes_n32(c, snap, T, Q32, t32, u16, band0, proxy,
                                                       rec["16"]["full"]["n_minus"], OLD[c]["32"]["band"])
                rec["refinement_response"]["32"] = refine[32]
            band = bands[N]
            Q = to_np(CQ.central_block(Qfull, N) if N < 32 else Qfull).real
            Tinf = ta_ts.KernelProvider(nv, S).T_inf_matrix(c, N, 40)
            R = Q - TS
            bases = CP.class_bases(c, N, 40)
            e_inf = np.linalg.eigvalsh(Q - Tinf)
            r = {"probe": pr[(c, N)], "refinement_response": refine[N], "band": band,
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
                          "eigs": [float(x) for x in e], "dim": int(e.size)}
            # discriminator (2): R_S compressed to the resolved coordinates |n| <= N/2
            half = np.abs(nn) <= N // 2
            eh = np.linalg.eigvalsh(R[np.ix_(half, half)])
            r["resolved_half"] = {"dim": int(half.sum()), "low3": [float(x) for x in eh[:3]],
                                  "n_minus": int((eh < -band).sum()), "n_undecided": int((abs(eh) <= band).sum())}
            rec[str(N)] = r
            if N == 32:
                rec["modes_N32"] = m32
        if ready32:
            rec["band_cell"] = max(bands.values())
            for N in order:
                for cls in ("full", "minus", "minus_zero"):
                    e = np.array(rec[str(N)][cls]["eigs"])
                    rec[str(N)][cls]["n_minus_at_band_cell"] = int((e < -rec["band_cell"]).sum())
        else:
            rec["32"] = {"pending": cell_pending}
        for N in order:
            for cls in ("full", "minus", "minus_zero"):
                del rec[str(N)][cls]["eigs"]
        # discriminator (1): N = 16 at S = 1600, 80 / 120 / 160 modes, one threshold (band(c, 16));
        # and the N = 8 central blocks of the same three builds, at band(c, 8)
        Q16 = to_np(CQ.central_block(Qfull, 16)).real
        disc = {}
        n16 = np.arange(-16, 17)
        for nv, SS, key in ((80, 1600, "80"), (120, 1600, "120"), (160, 1600, "160"), (80, 1200, "80_S1200")):
            R16 = Q16 - T[unit_key(c, 16, 40, nv, SS)]
            e16 = np.linalg.eigvalsh(R16)
            e8 = np.linalg.eigvalsh(R16[8:25, 8:25])
            k16 = int((e16 < -bands[16]).sum())
            w16, V16 = np.linalg.eigh(R16)
            top16 = (V16[np.abs(n16) > 8, :] ** 2).sum(0)
            disc[key] = {"N16_low3": [float(x) for x in e16[:3]],
                         "N16_n_minus_top_half": int(((w16 < -bands[16]) & (top16 > 0.5)).sum()),
                         "N16_n_minus": k16,
                         "N16_last_two_counted": [float(x) for x in e16[max(0, k16 - 2):k16]],
                         "N8_block_low3": [float(x) for x in e8[:3]],
                         "N8_block_n_minus": int((e8 < -bands[8]).sum())}
            if ready32:
                disc[key]["N16_n_minus_at_band_cell"] = int((e16 < -rec["band_cell"]).sum())
        # |n| <= 16 of the N = 32 row at band(c, 16): the same coordinates and threshold
        # as the full N = 16 builds above, at the delivered N = 32 row (200, 2400)
        e = np.linalg.eigvalsh((Q32 - t32)[16:49, 16:49])
        k = int((e < -bands[16]).sum())
        disc["200_N32_on_n_le_16"] = {"low3": [float(x) for x in e[:3]], "n_minus_at_band16": k,
                                      "last_two_counted": [float(x) for x in e[max(0, k - 2):k]]}
        rec["modes_N16_S1600"] = disc
        rec["vs_old_route"] = vs_old(rec, OLD[c])
        out["cells"][c] = rec
        print(c, "analysed", f"(N = 32 pending: {cell_pending})" if not ready32 else "", flush=True)
    with open(OUT, "w") as fh:
        json.dump(out, fh, indent=1)
    return out


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--routed", default=None, help="two_adic/ commit routed by the coordinator (builds units)")
    ap.add_argument("--units", default=None, help="comma-separated indices into UNITS (run in pieces)")
    ap.add_argument("--rebuild-rho", action="store_true",
                    help="build the snapshot from modal/out_rho (follow-up 2, s7.8; no local build)")
    ap.add_argument("--timed-out", default="", help="comma-separated unit keys modal/RUNS.md s7.6 records as timed out")
    ap.add_argument("--analyse", default=None, metavar="PROBE_COMMIT",
                    help="analyse after the snapshot step, reading two_adic/'s probe at this commit")
    a = ap.parse_args()
    if a.routed is None and not a.rebuild_rho:
        ap.error("--routed or --rebuild-rho")
    if a.routed is not None:
        only = None if a.units is None else {int(x) for x in a.units.split(",")}
        s = snapshot(a.routed, only)
    if a.rebuild_rho:
        s = rebuild_rho(tuple(x for x in a.timed_out.split(",") if x))
    if a.analyse:
        analyse(s, a.analyse)

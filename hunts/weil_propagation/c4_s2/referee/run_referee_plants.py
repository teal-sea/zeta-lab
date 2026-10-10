"""referee/, phase 1: planted errors of known size in the Delta_T build.

Written before any code in bound_trunc/, bound_quad/ or assembler/ was read.
Runs the plants of BRIEF.md "Phase 1" item 1 locally (every unit under ten
minutes) and writes referee_plants.json: per unit its configuration, run
time, cond(F) of both Gram factors, and a sha256 of each Delta_T it built;
per pair (degraded or perturbed build a, reference b) and per (c, N) the
spectral norm ||Delta_T_a - Delta_T_b||_2 (float64 eigvalsh, one route),
an exact lower bound of it (a Rayleigh quotient over the rationals) and an
exact upper bound of the Frobenius norm (every entry difference formed over
the rationals). The bounds are not read here; test_referee_bounds.py
compares these numbers with them.

Kinds of pair (the fixed interface eps(c, N, nvec, S, Kmax) decides which):

- "interface": a and b differ only in (nvec, S, Kmax), so the bound can be
  evaluated at both. Implied by a valid bound: change <= eps_a + eps_b.
- "refinement": b refines a knob the interface does not carry (w Gauss nodes
  per panel, s panel width or nodes, tail-series terms, derivative orders),
  or perturbs a by a relative size at or below the samples' measured float64
  error, or replaces a stable step by another stable route. The bound can
  only be evaluated at a's configuration.
- "outside": a coarsens a knob the interface does not carry; measured only,
  the bound makes no statement about it.
- "defect": a is a code defect (a dropped mode, the pre-2026-09-24 explicit
  inverse); the bound is not meant to cover it.

    PYTHONPATH=<worktree root> <venv python> run_referee_plants.py [--only u1,u2] [--pairs]
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)

import numpy as np  # noqa: E402

import referee_lib as RL  # noqa: E402

NS = (8, 16, 32)
EPS_REL = 2.0 ** -53  # unit roundoff, as two_adic/ s10.2 A3
SAMPLE_REL = 1e-13  # the float64 samples' measured relative error at s = 0 (two_adic/ s10.1: 1.2e-13)

# name: kwargs of referee_lib.delta_T_knobs. Units whose knobs leave the hats
# unchanged (a perturbation of Z, B, J, A, the rho route, the assembly, a
# dropped mode) reuse the last hats evaluation (referee_lib._HATS_CACHE), so
# run them right after their base unit.
UNITS = {
    # interface family: nvec, S, Kmax
    "ref_80_2400": dict(nvec=80, S=2400),
    "tr_40_2400": dict(nvec=40, S=2400),
    "tr_60_2400": dict(nvec=60, S=2400),
    "sq_80_800": dict(nvec=80, S=800),
    "sq_80_1200": dict(nvec=80, S=1200),
    "km_40_1200_K8": dict(nvec=40, S=1200, Kmax=8),
    "km_40_1200_K9": dict(nvec=40, S=1200, Kmax=9),
    "km_40_1200_K10": dict(nvec=40, S=1200, Kmax=10),
    "km_40_1200_K12": dict(nvec=40, S=1200, Kmax=12),
    # refinements and perturbations of (80, 1200), a stored build
    "wpp16_80_1200": dict(nvec=80, S=1200, w_per_panel=16),
    "spp12_80_1200": dict(nvec=80, S=1200, s_per_panel=12),
    "sw05_80_1200": dict(nvec=80, S=1200, s_width=0.5),
    "terms40_80_1200": dict(nvec=80, S=1200, terms=40, far_terms=16, far_mmax=8),
    "mderiv20_80_1200": dict(nvec=80, S=1200, mderiv=20),
    "pert_eps_80_1200": dict(nvec=80, S=1200, perturb={"Z": EPS_REL, "B": EPS_REL, "J": EPS_REL, "A": EPS_REL}),
    "pert_zw_80_1200": dict(nvec=80, S=1200, perturb={"zeta_w": SAMPLE_REL}),
    "svd_80_1200": dict(nvec=80, S=1200, rho_route="svd"),
    "fsum_80_1200": dict(nvec=80, S=1200, assembly="fsum", Ns=(8, 16)),
    # the ill-conditioned regime: cond(F_z) 6.7e11 at (80, 200) and 3.8e14 at (80, 150)
    # (two_adic/ s10.3 A2), around the 1.9e13 to 2.1e13 of the stored 280, 319, 364-mode rows
    "base_80_200": dict(nvec=80, S=200),
    "pert_eps_80_200": dict(nvec=80, S=200, perturb={"Z": EPS_REL, "B": EPS_REL, "J": EPS_REL, "A": EPS_REL}),
    "svd_80_200": dict(nvec=80, S=200, rho_route="svd"),
    "inv_80_200": dict(nvec=80, S=200, rho_route="inv"),
    "pert_zw_80_200": dict(nvec=80, S=200, perturb={"zeta_w": SAMPLE_REL}),
    "base_80_150": dict(nvec=80, S=150),
    "pert_eps_80_150": dict(nvec=80, S=150, perturb={"Z": EPS_REL, "B": EPS_REL, "J": EPS_REL, "A": EPS_REL}),
    "svd_80_150": dict(nvec=80, S=150, rho_route="svd"),
    "pert_zw_80_150": dict(nvec=80, S=150, perturb={"zeta_w": SAMPLE_REL}),
    # outside the interface (measured only)
    "wpp6_40_1200": dict(nvec=40, S=1200, Kmax=10, w_per_panel=6),
    # code defects (not covered, labelled)
    "drop0_80_2400": dict(nvec=80, S=2400, drop=(0,)),
    "drop10_80_2400": dict(nvec=80, S=2400, drop=(10,)),
}

# (a, b, kind, what it plants, the error source of BRIEF.md's table it exercises)
PAIRS = [
    ("tr_40_2400", "ref_80_2400", "interface", "nvec 40 against 80 at S = 2400, Kmax 10", "trunc"),
    ("tr_60_2400", "ref_80_2400", "interface", "nvec 60 against 80 at S = 2400, Kmax 10", "trunc"),
    ("tr_40_2400", "tr_60_2400", "interface", "nvec 40 against 60 at S = 2400, Kmax 10", "trunc"),
    ("sq_80_800", "ref_80_2400", "interface", "S 800 against 2400 at nvec 80", "s_cutoff"),
    ("sq_80_1200", "ref_80_2400", "interface", "S 1200 against 2400 at nvec 80", "s_cutoff"),
    ("sq_80_800", "sq_80_1200", "interface", "S 800 against 1200 at nvec 80", "s_cutoff"),
    ("km_40_1200_K8", "km_40_1200_K12", "interface", "Kmax 8 against 12 at (40, 1200)", "w_dyadic"),
    ("km_40_1200_K9", "km_40_1200_K12", "interface", "Kmax 9 against 12 at (40, 1200)", "w_dyadic"),
    ("km_40_1200_K10", "km_40_1200_K12", "interface", "Kmax 10 against 12 at (40, 1200)", "w_dyadic"),
    ("base_80_200", "ref_80_2400", "interface", "S 200 against 2400 at nvec 80 (cond(F_z) about 7e11)", "s_cutoff"),
    ("base_80_150", "ref_80_2400", "interface", "S 150 against 2400 at nvec 80 (cond(F_z) about 4e14)", "s_cutoff"),
    ("sq_80_1200", "wpp16_80_1200", "refinement", "w Gauss nodes per panel 12 -> 16", "w_panels"),
    ("sq_80_1200", "spp12_80_1200", "refinement", "s Gauss nodes per panel 8 -> 12", "s_panels"),
    ("sq_80_1200", "sw05_80_1200", "refinement", "s panel width 1 -> 0.5", "s_panels"),
    ("sq_80_1200", "terms40_80_1200", "refinement", "tail series 25 -> 40 terms, dilates 8 -> 16 terms and orders 4 -> 8", "w_tail_terms"),
    ("sq_80_1200", "mderiv20_80_1200", "refinement", "derivative orders of phi~_n at 1, 14 -> 20", "w_tail_terms"),
    ("sq_80_1200", "pert_eps_80_1200", "refinement", "Z, B, J, A times (1 + 2^-53 u), u uniform", "gram_step"),
    ("sq_80_1200", "pert_zw_80_1200", "refinement", "zeta_n(w) samples times (1 + 1e-13 u)", "mode_data"),
    ("sq_80_1200", "svd_80_1200", "refinement", "rho by SVD of the Gram factor instead of QR", "gram_step"),
    ("sq_80_1200", "fsum_80_1200", "refinement", "assembly sums over s correctly rounded (math.fsum)", "assembly"),
    ("base_80_200", "pert_eps_80_200", "refinement", "Z, B, J, A times (1 + 2^-53 u) at cond(F_z) about 7e11", "gram_step"),
    ("base_80_200", "pert_zw_80_200", "refinement", "zeta_n(w) samples times (1 + 1e-13 u) at cond(F_z) about 7e11", "mode_data"),
    ("base_80_200", "svd_80_200", "refinement", "rho by SVD instead of QR at cond(F_z) about 7e11", "gram_step"),
    ("base_80_150", "pert_eps_80_150", "refinement", "Z, B, J, A times (1 + 2^-53 u) at cond(F_z) about 4e14", "gram_step"),
    ("base_80_150", "pert_zw_80_150", "refinement", "zeta_n(w) samples times (1 + 1e-13 u) at cond(F_z) about 4e14", "mode_data"),
    ("base_80_150", "svd_80_150", "refinement", "rho by SVD instead of QR at cond(F_z) about 4e14", "gram_step"),
    ("wpp6_40_1200", "km_40_1200_K10", "outside", "w Gauss nodes per panel 6 against 12 (a coarsening the interface cannot express)", "w_panels"),
    ("drop0_80_2400", "ref_80_2400", "defect", "mode 0 dropped from the family of 80", "none"),
    ("drop10_80_2400", "ref_80_2400", "defect", "mode 10 dropped from the family of 80", "none"),
    ("inv_80_200", "base_80_200", "defect", "rho by np.linalg.inv of the formed Gram (the pre-c3dca00 route) at cond(G_z) about 4.5e23", "none"),
]

OUT = RL.PLANTS_JSON


def sha(D):
    return hashlib.sha256(np.ascontiguousarray(np.asarray(D, dtype=float)).tobytes()).hexdigest()


def upper_float(q):
    """A float64 at or above the rational q."""
    f = float(q)
    while RL.to_q(f) < q:
        f = math.nextafter(f, math.inf)
    return f


def lower_float(q):
    """A float64 at or below the rational q."""
    f = float(q)
    while RL.to_q(f) > q:
        f = math.nextafter(f, -math.inf)
    return f


def build(name):
    kw = dict(UNITS[name])
    Ns = kw.pop("Ns", NS)
    nvec, S = kw.pop("nvec"), kw.pop("S")
    t = time.time()
    out, diag = RL.delta_T_knobs(nvec, S, Ns=Ns, **kw)
    rec = {"config": {"nvec": nvec, "S": S, **{k: (list(v) if isinstance(v, tuple) else v) for k, v in kw.items()}},
           "Ns": list(Ns), "diag": diag, "seconds": round(time.time() - t, 1),
           "sha256": {f"{c}|{N}": sha(D) for (c, N), D in out.items()}}
    return rec, out


def load_out():
    if os.path.exists(OUT):
        with open(OUT) as fh:
            return json.load(fh)
    return {"meta": {}, "units": {}, "pairs": []}


def save(doc):
    with open(OUT, "w") as fh:
        json.dump(doc, fh, indent=1)


def run_units(names, cache):
    doc = load_out()
    for name in names:
        print("unit", name, flush=True)
        rec, out = build(name)
        doc["units"][name] = rec
        cache[name] = out
        np.savez_compressed(os.path.join(SCRATCH, f"{name}.npz"),
                            **{f"{c}|{N}": D for (c, N), D in out.items()})
        save(doc)  # checkpoint per unit
        print("  ", rec["seconds"], "s", rec["diag"], flush=True)


def load_mats(name, snap):
    if name.startswith("stored:"):
        nv, S, N = (int(x) for x in name.split(":")[1].split("|"))
        return {(c, N): RL.stored_TS(snap, c, N, nv, S) - RL.T_inf(c, N) for c in RL.CELLS}
    z = np.load(os.path.join(SCRATCH, f"{name}.npz"))
    out = {}
    for k in z.files:
        c, N = k.split("|")
        out[(float(c), int(N))] = z[k]
    return out


def run_pairs():
    doc = load_out()
    snap = RL.load_json(RL.SNAPSHOT)
    pairs = []
    for a, b, kind, what, source in PAIRS:
        Ma, Mb = load_mats(a, snap), load_mats(b, snap)
        rows = []
        for key in sorted(set(Ma) & set(Mb)):
            D = Ma[key] - Mb[key]
            lo = RL.rayleigh_lower_q(Ma[key], Mb[key])
            rows.append({"c": key[0], "N": key[1], "spec": RL.spec(D),
                         "spec_lower": lower_float(lo),
                         "frob_upper": upper_float(RL.frob_upper_q(Ma[key], Mb[key]))})
        cfg = lambda n: doc["units"][n]["config"] if n in doc["units"] else {"stored": n}  # noqa: E731
        pairs.append({"a": a, "b": b, "kind": kind, "what": what, "source": source,
                      "config_a": cfg(a), "config_b": cfg(b), "rows": rows})
        print(a, b, kind, max(r["spec"] for r in rows), flush=True)
    doc["pairs"] = pairs
    doc["meta"] = {"script": "referee/run_referee_plants.py", "eps_rel": EPS_REL, "sample_rel": SAMPLE_REL,
                   "numpy": np.__version__, "python": sys.version.split()[0],
                   "note": "Delta_T as the snapshot stores it: real part of the Hermitian part of M_inf - M_S"}
    save(doc)


SCRATCH = os.environ.get("REFEREE_SCRATCH", os.path.join(HERE, ".plants_cache"))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--only", default=None, help="comma-separated unit names")
    ap.add_argument("--pairs", action="store_true", help="form the pair norms from cached units")
    a = ap.parse_args()
    os.makedirs(SCRATCH, exist_ok=True)
    if a.only:
        run_units(a.only.split(","), {})
    if a.pairs:
        run_pairs()


if __name__ == "__main__":
    main()

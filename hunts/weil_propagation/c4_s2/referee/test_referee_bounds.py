"""referee/, phase 1: falsification tests of the Delta_T error bound.

Written and committed before any code or text in bound_trunc/, bound_quad/
or assembler/ was read (BRIEF.md, Independence). They test the bound
through the interface BRIEF.md fixed in advance:

    bound_trunc/eps_trunc.py: eps_trunc(c, N, nvec, S, Kmax) -> flint.arb
    bound_quad/eps_quad.py:   eps_quad(c, N, nvec, S, Kmax) -> flint.arb
    bound_trunc/eps_trunc.json, bound_quad/eps_quad.json: lists of entries
        {"c", "N", "nvec", "S", "Kmax", "eps_upper", "grade", "assumptions"}

called here as eps(c: float, N: int, nvec: int, S: float, Kmax: int). The
bound on Delta_T of one build is eps = eps_trunc + eps_quad (Q and T_inf
cancel in every difference below, so assembler/'s terms do not enter).

The inequality. For two builds a, b of the same (c, N), a valid bound gives

    ||Delta_T_a - Delta_T_b||_2 <= ||Delta_T_a - Delta_T_exact||_2 + ||Delta_T_exact - Delta_T_b||_2 <= eps_a + eps_b.   (I)

That is all it implies. Anything stronger carries an assumption, named where
it is used:

  M  (refined reference): b refines a far enough that the change a -> b is
     most of a's error, so eps_a alone >= ||Delta_T_a - Delta_T_b||_2. The
     brief's "the bound at the degraded configuration dominates the measured
     change" is (I) under M.
  R  (refinement inside the model): a knob the interface does not carry is
     refined, or the samples are perturbed within their measured float64
     error, and the bound at a's (c, N, nvec, S, Kmax) is taken to cover the
     refined or perturbed build as well; then (I) reads change <= 2 eps_a.
  D  (decomposition): eps_quad bounds the distance from the stored Delta_T to
     the exact Delta_T of the same nvec modes, as the error-source table of
     BRIEF.md assigns it; then a change that leaves the modes fixed is at
     most 2 eps_quad(a) under R.

The interface mismatch (a finding about the interface, not a test detail).
eps takes (c, N, nvec, S, Kmax) only. The w Gauss nodes per panel (12), the
s panel width (1) and nodes (8), the term counts of the 1/w tail series (25,
and 8 for the dilates beyond Kmax) and the derivative orders of phi~_n at 1
(14) are fixed inside two_adic/ and absent from it. So a coarsening of any of
them cannot be tested against the bound (eps cannot be evaluated at the
coarse build); only refinements can, under R. And two_adic/ s7b's runs used
s panel width 2, not the width 1 of the stored builds, so the s7b dominance
test below needs a further assumption, W2: the bound at the s7b
configurations also covers width 2. Phase 2 checks M, R, D and W2 against
the derivations.

The measured left sides come from referee_plants.json (run_referee_plants.py)
for the plants and from the stored matrices (checker/'s snapshot, two_adic/'s
ta_gram_probe.json) for the observed responses. Each carries the float64
spectral norm and, for the plants, an exact lower bound (a Rayleigh quotient
over the rationals); a failure is reported as a refutation of (I) only when
the exact lower bound also exceeds the right side.

Skips. A bound folder whose module or JSON file is absent is a skip with its
reason; one that is present but malformed is a failure. referee_plants.json
absent is a failure. No bound test passes without comparing at least one
number.
"""

from __future__ import annotations

import math
import os
import sys

import numpy as np
import pytest

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)

import referee_lib as RL  # noqa: E402
import run_referee_plants as RP  # noqa: E402

FIXED_KEYS = {"c", "N", "nvec", "S", "Kmax", "eps_upper", "grade", "assumptions"}
U = 2.0 ** -53


# ------------------------------------------------------------------ fixtures


@pytest.fixture(scope="module")
def plants():
    assert os.path.exists(RL.PLANTS_JSON), "referee_plants.json missing: run run_referee_plants.py"
    doc = RL.load_json(RL.PLANTS_JSON)
    return doc


@pytest.fixture(scope="module")
def snap():
    return RL.load_json(RL.SNAPSHOT)


@pytest.fixture(scope="module")
def probe():
    return RL.load_json(RL.GRAM_PROBE)


def _module(py, name, fn):
    if not os.path.exists(py):
        pytest.skip(f"{os.path.relpath(py, RL.C4)} not present yet: phase 1 tests are written before the bound exists")
    mod = RL.load_module(py, name)
    assert hasattr(mod, fn), f"{os.path.relpath(py, RL.C4)} has no function {fn} (interface of BRIEF.md)"
    return getattr(mod, fn)


def _entries(path):
    if not os.path.exists(path):
        pytest.skip(f"{os.path.relpath(path, RL.C4)} not present yet")
    doc = RL.load_json(path)
    assert isinstance(doc, list), f"{os.path.relpath(path, RL.C4)} is not a list of entries"
    return doc


@pytest.fixture(scope="module")
def eps_trunc():
    return _module(RL.BOUND_TRUNC_PY, "referee_eps_trunc", "eps_trunc")


@pytest.fixture(scope="module")
def eps_quad():
    return _module(RL.BOUND_QUAD_PY, "referee_eps_quad", "eps_quad")


@pytest.fixture(scope="module")
def trunc_json():
    return _entries(RL.BOUND_TRUNC_JSON)


@pytest.fixture(scope="module")
def quad_json():
    return _entries(RL.BOUND_QUAD_JSON)


class Eps:
    """eps = eps_trunc + eps_quad at a configuration, as exact upper ends."""

    def __init__(self, ft, fq):
        self.ft, self.fq = ft, fq
        self.cache = {}

    raised: list = []

    def parts(self, c, N, nvec, S, Kmax):
        """Changed after routing (2026-09-24): a ValueError from an eps function
        (bound_quad/'s eps_quad raises one when S <= 2 pi N / L) is read as no
        bound at that configuration and recorded in Eps.raised (REVIEW.md)."""
        key = (float(c), int(N), int(nvec), float(S), int(Kmax))
        if key not in self.cache:
            out = []
            for fn in (self.ft, self.fq):
                try:
                    with RL.arb_prec(128):
                        out.append(RL.arb_upper_q(fn(float(c), int(N), int(nvec), float(S), int(Kmax))))
                except ValueError as e:
                    Eps.raised.append((key, fn.__name__, str(e)))
                    out.append(None)
            self.cache[key] = tuple(out)
        return self.cache[key]

    def total(self, *cfg):
        ut, uq = self.parts(*cfg)
        return None if ut is None or uq is None else ut + uq

    def quad(self, *cfg):
        return self.parts(*cfg)[1]


@pytest.fixture(scope="module")
def eps(eps_trunc, eps_quad):
    return Eps(eps_trunc, eps_quad)


def _cfg(unit_cfg, c, N):
    nv = unit_cfg["nvec"]
    return (c, N, nv, unit_cfg["S"], unit_cfg.get("Kmax") or RL.TP.kmax_for(nv))


def _pairs(plants, kind):
    return [p for p in plants["pairs"] if p["kind"] == kind]


def _cfg_b(p, c, N, snap):
    if p["b"].startswith("stored:"):
        nv, S, NN = (int(x) for x in p["b"].split(":")[1].split("|"))
        return (c, N, nv, RL.s_exact(snap, nv, S, NN), RL.TP.kmax_for(nv))
    return _cfg(p["config_b"], c, N)


# ----------------------------------------------- phase 1: the plants themselves


def test_replica_reproduces_the_stored_row(snap):
    """delta_T_knobs at its defaults is two_adic/'s build: (80, 1200), N = 8,
    against the snapshot row (T_S - T_inf), every c. Modal's own calibration
    of this unit against the laptop was 7.1e-15."""
    out, diag = RL.delta_T_knobs(80, 1200, Ns=(8,))
    assert diag["Kmax"] == 10
    for c in RL.CELLS:
        stored = RL.stored_TS(snap, c, 8, 80, 1200) - RL.T_inf(c, 8)
        assert np.abs(out[(c, 8)] - stored).max() < 1e-13


def test_plants_json_is_complete(plants):
    assert set(plants["units"]) == set(RP.UNITS)
    got = {(p["a"], p["b"]) for p in plants["pairs"]}
    assert got == {(a, b) for a, b, *_ in RP.PAIRS}
    for p in plants["pairs"]:
        assert p["rows"], p["a"]
        for r in p["rows"]:
            assert math.isfinite(r["spec"])
            # the exact enclosure of the float64 norm: lower <= spec <= Frobenius upper
            assert r["spec_lower"] <= r["spec"] * (1 + 1e-9) + 1e-300
            assert r["spec"] <= r["frob_upper"] * (1 + 1e-12)


def test_a_plant_reproduces_from_its_json_row(plants):
    """The S plant (80, 800) against (80, 1200), rebuilt here at N = 8, matches
    its JSON row: the stored norms are what the code produces."""
    base, _ = RL.delta_T_knobs(80, 1200, Ns=(8,))
    coarse, _ = RL.delta_T_knobs(80, 800, Ns=(8,))
    row = next(p for p in plants["pairs"] if (p["a"], p["b"]) == ("sq_80_800", "sq_80_1200"))
    n = 0
    for r in row["rows"]:
        if r["N"] != 8:
            continue
        got = RL.spec(coarse[(r["c"], 8)] - base[(r["c"], 8)])
        assert abs(got - r["spec"]) <= 1e-9 * r["spec"]
        n += 1
    assert n == 3


NOISE_PLANTS = ("wpp16_80_1200", "spp12_80_1200", "sw05_80_1200", "mderiv20_80_1200",
                "pert_eps_80_1200", "pert_zw_80_1200", "svd_80_1200", "fsum_80_1200")


def _noise_floor(plants):
    """The float64 floor at (80, 1200): the largest change among the refinements
    that should move nothing (w, s panels, derivative orders, eps-size and
    sample-size perturbations, the SVD route, the fsum assembly)."""
    return max(r["spec"] for p in plants["pairs"] if p["b"] in NOISE_PLANTS for r in p["rows"])


def test_the_noise_floor(plants):
    """Pinned: the eight refinements at (80, 1200) move Delta_T by at most 1.1e-14
    on every (c, N), so the build is at float64 noise in those knobs there."""
    assert _noise_floor(plants) < 2e-14


def test_interface_and_defect_plants_move_delta_T(plants):
    """Not vacuous: every interface plant and every defect moves Delta_T by more
    than ten times the noise floor (exact lower bound) on every (c, N). The
    smallest is Kmax 10 against 12 at (40, 1200), about 3e-13."""
    floor = 10 * _noise_floor(plants)
    for p in _pairs(plants, "interface") + _pairs(plants, "defect"):
        for r in p["rows"]:
            assert r["spec_lower"] > floor, (p["a"], p["b"], r)


def test_defects_against_the_mode_truncation_response(plants):
    """At N = 8 a dropped mode moves Delta_T by more than removing the top 20
    modes does (60 -> 80 at S = 2400), on every c. At N = 16 and 32 it does not:
    80 modes do not resolve those windows and the 60 -> 80 response (0.10 to
    0.15) exceeds the dropped mode's (0.05 to 0.08). So only at N = 8 can a
    valid truncation bound be expected to leave the defect outside it."""
    trunc = {(r["c"], r["N"]): r["spec"] for r in next(
        p for p in plants["pairs"] if (p["a"], p["b"]) == ("tr_60_2400", "ref_80_2400"))["rows"]}
    for name in ("drop0_80_2400", "drop10_80_2400"):
        rows = next(p for p in plants["pairs"] if p["a"] == name)["rows"]
        for r in rows:
            if r["N"] == 8:
                assert r["spec_lower"] > trunc[(r["c"], 8)], (name, r)
            else:
                assert r["spec"] < trunc[(r["c"], r["N"])], (name, r)


# ------------------------------------------------------- item 1: plants vs eps


def _check(pairs, snap, rhs, label):
    """Assert change <= rhs(p, c, N) on every row where rhs is not None."""
    bad, n = [], 0
    for p in pairs:
        for r in p["rows"]:
            R = rhs(p, r["c"], r["N"])
            if R is None:
                continue
            n += 1
            if RL.to_q(r["spec"]) > R:
                bad.append((p["a"], p["b"], r["c"], r["N"], r["spec"], r["spec_lower"], float(R),
                            "refutes (I)" if RL.to_q(r["spec_lower"]) > R else "float-level"))
    if n == 0:
        pytest.skip(f"{label}: no row has a finite bound on both sides")
    assert not bad, f"{label}: change above the bound on {len(bad)} of {n} rows: {bad[:6]}"


def test_interface_plants_satisfy_I(plants, snap, eps):
    """(I) on every interface plant: nvec (bound_trunc/), S and Kmax (bound_quad/)."""
    def rhs(p, c, N):
        a = eps.total(*_cfg(p["config_a"], c, N))
        b = eps.total(*_cfg_b(p, c, N, snap))
        return None if a is None or b is None else a + b
    _check(_pairs(plants, "interface"), snap, rhs, "(I)")


def test_interface_plants_degraded_bound_alone_under_M(plants, snap, eps):
    """Assumption M: the degraded build's own bound dominates the change."""
    def rhs(p, c, N):
        return eps.total(*_cfg(p["config_a"], c, N))
    _check(_pairs(plants, "interface"), snap, rhs, "(I) under M")


def test_refinement_plants_under_R(plants, snap, eps):
    """Assumption R: change <= 2 eps_a (w panels, s panels, tail terms, derivative
    orders, sample perturbations at float64 size, the second stable rho route,
    the assembly summation)."""
    def rhs(p, c, N):
        a = eps.total(*_cfg(p["config_a"], c, N))
        return None if a is None else 2 * a
    _check(_pairs(plants, "refinement"), snap, rhs, "(I) under R")


def test_refinement_plants_under_R_and_D(plants, snap, eps):
    """Assumptions R and D: the modes are fixed, so the quadrature bound alone,
    2 eps_quad(a), dominates the change."""
    def rhs(p, c, N):
        q = eps.quad(*_cfg(p["config_a"], c, N))
        return None if q is None else 2 * q
    _check(_pairs(plants, "refinement"), snap, rhs, "(I) under R and D")


def test_defects_are_not_covered(plants, snap, eps):
    """Labelled: what the bound does NOT cover. A dropped mode and the explicit
    inverse are code defects. The bound is a function of (c, N, nvec, S, Kmax)
    only, so it is blind to them by construction; where it is tight enough, a
    defective build lands outside (I). Asserted on the N = 8 rows of the dropped
    modes (where test_defects_against_the_mode_truncation_response shows the
    defect exceeds the truncation response) and on every row of the explicit
    inverse. A failure means the bound absorbs a code defect there: loose, not
    refuted."""
    rows, n = [], 0
    for p in _pairs(plants, "defect"):
        for r in p["rows"]:
            if p["a"].startswith("drop") and r["N"] != 8:
                continue
            a = eps.total(*_cfg(p["config_a"], r["c"], r["N"]))
            b = eps.total(*_cfg_b(p, r["c"], r["N"], snap))
            if a is None or b is None:
                continue
            n += 1
            if not RL.to_q(r["spec_lower"]) > a + b:
                rows.append((p["a"], r["c"], r["N"], r["spec_lower"], float(a + b)))
    if n == 0:
        pytest.skip("no defect row has a finite bound")
    assert not rows, f"a code defect sits inside eps_a + eps_b on {len(rows)} of {n} rows: {rows[:6]}"


# --------------------------------------- item 2: the observed responses vs eps


N16 = [(80, 1200), (80, 1600), (120, 1200), (120, 1600), (160, 1600)]
N32 = [(200, 2400), (240, 2400), (280, 2266), (319, 2633), (364, 3060)]


def _stored_pairs():
    out = []
    for N, builds in ((16, N16), (32, N32)):
        for i, a in enumerate(builds):
            for b in builds[i + 1 :]:
                out.append((N, a, b))
    return out


def test_stored_responses_satisfy_I(snap, eps):
    """(I) on every pair of stored builds of the same (c, N): N = 16 (nvec 80,
    120, 160 and S 1200, 1600) and N = 32 (200, 240, 280, 319, 364 modes).
    T_inf is the same kernel/ moments for every build of a (c, N), so
    T_S,a - T_S,b = Delta_T_a - Delta_T_b up to the float64 addition that
    formed each stored T_S, at most u ||T_S||_F per build (added to the right side)."""
    bad, n, none = [], 0, []
    for N, (na, Sa), (nb, Sb) in _stored_pairs():
        for c in RL.CELLS:
            Ta, Tb = RL.stored_TS(snap, c, N, na, Sa), RL.stored_TS(snap, c, N, nb, Sb)
            ea = eps.total(c, N, na, RL.s_exact(snap, na, Sa, N), RL.TP.kmax_for(na))
            eb = eps.total(c, N, nb, RL.s_exact(snap, nb, Sb, N), RL.TP.kmax_for(nb))
            if ea is None or eb is None:
                none.append((c, N, na, Sa, nb, Sb))
                continue
            n += 1
            lhs = RL.spec(Ta - Tb)
            slack = RL.to_q(U * (np.linalg.norm(Ta) + np.linalg.norm(Tb)) * (1 + 1e-6))
            if RL.to_q(lhs) > ea + eb + slack:
                bad.append((c, N, (na, Sa), (nb, Sb), lhs, float(ea + eb)))
    if n == 0:
        pytest.skip(f"no stored pair has finite bounds on both builds ({len(none)} pairs without)")
    assert not bad, f"(I) fails on {len(bad)} of {n} stored pairs: {bad[:6]}"


def _s7b_runs(probe):
    return {(r["nvec"], r["S"]): (np.array(r["dT"]), r["Kmax"]) for r in probe["runs"].values()}


def test_s7b_responses_satisfy_I_under_W2(probe, eps):
    """(I) on two_adic/ s7b's runs (c = 2.2, N = 8): the nvec chain 80 -> 200 at
    S = 4800 (every pair), the S chain 1200 -> 2400 -> 4800 at 80 modes, and
    4800 -> 9600 at 160. Assumption W2 (these runs use s panel width 2) and a
    route slack of 1e-10 per build: they were built with rho_inv, which
    two_adic/ s10.5 measured within 2.6e-14 of the QR route at three of them
    and expects below 1e-10 at the rest (cond(F) below about 1e3)."""
    runs = _s7b_runs(probe)
    c, N = float(probe["c"]), int(probe["N"])
    keys = sorted(runs)
    bad, n = [], 0
    route = RL.to_q(1e-10)
    for i, a in enumerate(keys):
        for b in keys[i + 1 :]:
            if not (a[1] == b[1] == 4800.0 or a[0] == b[0]):
                continue
            ea = eps.total(c, N, a[0], a[1], runs[a][1])
            eb = eps.total(c, N, b[0], b[1], runs[b][1])
            if ea is None or eb is None:
                continue
            n += 1
            lhs = RL.spec(runs[a][0] - runs[b][0])
            if RL.to_q(lhs) > ea + eb + 2 * route:
                bad.append((a, b, lhs, float(ea + eb)))
    if n == 0:
        pytest.skip("no s7b pair has finite bounds on both runs")
    assert not bad, f"(I) under W2 fails on {len(bad)} of {n} s7b pairs: {bad}"


def test_s7b_width_2_against_the_stored_width_1(probe, snap):
    """Measured, outside the interface: the s panel width 2 of s7b against the
    width 1 of the stored build at (80, 1200), c = 2.2, N = 8. This is the size
    W2 has to absorb at that configuration."""
    runs = _s7b_runs(probe)
    d7b = runs[(80, 1200.0)][0]
    stored = RL.stored_TS(snap, 2.2, 8, 80, 1200) - RL.T_inf(2.2, 8)
    got = RL.spec(d7b - stored)
    assert got == pytest.approx(W2_RESPONSE_80_1200, rel=1e-3, abs=1e-15)


W2_RESPONSE_80_1200 = 4.801938417109569e-13  # measured 2026-09-24, float64 eigvalsh


# ------------------------------------------------- item 3: internal consistency


def _match(entry, c, N, nv, S_ex):
    return (float(entry["c"]) == c and int(entry["N"]) == N and int(entry["nvec"]) == nv
            and float(entry["S"]) == float(S_ex))


@pytest.mark.parametrize("which", ["trunc", "quad"])
def test_json_entries_cover_every_stored_build(which, request, snap):
    """Exactly the 33 (c, build) entries, keyed by the S the build used
    (S_exact: 2266.10..., 2633.16..., 3060.08... for 280, 319, 364 modes),
    Kmax = kmax_for(nvec), and each either a decimal eps_upper with a grade and
    numbered assumptions, or null with a reason."""
    entries = request.getfixturevalue(f"{which}_json")
    want = [(c, N, nv, RL.s_exact(snap, nv, S, N)) for (nv, S, N) in RL.STORED_BUILDS for c in RL.CELLS]
    assert len(entries) == len(want), f"{len(entries)} entries, want {len(want)}"
    for c, N, nv, S_ex in want:
        hits = [e for e in entries if _match(e, c, N, nv, S_ex)]
        assert len(hits) == 1, f"{which}: {len(hits)} entries for c={c} N={N} nvec={nv} S={S_ex}"
        e = hits[0]
        assert FIXED_KEYS <= set(e), f"{which}: missing keys {FIXED_KEYS - set(e)}"
        assert int(e["Kmax"]) == RL.TP.kmax_for(nv)
        if e["eps_upper"] is None:
            extra = [v for k, v in e.items() if k not in FIXED_KEYS and isinstance(v, str) and v.strip()]
            assert extra or (isinstance(e["grade"], str) and e["grade"].strip()), f"{which}: null without a reason: {e}"
        else:
            assert isinstance(e["eps_upper"], str), "eps_upper must be a decimal string"
            RL.dec_to_q(e["eps_upper"])  # parses exactly
            assert isinstance(e["grade"], str) and e["grade"].strip()
            assert isinstance(e["assumptions"], list) and e["assumptions"], f"{which}: no assumptions listed: {e}"


@pytest.mark.parametrize("which", ["trunc", "quad"])
def test_eps_upper_is_at_least_the_ball_upper_end(which, request, snap):
    """eps_upper >= the upper end of the arb ball the function returns at the
    entry's configuration (exact comparison), and not a stale number: within 1 %
    of it."""
    entries = request.getfixturevalue(f"{which}_json")
    fn = request.getfixturevalue(f"eps_{which}")
    n = 0
    for e in entries:
        if e["eps_upper"] is None:
            continue
        with RL.arb_prec(128):
            ball = fn(float(e["c"]), int(e["N"]), int(e["nvec"]), float(e["S"]), int(e["Kmax"]))
        up = RL.arb_upper_q(ball)
        assert up is not None, f"{which}: finite eps_upper but a non-finite ball: {e}"
        val = RL.dec_to_q(e["eps_upper"])
        assert val >= up, f"{which}: eps_upper {e['eps_upper']} below the ball's upper end {float(up)}"
        assert val <= up * RL.dec_to_q("1.01") + RL.dec_to_q("1e-30"), f"{which}: eps_upper stale against the function: {e}"
        n += 1
    if n == 0:
        pytest.skip(f"{which}: every entry is null")


# ------------------------------------------- written after routing (phase 2)
#
# Everything below was written after the coordinator routed bound_trunc/,
# bound_quad/ and assembler/ (phase 1 is 4875122). It pins the numbers of
# REVIEW.md.


def _quad_module():
    if not os.path.exists(RL.BOUND_QUAD_PY):
        pytest.skip("bound_quad/eps_quad.py not present")
    return RL.load_module(RL.BOUND_QUAD_PY, "referee_eps_quad_mod")


def _no_finite_ball(fn, *args):
    try:
        with RL.arb_prec(128):
            return RL.arb_upper_q(fn(*args)) is None
    except ValueError:
        return True


def test_eps_quad_fails_closed_below_the_window_band():
    """REVIEW.md finding 5. Where S <= 2 pi N / L, Prop 2 (E1) has no bound, and
    eps_quad raises ValueError instead of returning a non-finite ball. That is
    fail-closed (no finite number escapes), which this test pins, and off the
    interface (the brief fixed the return type as flint.arb), which REVIEW.md
    records. The configurations are this folder's plants (80, 150) and
    (80, 200) at N = 32 (2 pi 32 / log 2.9 = 188.8; / log 2.2 = 255.0)."""
    fq = _quad_module().eps_quad
    for c, S in ((2.9, 150.0), (2.2, 150.0), (2.2, 200.0)):
        assert _no_finite_ball(fq, c, 32, 80, S, 10), (c, S)
    raised = False
    try:
        fq(2.9, 32, 80, 150.0, 10)
    except ValueError:
        raised = True
    assert raised, "eps_quad no longer raises here: update REVIEW.md finding 5"


@pytest.mark.parametrize("which", ["trunc", "quad"])
def test_null_entries_match_the_functions(which, request):
    """Internal consistency: every JSON entry whose eps_upper is null has a
    function value with no finite upper end (or a raise) at the same key."""
    entries = request.getfixturevalue(f"{which}_json")
    fn = request.getfixturevalue(f"eps_{which}")
    n = 0
    for e in entries:
        if e["eps_upper"] is not None:
            continue
        n += 1
        assert _no_finite_ball(fn, float(e["c"]), int(e["N"]), int(e["nvec"]), float(e["S"]), int(e["Kmax"])), e
    assert n > 0


def test_closing_pieces_of_eps_quad_against_the_plants(plants):
    """bound_quad/'s pieces that close (Prop 5, E6; Prop 6, E7) against the plants
    that exercise them at (80, 1200): the SVD route (under R, change <= 2 E6)
    and the fsum assembly (change <= E7 plus the fsum route's own rounding,
    taken as E7 again). Consistent by nine or more orders of magnitude."""
    mod = _quad_module()
    rows = {p["b"]: {(r["c"], r["N"]): r["spec"] for r in p["rows"]} for p in plants["pairs"]}
    n = 0
    for c in RL.CELLS:
        for N in (8, 16):
            parts = mod.eps_quad_parts(c, N, 80, 1200.0, 10)
            e6, e7 = RL.arb_upper_q(parts["E6"]), RL.arb_upper_q(parts["E7"])
            assert e6 is not None and e7 is not None
            assert RL.to_q(rows["svd_80_1200"][(c, N)]) <= 2 * e6
            assert RL.to_q(rows["fsum_80_1200"][(c, N)]) <= 2 * e7
            n += 1
    assert n == 6


def test_window_hat_is_real():
    """REVIEW.md finding 7 (closes assembler/ A2 = bound_quad/ A9): with
    k = 2 pi n / L - s, V_n(s) = -2 sin(sL/2) / (k sqrt(L)) is real, so
    M = (1/2pi) int rho V V^T is real symmetric for real rho. The computed
    window_hat's imaginary part is at rounding level against its modulus."""
    s, _ = RL.TM.s_grid(1200.0, width=1.0, per_panel=8)
    for c in RL.CELLS:
        L = math.log(c)
        V = RL.TM.window_hat(L, 16, s)
        k = 2 * math.pi * np.arange(-16, 17)[:, None] / L - s[None, :]
        with np.errstate(divide="ignore", invalid="ignore"):
            closed = -2 * np.sin(s[None, :] * L / 2) / (k * math.sqrt(L))
        ok = np.abs(k) > 1e-9
        assert np.abs(V.imag).max() <= 1e-12
        assert np.abs(V.real[ok] - closed[ok]).max() <= 1e-12


def test_lemma1_companion_by_a_second_route():
    """REVIEW.md finding 3. run_companion_check.py (two_adic/'s float64 w-quadrature
    hats) against bound_trunc/'s lemma1_companion.json (kernel/'s Tate closed
    form): c_j agree to 1.1e-10 absolute for j < 160; the slopes of P(n) per
    unit of log n are 0.98996 on [40, 80] and 0.99098 on [80, 160]."""
    path = os.path.join(HERE, "referee_companion.json")
    assert os.path.exists(path), "run run_companion_check.py"
    mine = RL.load_json(path)
    theirs_path = os.path.join(RL.C4, "bound_trunc", "lemma1_companion.json")
    if not os.path.exists(theirs_path):
        pytest.skip("bound_trunc/lemma1_companion.json not present")
    theirs = RL.load_json(theirs_path)
    a, b = np.array(mine["c_j"]), np.array(theirs["c_j"][: len(mine["c_j"])])
    assert np.abs(a - b).max() < 1.1e-10
    assert mine["slope_per_log_n"]["40-80"] == pytest.approx(0.98996, abs=1e-5)
    assert mine["slope_per_log_n"]["80-160"] == pytest.approx(0.99098, abs=1e-5)
    assert mine["w_f"] == pytest.approx(theirs["w_f"], abs=1e-12)


def test_lemma3_sandwich_holds_on_every_stored_T_S(snap):
    """REVIEW.md: every stored T_S lies strictly inside kappa T_inf <= T_S <= K T_inf
    (bound_trunc/ Lemma 3), on all 33 (c, build) matrices: the smallest
    eigenvalue of T_S - kappa T_inf is at least 1.09e-3 and that of
    K T_inf - T_S at least 2.78e-3 (c = 2.9, 364 modes). Measured, float64
    eigvalsh; a consistency check of the lemma with the data, not a proof."""
    kap, K = 17 - 12 * math.sqrt(2), 17 + 12 * math.sqrt(2)
    lo, hi = math.inf, math.inf
    for (nv, S, N) in RL.STORED_BUILDS:
        for c in RL.CELLS:
            TS, Ti = RL.stored_TS(snap, c, N, nv, S), RL.T_inf(c, N)
            lo = min(lo, np.linalg.eigvalsh(TS - kap * Ti)[0])
            hi = min(hi, np.linalg.eigvalsh(K * Ti - TS)[0])
    assert lo == pytest.approx(1.09e-3, abs=1e-5)
    assert hi == pytest.approx(2.78e-3, abs=1e-5)


def _pair(plants, a, b):
    return next(p for p in plants["pairs"] if (p["a"], p["b"]) == (a, b))["rows"]


def test_review_plant_numbers(plants):
    """The plant magnitudes REVIEW.md states (max over c and N unless named)."""
    mx = lambda a, b, N=None: max(r["spec"] for r in _pair(plants, a, b) if N is None or r["N"] == N)  # noqa: E731
    mn = lambda a, b, N=None: min(r["spec"] for r in _pair(plants, a, b) if N is None or r["N"] == N)  # noqa: E731
    assert mx("base_80_150", "pert_zw_80_150") == pytest.approx(2.41e-2, rel=1e-2)
    assert mx("base_80_200", "pert_zw_80_200") == pytest.approx(5.19e-5, rel=1e-2)
    assert mx("base_80_150", "pert_eps_80_150") == pytest.approx(7.36e-4, rel=1e-2)
    assert mx("base_80_200", "pert_eps_80_200") == pytest.approx(2.74e-6, rel=1e-2)
    assert mx("sq_80_1200", "terms40_80_1200") == pytest.approx(5.26e-9, rel=1e-2)
    assert mn("sq_80_1200", "terms40_80_1200") == pytest.approx(4.59e-9, rel=1e-2)
    assert mx("inv_80_200", "base_80_200") == pytest.approx(0.365, rel=1e-2)
    assert mn("drop0_80_2400", "ref_80_2400") == pytest.approx(4.55e-2, rel=1e-2)
    assert mx("drop10_80_2400", "ref_80_2400") == pytest.approx(7.82e-2, rel=1e-2)
    assert mn("tr_60_2400", "ref_80_2400", 16) == pytest.approx(9.92e-2, rel=1e-2)
    assert mx("tr_60_2400", "ref_80_2400", 32) == pytest.approx(0.146, rel=1e-2)
    assert mx("km_40_1200_K8", "km_40_1200_K12") == pytest.approx(2.40e-8, rel=1e-2)
    assert mx("km_40_1200_K10", "km_40_1200_K12") == pytest.approx(3.31e-13, rel=5e-2)
    assert mx("sq_80_1200", "ref_80_2400") == pytest.approx(2.84e-3, rel=1e-2)
    assert mx("base_80_150", "ref_80_2400") == pytest.approx(0.239, rel=1e-2)
    assert len(plants["units"]) == 30 and len(plants["pairs"]) == 30
    diag = plants["units"]
    assert diag["base_80_200"]["diag"]["cond_Fz"] == pytest.approx(6.7e11, rel=1e-2)
    assert diag["base_80_150"]["diag"]["cond_Fz"] == pytest.approx(3.84e14, rel=1e-2)

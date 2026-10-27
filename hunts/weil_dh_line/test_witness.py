"""Tests for the position-space DH form (witness.py), the S lesion and the
honest responses of scout.py (hunt weil_dh_line, #146, raised 2026-10-27).

Every number the raise states in PRICE.md is pinned here or read back from its
JSON artifact, and each instrument has a check that can fail: the form against
the hunt's own stored stage-A block and against the independent CCM closed
forms, with planted faults; the single-vector stage-A route against
scout.unit; the S lesion on the real run-B data.

Run from the repo root: .venv/bin/python -m pytest -q -n0 hunts/weil_dh_line/test_witness.py
"""
from __future__ import annotations

import json
import math
import random
import sys
from fractions import Fraction
from pathlib import Path

import pytest
from flint import acb, arb, arb_mat, ctx

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import price  # noqa: E402
import scout  # noqa: E402
import witness as W  # noqa: E402

L = W.L_DH_WINDOW
ENV = HERE / "k2env_dh_L_DH.json"
BLOCK = HERE / "c800_block100.json"
RECORD = HERE / "witness_q856.json"
VEC = HERE / "witness_v856.json"
STAGE_A = HERE / "stage_a_v800.json"
K2_SCOUTS = HERE / "k2_scouts.json"


def _load(path: Path):
    if not path.exists():
        pytest.skip(f"{path.name} not produced yet")
    return json.loads(path.read_text())


def _block(name: str, n: int) -> arb_mat:
    """Leading n x n block of the stored run-B C(800) or G(800) (50 digits)."""
    d = _load(BLOCK)
    vals = iter(d[name])
    M = arb_mat(n, n)
    for i in range(d["n"]):
        for j in range(i + 1):
            v = next(vals)
            if i < n and j < n:
                M[i, j] = arb(v)
                M[j, i] = M[i, j]
    return M


@pytest.fixture(scope="module")
def small_parts():
    ctx.prec = W.PREC
    N = 20
    Nx = W.default_Nx(N)
    return {"N": N, "Nx": Nx, "dh": W.unit(L, N, Nx, 0, 10 ** 9),
            "zeta_gamma": W.unit(L, N, Nx, 0, 10 ** 9, a=Fraction(1, 4))}


def _smooth_vectors(N: int):
    La = price.to_arb(L)
    fs = {"K8": lambda y: (1 - (y / La) ** 2) ** 8,
          "K8_u2": lambda y: (1 - (y / La) ** 2) ** 8 * ((y / La) ** 2 - arb(1) / 3),
          "K7_mix": lambda y: (1 - (y / La) ** 2) ** 7 * (1 + 3 * (y / La) ** 2 - 5 * (y / La) ** 6 + (y / La) ** 10)}
    return {k: W.legendre_coeffs_of(f, L, N) for k, f in fs.items()}


# ------------------------------------------------------------------ the form itself

def test_basis_change_and_identity_gram(small_parts):
    """K G(0) K^T = I: the Chebyshev work basis, the exact Legendre-to-Chebyshev
    coefficients and the Gauss sums reproduce the scout's orthonormal basis."""
    red = W.reduce_parts(L, small_parts["N"], [small_parts["dh"]])
    N = small_parts["N"]
    dev = max(float(abs(red["I_check"][i, j] - (1 if i == j else 0)).upper()) for i in range(N) for j in range(N))
    assert dev < 1e-70
    assert W.cheb_coeffs_even_legendre(1) == [Fraction(1, 4), Fraction(3, 4)]     # P_2 = 1/4 + 3/4 T_2
    # the fast K (a_j by recurrence, products in balls) encloses the exact coefficients
    assert W.a_coefs(40) == [W.a_coef(j) for j in range(40)]
    K = red["K"]
    La = price.to_arb(L)
    for i in range(N):
        for k, e in enumerate(W.cheb_coeffs_even_legendre(i)):
            assert K[i, k].overlaps(((arb(4 * i + 1) / 2) / La).sqrt() * price.to_arb(e))


def test_form_matches_the_stored_stage_a_block_on_smooth_vectors(small_parts):
    """Calibration against the hunt's own assembly at finite T#: on vectors
    whose transform decays like t^-9 or faster, Q(u) - u^T C(800) u is the
    frequency tail beyond 800, positive, below 1e-36, and about
    log(5 * 800 / 2 pi) times the tail mass 1 - u^T G(800) u. Each planted
    fault (comb sign, comb halved, conductor 1, zeta's Gamma(s/2)) moves the
    form by more than 1e-3."""
    ctx.prec = W.PREC
    N = small_parts["N"]
    C, G = _block("C", N), _block("G", N)
    Q = W.reduce_parts(L, N, [small_parts["dh"]])["Q"]
    faults = {"comb sign": W.reduce_parts(L, N, [small_parts["dh"]], comb_scale=-1)["Q"],
              "comb halved": W.reduce_parts(L, N, [small_parts["dh"]], comb_scale=Fraction(1, 2))["Q"],
              "conductor 1": W.reduce_parts(L, N, [small_parts["dh"]], conductor=1)["Q"],
              "zeta Gamma(s/2)": W.reduce_parts(L, N, [small_parts["zeta_gamma"]], a=Fraction(1, 4))["Q"]}
    tails, moves = [], []
    for name, u in _smooth_vectors(N).items():
        q, c, g = W.quad_form(Q, u), W.quad_form(C, u), W.quad_form(G, u)
        tail = q - c
        mass = 1 - g
        assert bool(tail > 0) and float(tail.upper()) < 1e-36, name
        tails.append(float(tail.mid()))
        ratio = float((tail / mass).mid())
        assert abs(ratio - math.log(5 * 800 / (2 * math.pi))) < 1.0, (name, ratio)
        for fk, Qf in faults.items():
            mv = float(abs(W.quad_form(Qf, u) - c).lower())
            assert mv > 1e-3, (name, fk)
            moves.append(mv)
    assert 2.7e-40 <= min(tails) and max(tails) <= 1.1e-38          # PRICE.md: 2.7e-40 to 1.0e-38
    assert 0.0115 <= min(moves) and max(moves) <= 1.61              # PRICE.md: 0.012 to 1.6


def test_form_matches_the_ccm_closed_forms():
    """Independent route: the CCM closed-form DH assembly (weil_trunc/galerkin.py,
    mpmath, digamma, trigamma and geometric series in e^{-2L}) on its even
    trigonometric basis at this window, against the position-space form on the
    Legendre projections of the same functions (projection tail below 1e-60 here)."""
    sys.path.insert(0, str(HERE.parent / "rogue_frontier" / "weil_trunc"))
    import galerkin
    from mpmath import mp
    ctx.prec = W.PREC
    N, Nc = 40, 6
    with mp.workdps(70):
        T = galerkin.Truncation(mp.exp(2 * mp.mpf(L.numerator) / L.denominator), Nc, kind="dh")
        E = T.even_matrix()
        Ecc = [[mp.nstr(E[i, j], 60) for j in range(Nc + 1)] for i in range(Nc + 1)]
    Q = W.reduce_parts(L, N, [W.unit(L, N, W.default_Nx(N), 0, 10 ** 9)])["Q"]
    La = price.to_arb(L)
    U = [[arb(1)] + [arb(0)] * (N - 1)]
    for k in range(1, Nc + 1):
        z = arb.pi() * k
        U.append([(-1) ** k / La.sqrt() * (-1) ** i * 2 * (La * (arb(2 * i) + arb(1) / 2)).sqrt()
                  * z.bessel_j(arb(2 * i) + arb(1) / 2) * (arb.pi() / (2 * z)).sqrt() for i in range(N)])
    for i in range(Nc + 1):
        for j in range(i, Nc + 1):
            x, y = arb_mat(N, 1, U[i]), arb_mat(N, 1, U[j])
            v = (x.transpose() * Q * y)[0, 0]
            dev = float(abs(v - arb(Ecc[i][j])).upper())
            if j <= 3:
                assert dev < 4e-60, (i, j, dev)                     # PRICE.md: below 4e-60 for k <= 3
            assert dev < 1e-42, (i, j, dev)                         # the 40-mode truncation at k = 6: 6e-44
    assert dev > 1e-46                                              # (6, 6): the truncation is visible


def test_node_gram_mirror_pairing_and_radius_bound():
    """The mirrored half-length product equals the full product V^T J V, and
    the carried bound eps covers the radii dropped by the midpoint product
    (compared with the full ball product). Planted fault: unmirrored rows give
    a different (non-Gram) matrix."""
    ctx.prec = W.PREC
    N = 12
    nodes = W.gl_sym(2 * N - 1)
    La = price.to_arb(L)
    s = arb(37) / 100
    G, eps = W.node_gram(s, nodes, N, La)
    # direct: rows with balls, full ball product
    rows = []
    for xi, w in nodes:
        u = s / 2 + (1 - s / 2) * xi
        sq = (La * (1 - s / 2) * w).sqrt()
        rows.append([sq * (2 * k * u.acos()).cos() for k in range(N)])
    M = len(nodes)
    V = arb_mat(M, N, [x for r in rows for x in r])
    VJ = arb_mat(M, N, [x for r in rows[::-1] for x in r])
    Gd = V.transpose() * VJ
    worst = max(float(abs(G[i, j].mid() - Gd[i, j].mid())) for i in range(N) for j in range(N))
    assert worst <= eps + max(float(Gd[i, j].rad()) for i in range(N) for j in range(N))
    assert eps < 1e-70
    Vbad = V.transpose() * V
    assert max(float(abs(Vbad[i, j] - Gd[i, j]).lower()) for i in range(N) for j in range(N)) > 1e-3
    # and the Gauss sum is the exact correlation integral: psi_0 * psi_0 at x = sL is L (2 - s)
    assert float(abs(G[0, 0] - La * (2 - s)).upper()) < 1e-70


def test_quadrature_bound_behaves():
    """The archimedean Gauss-Legendre bound falls with Nx and refuses an Nx
    below the polynomial degree."""
    b1 = W.quad_error_bound(L, 40, W.default_Nx(40, margin=40))
    b2 = W.quad_error_bound(L, 40, W.default_Nx(40, margin=90))
    assert b2 < b1 < 1e-20
    with pytest.raises(ValueError):
        W.quad_error_bound(L, 40, 70)


def test_stage_a_vector_route_matches_scout_unit():
    """The single-vector stage-A route (F_v by Gauss in position space with a
    Bernstein bound, Psi + H from scout.Symbol) reproduces scout.unit's v^T C v
    and v^T G v on one panel at t near 0 and one at t near 800 (N = 10), and
    its radius is honest (below 1e-70)."""
    ctx.prec = W.PREC
    N = 10
    random.seed(3)
    v = [arb(random.uniform(-1, 1)).mid() for _ in range(N)]
    venc = [x.mid().man_exp() for x in v]
    for k0, ny in ((0, 200), (1599, 1500)):
        C, G, _ = scout.unit(L, ENV, N, 64, Fraction(1, 2), k0, k0 + 1, W.PREC, "even", "fast")
        x = arb_mat(N, 1, v)
        vC, vG = (x.transpose() * C * x)[0, 0], (x.transpose() * G * x)[0, 0]
        _, _, c, g = W._stage_a_panels((L, str(ENV), venc, k0, k0 + 1, 64, Fraction(1, 2), W.PREC, ny, Fraction(2), 800))
        c, g = W._dec_arb(c), W._dec_arb(g)
        assert float(abs(c - vC).upper()) < 1e-70 and float(abs(g - vG).upper()) < 1e-70
        assert float(c.rad()) < 1e-70


# ------------------------------------------------------------------ honest responses and the S lesion

def test_rounded_response_rounds_the_data():
    """arb(x.mid()) under a lower working precision copies x exactly (the
    pre-2026-10-27 precision response); unary plus rounds. Planted check: the
    old construction leaves the data unchanged."""
    ctx.prec = 1280
    x = arb(1) / 3
    with ctx.workprec(1152):
        old = arb(x.mid())
        new = +(x.mid())
    assert old.mid() == x.mid()
    assert new.mid() != x.mid()
    assert bool(abs(new.mid() - x.mid()) < arb(2) ** -1150)       # rounded at 1152 bits, not further


def test_understated_S_flips_the_stage_a_verdict_on_the_stored_block():
    """K2 can go red. On the leading 100-mode block of the stored run-B
    stage-A data at T# = 800 the pipeline refuses (one negative pivot,
    lambda_min = -2.556e-30, as the reviewer measured); the same block with S
    understated by 30 (an invalid envelope) has no negative pivot. dS = 0 is
    the recorded verdict; the flip lies between 0 and 7 at this block size."""
    ctx.prec = W.PREC
    n = 100
    C, G = _block("C", n), _block("G", n)
    S = Fraction(_load(ENV)["S_exact"])
    rows = scout.lesion_rows(Fraction(800), "dh", S, C, G, n, W.PREC, [0, 7, 30])
    by = {r["dS"]: r for r in rows}
    assert by["0"]["n_neg"] == 1 and abs(float(by["0"]["lam_min"]) / -2.55643591124e-30 - 1) < 1e-8
    assert by["7"]["n_neg"] == 0 and by["30"]["n_neg"] == 0
    assert by["0"]["undecided"] == 0 and by["30"]["undecided"] == 0


# ------------------------------------------------------------------ the recorded results

def test_q856_record_is_internally_consistent():
    """witness_q856.json: the error budget is far below the eigenvalue scale,
    K G(0) K^T = I holds, the least eigenvalue is resolved, and the midpoint
    LDL finds exactly one negative pivot."""
    d = _load(RECORD)
    assert (d["N"], d["prec"], d["L"]) == (856, 256, "171079/100000")
    assert d["Nx"] == W.default_Nx(856)
    assert d["eps_spectral"] < 1e-63 and d["quad_bound"] < 1e-91 and d["dropped_l1"] < 1e-75
    assert abs(d["eps_spectral"] / 5.98e-64 - 1) < 0.01 and abs(d["quad_bound"] / 6.22e-92 - 1) < 0.01
    assert d["max_dev_K_G0_KT_from_I"] < 1e-72 and d["max_entry_radius"] < 1e-69
    assert d["inertia_midpoint"]["neg"] == 1 and d["inertia_midpoint"]["undecided"] == 0
    lam = float(d["lam_min"]["lam"])
    assert abs(lam / -1.94308362498385e-30 - 1) < 1e-12
    assert d["lam_min"]["residual"] < 1e-70


def test_the_856_mode_witness_is_negative_with_its_error_budget():
    """The headline at N = 856: the stored vector's Rayleigh quotient, with
    every step enclosed and the doubled spectral eps added, is strictly
    negative, so Q_856 has a negative eigenvalue."""
    d = _load(RECORD)
    w = d["witness"]
    assert w["negative"] and w["rq_upper_with_eps"] < -1.9430836249e-30
    assert abs(float(w["rq_mid"]) / -1.94308362498385e-30 - 1) < 1e-12 and w["rq_rad"] < 1e-69
    assert w["rq_upper_with_eps"] + 2 * d["eps_spectral"] < 0
    assert abs(float(w["boundary_value_f_L"]) / 9.0339e-15 - 1) < 1e-4


def test_the_onset_and_the_leading_blocks():
    """Leading principal blocks: no negative pivot at 50 and 100 modes, one
    negative pivot from 101 modes on, each with an enclosed negative quotient,
    and the least eigenvalue falling as the block grows (interlacing)."""
    d = _load(RECORD)
    rows = d["leading_blocks"]
    by = {r["N"]: r for r in rows}
    assert by[50]["neg"] == 0 and by[100]["neg"] == 0
    assert abs(float(by[100]["lam_nearest_0"]) / 4.06183356207e-32 - 1) < 1e-9
    neg_rows = [r for r in rows if r["N"] >= 101]
    assert neg_rows and all(r["neg"] == 1 and r["undecided"] == 0 and r["rq_upper_with_eps"] < 0 for r in neg_rows)
    lams = [float(r["lam"]) for r in neg_rows] + [float(d["lam_min"]["lam"])]
    assert all(b <= a * (1 - 1e-12) for a, b in zip(lams, lams[1:]))     # more negative as N grows
    assert abs(float(by[101]["lam"]) / -4.49000370077e-32 - 1) < 1e-9
    assert abs(float(by[150]["lam"]) / -1.17389383232e-30 - 1) < 1e-9
    assert abs(float(by[400]["lam"]) / -1.83716565448e-30 - 1) < 1e-9
    assert d["onset"] == {"last_block_without_negative_pivot": 100, "first_block_with_one": 101,
                          "witness_file": "witness_v101.json"}


def test_the_101_mode_witness_from_a_reassembly_at_its_own_size():
    """The onset witness re-verified from scratch: Q_101 assembled by the same
    code at its own size (201 Gauss nodes in y, 291 in x, 320 bits, none shared
    with the N = 856 assembly; a check of nodes and precision, not an
    independent implementation), evaluated at the stored vector with its own
    error budget: strictly negative and equal to the recorded quotient. Q_101 is the
    leading block of Q_N for every N >= 101, so this one check carries the
    negative eigenvalue at every N >= 101. About 30 s."""
    v = _load(HERE / "witness_v101.json")
    assert v["N"] == 101
    prec = 320
    ctx.prec = prec
    N = 101
    Nx = W.default_Nx(N)
    red = W.reduce_parts(L, N, [W.unit(L, N, Nx, 0, 10 ** 9, prec=prec)], prec)
    _, dropped = W.comb(L)
    eps = 2 * W.spectral_eps(L, N, Nx, red["E_psi"], red["K"], dropped)
    q = W.quad_form(red["Q"], [arb(s) for s in v["v"]])
    assert float((q + arb(0, eps)).upper()) < -4.4900037e-32
    assert float(abs(q - arb(v["rq_mid"])).upper()) < 1e-45
    rec = _load(RECORD)["reassembled_101"]
    assert (rec["N"], rec["Nx"], rec["M"], rec["prec"]) == (101, 291, 201, 320)


def test_the_t800_eigenvector_is_not_a_witness():
    """Q_856 at the T# = 800 eigenvector of R(800) is positive (enclosed); the
    stored row's R(800) value is reproduced at that vector, and the difference
    is the frequency tail beyond 800, close to the boundary-jump estimate
    (2 f(L)^2 / (pi T#)) (S + 1)."""
    d = _load(RECORD)
    v8 = d["v800"]
    assert v8["positive"] and v8["Q_rq_lower_with_eps"] > 6.366e-30
    assert abs(float(v8["Q_rq_mid"]) / 6.36613886240e-30 - 1) < 1e-10
    r = d["vs_R800"]
    assert r["R800_at_v800"] == "-4.15160674834e-30"
    tail = float(r["tail_at_v800"])
    mu = float(v8["boundary_value_f_L"])
    est = 2 * mu * mu / (math.pi * 800) * (_load(ENV)["S"] + 1)
    assert abs(tail / 1.05177e-29 - 1) < 1e-4 and abs(tail / est - 1) < 0.02
    assert float(r["R800_at_witness"]) < float(d["witness"]["rq_mid"])     # R(800) <= Q at the witness


def test_q_minus_r800_is_semidefinite_to_the_noise_floor():
    """R(800) <= Q_856 (the pipeline's soundness inequality), measured: the
    difference has near-null directions whose computed pivots fall below 0 at
    the noise floor, and D + 1e-66 I has no negative pivot."""
    d = _load(RECORD)
    counts = {c["sigma"]: c for c in d["Q_minus_R800_shifted_counts"]}
    assert counts["1e-66"]["neg"] == 0 and counts["1e-66"]["undecided"] == 0
    assert all(c["neg"] == 0 for c in counts.values())
    assert d["vs_R800"]["inertia_Q_minus_R800_midpoint"]["neg"] > 0       # the noise floor itself


def test_the_stage_a_block_at_800_is_not_semidefinite_with_enclosures():
    """Task 2 of the raise: the scout's discrete stage-A rule at T# = 800,
    evaluated at the T# = 800 eigenvector with every step enclosed and with
    no use of the stored state or the Bessel column, is strictly negative and
    equals the stored row; the exact integrals are within the recorded
    quadrature bound; the tail mass is the boundary-jump size."""
    d = _load(STAGE_A)
    assert (d["N"], d["T"], d["q"], d["h"], d["n_y"], d["prec"]) == (856, 800.0, 64, "1/2", 1500, 256)
    assert d["rq_discrete_upper"] < -4.1516067483e-30 and d["rq_discrete_rad"] < 1e-70
    assert abs(float(d["rq_discrete_mid"]) / -4.15160674834e-30 - 1) < 1e-11
    assert d["t_quad_bound"] < 1e-85 and d["rq_exact_integrals_upper"] < -4.1516067483e-30
    assert abs(float(d["mass_above_T_mid"]) / 1.4883465e-30 - 1) < 1e-6
    assert d["rq_discrete_mid"].startswith("-4.15160674833")


def test_honest_responses_and_timed_slices_recorded():
    """The responses of scout.responses_of at T# = 800 (leading 791-mode block;
    data rounded to 1152 bits) keep the refusal, and the timed slices that
    price the two unlaunched runs (PRICE.md door 5) are the recorded ones."""
    d = _load(RECORD)
    r = d["responses_T800"]["responses"]
    assert set(r) == {"leading_N_791", "rounded_1152"}
    assert all(x["n_neg"] == 1 and x["lam_min"] == "-4.15160674834e-30" for x in r.values())
    sl = {(s["L"], s["N"]): s["per_panel_cpu_s"] for s in d["timed_slices"]}
    assert abs(sl[("171079/100000", 856)] - 31.8) < 0.05
    assert abs(sl[("8503/5000", 856)] - 32.0) < 0.05
    assert abs(sl[("171079/100000", 1711)] - 123.5) < 0.05


def test_lesion_record_flips_between_43_and_44(tmp_path):
    """k2_scouts.json, DH at L_DH: the S-lesion rows from the stored state at
    T# = 800. dS = 0 reproduces the recorded verdict (one negative pivot,
    lambda_min = -4.15160674834e-30); the block keeps one negative pivot up to
    dS = 43 and has none from 44 on. Planted fault: the record assembler
    refuses rows that do not flip monotonically."""
    d = _load(K2_SCOUTS)["dh_LDH_even"]["lesion_S"]
    assert d["T"] == 800.0 and d["N"] == 856 and d["prec"] == 1280 and d["kind"] == "dh"
    assert d["flip_between"] == ["43", "44"]
    rows = {r["dS"]: r for r in d["rows"]}
    assert rows["0"]["n_neg"] == 1 and rows["0"]["lam_min"] == "-4.15160674834e-30"
    assert rows["43"]["n_neg"] == 1 and rows["44"]["n_neg"] == 0
    S = _load(ENV)["S"]
    for r in d["rows"]:
        beta = math.log(5 * 800 / (2 * math.pi)) - 1 / 800 - S + float(Fraction(r["dS"]))
        assert abs(beta - r["beta"]) < 1e-9
    bad_rows = [dict(r) for r in d["rows"]]
    for r in bad_rows:
        if r["dS"] == "50":
            r.pop("n_neg", None)
            r["lam_nearest"] = "-1e-31"
    p = tmp_path / "bad.json"
    p.write_text(json.dumps({k: d[k] for k in ("T", "N", "prec", "envelope", "S_exact", "kind")} | {"rows": bad_rows}))
    with pytest.raises(ValueError):
        price.lesion_record([p])


def test_binet_lower_bound_for_the_archimedean_term():
    """Link 4 of PRICE.md item 7: from Binet's second formula,
    Re digamma(3/4 + it/2) >= log(t/2) - 3/(2t^2) - 1/(9t), which is at least
    log(t/2) - 1/t exactly when t >= 27/16 (the bound the scout uses for
    beta*). Checked in Arb at 14 points from 2 to 1e9, not a proof; the slack of the first inequality tends to 1/(9t) as the
    integral term vanishes faster than its bound. Planted check: the bound
    with the integral term dropped fails at small t."""
    ctx.prec = 128
    for tf in (2, 2.5, 3, 5, 10, 27, 100, 528, 540, 800, 870.77, 1e4, 1e6, 1e9):
        t = arb(tf)
        re_psi = acb(arb(3) / 4, t / 2).digamma().real
        binet = (t / 2).log() - arb(3) / (2 * t * t) - 1 / (9 * t)
        assert bool(re_psi > binet) and bool(binet >= (t / 2).log() - 1 / t), tf
    t = arb(2)
    assert not bool(acb(arb(3) / 4, t / 2).digamma().real > (t / 2).log() + 1 / (2 * t))


def test_stage_a_block_at_800_is_not_psd_with_honest_radii():
    """stage_a_v800.json: v^T R(800) v / |v|^2 for the scout's discrete rule,
    with every step in Arb and independent of the stored state and the Bessel
    column, is strictly negative and equals the stored row; the exact
    integrals are within the t-quadrature bound; the tail mass matches the
    stored state's 1 - v^T G(800) v."""
    d = _load(STAGE_A)
    assert (d["N"], d["T"], d["q"], d["n_y"], d["prec"]) == (856, 800.0, 64, 1500, 256)
    assert d["rq_discrete_upper"] < -4.1516067483e-30 and d["rq_discrete_rad"] < 1e-70
    assert d["rq_discrete_mid"].startswith("-4.15160674833")
    assert d["rq_exact_integrals_upper"] < -4.1516067483e-30 and d["t_quad_bound"] < 1e-87
    assert abs(float(d["mass_above_T_mid"]) / 1.488346502e-30 - 1) < 1e-8


def test_stage_a_at_the_witness_and_the_robustness_margin():
    """stage_a_witness.json: R(800) at the 856-mode witness, enclosed by the
    single-vector route, equals the stored-state value of the analysis, lies
    below the witness's Q_856 (R <= Q), and its tail mass gives the margin in
    S (PRICE.md item 7, link 5): delta < |Q(v)| / m_800(v) = 13.66."""
    d, rec = _load(HERE / "stage_a_witness.json"), _load(RECORD)
    assert d["vector"] == "witness_v856.json" and d["T"] == 800.0
    assert d["rq_discrete_mid"].startswith("-2.8315572128")
    assert abs(float(d["rq_discrete_mid"]) / float(rec["vs_R800"]["R800_at_witness"]) - 1) < 1e-10
    assert d["rq_exact_integrals_upper"] < rec["witness"]["rq_upper_with_eps"]
    margin = -rec["witness"]["rq_upper_with_eps"] / d["mass_above_T_upper"]
    assert 13.66 < margin < 13.67


def test_the_witness_vector_reproduces_its_recorded_enclosure_on_a_leading_check():
    """The stored witness vector is exactly the one the record evaluates: its
    length, basis and digits; and (cheap partial re-check) its boundary value
    f(L) recomputed here equals the recorded one."""
    d, v = _load(RECORD), _load(VEC)
    assert v["N"] == d["N"] and len(v["v"]) == d["N"] and v["L"] == d["L"]
    ctx.prec = W.PREC
    La = price.to_arb(L)
    x = [arb(s) for s in v["v"]]
    mu = sum((x[i] * ((arb(4 * i + 1) / 2) / La).sqrt() for i in range(len(x))), arb(0))
    assert abs(float(mu.mid()) / float(d["witness"]["boundary_value_f_L"]) - 1) < 1e-4


def _runs_md_hash_claims():
    """(line number, file name, SHA-256) for every committed artifact of this
    hunt that RUNS.md names with a hash: the first 64-hex word after the name
    on the same line."""
    import re
    out = []
    for i, line in enumerate((HERE / "RUNS.md").read_text().splitlines(), 1):
        for m in re.finditer(r"hunts/weil_dh_line/([\w.]+)", line):
            hs = re.findall(r"\b[0-9a-f]{64}\b", line[m.end():])
            if hs and (HERE / m.group(1)).exists():
                out.append((i, m.group(1), hs[0]))
    return out


def test_runs_md_hashes_match_the_committed_artifacts(tmp_path):
    """Every SHA-256 that RUNS.md gives for a committed artifact of this hunt is
    the hash of its bytes. Planted fault: a one-byte change to a hashed file is
    caught."""
    import hashlib
    claims = _runs_md_hash_claims()
    names = {n for _, n, _ in claims}
    assert {"witness_q856.json", "witness_v856.json", "witness_v101.json", "stage_a_v800.json",
            "stage_a_witness.json", "joint_L_DH.json", "k2env_dh_L_DH.json"} <= names
    for line, name, h in claims:
        assert hashlib.sha256((HERE / name).read_bytes()).hexdigest() == h, (line, name)
    line, name, h = claims[0]
    bad = bytearray((HERE / name).read_bytes())
    bad[-1] ^= 1
    assert hashlib.sha256(bytes(bad)).hexdigest() != h


def test_s_bound_in_arb_and_the_margin_back_to_540():
    """PRICE.md item 7, link 6: the Arb branch-and-bound proves
    sup(P_DH - H) <= S_used + 34/5 (every cluster at its target, the targets
    U_c + slack_c summing with the dropped mass to S_used + 6.8 exactly), and
    with the enclosed tail mass from 540 the refusal margin is positive at every
    T# >= 540 for N >= 856: Q(v) + 6.8 m_540 < 0. The coarser record gives 12,
    which covers T# >= 800 (margin 13.66)."""
    env = _load(ENV)
    for name, delta in (("arb_S_delta6.8.json", Fraction(34, 5)), ("arb_S_delta12.json", Fraction(12))):
        d = _load(HERE / name)
        assert d["ok"] and all(c["ok"] for c in d["clusters"]) and d["envelope"] == "k2env_dh_L_DH.json"
        assert Fraction(d["delta"]) == delta and Fraction(d["S_used"]) == Fraction(env["S_exact"])
        assert Fraction(d["S_bound"]) == Fraction(env["S_exact"]) + delta
        for c, ce in zip(d["clusters"], env["clusters"]):
            assert c["primes"] == ce["primes"] and c["U_float"] == ce["U"]
            assert c["best_centre_value_lower"] <= ce["U"] <= c["target_float"]    # the float U is not contradicted
    rec, s800 = _load(RECORD), _load(HERE / "stage_a_witness.json")
    mid = _load(HERE / "stage_a_witness_540_800.json")
    assert mid["panels"] == [1080, 1600] and mid["vector"] == "witness_v856.json"
    q = rec["witness"]["rq_upper_with_eps"]
    m800 = s800["mass_above_T_upper"] + s800["t_quad_bound"]
    m540 = m800 + mid["mass_between_upper_exact"]
    assert q + 12 * m800 < 0 and q + 6.8 * m540 < -2.7e-31
    assert q + 12 * m540 > 0                       # why the tighter bound was needed for 540


def test_arb_sup_bound_live_and_a_planted_target_below_the_supremum():
    """The Arb branch-and-bound re-proved here on the cluster {17, 23} at
    target U + 1 (about 7 s), and a planted target just below its own best
    centre value cannot be proved (the run stops at the box cap with ok False)."""
    sys.path.insert(0, str(HERE))
    import joint
    env = _load(ENV)
    c = next(c for c in env["clusters"] if c["primes"] == [17, 23])
    om, hq = [tuple(k) for k in c["omega"]], [Fraction(x) for x in c["h"]]
    w = price._weights_from_spec(c.get("weights"))
    r = joint.arb_sup_bound(L, c["primes"], om, hq, Fraction(c["U"]) + 1, kind="dh", weights=w, level0=7)
    assert r["ok"] and r["max_discarded_bound"] <= c["U"] + 1
    bad = joint.arb_sup_bound(L, c["primes"], om, hq, Fraction(r["best_centre_value_lower"]) - Fraction(1, 100),
                              kind="dh", weights=w, level0=7, max_boxes=12000)
    assert not bad["ok"]


def test_arb_envelope_bound_refuses_settings_that_would_drop_a_cluster():
    """Review 2026-10-27: zip() over shorter settings lists once let the driver
    return ok with clusters missing (planted: two slacks for four clusters gave
    ok True, S_bound 3.08), and a part count of 0 would pass a cluster on
    all([]). Both now raise before any box is evaluated."""
    n = len(_load(ENV)["clusters"])
    with pytest.raises(ValueError):
        price.arb_envelope_bound(ENV, [1] * (n - 2), [7] * n, [1] * n)
    with pytest.raises(ValueError):
        price.arb_envelope_bound(ENV, [1] * n, [7] * n, [1] * (n - 1) + [0])

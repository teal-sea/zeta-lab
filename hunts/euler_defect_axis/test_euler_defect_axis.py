"""Pins for the numbers `RESULTS.md` and its front door `docs/40` state.

Run from the repository root:

    .venv/bin/python -m pytest -q hunts/euler_defect_axis

Written 2026-10-10, when the hunt was landed on main. Until then nothing pinned
these numbers: `probe.py` and `ordering.py` wrote artifacts, and
`artifacts/cutoff.json` came from a one-off command recorded in `RUNS.md` with
no script behind it. Here every number is recomputed from the forms
themselves and compared with the artifact and with the page, so a drift in
either goes red. Where a recomputation does not reproduce a stated number,
the test pins what does reproduce and `RESULTS.md` says so at the point of use.

Nothing writes into the tree: the two scripts are run with their artifact
directory redirected to a temporary one and their output compared byte for
byte with the committed files.

Nothing here bears on RH (`docs/08`).
"""
from __future__ import annotations

import itertools
import json
import math
import re
from pathlib import Path

import numpy as np
import pytest
from mpmath import mp
from scipy.stats import spearmanr

from hunts.euler_defect_axis import ordering as O
from hunts.euler_defect_axis import probe as P
from zeta.epstein import epstein_reduced_forms
from zeta.epstein import epstein_representation_count as rep

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
ART = HERE / "artifacts"
CUTOFFS = (61, 121, 201, 401)

#: The nine discriminants of class number above one, as RESULTS.md section 5 lists them.
LOUD = (-15, -20, -23, -24, -31, -39, -47, -71, -95)

#: RESULTS.md section 5 table: principal-form composite defect at n < 61 and n < 401.
TABLE_61 = {-15: 5.0847, -20: 3.8823, -23: 3.5569, -24: 3.8530, -31: 3.3991,
            -39: 3.3959, -47: 3.3630, -71: 3.2614, -95: 2.9608}
TABLE_401 = {-15: 10.5748, -20: 8.6847, -23: 7.8781, -24: 6.9748, -31: 6.8130,
             -39: 6.4807, -47: 6.1235, -71: 5.4149, -95: 5.0196}


def _axis() -> list[dict]:
    return json.loads((ART / "axis.json").read_text(encoding="utf-8"))


def _cutoff() -> dict:
    return json.loads((ART / "cutoff.json").read_text(encoding="utf-8"))


def _results() -> str:
    return (HERE / "RESULTS.md").read_text(encoding="utf-8")


def _series(form, d, nmax=P.NMAX):
    """a(n) = r_Q(n) / w for 1 <= n < nmax, a(0) unused."""
    w = P.units(d)
    return [mp.mpf(0)] + [mp.mpf(rep(n, form)) / w for n in range(1, nmax)]


def _defect(c, nmax) -> float:
    """The probe's composite defect, at any cutoff (the probe's own is fixed at 61)."""
    comp = [n for n in range(2, nmax) if not P.is_prime_power(n)]
    return float(mp.sqrt(sum((c[n] / mp.sqrt(n)) ** 2 for n in comp)))


def _principal(d):
    forms = epstein_reduced_forms(d)
    assert forms[0][0] == 1
    return forms[0]


# --- the two scripts reproduce their committed artifacts -------------------


def test_probe_reproduces_axis_json_byte_for_byte(tmp_path, monkeypatch):
    """Every number read off axis.json below is the probe's current output."""
    monkeypatch.setattr(P, "ART", tmp_path)
    with mp.workdps(mp.dps):  # main() sets mp.dps; restore it on exit
        P.main()
    assert (tmp_path / "axis.json").read_bytes() == (ART / "axis.json").read_bytes()


def test_ordering_reproduces_ordering_json_byte_for_byte(tmp_path, monkeypatch):
    (tmp_path / "cutoff.json").write_bytes((ART / "cutoff.json").read_bytes())
    monkeypatch.setattr(O, "ART", tmp_path)
    O.main()
    assert (tmp_path / "ordering.json").read_bytes() == (ART / "ordering.json").read_bytes()


def test_cutoff_json_is_the_principal_form_defect_at_each_cutoff():
    """cutoff.json had no script behind it (RUNS.md, the audit manifest).
    Recomputed here from the principal forms: equal to the last bit."""
    data = _cutoff()
    assert sorted(data, key=int) == [str(c) for c in CUTOFFS]
    with mp.workdps(P.DPS):
        for nmax in CUTOFFS:
            stored = dict((d, v) for d, v in data[str(nmax)])
            assert sorted(stored) == sorted(LOUD)
            for d in LOUD:
                a = _series(_principal(d), d, nmax)
                assert _defect(P.spectrum(a, nmax), nmax) == stored[d], (nmax, d)


# --- section 1 and 2: a(1), the counts, the table --------------------------


def test_the_counts_41_14_27_and_the_per_discriminant_table():
    rows = _axis()
    assert [r["discriminant"] for r in rows] == list(P.DISCRIMINANTS)
    forms = [f for r in rows for f in r["forms"]]
    assert len(forms) == 41
    assert sum(f["a1"] == 1.0 for f in forms) == 14
    assert sum(f["a1"] == 0.0 for f in forms) == 27
    assert all(f["a1"] in (0.0, 1.0) for f in forms)
    expected_h = {-3: 1, -4: 1, -7: 1, -8: 1, -11: 1, -15: 2, -20: 2, -24: 2,
                  -23: 3, -31: 3, -39: 4, -47: 5, -71: 7, -95: 8}
    for r in rows:
        d = r["discriminant"]
        assert r["class_number"] == expected_h[d]
        assert r["n_forms_entitled"] == 1
        # section 6: the class-group sum is silent on every discriminant
        assert r["class_group_sum_defect"] < 1e-25, d
        assert r["class_group_sum_identity_residual"] < 1e-25, d
        ones = [f for f in r["forms"] if f["a1"] == 1.0]
        assert len(ones) == 1 and ones[0]["form"][0] == 1 and ones[0]["recursion_entitled"]
        # a(1) is the exact count r_Q(1) / w, not a float reading
        for f in r["forms"]:
            assert rep(1, tuple(f["form"])) == (P.units(d) if f["form"][0] == 1 else 0)


def test_no_rescaling_reaches_z_q():
    """None of the 27 represents only multiples of its least represented value."""
    rows = _axis()
    bad = [f for r in rows for f in r["forms"] if f["a1"] == 0.0]
    assert len(bad) == 27
    assert not any(f["all_represented_values_divisible_by_least"] for f in bad)
    assert P.represented_values((2, 1, 2))[:2] == [2, 3]
    assert P.represented_values((2, -1, 3))[:2] == [2, 3]
    assert (2, 1, 2) in epstein_reduced_forms(-15)
    assert (2, -1, 3) in epstein_reduced_forms(-23)


def test_the_published_axis_and_the_entitled_axis_at_61():
    rows = {r["discriminant"]: r for r in _axis()}
    published = max(r["max_defect_as_published"] for r in rows.values())
    assert f"{published:.4f}" == "36.0644"
    d15 = rows[-15]
    loudest = max(d15["forms"], key=lambda f: f["reported_composite_defect"])
    assert loudest["form"] == [2, 1, 2]
    assert f"{loudest['identity_max_residual']:.4f}" == "189.6888"
    assert loudest["identity_max_residual"] == max(
        f["identity_max_residual"] for r in rows.values() for f in r["forms"])
    for d, r in rows.items():
        if r["class_number"] == 1:
            assert r["max_defect_over_entitled_forms"] < 1e-25
    entitled = [rows[d]["max_defect_over_entitled_forms"] for d in LOUD]
    assert (f"{min(entitled):.4f}", f"{max(entitled):.4f}") == ("2.9608", "5.0847")


def test_the_residual_is_a_rescaling_of_max_c():
    """R = |1 - a(1)| * max_n |c(n)| identically (RESULTS.md section 2).

    The page's split, 0.0 on 40 rows and 1.6e-30 on one, does not reproduce;
    this pins what does. In the probe's float output, R equals the float
    product exactly on all 27 non-principal rows. On the 14 principal rows
    the product is exactly 0, so the difference is R itself: 0.0 on 6 and
    between 7.9e-31 and 3.2e-30 on 8. At working precision the identity
    holds to below 3e-29 on all 41.
    """
    zero, nonzero, worst_mp = 0, [], mp.mpf(0)
    with mp.workdps(P.DPS):
        for d in P.DISCRIMINANTS:
            for f in epstein_reduced_forms(d):
                a = _series(f, d)
                c = P.spectrum(a)
                R, _ = P.identity_residual(a, c)
                prod = abs(1 - a[1]) * max(abs(c[n]) for n in range(2, P.NMAX))
                diff = abs(R - float(prod))
                if a[1] == 0:
                    assert diff == 0.0, (d, f)
                else:
                    assert prod == 0 and diff == R
                if diff == 0.0:
                    zero += 1
                else:
                    nonzero.append(diff)
                rhs_worst = mp.mpf(0)
                for n in range(2, P.NMAX):
                    rhs = sum(c[k] * a[n // k] for k in range(1, n + 1) if n % k == 0)
                    rhs_worst = max(rhs_worst, abs(a[n] * mp.log(n) - rhs))
                worst_mp = max(worst_mp, abs(rhs_worst - prod))
    assert (zero, len(nonzero)) == (33, 8)
    assert 7.8e-31 < min(nonzero) and max(nonzero) < 3.2e-30
    assert worst_mp < mp.mpf("3e-29")
    assert zero != 40  # the stated split, recorded as not reproduced


def test_defect_and_residual_are_two_norms_of_one_vector():
    """corr 0.99 over the 27 rows, shared argmax (RESULTS.md section 2)."""
    bad = [f for r in _axis() for f in r["forms"] if f["a1"] == 0.0]
    D = np.array([f["reported_composite_defect"] for f in bad])
    R = np.array([f["identity_max_residual"] for f in bad])
    assert f"{np.corrcoef(D, R)[0, 1]:.2f}" == "0.99"
    assert int(np.argmax(D)) == int(np.argmax(R))


# --- section 3: the published numbers are 1 + Z_Q(s) ------------------------


def _dirichlet_log_c(a, nmax=P.NMAX):
    """c(n) = b(n) log n with log f = sum_k (-1)^(k+1) u^{*k} / k, u = a - delta_1.

    Shares no code with the recursion: repeated Dirichlet convolution of u,
    which terminates because u^{*k} vanishes below 2^k.
    """
    u = [mp.mpf(0), mp.mpf(0)] + [a[n] for n in range(2, nmax)]
    b = [mp.mpf(0)] * nmax
    power, k = u[:], 1
    while any(power[n] for n in range(2, nmax)):
        for n in range(2, nmax):
            b[n] += (-1) ** (k + 1) * power[n] / k
        new = [mp.mpf(0)] * nmax
        for m in range(2, nmax):
            if power[m]:
                for j in range(2, (nmax - 1) // m + 1):
                    new[m * j] += power[m] * u[j]
        power, k = new, k + 1
    return [b[n] * mp.log(n) if n >= 2 else mp.mpf(0) for n in range(nmax)]


def test_published_non_principal_numbers_are_composite_defects_of_one_plus_z_q():
    """Worst absolute disagreement 0.0 over all 27 rows, by a route sharing no
    code with the recursion; the coefficient vectors agree to below 3e-29."""
    worst_defect, worst_coeff, rows = 0.0, mp.mpf(0), 0
    with mp.workdps(P.DPS):
        for r in _axis():
            d = r["discriminant"]
            for f in r["forms"]:
                if f["a1"] != 0.0:
                    continue
                a = _series(tuple(f["form"]), d)
                a[1] = mp.mpf(1)
                c = _dirichlet_log_c(a)
                worst_defect = max(worst_defect, abs(P.defect(c) - f["reported_composite_defect"]))
                c_rec = P.spectrum(a)
                worst_coeff = max(worst_coeff, max(abs(c[n] - c_rec[n]) for n in range(2, P.NMAX)))
                rows += 1
    assert rows == 27
    assert worst_defect == 0.0
    assert worst_coeff < mp.mpf("3e-29")


def test_no_integer_indexed_c_solves_the_identity_for_a_non_principal_form():
    """Least squares over c(1..60), c(1) free: residual 2.18 to 5.79 on all 27."""
    norms = []
    for d in P.DISCRIMINANTS:
        for f in epstein_reduced_forms(d):
            if rep(1, f) > 0:
                continue
            w = P.units(d)
            a = [0.0] + [rep(n, f) / w for n in range(1, P.NMAX)]
            A = np.zeros((P.NMAX - 2, P.NMAX - 1))
            y = np.zeros(P.NMAX - 2)
            for i, n in enumerate(range(2, P.NMAX)):
                y[i] = a[n] * math.log(n)
                for k in range(1, n + 1):
                    if n % k == 0:
                        A[i, k - 1] += a[n // k]
            sol, *_ = np.linalg.lstsq(A, y, rcond=None)
            norms.append(float(np.linalg.norm(A @ sol - y)))
    assert len(norms) == 27
    assert (f"{min(norms):.2f}", f"{max(norms):.2f}") == ("2.18", "5.79")


# --- section 4: the class-number-one control ---------------------------------


def _chi_euler(d: int, n: int) -> int:
    """Kronecker symbol (d/n), built independently of probe.kronecker: complete
    multiplicativity over the factorisation of n, Euler's criterion at odd p,
    and the d mod 8 rule at p = 2."""
    out, m, p = 1, n, 2
    while m > 1:
        if m % p == 0:
            e = 0
            while m % p == 0:
                m //= p
                e += 1
            if p == 2:
                v = 0 if d % 2 == 0 else (1 if d % 8 in (1, 7) else -1)
            else:
                r = pow(d % p, (p - 1) // 2, p)
                v = 0 if r == 0 else (1 if r == 1 else -1)
            out *= v ** e
        p += 1
    return out


def _lambda(n: int):
    for p in range(2, n + 1):
        if n % p == 0:
            while n % p == 0:
                n //= p
            return mp.log(p) if n == 1 else mp.mpf(0)
    return mp.mpf(0)


def test_kronecker_agrees_with_an_independent_construction():
    for d in P.DISCRIMINANTS:
        for n in range(1, 400):
            assert P.kronecker(d, n) == _chi_euler(d, n), (d, n)


def test_class_number_one_control_and_its_teeth():
    """c(n) = Lambda(n)(1 + chi_d(n)) matches the recursion to 2.8e-30 on the five
    h = 1 discriminants, and misses by more than 1 on every h > 1 principal form,
    so the control is not one that passes everything."""
    rows = {r["discriminant"]: r for r in _axis()}
    stored = max(r["euler_prediction_max_defect"] for r in rows.values() if r["class_number"] == 1)
    assert f"{stored:.1e}" == "2.8e-30"
    with mp.workdps(P.DPS):
        for d in P.DISCRIMINANTS:
            c = P.spectrum(_series(_principal(d), d))
            pred = [mp.mpf(0)] + [_lambda(n) * (1 + _chi_euler(d, n)) for n in range(1, P.NMAX)]
            miss = max(abs(c[n] - pred[n]) for n in range(2, P.NMAX))
            if rows[d]["class_number"] == 1:
                assert miss < 3e-30, d
            else:
                assert miss > 1, d


def test_the_entitled_rows_are_the_e7_column_on_main():
    """The repair #296 applied: docs/34 table E7's principal-form column is the
    number this hunt measured, row for row."""
    e7 = json.loads((ROOT / "hunts" / "zeta_temperament" / "results_euler.json")
                    .read_text(encoding="utf-8"))["epstein"]
    ours = {r["discriminant"]: r["principal_form_defect"] for r in _axis()}
    assert {r["discriminant"]: r["principal_form_defect"] for r in e7} == ours


# --- section 5: the corrected axis across cutoffs ----------------------------


def test_section_5_table_and_bands():
    data = {int(k): dict((d, v) for d, v in rows) for k, rows in _cutoff().items()}
    for d in LOUD:
        assert data[61][d] == pytest.approx(TABLE_61[d], abs=5e-5), d
        assert data[401][d] == pytest.approx(TABLE_401[d], abs=5e-5), d
    bands = {c: (min(data[c].values()), max(data[c].values())) for c in CUTOFFS}
    assert [f"{bands[c][0]:.2f} .. {bands[c][1]:.2f}" for c in CUTOFFS] == [
        "2.96 .. 5.08", "3.78 .. 6.17", "4.18 .. 7.15", "5.02 .. 10.57"]
    width_over_mean = [(bands[c][1] - bands[c][0]) / np.mean(list(data[c].values()))
                       for c in CUTOFFS]
    assert [f"{x:.2f}" for x in width_over_mean] == ["0.58", "0.52", "0.54", "0.78"]
    # doors, frozen constant: "the band roughly doubles from cutoff 61 to 401"
    lo, hi = bands[401][0] / bands[61][0], bands[401][1] / bands[61][1]
    assert 1.6 < lo < 1.8 and 2.0 < hi < 2.1


def test_class_number_one_stays_silent_at_cutoff_401():
    """RESULTS.md section 1: '0, then 5.0196 .. 10.5748' at n < 401."""
    with mp.workdps(P.DPS):
        for d in (-3, -4, -7, -8, -11):
            a = _series(_principal(d), d, 401)
            assert _defect(P.spectrum(a, 401), 401) < 1e-25, d


def test_the_ordering_is_nearly_stable():
    """Six of nine positions fixed at every cutoff, movement only inside
    -20, -23, -24, Spearman 0.9500, 0.9833, 0.9833 against 61, and 1.0000
    between 201 and 401."""
    order = O.orderings(_cutoff())
    assert O.fixed_positions(order) == [0, 4, 5, 6, 7, 8]
    assert order["61"][0] == -15 and order["61"][4:] == [-31, -39, -47, -71, -95]
    moved = {x for c in ("121", "201", "401") for pair in O.inversions(order["61"], order[c])
             for x in pair}
    assert moved == {-20, -23, -24}
    assert O.inversions(order["61"], order["401"]) == [(-24, -23)]
    assert order["201"] == order["401"] != order["61"]
    data = _cutoff()

    def rho(a, b):
        va, vb = dict(data[a]), dict(data[b])
        return float(spearmanr([va[k] for k in LOUD], [vb[k] for k in LOUD]).statistic)

    assert [f"{rho('61', c):.4f}" for c in ("121", "201", "401")] == ["0.9500", "0.9833", "0.9833"]
    assert f"{rho('201', '401'):.4f}" == "1.0000"


def _loud_arrays():
    data = dict((d, v) for d, v in _cutoff()["61"])
    defect = np.array([data[d] for d in LOUD])
    h = np.array([len(epstein_reduced_forms(d)) for d in LOUD], dtype=float)
    logd = np.log(-np.array(LOUD, dtype=float))
    return defect, h, logd


def test_correlations_and_the_withdrawn_attribution():
    defect, h, logd = _loud_arrays()
    assert f"{np.corrcoef(defect, h)[0, 1]:.2f}" == "-0.69"
    assert f"{np.corrcoef(defect, logd)[0, 1]:.2f}" == "-0.82"
    assert f"{np.corrcoef(h, logd)[0, 1]:+.2f}" == "+0.97"
    assert f"{spearmanr(defect, h).statistic:.3f}" == "-0.979"  # ties in h: tie-corrected
    assert f"{spearmanr(defect, logd).statistic:.3f}" == "-0.983"


def test_the_permutation_p_value_for_the_gap():
    """The page's p = 0.113 is the audit's 200,000-draw Monte Carlo estimate.
    The exact value over all 9! orderings of the defect is 0.1124, inside
    three Monte Carlo standard errors of 0.113."""
    defect, h, logd = _loud_arrays()

    def z(v):
        return (v - v.mean()) / v.std()

    zd, zh, zl = z(defect), z(h), z(logd)
    observed = abs(zd @ zl) / 9 - abs(zd @ zh) / 9
    perms = np.array(list(itertools.permutations(range(9))), dtype=np.int8)
    x = zd[perms]
    gaps = np.abs(x @ zl) / 9 - np.abs(x @ zh) / 9
    p = float(np.mean(gaps >= observed - 1e-12))
    assert f"{p:.4f}" == "0.1124"
    se = math.sqrt(p * (1 - p) / 200_000)
    assert abs(0.113 - p) < 3 * se


def test_the_sparsity_proxy_does_not_carry_the_mechanism():
    """corr +0.47, R^2 0.22, t 1.39 against the count of represented n < 61, and
    the coefficient on the count turns negative once log|d| is in the model."""
    defect, _, logd = _loud_arrays()
    count = np.array([sum(1 for n in range(1, P.NMAX) if rep(n, _principal(d)) > 0)
                      for d in LOUD], dtype=float)
    r = float(np.corrcoef(defect, count)[0, 1])
    t = r * math.sqrt(len(LOUD) - 2) / math.sqrt(1 - r * r)
    assert (f"{r:+.2f}", f"{r * r:.2f}", f"{t:.2f}") == ("+0.47", "0.22", "1.39")
    X = np.column_stack([np.ones(len(LOUD)), count, logd])
    beta, *_ = np.linalg.lstsq(X, defect, rcond=None)
    assert r > 0 and beta[1] < 0


# --- section 7, door 2: the class-group characters ---------------------------


def _character_tables():
    """Characters of the cyclic class groups where the group is forced by
    inverse pairs: (a, b, c) and (a, -b, c) are inverse classes, and at
    d = -39 the ambiguous form (3, 3, 4) is the element of order 2."""
    w3 = mp.exp(2j * mp.pi / 3)
    tables = []
    for d in (-15, -20, -24):
        tables.append((d, {_principal(d): 1, [f for f in epstein_reduced_forms(d)
                                              if f[0] != 1][0]: -1}))
    for d, (g, ginv) in ((-23, ((2, 1, 3), (2, -1, 3))), (-31, ((2, 1, 4), (2, -1, 4)))):
        tables.append((d, {_principal(d): 1, g: w3, ginv: w3 ** 2}))
        tables.append((d, {_principal(d): 1, g: w3 ** 2, ginv: w3}))
    g, ginv, g2 = (2, 1, 5), (2, -1, 5), (3, 3, 4)
    tables.append((-39, {(1, 1, 10): 1, g: 1j, ginv: -1j, g2: -1}))
    tables.append((-39, {(1, 1, 10): 1, g: -1, ginv: -1, g2: 1}))
    return tables


def _character_defect(d, chi):
    assert set(chi) == set(epstein_reduced_forms(d))
    w = P.units(d)
    a = [mp.mpc(0)] + [sum(mp.mpc(v) * rep(n, f) for f, v in chi.items()) / w
                       for n in range(1, P.NMAX)]
    assert abs(a[1] - 1) < 1e-28
    c = [mp.mpc(0)] * P.NMAX
    for n in range(2, P.NMAX):
        s = a[n] * mp.log(n)
        for k in range(1, n):
            if n % k == 0:
                s -= c[k] * a[n // k]
        c[n] = s
    return float(mp.sqrt(sum(abs(c[n]) ** 2 / n for n in P.COMPOSITES)))


def test_every_class_group_character_has_an_euler_product():
    """Door 2: L(s, chi) = sum_Q chi(Q) zeta_Q(s) has a(1) = 1 and defect zero,
    checked on h = 2, 3, 4 (d = -15, -20, -24, -23, -31, -39), real and complex
    characters. The planted fault, a table that is not a homomorphism, is loud."""
    with mp.workdps(P.DPS):
        for d, chi in _character_tables():
            assert _character_defect(d, chi) < 1e-28, (d, chi)
        w3 = mp.exp(2j * mp.pi / 3)
        not_a_character = {(1, 1, 6): 1, (2, 1, 3): w3, (2, -1, 3): w3}
        assert _character_defect(-23, not_a_character) > 1
        swapped = {(1, 1, 10): 1, (2, 1, 5): 1j, (2, -1, 5): -1, (3, 3, 4): -1j}
        assert _character_defect(-39, swapped) > 1


# --- the page states what is pinned ------------------------------------------


def test_results_states_the_pinned_numbers():
    text = _results()
    for s in ("36.0644", "189.6888", "2.9608 .. 5.0847", "5.0196 .. 10.5748", "2.8e-30",
              "2.18 to 5.79", "`0.9500`", "`0.9833`", "`rho = 1.0000`", "p = 0.113",
              "`corr(h, log|d|) = +0.97`", "`-0.979`", "`-0.983`", "`R^2 = 0.22`"):
        assert s in text, s
    for d in LOUD:
        assert re.search(rf"\| {d} \| \d \| {TABLE_61[d]:.4f} \| {TABLE_401[d]:.4f} \|", text), d


def test_the_front_door_states_the_pinned_numbers():
    page = (ROOT / "docs" / "40-one-form-per-discriminant.md").read_text(encoding="utf-8")
    assert page.startswith("# 40. ")
    for s in ("**Hunt #127,", "`36.0644` at `d = -15`", "41 reduced binary quadratic forms",
              "`+0.97`", "`-0.983` and `-0.979`", "`p = 0.113`", "`0.1124`", "`R^2 = 0.22`",
              "`5.02` to `10.57` instead of `2.96` to `5.08`", "residual 2.18 to 5.79",
              "correlated at 0.99", "worst disagreement `0.0`"):
        assert s in page, s


def test_audit_counts_the_page_quotes():
    """'eight attacks' and 'eleven places': AUDIT.md numbers its attacks 1 to 8
    (some with a lettered follow-up) and lists eleven overclaimed sentences."""
    audit = (HERE / "AUDIT.md").read_text(encoding="utf-8")
    attacks = {int(m) for m in re.findall(r"^### \d+\. Attack (\d+)[a-z]?:", audit, re.M)}
    assert attacks == set(range(1, 9))
    tail = audit.split("## Sentences the audit called overclaims", 1)[1]
    assert len(re.findall(r"^- ", tail, re.M)) == 11

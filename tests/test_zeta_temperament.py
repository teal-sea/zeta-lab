"""Pins for hunt #76 (`hunts/zeta_temperament/`): the Riemann zeros in tuning units.

theta = gamma ln2 / 2pi is a zero's ordinate in steps per octave. Landau's
formula says the mean over zeros of n^{i gamma} is -Lambda(n)/sqrt(n) divided
by the mean of log(gamma/2pi), up to O(log T / N). In these units that is the
Fourier coefficient of the zeros mod 1 at frequency log2 n. The always-on
check uses the laboratory's own 2000 cached zeros (independent of Odlyzko's
table); the 100,000-zero checks run when `data/odlyzko/zeros1` is present.
"""

from __future__ import annotations

import json
import sys
from math import log, sqrt
from pathlib import Path

import numpy as np
import pytest
from mpmath import mp

_ROOT = Path(__file__).resolve().parents[1]
_HUNT = _ROOT / "hunts" / "zeta_temperament"
if str(_HUNT) not in sys.path:
    sys.path.insert(0, str(_HUNT))

import probe_euler_discriminator as pe  # noqa: E402
import probe_landau_edo as pl  # noqa: E402

LN2 = log(2.0)


def _own_zeros():
    from zeta.explicit import first_zeros

    g = first_zeros(2000)
    if len(g) < 2000:
        pytest.skip("fewer than 2000 cached zeros")
    return g


def test_von_mangoldt():
    assert [pl.lam(n) for n in (2, 3, 4, 6, 8, 9, 12)] == pytest.approx(
        [log(2), log(3), log(2), 0.0, log(2), log(3), 0.0])


@pytest.mark.slow
# Marked slow 2026-08-24: measured at 571s in CI, the second-slowest test in the fast tier. The measurement is unchanged; it runs in the slow tier.
def test_landau_in_tuning_units_on_own_zeros():
    """Prime powers carry Landau's coefficient to within 6 percent on 2000
    zeros; composites sit within three random-points standard errors of zero."""
    g = _own_zeros()
    th = g * LN2 / (2 * np.pi)
    L = np.mean(np.log(g / (2 * np.pi)))
    se = 1 / sqrt(2 * len(g))
    for n in (2, 3, 4, 5, 7, 8, 9, 11, 13):
        c = np.mean(np.exp(2j * np.pi * th * np.log2(n))).real
        pred = -pl.lam(n) / sqrt(n) / L
        assert abs(c - pred) < 0.06 * abs(pred), (n, c, pred)
    for n in (6, 10, 12, 15):
        c = np.mean(np.exp(2j * np.pi * th * np.log2(n)))
        assert abs(c) < 3 * se, (n, c)


def test_zeros_avoid_integer_temperaments_on_own_zeros():
    g = _own_zeros()
    th = g * LN2 / (2 * np.pi)
    frac = th - np.round(th)
    L = np.mean(np.log(g / (2 * np.pi)))
    measured = pl.box_density(frac)
    predicted = pl.predicted_box_density(L, 2)
    assert measured < 0.75
    assert abs(measured - predicted) < 0.05
    assert np.mean(np.abs(frac) < 0.05) < 0.07  # uniform would give 0.10


def test_planted_fault_is_caught():
    """Shift every zero by half a step: the integer deficit must disappear."""
    g = _own_zeros()
    th = g * LN2 / (2 * np.pi) + 0.5
    frac = th - np.round(th)
    assert pl.box_density(frac) > 1.0


def _odlyzko_results():
    path = _HUNT / "results_landau.json"
    if not path.is_file():
        pytest.skip("results_landau.json not generated")
    return json.loads(path.read_text())["odlyzko"]


def test_odlyzko_table_matches_landau_to_four_decimals():
    r = _odlyzko_results()
    assert r["zeros"] == 100_000
    for c in r["coefficients"]:
        if c["prime_power"]:
            assert abs(c["measured_re"] - c["predicted"]) < 0.0015, c
        else:
            assert abs(c["measured_re"]) < 0.0005 and abs(c["measured_im"]) < 0.0005, c
    assert r["density_integer"] == pytest.approx(0.801, abs=0.003)
    assert r["density_integer_predicted"] == pytest.approx(0.800, abs=0.003)
    assert r["density_fifth_perfect"] == pytest.approx(0.762, abs=0.003)
    assert r["density_composite6_control"] == pytest.approx(1.0, abs=0.01)
    dens = [b["measured"] for b in r["bands"]]
    assert dens == sorted(dens)  # the deficit shrinks with height, as 1/log t


def test_peaks_calibration_reproduces_the_known_ranking():
    path = _HUNT / "results_peaks.json"
    if not path.is_file():
        pytest.skip("results_peaks.json not generated")
    r = json.loads(path.read_text())
    assert r["spearman_by_prime_set"]["3,5,7,11,13"]["raw"] < -0.7
    assert r["null_abs_spearman_p999"] < 0.3
    assert r["classic_in_top24"] >= 6
    assert r["classic_ranks_of_396"]["311"] == 1
    twelve = next(h for h in r["horizon"] if h["x"] == 12)
    assert twelve["N"] == 4
    assert abs(twelve["remainder"]) < 0.35


# --- the correction: this hunt re-measured a quantity the repo already had ---


def test_prime_spectrum_already_computes_this_hunts_measurement():
    """`zeta.explicit.prime_spectrum` is the same quantity as E1, up to -2N.

    This pins the correction notice at the head of `docs/34`. E1 measured the
    mean of n^{i gamma} over zeros; the repository already exposed
    D(u) = -2 sum_gamma cos(gamma u), whose docstring states that it peaks at
    u = log p^k "and no peak anywhere else". If this test ever fails, either
    the core function changed or the correction notice needs revisiting.
    """
    import numpy as np
    from zeta.explicit import first_zeros, prime_spectrum

    g = first_zeros(2000)
    if len(g) < 2000:
        pytest.skip("fewer than 2000 cached zeros")
    us = [np.log(n) for n in (2, 3, 5, 6, 7, 10)]
    lab = prime_spectrum(g, us, window=None, normalize=False)
    for u, d in zip(us, lab):
        mine = float(np.mean(np.cos(g * u)))
        assert d == pytest.approx(-2 * len(g) * mine, rel=1e-9)
    # and the composites are the small ones, in both routes
    assert abs(lab[3]) < 10 and abs(lab[5]) < 10          # n = 6, 10
    assert all(abs(lab[i]) > 300 for i in (0, 1, 2, 4))   # n = 2, 3, 5, 7


# --- the Euler-product discriminator (section 6 of docs/34) -----------------


def _euler():
    path = _HUNT / "results_euler.json"
    if not path.is_file():
        pytest.skip("results_euler.json not generated")
    return json.loads(path.read_text())


def test_the_spectrum_recursion_reproduces_von_mangoldt_for_zeta():
    r = _euler()
    assert r["zeta"]["matches_von_mangoldt"]
    assert r["zeta"]["composite_defect"] < 1e-25
    assert r["zeta"]["c"]["2"] == pytest.approx(np.log(2), abs=1e-12)
    assert r["zeta"]["c"]["9"] == pytest.approx(np.log(3), abs=1e-12)
    assert r["zeta"]["c"]["6"] == pytest.approx(0.0, abs=1e-25)


def test_davenport_heilbronns_loudest_spectral_line_is_composite():
    """DH shares the functional equation and has no Euler product, so its
    composite lines do not vanish; the loudest line of all is a composite."""
    r = _euler()["davenport_heilbronn"]
    assert r["composite_defect"] > 1.0
    assert r["loudest_line"]["is_composite"]
    assert r["loudest_line"]["n"] == 51
    assert abs(r["loudest_line"]["c"]) > r["loudest_prime_line_abs"]


def test_epstein_class_number_one_is_silent_and_the_class_group_sum_restores_it():
    """Class number 1 gives an Euler product and a vanishing composite defect.
    Class number > 1 gives a loud principal form, and the class-group sum,
    which is w * zeta_K, is silent again.

    Until 2026-10-10 this test read the maximum over every reduced form and
    asserted it exceeded 30 at d = -15. That pinned 36.0644, which belongs to
    1 + Z_Q(s) for the non-principal form (2, 1, 2), not to Z_Q (issue #93);
    nothing in the corrected column reaches 30, so the line has no replacement
    at that strength.
    """
    r = _euler()["epstein"]
    assert len(r) >= 14
    for f in r:
        if f["class_number"] == 1:
            assert f["principal_form_defect"] < 1e-25, f["discriminant"]
        else:
            assert f["principal_form_defect"] > 1.0, f["discriminant"]
        assert f["class_group_sum_defect"] < 1e-25, f["discriminant"]


# --- the a(1) = 1 hypothesis, and the repair of table E7 (issue #93) --------

#: docs/34 table E7, principal-form column, as corrected 2026-10-10.
E7_PRINCIPAL_FORM_DEFECT = {
    -15: 5.0847, -20: 3.8823, -23: 3.5569, -24: 3.8530, -31: 3.3991,
    -39: 3.3959, -47: 3.3630, -71: 3.2614, -95: 2.9608,
}

#: The per-form maxima the first E7 table printed and the correction keeps as
#: "was": each is the composite defect of 1 + Z_Q(s) for a non-principal form.
E7_SUPERSEDED_MAX_FORM_DEFECT = {
    -15: 36.0644, -20: 18.6176, -24: 12.4955, -39: 7.6474, -47: 3.4709, -95: 4.2511,
}


def _epstein_series(form, d):
    """a(n) = r_Q(n) / w for n < NMAX, a(0) unused."""
    from zeta.epstein import epstein_representation_count as rep

    w = pe.units(d)
    return [mp.mpf(0)] + [mp.mpf(rep(n, form)) / w for n in range(1, pe.NMAX)]


def _class_group_sum(d):
    from zeta.epstein import epstein_reduced_forms

    total = [mp.mpf(0)] * pe.NMAX
    for f in epstein_reduced_forms(d):
        a = _epstein_series(f, d)
        for n in range(1, pe.NMAX):
            total[n] += a[n]
    return [mp.mpf(0)] + [total[n] / total[1] for n in range(1, pe.NMAX)]


def _identity_residual(a, c):
    """max over 2 <= n < NMAX of |a(n) log n - sum_{d|n} c(d) a(n/d)|, summed
    over every divisor including d = n, which the recursion isolates."""
    worst = mp.mpf(0)
    for n in range(2, pe.NMAX):
        rhs = sum(c[d] * a[n // d] for d in range(1, n + 1) if n % d == 0)
        worst = max(worst, abs(a[n] * mp.log(n) - rhs))
    return worst


def test_every_reported_defect_solves_the_identity_it_claims():
    """A composite defect is a statement about c; c is defined by
    a(n) log n = sum_{d|n} c(d) a(n/d). A row whose residual is nonzero is
    not a defect at all.

    Every row of results_euler.json is rebuilt from its subject, its c is
    recomputed, the identity is checked at that c, and the defect computed
    from that c must be the one reported. The planted fault is the row the
    first E7 table printed for (2, 1, 2) of d = -15: the c that the
    unguarded recursion returned there leaves the identity far from solved.
    """
    from zeta.epstein import dh_coefficient

    r = _euler()
    with mp.workdps(pe.DPS):
        subjects = [
            ([mp.mpf(0)] + [mp.mpf(1)] * (pe.NMAX - 1), r["zeta"]["composite_defect"]),
            ([mp.mpf(0)] + [dh_coefficient(n, 25) for n in range(1, pe.NMAX)],
             r["davenport_heilbronn"]["composite_defect"]),
        ]
        for row in r["epstein"]:
            d = row["discriminant"]
            for f in row["forms"]:
                subjects.append((_epstein_series(tuple(f["form"]), d), f["composite_defect"]))
            subjects.append((_class_group_sum(d), row["class_group_sum_defect"]))
        for a, reported in subjects:
            c = pe.spectrum(a)
            assert _identity_residual(a, c) < mp.mpf(10) ** -25
            assert pe.defect(c) == pytest.approx(reported, rel=1e-12, abs=1e-30)
        assert len(subjects) == 2 + 2 * 14

        # planted fault: the old route never read a(1), so on a(1) = 0 it
        # returned the c of the same series with a(1) replaced by 1
        bad = _epstein_series((2, 1, 2), -15)
        assert bad[1] == 0
        old_c = pe.spectrum([bad[0], mp.mpf(1)] + bad[2:])
        assert _identity_residual(bad, old_c) > 1


def test_the_a1_guard_fires_on_the_planted_fault():
    """(2, 1, 2) of d = -15 represents 2 and 3 but not 1: a(1) = 0, and the
    recursion must refuse it rather than return a number for it."""
    from zeta.epstein import epstein_reduced_forms

    r = _euler()
    assert r["planted_fault"]["discriminant"] == -15
    assert r["planted_fault"]["form"] == [2, 1, 2]
    assert "does not determine c" in r["planted_fault"]["refused"]
    assert (2, 1, 2) in epstein_reduced_forms(-15)
    with mp.workdps(pe.DPS):
        a = _epstein_series((2, 1, 2), -15)
        assert [n for n in range(1, 4) if a[n] != 0] == [2, 3]
        with pytest.raises(ValueError, match="does not determine c"):
            pe.spectrum(a)


def test_only_the_principal_form_represents_one():
    """41 reduced forms over the 14 discriminants of table E7: a(1) = 1 on the
    14 principal forms (1, b, c), one per discriminant, and a(1) = 0 on the
    other 27. The per-form row is the principal form."""
    from zeta.epstein import epstein_reduced_forms
    from zeta.epstein import epstein_representation_count as rep

    r = _euler()["epstein"]
    assert len(r) == 14
    total = principal = 0
    for row in r:
        forms = epstein_reduced_forms(row["discriminant"])
        assert len(forms) == row["class_number"]
        ones = [f for f in forms if rep(1, f) > 0]
        assert len(ones) == 1 and ones[0][0] == 1, row["discriminant"]
        assert [f["form"] for f in row["forms"]] == [list(ones[0])]
        assert rep(1, ones[0]) == pe.units(row["discriminant"])  # a(1) = 1 exactly
        total += len(forms)
        principal += len(ones)
    assert (total, principal, total - principal) == (41, 14, 27)


def test_docs34_table_e7_principal_form_column():
    """docs/34 table E7 after the 2026-10-10 correction: the principal-form
    defect for the nine discriminants of class number above one, and the
    band 2.96 to 5.08 the prose quotes."""
    r = {f["discriminant"]: f for f in _euler()["epstein"]}
    for d, v in E7_PRINCIPAL_FORM_DEFECT.items():
        assert r[d]["principal_form_defect"] == pytest.approx(v, abs=5e-5), d
    band = [r[d]["principal_form_defect"] for d in E7_PRINCIPAL_FORM_DEFECT]
    assert f"{min(band):.2f}" == "2.96" and min(band) == r[-95]["principal_form_defect"]
    assert f"{max(band):.2f}" == "5.08" and max(band) == r[-15]["principal_form_defect"]
    assert set(E7_PRINCIPAL_FORM_DEFECT) == {d for d in r if r[d]["class_number"] > 1}


def test_the_superseded_e7_numbers_are_composite_defects_of_one_plus_z_q():
    """The first E7 table printed the largest defect over every reduced form.
    Rebuild 1 + Z_Q(s) explicitly, a(1) set to 1, for each non-principal form,
    and the six numbers the correction keeps as "was" come back, 36.0644 from
    (2, 1, 2) at d = -15. On the three remaining discriminants of class number
    above one the old maximum was already the principal form's."""
    from zeta.epstein import epstein_reduced_forms
    from zeta.epstein import epstein_representation_count as rep

    r = {f["discriminant"]: f for f in _euler()["epstein"]}
    loudest = {}
    with mp.workdps(pe.DPS):
        for d in E7_PRINCIPAL_FORM_DEFECT:
            one_plus = {}
            for f in epstein_reduced_forms(d):
                if rep(1, f) > 0:
                    continue
                a = _epstein_series(f, d)
                assert a[1] == 0
                a[1] = mp.mpf(1)
                one_plus[f] = pe.defect(pe.spectrum(a))
            loudest[d] = max(one_plus, key=one_plus.get)
            old_max = max(one_plus[loudest[d]], r[d]["principal_form_defect"])
            if d in E7_SUPERSEDED_MAX_FORM_DEFECT:
                assert old_max == one_plus[loudest[d]], d
                assert old_max == pytest.approx(E7_SUPERSEDED_MAX_FORM_DEFECT[d], abs=5e-5), d
            else:
                assert old_max == r[d]["principal_form_defect"], d
    assert loudest[-15] == (2, 1, 2)

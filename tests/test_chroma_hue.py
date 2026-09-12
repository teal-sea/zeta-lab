"""Pins for hunt #75 (`hunts/chroma_hue/`): pitch classes against the colour wheel.

Everything here is either a derivable fact re-checked by enumeration, a
published reference value (CIEDE2000 test pairs), or a number the probes
measured. The hunt's one load-bearing claim is negative: the only structure a
note-to-hue bijection can carry is a character of Z_12, so the colour side
contributes nothing beyond "a circle". The tests keep that claim honest by
re-deriving its ingredients rather than reading them from the results files.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np
import pytest

_ROOT = Path(__file__).resolve().parents[1]
_HUNT = _ROOT / "hunts" / "chroma_hue"
if str(_HUNT) not in sys.path:
    sys.path.insert(0, str(_HUNT))

import colorspace as cs  # noqa: E402
import pc  # noqa: E402


# --- colour side: the conversions are pinned to published values ------------


@pytest.mark.parametrize("lab1,lab2,want", cs.SHARMA_PAIRS)
def test_ciede2000_matches_sharma_test_pairs(lab1, lab2, want):
    assert cs.ciede2000(lab1, lab2) == pytest.approx(want, abs=5e-4)


def test_oklab_round_trip_and_white():
    rgb = np.array([0.2, 0.6, 0.9])
    assert np.abs(cs.oklab_to_srgb(cs.srgb_to_oklab(rgb)) - rgb).max() < 1e-12
    L, a, b = cs.srgb_to_oklab([1.0, 1.0, 1.0])
    assert L == pytest.approx(1.0, abs=1e-6)
    assert abs(a) < 1e-4 and abs(b) < 1e-4


def test_srgb_red_in_cielab():
    L, a, b = cs.srgb_to_lab([1.0, 0.0, 0.0])
    assert (L, a, b) == pytest.approx((53.24, 80.09, 67.20), abs=0.01)


# --- music side: derivable facts, re-derived ---------------------------------


def test_only_affine_bijections_make_hue_distance_a_function_of_interval():
    """Backtracking over all bijections f: Z_12 -> 12-gon with
    d(f(x), f(y)) depending only on x - y. Exactly the 48 affine maps."""
    n = 12
    found, D, f, used = [], {}, [None] * n, set()

    def rec(x):
        if x == n:
            found.append(tuple(f))
            return
        for v in range(n):
            if v in used:
                continue
            ok, added = True, []
            for y in range(x):
                d = min((v - f[y]) % n, (f[y] - v) % n)
                k = (x - y) % n
                for key in (k, (-k) % n):
                    if key in D:
                        if D[key] != d:
                            ok = False
                            break
                    else:
                        D[key] = d
                        added.append(key)
                if not ok:
                    break
            if ok:
                f[x] = v
                used.add(v)
                rec(x + 1)
                used.discard(v)
                f[x] = None
            for key in added:
                D.pop(key, None)

    rec(0)
    assert len(found) == 48
    assert set(found) == set(pc.affine_maps(12))


def test_tritone_is_complementary_under_every_affine_wheel():
    for f in pc.affine_maps(12):
        D = pc.hue_distance_matrix(f)
        assert all(D[x, (x + 6) % 12] == 6 for x in range(12))


def test_injective_wheel_classes_phi_over_two_and_twelve_is_the_largest_with_two():
    classes = {n: len(pc.units(n)) // 2 for n in range(3, 37)}
    assert classes[12] == 2
    assert [n for n, c in classes.items() if c <= 2] == [3, 4, 5, 6, 8, 10, 12]


def test_dissonance_mds_is_diagonal_in_fourier_modes_and_mode_five_wins():
    """A transposition-invariant dissimilarity is circulant, so classical MDS
    is diagonalised by the DFT. For all three measures mode 5 (fifths) has the
    largest eigenvalue; mode 1 (chromatic) is negative for Sethares and the
    ordinal ranking and below 3 percent of mode 5 for Tenney height."""
    n = 12
    J = np.eye(n) - np.ones((n, n)) / n
    for name, m in pc.dissonance_measures(n).items():
        D = pc.circulant_from_ic(m, n)
        B = -0.5 * J @ (D**2) @ J
        lam = np.real(np.fft.fft(B[0]))
        # circulant check: B's eigenvectors are Fourier modes
        w = np.linalg.eigvalsh(B)
        assert np.allclose(sorted(w), sorted(np.concatenate([lam[:7], lam[1:6]])), atol=1e-9), name
        assert int(np.argmax(lam[1:7])) + 1 == 5, name
        assert lam[1] < 0.03 * lam[5], name
    seth = pc.circulant_from_ic(pc.dissonance_measures(n)["sethares"], n)
    assert np.real(np.fft.fft((-0.5 * J @ (seth**2) @ J)[0]))[1] < 0


def test_maximally_even_sets_are_the_most_saturated_chord_colours():
    """|f_5| among 7-sets is maximised only by the diatonic scale, |f_1| only
    by the chromatic cluster, |f_5| among 5-sets only by the pentatonic."""
    import itertools

    def prime_form(S):
        best = None
        for inv in (1, -1):
            for t in range(12):
                c = tuple(sorted(((inv * x + t) % 12) for x in S))
                best = c if best is None or c < best else best
        return best

    def argmax(d, k):
        best, sets = -1.0, set()
        for S in itertools.combinations(range(12), d):
            v = abs(pc.dft(S)[k])
            if v > best + 1e-9:
                best, sets = v, {prime_form(S)}
            elif abs(v - best) <= 1e-9:
                sets.add(prime_form(S))
        return sets

    assert argmax(7, 5) == {prime_form((0, 2, 4, 5, 7, 9, 11))}
    assert argmax(7, 1) == {tuple(range(7))}
    assert argmax(5, 5) == {prime_form((0, 2, 4, 7, 9))}


# --- measured numbers, read back from the probes' results files --------------


def _results(name):
    path = _HUNT / f"results_{name}.json"
    if not path.is_file():
        pytest.skip(f"{path.name} not generated")
    return json.loads(path.read_text())


def test_exhaustive_search_found_fifths_as_the_unique_argmax():
    r = _results("consonance")
    assert r["evaluated"] == 21_772_800
    fifths = tuple((7 * x) % 12 for x in range(12))
    for name, m in r["measures"].items():
        assert m["best_is_affine"], name
        assert m["best"] == pytest.approx(m["fifths"], abs=1e-9), name
        assert m["chromatic"] < 0, name
        assert m["null_max"] < m["fifths"], name
        # the argmax is the fifths wheel up to hue rotation/reflection
        best = pc.hue_distance_matrix(m["best_map"])
        assert np.array_equal(best, pc.hue_distance_matrix(fifths)), name
    s = r["measures"]["sethares"]
    assert s["fifths"] == pytest.approx(0.6093, abs=1e-3)
    assert s["chromatic"] == pytest.approx(-0.7302, abs=1e-3)
    assert r["measures"]["tenney"]["fifths"] == pytest.approx(0.7023, abs=1e-3)


def test_affine_maps_take_exactly_two_consonance_scores():
    """48 affine maps, two values: the hue side sees only chromatic-vs-fifths."""
    r = _results("consonance")
    for m in r["measures"].values():
        assert len(m["affine_distinct_scores"]) == 2


def test_the_hsl_wheel_is_not_a_perceptual_twelve_gon():
    p = _results("perceptual")
    hsl = p["hsl_wheel"]
    assert hsl["oklch_hue_step_max_over_min"] > 9.0
    assert hsl["de2000_adjacent_max_over_min"] > 8.0
    # a fixed-chroma OKLCH wheel is close to circulant but its steps still vary by half
    ok = p["oklch_fixed_chroma"]
    assert ok["non_circulant_fraction"] < 0.02
    assert 1.4 < ok["de2000_adjacent_max_over_min"] < 1.6
    assert p["oklch_max_chroma"]["max_chroma_max_over_min"] > 2.5


def test_the_visible_band_is_one_octave_but_hue_is_not_a_circle_of_frequency():
    s = _results("spectrum")
    assert s["check_equal_energy_xy"] == pytest.approx([1 / 3, 1 / 3], abs=2e-3)
    assert s["check_dominant_wavelengths_sRGB"]["R"] == pytest.approx(611, abs=3)
    assert s["check_dominant_wavelengths_sRGB"]["G"] == pytest.approx(549, abs=3)
    assert s["check_dominant_wavelengths_sRGB"]["B"] == pytest.approx(464, abs=3)
    assert 0.97 < s["visible_octaves_380_750nm"] < 1.0
    assert 260 < s["spectral_hue_range_deg"] < 290
    assert s["non_spectral_purple_arc_deg"] > 70
    assert s["hue_step_max_over_min_abs"] > 20


# --- round two: the cyclotomic ontology and the paths first skipped ---------


def _cyclotomic_data():
    import itertools

    zeta = np.exp(2j * np.pi / 12)
    rows = []
    for d in range(13):
        for S in itertools.combinations(range(12), d):
            z = pc.dft(S)
            iv = [0] * 7
            for a, b in itertools.combinations(S, 2):
                iv[pc.ic(a - b)] += 1
            rows.append((S, z, iv, sum(zeta ** (-5 * x) for x in S)))
    return rows


def test_fifths_wheel_is_the_galois_conjugate_of_the_chromatic_wheel():
    """f_5(S) = sigma_5(f_1(S)) for every subset: the two injective wheels are
    the two complex places of Q(zeta_12) and carry the same information."""
    for S, z, iv, sigma5 in _cyclotomic_data():
        assert abs(z[5] - sigma5) < 1e-9


def test_chromatic_times_fifths_saturation_is_a_rational_integer():
    """|f_1|^2 |f_5|^2 is the field norm, hence an integer, and equals
    (|S| + iv2 - iv4 - 2 iv6)^2 - 3 (iv1 - iv5)^2 in interval-vector terms."""
    seen = set()
    for S, z, iv, _ in _cyclotomic_data():
        norm = abs(z[1]) ** 2 * abs(z[5]) ** 2
        assert abs(norm - round(norm)) < 1e-7
        pred = (len(S) + iv[2] - iv[4] - 2 * iv[6]) ** 2 - 3 * (iv[1] - iv[5]) ** 2
        assert abs(norm - pred) < 1e-7
        seen.add(int(round(norm)))
    assert seen == {0, 1, 4, 9, 13, 16, 25, 36, 37, 64}


def test_units_are_common_major_triad_included():
    """84 of the 224 set classes have norm 1; the major and minor triads,
    the diminished triad and the pentatonic among them. A unit is not rare."""
    r = _results("cyclotomic")
    assert r["set_classes"] == 224
    assert r["norm_distribution_over_set_classes"]["1"] == 84
    assert r["named_chords"]["minor triad"]["norm"] == 1
    assert r["named_chords"]["pentatonic"]["norm"] == 1
    assert r["named_chords"]["augmented"]["norm"] == 0
    assert r["distinct_norms"] == 10
    assert r["distinct_interval_vectors"] == 200


def test_metamerism_counts_and_galois_redundancy():
    r = _results("round2")["metamerism"]
    assert r["subsets"] == 4096
    assert r["wheel_1"] == 1763 and r["wheel_5"] == 1763
    assert r["wheels_1_and_5_together"] == 1763  # the fifths wheel adds nothing
    assert r["full_dft_distinct"] == 4096
    assert r["wheel_6"] == 49
    assert r["largest_metamer_class_wheel_5"]["size"] == 24


def test_chroma_tracks_orbifold_radius_but_is_not_a_function_of_it():
    r = _results("round2")["orbifold"]
    for d in ("card_3", "card_4", "card_6"):
        assert r[d]["spearman_radius_vs_f1"] > 0.9
        assert not r[d]["function_of_radius"]


def test_perceptual_geometry_does_not_rescue_a_non_affine_wheel():
    """With real CIEDE2000 geometry in place of the cyclic metric, every
    rotation of an affine wheel scores the same (provably, for any distance
    matrix), and a hill climb over non-affine maps gains at most 0.02."""
    r = _results("round2")["perceptual_search"]
    for wheel in r.values():
        for m in wheel.values():
            assert m["fifths_any_rotation_max"] == pytest.approx(m["fifths_rotation_min"], abs=1e-9)
            assert m["hill_climb_best"] - m["best_affine"] < 0.02
            assert m["null_max"] < m["best_affine"]

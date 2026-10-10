"""Checks for the explicit class-number bound and the class-number search."""

from __future__ import annotations

import json
import math
import random
from fractions import Fraction
from pathlib import Path

import pytest
from flint import arb, ctx

from hunts.qrh_class_number import classno, explicit as ex, lbound as lb

HERE = Path(__file__).resolve().parent


def _load(name):
    return json.loads((HERE / name).read_text())


# ------------------------------------------------------------ constants


def test_meissel_mertens_encloses_the_published_value():
    B = lb.meissel_mertens()
    ref = arb('0.26149721284764278375542683860869585905156664826120')
    assert B.overlaps(ref)
    assert B.rad() < arb('1e-30')


def test_prime_sum_P_matches_direct_sum():
    # sum_p log p/(p^3 + 1) by direct summation; tail beyond 10^4 < 2e-8
    with ctx.workprec(100):
        direct = sum(arb(int(p)).log() / (arb(int(p)) ** 3 + 1)
                     for p in lb.primes_upto(10**4))
        val = lb.P_sum(arb(3))
        assert abs(float((val - direct).mid())) < 2e-8
        assert float((val - direct).mid()) > 0          # the tail is positive


def test_rosser_schoenfeld_upper_bound_on_exact_range():
    # S(t) < log log t + B + 1/(2 log^2 t) at every prime 286 < p <= 10^6
    tab = lb.tables()
    B = float(lb.meissel_mertens().mid())
    S = 0.0
    worst = 1.0
    for p in tab.p[tab.p <= 10**6].tolist():
        S += 1.0 / p
        if p > 286:
            lt = math.log(p)
            worst = min(worst, math.log(lt) + B + 1 / (2 * lt * lt) - S)
    assert worst > 0


# --------------------------------------------------------- the bound


def test_dtable_row_recomputes():
    dt = _load('dtable.json')
    row = dt['intervals'][len(dt['intervals']) // 2]
    params = (Fraction(row['a']), Fraction(row['b']), Fraction(row['dx']), Fraction(row['dy']))
    again = ex.interval_bound(row['q_lo'], row['q_hi'], params)
    assert again['h_lower'] == pytest.approx(row['h_lower'], rel=1e-12)
    assert again['h_lower'] > 0


def test_dtable_is_consistent_and_covers_the_search():
    dt = _load('dtable.json')
    rows = dt['intervals']
    for r0, r1 in zip(rows, rows[1:]):
        assert r0['q_hi'] == r1['q_lo']
    D = [r['D_bound'] for r in dt['D_bound']]
    assert D == sorted(D)
    for H in (100, 1000, 1500):
        s = _load(f'search_H{H}.json')
        assert s['X'] >= D[H - 1]
        assert s['max_absD_overall'] <= D[H - 1]
        assert s['stats']['found'] == s['found']


def test_bound_below_exact_L_with_margin():
    c = _load('controls_exact_l.json')
    assert c['fundamental_checked'] > 900000
    assert c['worst_margin']['margin'] > 1
    assert c['max_rel_diff_pari'] < 1e-12


def test_a_planted_inflation_is_caught():
    """The exact-L control has teeth: inflating the bound by the observed
    worst margin times 1.01 produces a violation."""
    c = _load('controls_exact_l.json')
    w = c['worst_margin']
    assert w['L_lower_bound'] * w['margin'] * 1.01 > w['L_exact']


def test_weakened_abscissa_weakens_the_bound():
    rows = _load('abscissae.json')
    by = {}
    for r in rows:
        by.setdefault(r['q_hi'], {})[r['sigma0']] = r['L_lower']
    for q, d in by.items():
        assert d['1/2'] > d['7/8'] > d['11/12'] > d['15/16'] > 0


def test_theorem_a_tail_recomputes():
    t = _load('theorem_a.json')
    tl = t['tail']
    again = ex.tail_constant(t['Q1'], Fraction(tl['lambda']), Fraction(tl['eta']),
                             Fraction(tl['dx']), Fraction(tl['dy']))
    assert again['c_lower'] == pytest.approx(tl['c_lower'], rel=1e-12)
    assert again['c_lower'] >= 0.1
    assert t['min_L_loglogq_on_cover_after_start'] >= 0.1


# ------------------------------------------------- class numbers


def test_cn_matches_brute_force_and_pari(tmp_path):
    res = classno.run(3, 4000, 20000, tmp_path / 'a.txt')
    got = dict(res['rows'])
    fund = [n for n in range(3, 4001) if classno.is_fundamental_negative(n)]
    assert sorted(got) == fund
    for n in fund:
        assert got[n] == classno.reference_h(n)
    rng = random.Random(1)
    res = classno.run(10**6, 10**6 + 3000, 20000, tmp_path / 'b.txt')
    for n, h in rng.sample(res['rows'], 60):
        assert h == classno.pari_h(n)


def test_filter_agrees_with_full_count(tmp_path):
    full = classno.run(3, 300000, 20000, tmp_path / 'full.txt')['rows']
    for H in (7, 60):
        filt = classno.run(3, 300000, H, tmp_path / f'f{H}.txt')['rows']
        assert sorted(filt) == sorted((n, h) for n, h in full if h <= H)


def test_fast_and_slow_exact_counts_agree(tmp_path, monkeypatch):
    monkeypatch.setenv('CN_CHECK', '1')
    res = classno.run(40000000, 40030000, 1000, tmp_path / 'c.txt')
    assert res['stats']['exact'] > 300


@pytest.mark.parametrize('H', [100, 1000, 1500])
def test_watkins_counts_reproduced(H):
    s = _load(f'search_H{H}.json')
    w = _load('watkins.json')
    for h in range(1, 101):
        assert s['count_by_h'][str(h)] == w['count_by_h'][str(h)]
        assert s['max_squarefree_k_by_h'][str(h)] == w['max_squarefree_k_by_h'][str(h)]


def test_odd_counts_match_holmin_kurlberg():
    s = _load('search_H1500.json')
    hk = _load('holmin_kurlberg_odd.json')['count_by_odd_h']
    for h in range(1, 1501, 2):
        assert s['count_by_h'][str(h)] == hk[str(h)]
    assert all(s['count_by_h'][str(h)] > 0 for h in range(1, 1501))
    assert s['found'] == 9245562 and s['max_absD_overall'] == 562394347


def test_runs_agree_on_their_common_sub_lists():
    s100, s1000 = _load('search_H100.json'), _load('search_H1000.json')
    p = _load('controls_pari_H1500.json')
    assert p['mismatches'] == [] and p['checked'] >= 1900
    assert p['sha256_sublist_h_le']['1000'] == s1000['sha256_sorted_list']
    assert p['sha256_sublist_h_le']['100'] == s100['sha256_sorted_list']
    s1500 = _load('search_H1500.json')
    for h in range(1, 1001):
        assert s1500['count_by_h'][str(h)] == s1000['count_by_h'][str(h)]


def test_streamed_counts_recompute(tmp_path, monkeypatch):
    """The filter can only lose a field by over-counting: recompute every
    streamed count with Jacobi symbols and no periodic patterns."""
    monkeypatch.setenv('CN_CHECK_STREAM', '1')
    for lo, hi, H in [(100000, 160000, 100), (300000000, 300006000, 1000),
                      (1000000000, 1000006000, 1500), (2000000000, 2000006000, 1000)]:
        res = classno.run(lo, hi, H, tmp_path / f's{lo}.txt')
        assert res['stats']['stream_checked'] == res['stats']['fundamental'] > 1000


def test_eleven_twelfths_variant():
    e = _load('eleven_twelfths.json')
    assert e['tail']['c_lower'] >= 1 / 16
    assert e['theorem_a_cover_min'] >= 1 / 16
    assert e['D_bound']['1000'] <= _load('search_H1500.json')['X']


def test_theorem_a_small_range_from_exact_values():
    c = _load('controls_exact_l.json')['theorem_a_small_range']
    assert c['D0'] == 4
    assert c['min_L_loglogq_from_D0'] >= 0.1

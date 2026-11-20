"""Checks for the GRH cutoff table D_GRH(h) and the H = 5000 class-number search."""

from __future__ import annotations

import json
import math
import subprocess
from fractions import Fraction
from pathlib import Path

import pytest
from flint import arb, ctx

from hunts.grh_class_number import bounds, controls, search
from hunts.qrh_class_number import classno, explicit as ex, lbound as lb

HERE = Path(__file__).resolve().parent
SIBLING = HERE.parent / 'qrh_class_number'
H = 5000


def _load(name, where=HERE):
    return json.loads((where / name).read_text())


def _cnx(tmp_path, H, plan_lines, env=None):
    """Run cnx on plan lines (lo, hi, mode, A0, name); return rows and stats per name."""
    import os
    search.build()
    plan = tmp_path / 'plan'
    plan.write_text(''.join(f'{lo} {hi} {mode} {a0} {tmp_path / name}\n'
                            for lo, hi, mode, a0, name in plan_lines))
    e = dict(os.environ)
    e.update(env or {})
    subprocess.run([str(search.BIN), str(H), str(plan)], check=True, env=e,
                   stdout=subprocess.DEVNULL)
    out = {}
    for lo, hi, mode, a0, name in plan_lines:
        rows = [tuple(map(int, line.split())) for line in (tmp_path / name).read_text().splitlines()]
        out[name] = (rows, search.read_stats(tmp_path / name)[0])
    return out


def _cn(tmp_path, lo, hi, H, name):
    """The sibling's cn.c, compiled here (its own build directory is not touched)."""
    binary = search.BUILD / 'cn'
    src = SIBLING / 'cn.c'
    search.BUILD.mkdir(exist_ok=True)
    if not binary.exists() or binary.stat().st_mtime < src.stat().st_mtime:
        subprocess.run(['gcc', '-O3', '-march=native', '-o', str(binary), str(src), '-lm'], check=True)
    subprocess.run([str(binary), str(lo), str(hi), str(H), str(tmp_path / name)], check=True)
    return sorted(classno.parse(tmp_path / name)['rows'])


# ------------------------------------------------------------- the bound


def test_cover_has_no_gaps_and_the_table_follows_from_it():
    dt = _load('dtable_grh.json')
    assert dt['sigma0'] == '1/2'
    cells, bridge = dt['intervals'], dt['bridge_intervals']
    bounds.assert_adjacent(cells, 10**2, 10**11)
    bounds.assert_adjacent(bridge, 10**11, 10**50)
    with pytest.raises(AssertionError):                    # the assertion has teeth
        bounds.assert_adjacent(cells[:5] + cells[6:])
    D = dt['D_bound']
    assert len(D) == dt['h_tab'] == 10000 and D == sorted(D)
    hl = [c['h_lower'] for c in cells]
    assert hl == sorted(hl)                                # monotone, so D(h) is a single threshold
    for h in (1, 2, 3, 10, 100, 1000, 1500, 2000, 5000, 9999, 10000):
        last = max(c['q_hi'] for c in cells if c['h_lower'] <= h)
        assert D[h - 1] == last
    assert D[0] == 399 and D[99] == 5554909 and D[1499] == 1432212849 and D[4999] == 16396235837
    # beyond the fine cover: every bridge cell and the tail exclude h <= 10000
    assert cells[-1]['h_lower'] > 10000
    assert min(c['h_lower'] for c in bridge) == dt['beyond_cover']['bridge_min_h_lower'] > 10000
    assert dt['beyond_cover']['tail_h_lower_at_Q1'] > 10**20


@pytest.mark.parametrize('pick', ['middle', 'cutoff_5000', 'first', 'last'])
def test_cells_recompute_in_arb(pick):
    dt = _load('dtable_grh.json')
    cells = dt['intervals']
    c = {'middle': cells[len(cells) // 2], 'first': cells[0], 'last': cells[-1],
         'cutoff_5000': next(c for c in cells if c['q_hi'] == dt['D_bound'][4999])}[pick]
    again = ex.interval_bound(c['q_lo'], c['q_hi'], controls.cell_params(c), sigma0='1/2')
    assert again['h_lower'] == pytest.approx(c['h_lower'], rel=1e-12)
    assert again['L_lower'] == pytest.approx(c['L_lower'], rel=1e-12)
    if pick == 'cutoff_5000':
        nxt = cells[cells.index(c) + 1]
        assert c['h_lower'] <= 5000 < nxt['h_lower']


def test_the_bound_is_monotone_in_sigma0():
    lad = _load('controls_ladder.json')
    assert lad['cells_compared'] == 2041
    assert lad['min_ratio_L_half_over_L_seven_eighths'] > 2.5
    # one point again, at identical parameters
    p = lad['same_parameter_points'][20]
    cells = _load('dtable_grh.json')['intervals']
    c = controls.cell_of(cells, p['q'])
    src = c if p['params_from'] == '1/2' else controls.cell_of(_load('dtable.json', SIBLING)['intervals'], p['q'])
    params = controls.cell_params(src)
    with ctx.workprec(lb.PREC):
        vals = [lb.log_L1_lower(p['q'], *params, sigma0=s) for s in ('1/2', '3/4', '7/8')]
        assert vals[0] > vals[1] > vals[2]
        assert ex._lower(vals[0]) == pytest.approx(p['logL_half'], rel=1e-12)


def test_arb_value_agrees_with_a_second_route():
    """mpmath quadrature and a direct prime sum against the Arb tables and
    upper Riemann sums: same M, and R above the true integral by the grid
    loss only."""
    c = _load('controls_independent.json')
    assert c['max_abs_M_difference'] < 1e-14
    assert 1 < c['min_R_ratio'] <= c['max_R_ratio'] < 1.001
    assert 0 < c['min_logL_gap'] <= c['max_logL_gap'] < 3e-4
    cell = controls.cell_of(_load('dtable_grh.json')['intervals'], 163)
    prm = controls.cell_params(cell)
    M, Rx, Ry, T = controls.independent_bound(cell['q_hi'], *prm)
    with ctx.workprec(lb.PREC):
        d = lb.log_L1_lower(cell['q_hi'], *prm, sigma0='1/2', detail=True)
        assert float(d['M'].mid()) == pytest.approx(M, abs=1e-14)
        assert 1 < float(d['Rx'].mid()) / Rx < 1.001 and 1 < float(d['Ry'].mid()) / Ry < 1.001
        second = M - (Rx + Ry + T) / float(prm[1] - prm[0])
        assert 0 < second - float(d['logL'].mid()) < 3e-4


def test_theorem_a_tail_and_cover():
    t = _load('theorem_a_grh.json')
    tl = t['tail']
    again = ex.tail_constant(t['Q1'], Fraction(tl['lambda']), Fraction(tl['eta']),
                             Fraction(tl['dx']), Fraction(tl['dy']), sigma0='1/2')
    assert again['c_lower'] == pytest.approx(tl['c_lower'], rel=1e-12)
    assert again['c_lower'] >= 0.3857 > 1 / 3
    with ctx.workprec(lb.PREC):                             # Rosser-Schoenfeld needs e^a >= 286
        assert arb(tl['a1']) > arb(286).log()
    assert t['min_L_loglogq_on_cover_after_start'] >= 1 / 3
    assert t['q_start_cover'] == 22786
    bounds.assert_adjacent(t['intervals'], 10**2, 10**50)
    small = _load('theorem_a_small.json')
    assert small['range'][1] >= t['q_start_cover']          # the exact range reaches the cover
    assert small['discriminants_with_L_loglog_below_one_third'] == [3, 4]
    assert small['min_L_loglog_from_7'] > 0.4 and small['attained_at_absD'] == 163
    assert small['equal_to_sibling_full_list']


def test_lls_comparison_is_explained_not_assumed():
    c = _load('controls_lls.json')
    assert c['this_hunt_stronger_on_every_cell']
    assert 1 < c['min_ratio'] < 1.06                        # the two bounds share Littlewood's limit
    assert c['samples'][-1]['q_hi'] == 10**100 and c['samples'][-1]['ratio'] < 1.02
    # LLS, Corollary 1.3: "on GRH h(-q) >= 9053 when q >= 10^11"
    assert math.ceil(c['lls_h_at_1e11']) == 9053
    # the gap sits in the zero term, and the zero term is checked against real zeros
    z = _load('controls_zero_term.json')
    assert z['max_Z_over_R'] < 1
    assert z['max_abs_identity_defect'] < 1e-4
    assert z['min_prime_sum_minus_M'] > 0


def test_zero_term_control_recomputes_at_minus_163():
    r = controls.zero_term_one(-163, 60.0)
    assert r['h'] == 1 and r['zeros_used'] > 50
    assert abs(r['identity_defect']) < 3 * r['identity_tail_estimate'] < 0.01
    assert 0 < r['Z_x_over_R_x'] < 1 and 0 < r['Z_y_over_R_y'] < 1
    assert r['prime_sum_minus_M'] > 0
    assert abs(r['E_actual']) < r['E_bound']
    assert 1 < r['L_exact_over_bound'] < 1.6


def test_bound_below_exact_L_for_every_listed_field():
    c = _load('controls_exact_l.json')
    s = _load(f'search_H{H}.json')
    assert c['listed_fields_checked'] > 10**8
    assert c['worst_margin']['margin'] > 1
    assert sum(c['margin_histogram_bins_of_0.05_from_1']) == c['listed_fields_checked']
    assert c['all_discriminants_range'][1] > 0.98 * s['X']


def test_a_planted_sign_fault_turns_the_control_red():
    """The zero term with the wrong sign: exp(M + E).  The exact L(1, chi_D)
    of a listed field must then fall below the 'bound'."""
    f = _load('controls_fault.json')
    assert f['control_goes_red'] and f['violations_with_fault'] > 0
    assert f['violations_without_fault'] == 0
    w = f['clearest_violation']
    cells = _load('dtable_grh.json')['intervals']
    c = controls.cell_of(cells, w['absD'])
    L = math.pi * w['h'] / math.sqrt(w['absD'])
    assert classno.pari_h(w['absD']) == w['h']
    good = math.exp(controls.faulty_log_L(c['q_hi'], controls.cell_params(c), 'none'))
    bad = math.exp(controls.faulty_log_L(c['q_hi'], controls.cell_params(c), 'zero_sign'))
    assert good < L < bad                                   # green without the fault, red with it


# ------------------------------------------------------ class numbers


def test_cnx_matches_brute_force(tmp_path):
    res = _cnx(tmp_path, 20000, [(3, 6000, 1, 0, 'a.txt')])['a.txt']
    got = dict(res[0])
    fund = [n for n in range(3, 6001) if classno.is_fundamental_negative(n)]
    assert sorted(got) == fund == [n for n, _ in res[0]]
    for n in fund:
        assert got[n] == classno.reference_h(n)
    assert res[1]['fundamental'] == res[1]['found'] == len(fund)


def test_full_and_filter_modes_agree_with_cn(tmp_path):
    ref = _cn(tmp_path, 3, 400000, 60, 'cn.txt')
    res = _cnx(tmp_path, 60, [(3, 400000, 1, 0, 'full.txt'), (3, 400000, 0, 30, 'filt.txt'),
                              (3, 400000, 0, 1, 'primes.txt')])
    for name in ('full.txt', 'filt.txt', 'primes.txt'):
        assert res[name][0] == ref, name
    ref = _cn(tmp_path, 3 * 10**9, 3 * 10**9 + 60000, H, 'cn2.txt')
    res = _cnx(tmp_path, H, [(3 * 10**9, 3 * 10**9 + 60000, 1, 0, 'full2.txt'),
                             (3 * 10**9, 3 * 10**9 + 60000, 0, 100000, 'filt2.txt')])
    assert res['full2.txt'][0] == res['filt2.txt'][0] == ref and len(ref) > 10


def test_enumerated_class_numbers_recompute(tmp_path):
    """Mode 1 against the sibling's exact_h on every fundamental discriminant."""
    res = _cnx(tmp_path, H, [(3, 200000, 1, 0, 'a.txt'), (10**9, 10**9 + 20000, 1, 0, 'b.txt'),
                             (2999990000, 3 * 10**9, 1, 0, 'c.txt')], env={'CNX_CHECK_FULL': '1'})
    for name in ('a.txt', 'b.txt', 'c.txt'):
        st = res[name][1]
        assert st['checked_full'] == st['fundamental'] > 3000


def test_streamed_counts_recompute(tmp_path):
    """The filter can only lose a field by over-counting: recompute sampled
    streamed counts with Jacobi symbols and no periodic patterns."""
    res = _cnx(tmp_path, H, [(4 * 10**9, 4 * 10**9 + 150000, 0, 28000, 'a.txt'),
                             (16 * 10**9, 16 * 10**9 + 150000, 0, 1, 'b.txt')],
               env={'CNX_CHECK_STREAM': '97'})
    for name in ('a.txt', 'b.txt'):
        assert res[name][1]['checked_stream'] > 400


def test_search_summary_invariants():
    s = _load(f'search_H{H}.json')
    D = _load('dtable_grh.json')['D_bound']
    assert s['H'] == H and s['X'] == D[H - 1] == 16396235837
    assert s['found'] == sum(s['count_by_h'].values()) == s['stats']['found']
    assert s['max_absD_overall'] <= s['X']
    assert all(s['count_by_h'][str(h)] > 0 for h in range(1, H + 1))
    for h in range(1, H + 1):                               # no field beyond its own cutoff
        assert s['max_absD_by_h'][str(h)] <= D[h - 1]
    cs = search.chunks(s['X'])
    assert len(cs) == s['chunks'] and cs[0][0] == 3 and cs[-1][1] == s['X']
    assert all(c0[1] + 1 == c1[0] for c0, c1 in zip(cs, cs[1:]))
    cum = 0
    for k in range(100, H + 1, 100):
        cum += sum(s['count_by_h'][str(h)] for h in range(k - 99, k + 1))
        assert s['cumulative_by_hundreds'][str(k)][0] == cum


def test_lists_agree_with_every_published_table():
    c = _load('crosschecks.json')
    assert c['all_agree'] and c['every_h_occurs']
    s = _load(f'search_H{H}.json')
    sib = _load('search_H1500.json', SIBLING)
    assert s['sha256_sublist_h_le']['1500'] == sib['sha256_sorted_list']
    for h in range(1, 1501):
        assert s['count_by_h'][str(h)] == sib['count_by_h'][str(h)]
        assert s['max_absD_by_h'][str(h)] == sib['max_absD_by_h'][str(h)]
    w = _load('watkins.json', SIBLING)
    for h in range(1, 101):
        assert s['count_by_h'][str(h)] == w['count_by_h'][str(h)]
        assert s['max_squarefree_k_by_h'][str(h)] == w['max_squarefree_k_by_h'][str(h)]
    hk = _load('holmin_kurlberg_odd_5000.json')['count_by_odd_h']
    assert len(hk) == 2500
    for h in range(1, H + 1, 2):
        assert s['count_by_h'][str(h)] == hk[str(h)]
    for k, (cnt, mx) in controls.GGLM_TABLE1.items():
        assert s['cumulative_by_hundreds'][str(k)] == [cnt, mx]


def test_a_planted_miscount_is_caught_by_the_cross_checks():
    s = _load(f'search_H{H}.json')
    hk = _load('holmin_kurlberg_odd_5000.json')['count_by_odd_h']
    lost = dict(s['count_by_h'])
    lost['4999'] -= 1                                       # one field dropped
    assert any(lost[str(h)] != hk[str(h)] for h in range(1, H + 1, 2))


def test_pari_agrees():
    p = _load('controls_pari.json')
    assert p['largest_absD_of_every_h'] == {'checked': H, 'mismatches': []}
    assert p['random_entries']['mismatches'] == [] and p['random_entries']['checked'] >= 400
    assert p['windows_inside_range']['mismatches'] == []
    assert p['windows_inside_range']['fundamental_checked'] > 10000
    for h, row in p['windows_above_D_GRH'].items():
        assert row['violations'] == 0 and row['smallest_class_number'] > int(h)

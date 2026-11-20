"""Checks for the GRH cutoff table D_GRH(h) and the H = 5000 class-number search."""

from __future__ import annotations

import json
import math
import subprocess
from fractions import Fraction
from pathlib import Path

import pytest
from flint import arb, ctx

from hunts.grh_class_number import bounds, controls, lls_route, search, sweep
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


def test_the_cover_is_valid_but_stalled_below_log_49():
    """Review finding: the cover warm-starts every cell from the previous
    optimum and stays with y below 49 from q = 2.99 * 10^7 to 4 967 973 832.
    A restart at a = 3.9 on the cell at 10^9 gives a larger Arb-enclosed
    bound; the committed table stays valid (each cell's value is a true
    lower bound) and is that much weaker there."""
    cells = _load('dtable_grh.json')['intervals']
    low = [c for c in cells if Fraction(c['a']) < Fraction(3892, 1000) and c['q_hi'] > 3 * 10**7]
    assert len(low) == 514 and low[0]['q_lo'] == 29853308 and low[-1]['q_hi'] == 4967973832
    c = next(c for c in cells if c['q_lo'] == 991098295)
    assert c['a'] == '177/50' and c['b'] == '187/25'
    again = ex.interval_bound(c['q_lo'], c['q_hi'],
                              (Fraction(39, 10), Fraction(751, 100), Fraction(c['dx']), Fraction(c['dy'])),
                              sigma0='1/2')
    assert again['logL_lower'] - c['logL_lower'] == pytest.approx(0.005739, abs=2e-6)
    assert again['L_lower'] == pytest.approx(0.126172, abs=1e-6)
    # L_lower is not monotone: one jump up, and 76 cells beaten by a later one
    L = [x['L_lower'] for x in cells]
    ups = [i for i in range(1, len(L)) if L[i] > L[i - 1]]
    assert [cells[i]['q_lo'] for i in ups] == [4967973832]
    later = [max(L[i + 1:], default=0) for i in range(len(L))]
    assert sum(1 for i in range(len(L)) if later[i] > L[i]) == 76
    # and h_lower, which the table reads, is nondecreasing all the same
    hl = [x['h_lower'] for x in cells]
    assert hl == sorted(hl)


def test_cell_ratios_as_stated():
    dt = _load('dtable_grh.json')
    assert 1.0198 < max(c['q_hi'] / c['q_lo'] for c in dt['intervals']) < 1.0199
    assert max(math.log(c['q_hi']) / math.log(c['q_lo']) for c in dt['bridge_intervals']) < 1.02 + 1e-9
    t = _load('theorem_a_grh.json')['intervals']
    assert 1.0212 < max(math.log(c['q_hi']) / math.log(c['q_lo']) for c in t) < 1.0213
    fail = [c for c in t if c['L_loglogq_lower'] < 1 / 3]
    assert len(t) == 163 and len(fail) == 39 and fail[-1]['q_hi'] == 22786
    assert all(c['q_lo'] >= 22786 for c in t if c not in fail)


def test_rosser_schoenfeld_form_used_by_the_tail():
    """S(t) < log log t + B + 1/(2 log^2 t) for t >= 286, checked at every
    prime to 3 * 10^6 (the right side increases between primes, so primes
    suffice); it fails at 283.  Float grade: a measurement of the cited
    inequality, not a proof of it."""
    import numpy as np
    N = 3 * 10**6
    s = np.ones(N + 1, bool)
    s[:2] = False
    for i in range(2, int(N**0.5) + 1):
        if s[i]:
            s[i * i::i] = False
    p = np.nonzero(s)[0]
    S = np.cumsum(1.0 / p)
    lt = np.log(p.astype(float))
    margin = np.log(lt) + 0.2614972128476428 + 1 / (2 * lt**2) - S
    assert margin[p >= 286].min() > 0.0011
    assert margin[p == 283][0] < 0


def test_the_lls_route_door_is_measured_not_adopted():
    """First door: the LLS route evaluated numerically at q = 10^10 beats
    Theorem B's cell there by about 11% in L.  Float grade, not used."""
    v = math.exp(lls_route.log_L_lower(1e10, 1374.0, 240.0))
    cell = controls.cell_of(_load('dtable_grh.json')['intervals'], 10**10)
    assert v == pytest.approx(0.13671, abs=2e-5)
    assert 1.10 < v / cell['L_lower'] < 1.11


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


def test_control_a_cannot_see_a_fault_below_its_floor():
    """Control (a) is blind to any error that raises the bound by less than
    the factor 1.449 in L (2.1 in D): dropping the zero term altogether, or
    halving it, stays green.  The size of the zero term is checked only by the
    seven-character zero-term control and by the written proof."""
    f = _load('controls_fault.json')
    assert 1.449 < f['detection_floor_in_L'] < 1.4492
    assert 2.10 < f['detection_floor_in_D'] < 2.11
    o = f['other_plants']
    assert not o['zero_dropped']['caught'] and 1.12 < o['zero_dropped']['min_ratio'] < 1.121
    assert not o['zero_half']['caught'] and 1.28 < o['zero_half']['min_ratio'] < 1.282
    assert o['none']['violations'] == 0
    assert o['none']['min_ratio'] == pytest.approx(f['detection_floor_in_L'], rel=1e-9)


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


def _published_table_mismatches(counts, cumulative):
    """Every comparison with a published table that a per-h count can fail."""
    sib = _load('search_H1500.json', SIBLING)
    w = _load('watkins.json', SIBLING)
    hk = _load('holmin_kurlberg_odd_5000.json')['count_by_odd_h']
    bad = [('sibling', h) for h in range(1, 1501) if counts[str(h)] != sib['count_by_h'][str(h)]]
    bad += [('watkins', h) for h in range(1, 101) if counts[str(h)] != w['count_by_h'][str(h)]]
    bad += [('holmin_kurlberg', h) for h in range(1, H + 1, 2) if counts[str(h)] != hk[str(h)]]
    bad += [('gglm', k) for k, (c, _) in controls.GGLM_TABLE1.items() if cumulative(counts, k) != c]
    return bad


def _cumulative(counts, k):
    return sum(counts[str(h)] for h in range(1, k + 1))


def test_an_odd_h_drop_is_caught_by_the_published_tables():
    """Plant: one field with odd h = 4999 dropped.  Holmin-Kurlberg sees it."""
    s = _load(f'search_H{H}.json')
    assert _published_table_mismatches(s['count_by_h'], _cumulative) == []
    lost = dict(s['count_by_h'])
    lost['4999'] -= 1
    assert _published_table_mismatches(lost, _cumulative) == [('holmin_kurlberg', 4999)]


@pytest.mark.parametrize('h_even', [2002, 3000, 4998])
def test_an_even_h_drop_above_2000_escapes_every_published_table(h_even):
    """Plant: one field with even h in (2000, 5000] dropped.  No published
    table can see it (none exists for those h); only the full-range sweep of
    controls_sweep.json and the field-level PARI checks can.  This test pins
    the blindness, so that nobody reads the table comparisons as covering it."""
    s = _load(f'search_H{H}.json')
    lost = dict(s['count_by_h'])
    lost[str(h_even)] -= 1
    assert _published_table_mismatches(lost, _cumulative) == []


def test_the_sweep_catches_an_even_h_drop_but_not_a_small_shift(tmp_path):
    """The independent sweep (lsieve.c Euler products plus PARI) on a window
    at 1.5 * 10^9, against cnx's list there.  Clean: nothing flagged.  Plant
    1, one field with even h > 2000 dropped: reported missing.  Plant 2, a
    listed class number moved by 2 (inside the 2.5% tolerance): NOT caught,
    which is the sweep's documented blind spot (the field-level PARI checks
    cover it only on samples)."""
    lo, hi = 1_500_000_000, 1_500_200_000
    rows = _cnx(tmp_path, H, [(lo, hi, 1, 0, 'w.txt')])['w.txt'][0]
    Ln = [n for n, _ in rows]
    Lh = [h for _, h in rows]
    import numpy as np
    Ln, Lh = np.array(Ln, dtype=np.int64), np.array(Lh, dtype=np.int64)
    clean = sweep.sweep_window(lo, hi, Ln, Lh, 20000, 0.025, tmp_path / 'c.bin')
    assert clean['MISSING'] == [] and clean['WRONG'] == [] and clean['listed'] > 200
    k = next(i for i in range(len(Lh)) if Lh[i] > 2000 and Lh[i] % 2 == 0)
    keep = np.arange(len(Ln)) != k
    dropped = sweep.sweep_window(lo, hi, Ln[keep], Lh[keep], 20000, 0.025, tmp_path / 'd.bin')
    assert dropped['MISSING'] == [(int(Ln[k]), int(Lh[k]))]
    shifted = Lh.copy()
    shifted[k] += 2
    blind = sweep.sweep_window(lo, hi, Ln, shifted, 20000, 0.025, tmp_path / 's.bin')
    assert blind['MISSING'] == [] and blind['WRONG'] == []


def test_the_full_range_sweep_record():
    """The reviewer's full-range sweep and the repair's rerun of part of it."""
    c = _load('controls_sweep.json')
    z = c['reviewer_run']['zones']
    assert z['fullzone']['lo'] == 3 and z['fullzone']['hi'] + 1 == z['fullzone_b']['lo']
    assert z['fullzone_b']['hi'] + 1 == z['filterzone']['lo'] and z['filterzone']['hi'] == 16396235837
    for zone in z.values():
        assert zone['missing'] == 0 and zone['wrong'] == 0 and zone['min_h_unlisted'] > H
        ch = zone['chunks']
        assert all(a['hi'] + 1 == b['lo'] for a, b in zip(ch, ch[1:]))
    s = _load(f'search_H{H}.json')
    assert sum(zone['listed'] for zone in z.values()) == s['found']
    assert sum(zone['fundamental'] for zone in z.values()) == s['stats']['fundamental']
    assert c['reviewer_run']['above_X_against_D_GRH_table']['violations'] == 0
    assert c['missing_total'] == 0 and c['wrong_total'] == 0
    for tag, r in c['rerun_reproduces_reviewer'].items():
        assert r['rows'] > 0 and r['identical_rows'] == r['rows'], tag


def test_the_list_equals_molteni_per_field_file_for_h_le_2000():
    m = _load('controls_molteni.json')
    assert m['sha256_matches_record'] and m['lines'] == 2000
    assert m['h_with_different_sets'] == []
    assert m['fields_in_file'] == m['fields_in_list_h_le_2000'] == 16453493
    assert controls.GGLM_TABLE1[2000] == (16453493, 1062350083)


def test_pari_agrees():
    p = _load('controls_pari.json')
    assert p['largest_absD_of_every_h'] == {'checked': H, 'mismatches': []}
    assert p['random_entries']['mismatches'] == [] and p['random_entries']['checked'] >= 400
    assert p['windows_inside_range']['mismatches'] == []
    assert p['windows_inside_range']['fundamental_checked'] > 10000
    for h, row in p['windows_above_D_GRH'].items():
        assert row['violations'] == 0 and row['smallest_class_number'] > int(h)

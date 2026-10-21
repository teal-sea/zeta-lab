"""Bounded block residual-energy experiment, with all cross terms retained."""
from __future__ import annotations

import argparse
from fractions import Fraction
import json
from pathlib import Path
import sys
from time import perf_counter

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from flint import arb, arb_mat, ctx
from mpmath import mp
from hunts.rogue_frontier.nyman_beurling.vasyunin import (
    GramBuilder, dot, gram_entry_mp, gram_entry_quad,
)
from hunts.mobius_orbits.probe import mobius_sieve


def block(A, r0, r1, c0, c1):
    return arb_mat([[A[r, c] for c in range(c0, c1)] for r in range(r0, r1)])


def record(x):
    return {'ball': x.str(35), 'mid': float(x.mid()), 'radius': float(x.rad())}


def one_case(full_G, full_b, N, mu):
    G = block(full_G, 0, N, 0, N)
    C = block(full_G, 0, N, N, 2 * N)
    D = block(full_G, N, 2 * N, N, 2 * N)
    b = block(full_b, 0, N, 0, 1)
    d = block(full_b, N, 2 * N, 0, 1)
    joint_G = block(full_G, 0, 2 * N, 0, 2 * N)
    joint_b = block(full_b, 0, 2 * N, 0, 1)
    a = G.solve(b)
    H = G.solve(C)
    S = D - C.transpose() * H
    u = d - C.transpose() * a
    E_old = 1 - dot(b, a)
    gain_opt = dot(u, S.solve(u))
    E_new = 1 - dot(joint_b, joint_G.solve(joint_b))
    assert E_old > 0 and E_new > 0 and gain_opt > 0
    assert (E_old - gain_opt - E_new).contains(0)
    # This arithmetic shell is fixed in MISSION.md before the experiment.
    v = arb_mat(N, 1, [-int(mu[k]) * (arb(2 * N) / k).log() for k in range(N + 1, 2 * N + 1)])
    numerator = dot(v, u)
    denominator = dot(v, S * v)
    assert denominator > 0
    alpha = numerator / denominator
    gain = numerator * numerator / denominator
    assert gain > 0 and (gain_opt - gain) > 0
    correction = H * v
    z = arb_mat(2 * N, 1, [a[j, 0] - alpha * correction[j, 0] for j in range(N)] +
                [alpha * v[j, 0] for j in range(N)])
    residual = 1 - 2 * dot(joint_b, z) + dot(z, joint_G * z)
    assert (residual - (E_old - gain)).contains(0)
    assert residual < E_old
    wrong = arb_mat(2 * N, 1, [a[j, 0] + alpha * correction[j, 0] for j in range(N)] +
                    [-alpha * v[j, 0] for j in range(N)])
    wrong_energy = 1 - 2 * dot(joint_b, wrong) + dot(wrong, joint_G * wrong)
    assert (wrong_energy - (E_old + 3 * gain)).contains(0)
    assert wrong_energy > E_old
    # Removing cross-block geometry must not pass as the exact optimum.
    omitted_cross = E_old - dot(u, D.solve(u))
    assert not (omitted_cross - E_new).contains(0)
    # Review addition: a residual-matched fallback cannot be orthogonal to u.
    moment = dot(u, u)
    trace_S = sum(S[j, j] for j in range(N))
    trace_D = sum(D[j, j] for j in range(N))
    trace_cap = ((2 * arb.pi()).log() - arb.const_euler()) * arb(2).log()
    assert moment > 0 and trace_S > 0
    assert trace_D > trace_S and trace_cap > trace_D
    adaptive_denominator = dot(u, S * u)
    adaptive_gain = moment * moment / adaptive_denominator
    trace_gain = moment / trace_S
    assert adaptive_denominator > 0 and adaptive_gain > trace_gain
    assert gain_opt > adaptive_gain
    adaptive_alpha = moment / adaptive_denominator
    adaptive_correction = H * u
    zu = arb_mat(2 * N, 1,
                 [a[j, 0] - adaptive_alpha * adaptive_correction[j, 0] for j in range(N)] +
                 [adaptive_alpha * u[j, 0] for j in range(N)])
    adaptive_energy = 1 - 2 * dot(joint_b, zu) + dot(zu, joint_G * zu)
    assert (adaptive_energy - E_old + adaptive_gain).contains(0)
    assert adaptive_energy < E_old
    if gain > adaptive_gain:
        selected = 'mobius_shell'
        selected_gain = gain
    elif adaptive_gain > gain:
        selected = 'residual_matched'
        selected_gain = adaptive_gain
    else:
        raise ArithmeticError('selection undecided at this precision')
    return {'N': N, 'E_N': record(E_old), 'E_2N': record(E_new),
            'full_block_gain': record(gain_opt), 'shell_gain': record(gain),
            'residual_moment': record(moment), 'trace_S': record(trace_S),
            'trace_D': record(trace_D), 'uniform_trace_cap': record(trace_cap),
            'adaptive_gain': record(adaptive_gain), 'adaptive_energy': record(adaptive_energy),
            'trace_gain_lower_bound': record(trace_gain),
            'moment_over_trace_E_squared': record(trace_gain / (E_old * E_old)),
            'adaptive_gain_over_E_squared': record(adaptive_gain / (E_old * E_old)),
            'adaptive_update_identity_defect': record(adaptive_energy - E_old + adaptive_gain),
            'selected_direction': selected, 'selected_gain': record(selected_gain),
            'shell_gain_over_E_squared': record(gain / (E_old * E_old)),
            'optimal_gain_over_E_squared': record(gain_opt / (E_old * E_old)),
            'shell_energy': record(residual), 'alpha': record(alpha),
            'schur_identity_defect': record(E_old - gain_opt - E_new),
            'line_update_identity_defect': record(residual - E_old + gain),
            'wrong_sign_increase': record(wrong_energy - E_old),
            'omitted_cross_identity_defect': record(omitted_cross - E_new)}


def one_precision(Ns, bits):
    previous = ctx.prec
    try:
        ctx.prec = bits
        size = 2 * max(Ns)
        builder = GramBuilder(bits)
        builder.extend(size)
        G, _ = builder.gram(size, want_float=False)
        b = builder.rhs(size)
        mu = mobius_sieve(size)
        return [one_case(G, b, N, mu) for N in Ns]
    finally:
        ctx.prec = previous


def independent_small():
    # Independent Gram entry implementation and a separate scalar Schur solve.
    with mp.workdps(65):
        N = 4
        G = mp.matrix([[gram_entry_mp(i, j, dps=65) for j in range(1, 9)] for i in range(1, 9)])
        b = mp.matrix([(1 - mp.euler + mp.log(k)) / k for k in range(1, 9)])
        A = G[:N, :N]
        C = G[:N, N:]
        D = G[N:, N:]
        a = mp.lu_solve(A, b[:N, :])
        H = mp.matrix(N, N)
        for col in range(N):
            sol = mp.lu_solve(A, C[:, col])
            for row in range(N):
                H[row, col] = sol[row]
        S = D - C.T * H
        u = b[N:, :] - C.T * a
        E_old = 1 - (b[:N, :].T * a)[0]
        E_new = 1 - (b.T * mp.lu_solve(G, b))[0]
        full_gain = (u.T * mp.lu_solve(S, u))[0]
        mu = mobius_sieve(8)
        v = mp.matrix([-mu[k] * mp.log(mp.mpf(8) / k) for k in range(5, 9)])
        shell_gain = (v.T * u)[0] ** 2 / (v.T * S * v)[0]
        moment = (u.T * u)[0]
        adaptive_gain = moment ** 2 / (u.T * S * u)[0]
        trace_gain = moment / sum(S[k, k] for k in range(N))
        assert abs(E_old - full_gain - E_new) < mp.mpf('1e-55')
        # Cotangent-free quadrature with analytic tail from the existing oracle.
        quad_defects = []
        for j, k in [(1, 1), (1, 2), (2, 3)]:
            q = gram_entry_quad(j, k, dps=40, M=10)
            err = abs(q - gram_entry_mp(j, k, dps=55))
            assert err < mp.mpf('1e-35')
            quad_defects.append({'j': j, 'k': k, 'defect': mp.nstr(err, 8)})
        return {'N': N, 'E_N': mp.nstr(E_old, 55), 'E_2N': mp.nstr(E_new, 55),
                'adaptive_gain': mp.nstr(adaptive_gain, 55),
                'trace_gain_lower_bound': mp.nstr(trace_gain, 55),
                'shell_gain': mp.nstr(shell_gain, 55), 'quad_defects': quad_defects}


def plateau_control():
    # This Hilbert-space energy decreases forever but stays above 1/4.
    rows = []
    for j in (1, 4, 16, 64, 256, 1024):
        E = Fraction(1, 4) + Fraction(3, 4 * (j + 1))
        next_E = Fraction(1, 4) + Fraction(3, 4 * (j + 2))
        gain = E - next_E
        assert Fraction(1, 4) < next_E < E <= 1
        rows.append({'j': j, 'E': str(E), 'gain': str(gain), 'gain_over_E_squared': str(gain / E ** 2)})
    return rows


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--max-n', type=int, choices=(4, 8, 16, 32, 64), default=64)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    start = perf_counter()
    Ns = [N for N in (4, 8, 16, 32, 64) if N <= args.max_n]
    runs = {str(bits): one_precision(Ns, bits) for bits in (128, 192)}
    ctx.prec = 256  # Do not round serialized comparison balls to the default 53 bits.
    for low, high in zip(runs['128'], runs['192']):
        assert low['N'] == high['N']
        for key in ('E_N', 'E_2N', 'shell_gain', 'full_block_gain', 'adaptive_gain', 'trace_gain_lower_bound'):
            assert arb(low[key]['ball']).overlaps(arb(high[key]['ball']))
            assert high[key]['radius'] < low[key]['radius']
    cross = independent_small()
    with mp.workdps(60):
        # Compare to midpoint independently; high-precision balls are reported separately.
        for key in ('E_N', 'E_2N', 'shell_gain', 'adaptive_gain', 'trace_gain_lower_bound'):
            txt = runs['192'][0][key]['ball'].split('+/-')[0].strip(' []')
            assert abs(mp.mpf(txt) - mp.mpf(cross[key])) < mp.mpf('1e-32')
    result = {'status': 'finite block identities and descent checks passed; uniform decrease unproved',
              'runs': runs, 'independent_small': cross, 'plateau_control': plateau_control(),
              'elapsed_seconds': perf_counter() - start,
              'scope': 'bound on an RH-equivalent approximation error, not a proved square-root prime error',
              'sources': ['math/0202141v2', 'hunts/rogue_frontier/nyman_beurling/SOURCES.md']}
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'status': result['status'], 'elapsed_seconds': result['elapsed_seconds'],
                      'cases_per_precision': len(Ns), 'precisions': [128, 192],
                      'rows': [{'N': r['N'], 'E_N': r['E_N']['mid'], 'E_2N': r['E_2N']['mid'],
                                'shell_kappa': r['shell_gain_over_E_squared']['mid'],
                                'adaptive_kappa': r['adaptive_gain_over_E_squared']['mid'],
                                'trace_moment_kappa': r['moment_over_trace_E_squared']['mid'],
                                'selected': r['selected_direction'],
                                'optimal_kappa': r['optimal_gain_over_E_squared']['mid']}
                               for r in runs['192']]}, indent=2))

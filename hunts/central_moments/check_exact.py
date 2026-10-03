"""Check saved control witnesses with SymPy, independently of probe.py."""
import json
from pathlib import Path

import sympy as sp
from flint import arb, arb_mat, ctx


def main():
    data = json.loads(Path(__file__).with_name('results.json').read_text())
    w, c = sp.symbols('w c')
    # Independently derive the small symbolic determinant.
    f = 1 + sum(w**k / ((c+1)*sp.factorial(2*k)) for k in range(1, 4))
    q = sp.series(sp.diff(f, w)/f, w, 0, 3).removeO().expand()
    m = [sp.factor((-1)**k*q.coeff(w, k)) for k in range(3)]
    d = sp.factor(sp.det(sp.Matrix([[m[0], m[1]], [m[1], m[2]]])))
    assert sp.simplify(d - (8-7*c)/(1440*(c+1)**3)) == 0
    assert d.subs(c, sp.Rational(6, 5)) == sp.Rational(data['controls']['negative_H0_size2']) < 0

    witness = data['controls']['finite_false_positive']
    value = sp.Rational(witness['c'])
    assert value > 1
    f = 1 + sum(w**k / ((value+1)*sp.factorial(2*k)) for k in range(1, 9))
    # Polynomial inversion uses SymPy's algorithm, not the producer recurrence.
    q = sp.Poly(sp.rem(sp.diff(f, w)*sp.invert(f, w**8, w), w**8, w), w)
    m = [(-1)**k*q.nth(k) for k in range(8)]
    assert len(witness['matrices']) == 8
    assert {(row['shift'], row['size']) for row in witness['matrices']} == {
        (shift, size) for shift in (0, 1) for size in range(1, 5)}
    for row in witness['matrices']:
        r, shift = row['size'], row['shift']
        mat = sp.Matrix(r, r, lambda i, j: m[i+j+shift])
        exact = mat.det(method='berkowitz')
        assert exact == sp.Rational(row['det']) > 0
    extension = json.loads(Path(__file__).with_name('control_extension.json').read_text())
    assert sp.Rational(extension['c']) == value
    f = 1 + sum(w**k / ((value+1)*sp.factorial(2*k)) for k in range(1, 11))
    q = sp.Poly(sp.rem(sp.diff(f, w)*sp.invert(f, w**10, w), w**10, w), w)
    m = [(-1)**k*q.nth(k) for k in range(10)]
    assert {(row['shift'], row['size']) for row in extension['matrices']} == {(0, 5), (1, 5)}
    assert len(extension['matrices']) == 2
    for row in extension['matrices']:
        mat = sp.Matrix(5, 5, lambda i, j: m[i+j+row['shift']])
        assert mat.det(method='berkowitz') == sp.Rational(row['det']) < 0
    print('PASS: 1 symbolic identity, 3 exact negative witnesses, 8 exact positive determinants with c>1')
    balls = json.loads(Path(__file__).with_name('ball_results.json').read_text())
    assert [run['bits'] for run in balls['runs']] == [256, 384]
    assert [run['dps'] for run in data['numerics']] == [50, 80]
    with ctx.workprec(384):
        for run in balls['runs']:
            assert len(run['moments']) == 8 and len(run['scaled_minors']) == 8
            m = [arb(value) for value in run['moments']]
            assert m[0] > 0
            scaled = [value/m[0]**(n+1) for n, value in enumerate(m)]
            for row in run['scaled_minors']:
                r, shift = row['size'], row['shift']
                # Arb's matrix determinant uses a separate implementation
                # from the producer's explicit permutation sum.
                value = arb_mat([[scaled[i+j+shift] for j in range(r)] for i in range(r)]).det()
                saved = arb(row['enclosure'])
                assert value > 0 and saved > 0 and value.overlaps(saved)
        reference = balls['runs'][-1]
        for numeric in data['numerics']:
            for measured, enclosure in zip(numeric['moments'], reference['moments'], strict=True):
                target = arb(enclosure)
                assert abs(arb(measured)-target) < abs(target)*arb('1e-39')
            for route in ('scaled_minors', 'theta_scaled_minors'):
                for measured, enclosure in zip(numeric[route], reference['scaled_minors'], strict=True):
                    assert (measured['shift'], measured['size']) == (enclosure['shift'], enclosure['size'])
                    target = arb(enclosure['enclosure'])
                    assert abs(arb(measured['det'])-target) < abs(target)*arb('1e-30')
    print('PASS: 16 positive Arb determinant enclosures rechecked; both numerical routes at both precisions agree')


if __name__ == '__main__':
    main()

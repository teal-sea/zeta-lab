"""Exact finite examples and independent evaluations of the cycle constants."""

from __future__ import annotations

import json
from pathlib import Path

import numpy as np
import sympy as sp
from flint import arb, ctx
from mpmath import mp


def constants():
    """Compare direct integration, closed forms, and interval evaluation."""
    with mp.workdps(60):
        h = 1 / mp.sqrt(2)
        k = h * mp.cot(h)
        c2 = k + mp.mpf(1)/2
        p = lambda x: mp.cos(mp.sqrt(2)*x)/(mp.sqrt(2)*mp.sin(h))
        # Evaluate the absolute-distance integral independently on each side.
        def potential(x):
            return (mp.quad(lambda y: (x-y)*p(y), [-h*h, x])
                    + mp.quad(lambda y: (y-x)*p(y), [x, h*h]))
        a2 = mp.quad(lambda x: p(x)**2, [-h*h, h*h])
        a3 = mp.quad(lambda x: p(x)**3, [-h*h, h*h])
        c3 = 3*c2*a2-2*a3
        direct = mp.quad(lambda x: p(x)**3+3*p(x)**2*potential(x), [-h*h, h*h])
        delta = (6*k-5)*(6*k*k+6*k-1)/24
        assert abs(direct-c3) < mp.mpf('1e-50')
        assert abs(c3-3*c2+2-delta) < mp.mpf('1e-50')
        out = {name: mp.nstr(value, 50) for name, value in
               [('k', k), ('c2', c2), ('c3', c3), ('delta3', delta),
                ('quadrature_defect', abs(direct-c3))]}
    old_prec = ctx.prec
    try:
        ctx.prec = 160
        u = arb(2).sqrt()/2
        v = u.cos()/u.sin()/arb(2).sqrt()
        d = (6*v-5)*(6*v*v+6*v-1)/24
        assert d < 0
        out['delta3_interval'] = str(d)
        out['interval_bits'] = 160
    finally:
        ctx.prec = old_prec
    return out


def exact_example():
    """Two unit vectors yield a strict gain, checked by rational traces."""
    a = sp.Matrix([[sp.Rational(5, 4), sp.sqrt(3)/4],
                   [sp.sqrt(3)/4, sp.Rational(3, 4)]])
    m = [sp.trace(a**j) for j in range(1, 5)]
    old = 2*m[0]-m[1]
    new = 4*m[0]-6*m[1]+4*m[2]-m[3]
    assert m == [2, sp.Rational(5, 2), sp.Rational(7, 2), sp.Rational(41, 8)]
    assert old == sp.Rational(3, 2) and new == sp.Rational(15, 8)
    assert new-old == sp.Rational(3, 8)
    return {'moments': list(map(str, m)), 'quadratic': str(old),
            'quartic': str(new), 'gain': str(new-old)}


def complex_cycle_identity():
    """Check the signed feature operator against complex kernel cycle sums."""
    from itertools import product

    with mp.workdps(70):
        frequencies = [mp.mpf(1)/7, mp.mpf(2)/5, mp.mpf(1)/2]
        weights = [mp.mpf(1)/6, mp.mpf(1)/3, mp.mpf(1)/2]
        # One simple real point, one double point, and a nonreal pair.
        points = [mp.mpf(0), mp.mpf(1)/3, mp.mpf(1)/3,
                  mp.mpc(mp.mpf(4)/5, mp.mpf(2)/7),
                  mp.mpc(mp.mpf(4)/5, -mp.mpf(2)/7)]
        def feature(z):
            return mp.matrix([mp.sqrt(w)*g(2*mp.pi*x*z)
                              for x, w in zip(frequencies, weights)
                              for g in (mp.cos, mp.sin)])
        def kernel(z):
            return sum(w*mp.cos(2*mp.pi*x*z)
                       for x, w in zip(frequencies, weights))
        a = mp.zeros(2*len(frequencies))
        for z in points:
            v = feature(z)
            # Transpose is intentional: conjugate pairs make the sum real.
            a += v*v.T
        assert max(abs(mp.im(v)) for v in a) < mp.mpf('1e-60')
        assert abs(sum(a[i, i] for i in range(a.rows))-len(points)) < mp.mpf('1e-60')
        defects = {}
        for degree in [2, 3, 4]:
            power = a**degree
            trace = sum(power[i, i] for i in range(a.rows))
            cycle = sum(mp.fprod(kernel(z[j]-z[(j+1) % degree])
                                 for j in range(degree))
                        for z in product(points, repeat=degree))
            defect = abs(trace-cycle)
            assert defect < mp.mpf('1e-55')
            defects[str(degree)] = mp.nstr(defect, 12)
        return {'points_with_multiplicity': len(points), 'simple_real': 1,
                'nonreal_pairs': 1, 'decimal_precision': 70,
                'trace_cycle_defects': defects}


def signed_examples(seed=20260905, count=300):
    """Measured tests of the theorem on genuinely indefinite operators."""
    rng = np.random.default_rng(seed)
    minimum_margin = float('inf')
    indefinite = 0
    for _ in range(count):
        dim = int(rng.integers(2, 9))
        simple = int(rng.integers(0, 8))
        multiple = int(rng.integers(0, 4))
        pairs = int(rng.integers(1, 4))
        a = np.zeros((dim, dim))
        total = simple
        for _ in range(simple):
            v = rng.normal(size=dim); v /= np.linalg.norm(v)
            a += np.outer(v, v)
        for _ in range(multiple):
            v = rng.normal(size=dim); v /= np.linalg.norm(v)
            mult = int(rng.integers(2, 5)); total += mult
            a += mult*np.outer(v, v)
        for _ in range(pairs):
            q, _ = np.linalg.qr(rng.normal(size=(dim, 2)))
            height = float(rng.uniform(0.05, 1.5))
            g = np.sqrt(1+height**2)*q[:, 0]
            h = height*q[:, 1]
            mult = int(rng.integers(1, 4)); total += 2*mult
            a += 2*mult*(np.outer(g, g)-np.outer(h, h))
        eig = np.linalg.eigvalsh(a)
        indefinite += int(eig.min() < -1e-9)
        assert abs(eig.sum()-total) < 1e-10
        for t in [-0.75, -0.3, 0.0, 0.3, 0.75]:
            score = eig*(2-eig)*(1+t*(eig-1)+t*t*(eig-1)**2)
            bound = float(score.sum()/(1+t*t/(4*(1-t*t))))
            margin = simple-bound
            assert margin >= -1e-8
            minimum_margin = min(minimum_margin, margin)
    return {'seed': seed, 'configurations': count, 'indefinite': indefinite,
            'tested_parameters': [-0.75, -0.3, 0.0, 0.3, 0.75],
            'minimum_margin_measured': minimum_margin}


if __name__ == '__main__':
    result = {'status': 'finite theorem checks; no new zeta proportion',
              'constants': constants(), 'exact_example': exact_example(),
              'complex_cycle_identity': complex_cycle_identity(),
              'signed_examples': signed_examples()}
    destination = Path(__file__).with_name('results.json')
    destination.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))

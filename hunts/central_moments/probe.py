"""Bounded central-moment measurements and exact rational controls.

Run from the repository root. No zero list enters the zeta calculation.
The numerical rows are floating-point measurements, not enclosures.
"""
from __future__ import annotations

import json
from fractions import Fraction
from math import factorial
from pathlib import Path

import mpmath
from mpmath import mp


def moments(a):
    """Return m_n = (-1)^n [w^n] F'(w)/F(w), requiring a_0 = 1."""
    if a[0] != 1:
        raise ValueError("coefficients must be normalized")
    b = []
    for n in range(len(a) - 1):
        b.append((n + 1) * a[n + 1] - sum(a[k] * b[n-k] for k in range(1, n+1)))
    return [(-1)**n * v for n, v in enumerate(b)]


def determinant(rows):
    """Gaussian elimination, preserving Fraction arithmetic for exact inputs."""
    a = [list(row) for row in rows]
    result = 1
    for k in range(len(a)):
        pivot = next((j for j in range(k, len(a)) if a[j][k] != 0), None)
        if pivot is None:
            return a[0][0] * 0
        if pivot != k:
            a[k], a[pivot] = a[pivot], a[k]
            result = -result
        v = a[k][k]
        result *= v
        for j in range(k + 1, len(a)):
            ratio = a[j][k] / v
            for i in range(k + 1, len(a)):
                a[j][i] -= ratio * a[k][i]
    return result


def minors(m, size):
    return [
        {"shift": shift, "size": r,
         "det": determinant([[m[i+j+shift] for j in range(r)] for i in range(r)])}
        for shift in (0, 1) for r in range(1, size + 1)
    ]


def control(c, count):
    return moments([Fraction(1)] + [1 / ((c+1)*factorial(2*k)) for k in range(1, count+1)])


def xi(s):
    return s*(s-1)*mp.power(mp.pi, -s/2)*mp.gamma(s/2)*mp.zeta(s)/2


def theta_coefficients(count, terms=12, upper=2):
    # Finite quadrature parameters are recorded, not hidden error guarantees.
    def phi(u):
        x = mp.exp(4*u)
        return mp.fsum((2*mp.pi**2*n**4*mp.exp(9*u)-3*mp.pi*n*n*mp.exp(5*u))
                       * mp.exp(-mp.pi*n*n*x) for n in range(1, terms+1))
    integrals = [mp.quad(lambda u: phi(u)*u**(2*k), [0, mp.mpf('0.5'), 1, upper])
                 for k in range(count+1)]
    return [4**k*integrals[k]/(mp.factorial(2*k)*integrals[0]) for k in range(count+1)]


def exact_checks():
    c = Fraction(6, 5)
    m = control(c, 4)
    d = determinant([[m[0], m[1]], [m[1], m[2]]])
    expected = (8-7*c)/(1440*(c+1)**3)
    assert d == expected < 0 and m[1] > 0
    # An unrelated finite product checks recurrence and determinant conventions.
    a = [Fraction(1), Fraction(3, 2), Fraction(1, 2)]
    a += [Fraction(0)]*6
    assert moments(a) == [Fraction(1)+Fraction(1, 2)**(n+1) for n in range(8)]
    assert minors(moments(a), 2)[0]['det'] == Fraction(3, 2)
    passed = None
    for exponent in range(1, 25):
        candidate = Fraction(1) + Fraction(1, 10**exponent)
        rows = minors(control(candidate, 8), 4)
        if all(row['det'] > 0 for row in rows):
            passed = {"c": str(candidate), "matrices": [dict(row, det=str(row['det'])) for row in rows]}
            break
    if passed is None:
        raise RuntimeError("bounded control search found zero examples")
    return {"negative_control_c": str(c), "negative_H0_size2": str(d),
            "positive_m1": str(m[1]), "finite_false_positive": passed}


def run():
    report = {"status": "measured; RH unresolved", "mpmath": mpmath.__version__,
              "matrix_sizes": [1, 2, 3, 4], "theta_terms": 12, "theta_upper": 2,
              "controls": exact_checks(), "numerics": []}
    for dps in (50, 80):
        print(f"START dps={dps}, 9 coefficients, 8 matrices per route", flush=True)
        with mp.workdps(dps):
            taylor = mp.taylor(xi, mp.mpf('0.5'), 16)
            a = [taylor[2*k]/taylor[0] for k in range(9)]
            b = theta_coefficients(8)
            direct, theta = moments(a), moments(b)
            relative = max(abs(x-y)/abs(x) for x, y in zip(direct, theta))
            if relative >= mp.mpf('1e-30'):
                raise ArithmeticError(f"independent routes disagree: {relative}")
            scale = direct[0]
            scaled_direct = [v/scale**(n+1) for n, v in enumerate(direct)]
            scaled_theta = [v/scale**(n+1) for n, v in enumerate(theta)]
            rows = minors(scaled_direct, 4)
            other_rows = minors(scaled_theta, 4)
            for row, other in zip(rows, other_rows):
                if (row['det'] > 0) != (other['det'] > 0):
                    raise ArithmeticError("routes disagree on determinant sign")
            report['numerics'].append({"dps": dps,
                "max_relative_moment_difference": mp.nstr(relative, 15),
                "moments": [mp.nstr(v, 42) for v in direct],
                "scaled_minors": [dict(row, det=mp.nstr(row['det'], 35)) for row in rows],
                "theta_scaled_minors": [dict(row, det=mp.nstr(row['det'], 35)) for row in other_rows]})
            print(f"DONE dps={dps}, positive={sum(r['det'] > 0 for r in rows)}/8, max relative difference={mp.nstr(relative, 6)}", flush=True)
    output = Path(__file__).with_name('results.json')
    output.write_text(json.dumps(report, indent=2) + '\n')
    c = Fraction(report['controls']['finite_false_positive']['c'])
    extension = [dict(row, det=str(row['det'])) for row in minors(control(c, 10), 5)
                 if row['size'] == 5]
    if not all(Fraction(row['det']) < 0 for row in extension):
        raise ArithmeticError('size-five control expectation failed')
    output.with_name('control_extension.json').write_text(
        json.dumps({'c': str(c), 'matrices': extension}, indent=2) + '\n')
    print(f"WROTE {output}; 2 numerical runs, 16 matrix comparisons, RH unresolved", flush=True)


if __name__ == '__main__':
    run()

"""Finite central-moment signs with Arb enclosures through every operation."""
import itertools
import json
from pathlib import Path

import flint
from flint import arb, arb_series, ctx


def det_leibniz(matrix):
    """No pivot selection or point approximations enter this determinant."""
    n = len(matrix)
    total = arb(0)
    for permutation in itertools.permutations(range(n)):
        inversions = sum(permutation[i] > permutation[j] for i in range(n) for j in range(i+1, n))
        term = arb((-1)**inversions)
        for i, j in enumerate(permutation):
            term *= matrix[i][j]
        total += term
    return total


def run_at(bits):
    with ctx.workprec(bits):
        s = arb_series([arb(1)/2, 1], prec=17)
        completed = s*(s-1)/2 * (-s*arb.pi().log()/2).exp() * (s/2).gamma() * s.zeta()
        if not completed[0] > 0:
            raise ArithmeticError('central value sign undecided')
        if not all(completed[k].contains(0) for k in range(1, 17, 2)):
            raise ArithmeticError('functional-equation parity check failed')
        # Build the even F series and obtain the logarithmic derivative with
        # Arb series division, independently of the recurrence in probe.py.
        f = arb_series([arb(1)] + [completed[2*k]/completed[0] for k in range(1, 9)], prec=9)
        quotient = f.derivative()/f
        moments = [(-1)**n * quotient[n] for n in range(8)]
        if not moments[0] > 0:
            raise ArithmeticError('scaling sign undecided')
        scaled = [v / moments[0]**(n+1) for n, v in enumerate(moments)]
        rows = []
        for shift in (0, 1):
            for size in range(1, 5):
                value = det_leibniz([[scaled[i+j+shift] for j in range(size)] for i in range(size)])
                if not value > 0:
                    raise ArithmeticError(f'not a positive enclosure: shift={shift}, size={size}, value={value}')
                # Decimal strings include the outward error radius.
                text = value.str(45)
                if not arb(text) > 0:
                    raise ArithmeticError('serialized enclosure lost its positive sign')
                rows.append({'shift': shift, 'size': size, 'enclosure': text})
        return {'bits': bits, 'moments': [v.str(45) for v in moments], 'scaled_minors': rows}


def main():
    previous_cap = ctx.cap
    try:
        ctx.cap = 17
        runs = []
        for bits in (256, 384):
            print(f'START Arb bits={bits}, 8 finite matrices', flush=True)
            runs.append(run_at(bits))
            print(f'DONE Arb bits={bits}, positive enclosures=8/8', flush=True)
        result = {'scope': 'eight finite matrices only; RH unresolved',
                  'python_flint': flint.__version__, 'runs': runs}
        Path(__file__).with_name('ball_results.json').write_text(json.dumps(result, indent=2)+'\n')
    finally:
        ctx.cap = previous_cap


if __name__ == '__main__':
    main()

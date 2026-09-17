"""Reproduce the bounded mathematical packet from exact inputs."""

from __future__ import annotations

import hashlib
import json
import time
from datetime import datetime, timezone
from fractions import Fraction
from pathlib import Path

import mpmath as mp
from flint import acb, arb, ctx

from hunts.dh_minus_heat import odd_ball, phase_bound, pilot

HERE = Path(__file__).resolve().parent
RADIUS = '1/10000000'
DISKS = [
    {'label': 'time_one', 't': '1',
     'centre': ('7.646830873064', '0.425938287679'),
     'h_upper': '1e-14', 'hp_lower': '0.015', 'm2_upper': '2.35'},
    {'label': 'time_217_over_200', 't': '217/200',
     'centre': ('7.543145542463', '0.072646330251'),
     'h_upper': '1e-14', 'hp_lower': '0.0028', 'm2_upper': '1.9'},
]


def verify():
    start = time.monotonic()
    rows = []
    for disk in DISKS:
        for prec, nmax, upper in [(96, 24, '4'), (128, 24, '4'),
                                  (160, 28, '4'), (128, 26, '7/2')]:
            row = odd_ball.rouche(
                disk['centre'], RADIUS, t=disk['t'], prec=prec,
                nmax=nmax, upper=upper,
            )
            row['label'] = disk['label']
            assert row['decided']
            assert Fraction(row['linear_lower']['lower']) > (
                Fraction(row['constant_upper']['upper'])+
                Fraction(row['remainder_upper']['upper']))
            assert Fraction(row['H_abs_upper']['upper']) < Fraction(disk['h_upper'])
            assert Fraction(row['Hprime_abs_lower']['lower']) > Fraction(disk['hp_lower'])
            assert Fraction(row['M2_upper']['upper']) < Fraction(disk['m2_upper'])
            rows.append(row)
    (HERE/'rouche.json').write_text(json.dumps({'frame': 'narrow s=1/2+iz',
                                              'runs': rows}, indent=2)+'\n')
    phase = phase_bound.check()
    for row in phase:
        assert Fraction(row['margin']['lower']) > 0
    (HERE/'phase.json').write_text(json.dumps(phase, indent=2)+'\n')
    first = phase_bound.first_function_check()
    for row in first:
        assert Fraction(row['coefficient_sum_upper']['upper']) < 1
    (HERE/'first_comparison.json').write_text(json.dumps(first, indent=2)+'\n')

    checks = []
    with mp.workdps(55):
        for disk in DISKS:
            z = mp.mpc(*disk['centre'])
            t = mp.mpf(Fraction(disk['t']).numerator) / Fraction(disk['t']).denominator
            values = [pilot.heat_mp(z, t, nmax=24),
                      mp.diff(lambda w: pilot.heat_mp(w, t, nmax=24), z)]
            with ctx.workprec(160):
                for order, ref in enumerate(values):
                    value = odd_ball.heat(
                        disk['centre'], disk['t'], prec=160, order=order,
                    )
                    ref_ball = acb(arb(mp.nstr(ref.real, 50)),
                                   arb(mp.nstr(ref.imag, 50)))
                    overlap = value.overlaps(ref_ball)
                    assert overlap
                    checks.append({
                        'name': f"{disk['label']}_heat_derivative_{order}",
                        'dps': 55, 'reference_real': mp.nstr(ref.real, 50),
                        'reference_imag': mp.nstr(ref.imag, 50),
                        'overlap': bool(overlap),
                        'reference_grade': 'floating-point quadrature, not an enclosure',
                    })
        x = mp.mpf('1.2')
        defect = abs(pilot.theta(1/x, 24)+x**mp.mpf('1.5')*pilot.theta(x, 24))
        assert defect < mp.mpf('1e-45')
        checks.append({'name': 'odd_theta_transform', 'dps': 55,
                       'absolute_defect': mp.nstr(defect, 12)})
        z = mp.mpc('2', '0.4')
        zero = pilot.heat_mp(z, mp.mpf(0), nmax=24)
        ref = -1j*pilot.completed(mp.mpf('0.5')+1j*z)
        assert abs(zero-ref) < mp.mpf('1e-45')
        checks.append({'name': 'zero_time_Hurwitz_identity', 'dps': 55,
                       'absolute_defect': mp.nstr(abs(zero-ref), 12)})
    lesion = odd_ball.rouche(DISKS[0]['centre'], RADIUS, nmax=2)
    assert not lesion['decided']
    checks.append({'name': 'underresolved_series_refuses', 'nmax': 2,
                   'decided': lesion['decided']})
    # A centre displacement larger than the radius must not inherit a decision.
    displaced = odd_ball.rouche(('7.646930873064', DISKS[0]['centre'][1]), RADIUS)
    assert not displaced['decided']
    checks.append({'name': 'displaced_centre_refuses', 'decided': displaced['decided']})
    written_margin = Fraction('1e-7')*Fraction('0.015')-Fraction('1e-14')-Fraction('1e-14')*Fraction('2.35')/2
    assert written_margin > 0
    later_margin = Fraction('1e-7')*Fraction('0.0028')-Fraction('1e-14')-Fraction('1e-14')*Fraction('1.9')/2
    assert later_margin > 0
    bound = Fraction(753, 400)**2/2
    (HERE/'verification.json').write_text(json.dumps({
        'timestamp': datetime.now(timezone.utc).isoformat(),
        'frame': 'narrow s=1/2+iz', 'checks': checks,
        'written_margins': {'time_one': str(written_margin),
                            'time_217_over_200': str(later_margin)},
        'narrow_bracket': {'strict_lower': '217/200', 'upper': str(bound)},
        'wide_bracket': {'strict_lower': '217/50', 'upper': str(4*bound)},
        'first_function_upper_narrow': '1/2',
        'seconds': time.monotonic()-start,
        'source_sha256': {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                          for p in sorted(HERE.glob('*.py'))}}, indent=2)+'\n')
    print(json.dumps({'rouche_runs': len(rows), 'phase_backends': len(phase),
                      'first_comparison_backends': len(first),
                      'checks': len(checks),
                      'written_margins': {'time_one': str(written_margin),
                                          'time_217_over_200': str(later_margin)},
                      'narrow_upper': str(bound), 'wide_upper': str(4*bound),
                      'seconds': time.monotonic()-start}, indent=2))


if __name__ == '__main__':
    verify()

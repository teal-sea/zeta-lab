"""Arb sine-flow integrals with explicit errors, in s=1/2+iz units.

The ordinary derivation and review status live in RESULTS.md. These functions
return enclosures, not a status for the surrounding analytic argument.
"""

from __future__ import annotations

from fractions import Fraction

from flint import acb, arb, ctx, fmpq


def _q(value):
    if isinstance(value, bool) or isinstance(value, float):
        raise TypeError('use exact integers, rational strings or Fraction')
    q = Fraction(value)
    return arb(fmpq(q.numerator, q.denominator))


def _tau():
    phi = (1 + arb(5).sqrt()) / 2
    return -phi - (1 + phi*phi).sqrt()


def _point(z):
    if not isinstance(z, (tuple, list)) or len(z) != 2:
        raise TypeError('z must be an exact (real, imaginary) pair')
    return acb(_q(z[0]), _q(z[1]))


def _tails(n, upper, t, y, order, magnitude):
    """Uniform series tail on [0,U], plus integral tail beyond U.

    |a_n|<=M. For n>N, n^2>=n(N+1), so the omitted omega sum
    is at most M (N+1) r^(N+1)/(1-r)^2 at x>=1, with
    r=exp(-pi(N+1)/5). Multiply by 4 U^(k+1)
    exp(t U^2+(3/2+y)U) for derivative order k.

    Beyond U>=1, sum n exp(-pi n^2 exp(2u)/5)<=2 exp(-pi exp(2u)/5)
    once exp(-pi exp(2U)/5)<29/100. With V=exp(2U) and
    c=pi/5-(t U^2+(3/2+y)U)/V>0, the tail is at most
    4 M U^k exp(-cV)/(cV). This follows by v=exp(2u) and
    monotonicity of (log v)^k/v for log(v)>=k, for k=0,1,2.
    """
    r = (-arb.pi()*(n+1)/5).exp()
    series = magnitude*(n+1)*r**(n+1)/(1-r)**2
    finite = 4*upper**(order+1)*(t*upper**2+(arb(3)/2+y)*upper).exp()*series
    v = (2*upper).exp()
    c = arb.pi()/5-(t*upper**2+(arb(3)/2+y)*upper)/v
    if not (upper >= 1 and (-arb.pi()*v/5).exp() < _q('29/100') and c > 0):
        raise ValueError('infinite-tail hypotheses not decided; increase upper')
    infinite = 4*magnitude*upper**order*(-c*v).exp()/(c*v)
    return finite.abs_upper(), infinite.abs_upper()


def _integrate(z, t, prec, nmax, upper, order, majorant, eval_limit):
    if not isinstance(prec, int) or isinstance(prec, bool) or prec < 64:
        raise ValueError('prec must be an integer >=64')
    if not isinstance(nmax, int) or isinstance(nmax, bool) or nmax < 2:
        raise ValueError('nmax must be an integer >=2')
    if order not in (0, 1, 2):
        raise ValueError('derivative order must be 0, 1 or 2')
    with ctx.workprec(prec):
        t = _q(t)
        if not t >= 0:
            raise ValueError('this instrument requires nonnegative heat time')
        upper = _q(upper)
        z = _point(z)
        y = arb(z.imag.abs_upper())
        tau = _tau()
        magnitude = (-tau).abs_upper()
        if not magnitude > 1:
            raise ValueError('coefficient majorant not established')
        pattern = [arb(0), arb(1), tau, -tau, arb(-1)]
        coeff = [n*(magnitude if majorant else pattern[n % 5])
                 for n in range(1, nmax+1)]

        def integrand(u, analytic):
            # This finite sum is entire in u. Tails are added on the real path.
            x = (2*u).exp()
            q = (-arb.pi()*x/5).exp()
            q2, power, step = q*q, q, q*q*q
            omega = coeff[0]*power
            for n in range(2, nmax+1):
                power *= step
                step *= q2
                omega += coeff[n-1]*power
            if majorant:
                wave = (y*u).exp()
            elif order == 1:
                wave = (z*u).cos()
            else:
                wave = (z*u).sin() * (-1 if order == 2 else 1)
            return 4*(t*u*u+3*u/2).exp()*omega*u**order*wave

        integral = acb.integral(integrand, 0, upper, eval_limit=eval_limit)
        finite, infinite = _tails(nmax, upper, t, y, order, magnitude)
        error = arb(0, (finite+infinite).abs_upper())
        result = integral+acb(error, error)
        if not result.is_finite():
            raise ArithmeticError('integration did not return a finite enclosure')
        return result


def heat(z, t, prec=128, nmax=24, upper='4', order=0, eval_limit=20000):
    """Enclose the specified derivative of the infinite sine heat integral."""
    return _integrate(z, t, prec, nmax, upper, order, False, eval_limit)


def second_bound(imaginary_bound, t, prec=128, nmax=24, upper='4', eval_limit=20000):
    """Bound |H''(z)| uniformly when |Im z|<=imaginary_bound."""
    if Fraction(imaginary_bound) < 0:
        raise ValueError('imaginary_bound must be nonnegative')
    value = _integrate(('0', imaginary_bound), t, prec, nmax, upper, 2, True, eval_limit)
    return value.real.abs_upper()


def endpoints(value):
    """Serialize exact dyadic endpoints rather than rounded decimal displays."""
    def rational(x):
        mantissa, exponent = x.man_exp()
        q = Fraction(int(mantissa))*Fraction(2)**int(exponent)
        return str(q)
    return {'lower': rational(value.lower()), 'upper': rational(value.upper())}


def rouche(centre, radius, t='1', prec=128, nmax=24, upper='4'):
    """Return quantities for the local Taylor/Rouche inequality."""
    r = Fraction(radius)
    if not 0 < r < abs(Fraction(centre[1])):
        raise ValueError('disk must have positive radius and avoid the real axis')
    with ctx.workprec(prec):
        h = heat(centre, t, prec, nmax, upper)
        hp = heat(centre, t, prec, nmax, upper, order=1)
        m2 = second_bound(abs(Fraction(centre[1]))+r, t, prec, nmax, upper)
        rr = _q(r)
        constant = h.abs_upper()
        linear = rr*hp.abs_lower()
        remainder = rr*rr*m2/2
        margin = linear-constant-remainder
        return {'centre': list(centre), 'radius': str(r), 't': str(t),
                'prec': prec, 'nmax': nmax, 'upper': str(upper),
                'H_abs_upper': endpoints(constant),
                'Hprime_abs_lower': endpoints(hp.abs_lower()),
                'M2_upper': endpoints(m2), 'linear_lower': endpoints(linear),
                'constant_upper': endpoints(constant),
                'remainder_upper': endpoints(remainder), 'margin': endpoints(margin),
                'decided': bool(margin > 0)}

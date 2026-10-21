"""Independent routes to H_t(x + iy), for checking ``effective.py``.

Two routes, neither sharing code with the evaluator:

* ``Ht_phi``: ``zeta.heatflow.H_t``, the defining integral
  H_t(z) = int_0^inf e^{t u^2} Phi(u) cos(z u) du by a composite Gauss-Legendre
  rule on Phi (or by ``mpmath.quadgl`` with ``quad="adaptive"``).  It loses
  about 0.17 digits per unit of x, so ``zeta.heatflow.recommended_dps`` sets the
  working precision.
* ``Ht_heat_kernel``: the heat-kernel representation (htz) of the paper,
  H_t(z) = int_R (1/8) xi((1 + iz)/2 + sqrt(t) v) e^{-v^2} / sqrt(pi) dv,
  integrated with ``mpmath.quad`` and mpmath's own zeta and gamma.  No
  cancellation is involved (xi carries the e^{-pi x/8} decay in its exponent), so
  modest precision suffices; the paper remarks (line 500) that it is fast and
  accurate for moderate x.

Both are floating-point routes at a requested precision: agreement between them
and with the evaluator is a measurement, not an enclosure.
"""

from __future__ import annotations

from typing import Any

from mpmath import mp


def Ht_phi(x: Any, y: Any, t: Any, digits: int = 20, quad: str = "cached") -> Any:
    """zeta.heatflow.H_t(x + iy, t) at the precision recommended for ``digits``."""
    from zeta import heatflow as hf

    dps = hf.recommended_dps(float(x) + 1.0, digits=digits)
    with mp.workdps(dps):
        z = mp.mpc(mp.mpf(str(x)), mp.mpf(str(y)))
        return hf.H_t(z, mp.mpf(str(t)), dps=dps, quad=quad)


def _xi(s: Any) -> Any:
    return s * (s - 1) / 2 * mp.pi ** (-s / 2) * mp.gamma(s / 2) * mp.zeta(s)


def Ht_heat_kernel(x: Any, y: Any, t: Any, dps: int = 30, V: float = 14.0) -> Any:
    """H_t(x + iy) from (htz) by mpmath.quad over [-V, V] (Gaussian tail beyond)."""
    with mp.workdps(dps + 10):
        x = mp.mpf(str(x))
        y = mp.mpf(str(y))
        t = mp.mpf(str(t))
        s0 = mp.mpc(1 - y, x) / 2
        if t == 0:
            return _xi(s0) / 8
        rt = mp.sqrt(t)

        def f(v: Any) -> Any:
            return _xi(s0 + rt * v) * mp.exp(-v * v)

        pts = [mp.mpf(k) for k in range(-int(V), int(V) + 1)]
        val = mp.quad(f, pts)
        return +(val / (8 * mp.sqrt(mp.pi)))

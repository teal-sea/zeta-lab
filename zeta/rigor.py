"""Certified computation: enclosures instead of estimates.

Why this module exists
----------------------
Every other number in this laboratory is an ordinary floating-point value: a
real number carrying an *unknown* error.  ``mp.dps = 25`` asks mpmath for 25
digits and mpmath almost always delivers them, but "almost always" is not a
proof, and nothing in a float records how far it might be from the truth.

Ball (interval) arithmetic replaces the number by an **enclosure**: a pair
``lo ≤ hi`` together with the guarantee that the true value lies in ``[lo, hi]``.
Every operation propagates the guarantee — ``[a,b] + [c,d] ⊇ {x+y}`` with the
endpoints rounded *outward* — so the final interval is a theorem about the true
value, not a hope about the computed one.

The pay-off here is one sentence long:

    **if an enclosure of Z(t) is strictly positive or strictly negative, the
    sign of Z(t) is proven.**

A sign change between two *proven* signs is then a proven zero of Hardy's Z
(Z is real and continuous, so it must vanish in between), and a count of such
sign changes is a rigorous lower bound for the number of zeros of ζ on the
critical line — a theorem rather than an observation.  Combined with a
*certified* N(T) it turns :func:`zeta.zeros.verify_rh_up_to` from "accurate" into
"rigorous".  This is exactly the standard that makes large verifications
citable: Platt–Trudgian's RH verification to height 3·10¹² and Helfgott's proof
of the ternary Goldbach conjecture both rest on interval/ball arithmetic for
precisely this reason.

What is and is not certified
----------------------------
Certified here means: *given* that the backend library implements ball
arithmetic correctly and that the mathematical identities quoted below are
correct, the returned enclosures contain the true values, and the returned
integers (signs, zero counts) are the true ones.  The residual trust is in the
library and in the standard theorems — not in floating-point luck.  Anything
this module cannot certify is reported rather than papered over: an undecided
sign comes back as ``0`` from :func:`proven_sign` and as an entry in
``undecided_points``, and a step of :func:`certified_zero_count` /
:func:`verify_rh_certified` that could not be closed is named in
``uncertified_steps``, with ``certified`` False whenever either is non-empty.
Nothing is ever silently upgraded to a certificate.

Backends
--------
``BACKEND`` names the ball-arithmetic engine chosen at import time:

* ``"python-flint"`` — the Arb library.  ζ, log Γ and π are computed as balls
  by Arb itself, which is the reference implementation of rigorous complex
  ball arithmetic.
* ``"mpmath.iv"`` — mpmath's own interval context, always available.  mpmath
  provides rigorous interval ``exp``/``log``/``atan``/``loggamma`` but **no**
  interval ζ, so ζ is built here from Euler–Maclaurin with the classical
  explicit remainder bound

      |E_{M,N}(s)| ≤ |(s+2M+1)/(σ+2M+1)| · |B_{2M+2}/(2M+2)! · (s)_{2M+1} ·
                      N^{−s−2M−1}|

  evaluated in interval arithmetic and added as a disc to the truncated sum.

Both backends are exposed through the same adapter, and every public function
takes ``backend=`` so the two can be run against each other: two independent
certified implementations must produce **overlapping** enclosures, and
``tests/test_rigor.py`` checks that they do.

Cost
----
Rigor is not free — see :func:`enclosure_width_report`, which measures how the
enclosure width shrinks with precision.  Roughly, the width of an Arb enclosure
of Z(t) falls by a factor 2 per extra bit until it hits the intrinsic width of
the input, so proving a sign costs ``O(log(1/|Z(t)|))`` bits.
"""

from __future__ import annotations

import json
import math
import os
import time
from fractions import Fraction
from typing import Sequence

import mpmath
from mpmath import iv, mp

__all__ = [
    "BACKEND",
    "BACKEND_REASON",
    "DATA_DIR",
    "available_backends",
    "certified_sign_changes",
    "certified_zero_count",
    "enclose_Z",
    "enclose_rs_theta",
    "enclosure_width_report",
    "proven_sign",
    "verify_rh_certified",
]

DATA_DIR = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "data")

_LOG2_10 = 3.321928094887362


# ---------------------------------------------------------------------------
# exact conversion of user input
# ---------------------------------------------------------------------------


def _exact(value) -> Fraction:
    """The *exact* rational value of ``value`` — no rounding anywhere.

    A float is a dyadic rational and is converted bit-exactly (``Fraction(0.1)``
    is 3602879701896397/36028797018963968, not 1/10 — which is right: the float
    the caller handed us really is that number, and the enclosure must be of
    Z at *that* point).  mpmath ``mpf`` values are read out of their
    ``(sign, man, exp, bc)`` representation, also bit-exactly.  Strings and
    ``Fraction``/``Decimal`` are taken at face value, so ``enclose_Z("14.5")``
    encloses Z at 29/2 exactly.
    """
    if isinstance(value, Fraction):
        return value
    if isinstance(value, bool):  # bool is an int; refuse it, it is always a bug
        raise TypeError("bool is not a valid abscissa")
    if isinstance(value, int):
        return Fraction(value)
    if isinstance(value, float):
        if not math.isfinite(value):
            raise ValueError(f"non-finite abscissa {value!r}")
        return Fraction(value)
    mpf_tuple = getattr(value, "_mpf_", None)
    if mpf_tuple is not None:
        sign, man, exp, bc = mpf_tuple
        if man == 0:
            if exp != 0:
                raise ValueError(f"non-finite abscissa {value!r}")
            return Fraction(0)
        out = Fraction(int(man)) * Fraction(2) ** int(exp)
        return -out if sign else out
    try:
        return Fraction(value)
    except (TypeError, ValueError):
        return Fraction(str(value))


def _mpf_exact(num: int, exp: int):
    """``num · 2**exp`` as an exact mpmath ``mpf`` (precision chosen to fit)."""
    digits = int(abs(num).bit_length() / _LOG2_10) + 10
    with mp.workdps(max(mp.dps, digits)):
        return mpmath.ldexp(mp.mpf(int(num)), int(exp))


# ---------------------------------------------------------------------------
# backend: python-flint (Arb)
# ---------------------------------------------------------------------------


class _PrecGuard:
    """Set a global precision for the duration of a block and restore it after.

    Both backends keep precision in a module-global (``flint.ctx.prec``,
    ``mpmath.iv.prec``).  The repo's house rule is that no global numerical
    state may leak out of a call, so every backend entry point wraps itself in
    one of these — the ball-arithmetic analogue of ``mp.workdps``.
    """

    def __init__(self, get, set_, prec):
        self._get, self._set, self._prec = get, set_, prec

    def __enter__(self):
        self._old = self._get()
        self._set(self._prec)
        return self

    def __exit__(self, *exc):
        self._set(self._old)
        return False


try:  # pragma: no cover - exercised by whichever branch the machine takes
    import flint as _flint

    _arb = _flint.arb
    _acb = _flint.acb
    _fmpq = _flint.fmpq
    _fctx = _flint.ctx

    _old_prec = _fctx.prec
    try:
        _fctx.prec = 64
        _probe = _acb(_arb(1) / 2, _arb(20)).zeta()
        if not _probe.is_finite() or not _arb("0.4299138604", "1e-9").contains(_probe.real):
            raise RuntimeError("python-flint imported but ζ(1/2+20i) probe failed")
    finally:
        _fctx.prec = _old_prec
    _HAVE_FLINT = True
    _FLINT_REASON = (
        f"python-flint {getattr(_flint, '__version__', '?')} (Arb ball arithmetic) "
        "imported and passed the ζ(1/2+20i) probe"
    )
except Exception as _exc:  # pragma: no cover - depends on the machine
    _HAVE_FLINT = False
    _FLINT_REASON = f"python-flint unavailable: {type(_exc).__name__}: {_exc}"


def _flint_prec(prec: int) -> _PrecGuard:
    return _PrecGuard(lambda: _fctx.prec, lambda p: setattr(_fctx, "prec", p), int(prec))


def _arb_bounds(x) -> tuple:
    """``(lo, hi)`` as exact mpmath ``mpf`` for an Arb ball ``x``.

    A ball that Arb could not bound at all (it happens for very wide inputs —
    ζ over the whole segment [1/2, 2] at a large height, say) comes back as
    ``(−inf, +inf)``.  That is still a true enclosure; it simply decides
    nothing, which is exactly what the callers should — and do — conclude.
    Never raise here: an unusable bound is information, not an error.
    """
    if not x.is_finite():
        return (mp.mpf("-inf"), mp.mpf("inf"))
    return tuple(_mpf_exact(*end.man_exp()) for end in (x.lower(), x.upper()))


class _FlintBackend:
    """Adapter over Arb's ``arb``/``acb`` ball types."""

    name = "python-flint"
    reason = _FLINT_REASON
    has_arb_nzeros = True

    @staticmethod
    def _ball(q: Fraction):
        """A ball provably containing the rational ``q`` (exact when dyadic)."""
        return _arb(_fmpq(q.numerator, q.denominator))

    @classmethod
    def _span(cls, lo: Fraction, hi: Fraction):
        return cls._ball(lo) if lo == hi else cls._ball(lo).union(cls._ball(hi))

    @classmethod
    def hardy_Z(cls, lo: Fraction, hi: Fraction, prec: int) -> tuple:
        with _flint_prec(prec):
            t = cls._span(lo, hi)
            theta = _acb(_arb(1) / 4, t / 2).lgamma().imag - (t / 2) * _arb.pi().log()
            return _arb_bounds((_acb(0, theta).exp() * _acb(_arb(1) / 2, t).zeta()).real)

    @classmethod
    def rs_theta(cls, lo: Fraction, hi: Fraction, prec: int) -> tuple:
        with _flint_prec(prec):
            t = cls._span(lo, hi)
            return _arb_bounds(_acb(_arb(1) / 4, t / 2).lgamma().imag - (t / 2) * _arb.pi().log())

    @classmethod
    def zeta_native(cls, x_lo: Fraction, x_hi: Fraction, y: Fraction, prec: int):
        with _flint_prec(prec):
            return _acb(cls._span(x_lo, x_hi), cls._ball(y)).zeta()

    @staticmethod
    def native_bounds(z, prec: int) -> tuple:
        with _flint_prec(prec):
            return _arb_bounds(z.real) + _arb_bounds(z.imag)

    @staticmethod
    def native_excludes_zero(z, prec: int) -> bool:
        with _flint_prec(prec):
            return bool(z.abs_lower() > 0)

    @staticmethod
    def native_div(zb, za, prec: int):
        with _flint_prec(prec):
            return zb / za

    @staticmethod
    def native_arg_right_half(z, prec: int):
        """Enclosure of Arg z, but only when Re z > 0 is *proven*; else None."""
        with _flint_prec(prec):
            if not z.real.lower() > 0:
                return None
            return _arb_bounds(z.arg())

    @classmethod
    def zeta_box(cls, x_lo: Fraction, x_hi: Fraction, y: Fraction, prec: int) -> tuple:
        return cls.native_bounds(cls.zeta_native(x_lo, x_hi, y, prec), prec)

    @classmethod
    def arb_zeta_nzeros(cls, T: Fraction, prec: int):
        """Arb's own rigorous zero count (Turing's method), or None if inconclusive."""
        with _flint_prec(prec):
            n = cls._ball(T).zeta_nzeros().unique_fmpz()
        return None if n is None else int(n)


# ---------------------------------------------------------------------------
# backend: mpmath.iv  (interval arithmetic + hand-rolled certified Euler–Maclaurin)
# ---------------------------------------------------------------------------


def _iv_prec(prec: int) -> _PrecGuard:
    return _PrecGuard(lambda: iv.prec, lambda p: setattr(iv, "prec", p), int(prec))


def _iv_bounds(x) -> tuple:
    """``(lo, hi)`` as plain mpmath ``mpf`` for an ``mpmath.iv`` real interval.

    ``x.a`` and ``x.b`` are *degenerate intervals*, not ``mpf``; arithmetic on
    them would silently stay in the interval world (and ``hi − lo`` would come
    back as an interval).  The raw ``_mpi_`` endpoints are exact, so this is a
    lossless conversion.
    """
    lo, hi = x._mpi_
    return mp.make_mpf(lo), mp.make_mpf(hi)


_BERN_CACHE: dict[int, Fraction] = {}


def _bern_coeff(k: int) -> Fraction:
    """The exact rational B_{2k}/(2k)!."""
    c = _BERN_CACHE.get(k)
    if c is None:
        p, q = mpmath.bernfrac(2 * k)
        c = Fraction(int(p), int(q) * math.factorial(2 * k))
        _BERN_CACHE[k] = c
    return c


class _MPIntervalBackend:
    """Adapter over ``mpmath.iv``, with ζ supplied by certified Euler–Maclaurin.

    mpmath's interval context has rigorous ``exp``, ``log``, ``atan``, ``pi``
    and — crucially — ``loggamma`` for complex intervals, but no interval ζ.
    :meth:`zeta_box` therefore evaluates

        ζ(s) = Σ_{n<N} n^{−s} + N^{−s}/2 + N^{1−s}/(s−1)
               + Σ_{k=1}^{M} B_{2k}/(2k)! (s)_{2k−1} N^{−s−2k+1} + E_{M,N}(s)

    in interval arithmetic and inflates the result by the classical bound on
    |E_{M,N}|.  The bound is the "first omitted term × |s+2M+1|/(σ+2M+1)"
    estimate (Edwards §6.4); ``tests/test_rigor.py`` checks the resulting
    enclosures against mpmath's own high-precision ζ at many points, and against
    the Arb backend when it is installed.
    """

    name = "mpmath.iv"
    reason = "mpmath's own interval context (always available)"
    has_arb_nzeros = False

    @staticmethod
    def _ival(q: Fraction):
        """An interval provably containing the rational ``q``."""
        if q.denominator == 1:
            return iv.mpf(q.numerator)
        return iv.mpf(q.numerator) / iv.mpf(q.denominator)

    @classmethod
    def _span(cls, lo: Fraction, hi: Fraction):
        if lo == hi:
            return cls._ival(lo)
        a, b = cls._ival(lo), cls._ival(hi)
        return iv.mpf([_iv_bounds(a)[0], _iv_bounds(b)[1]])

    @staticmethod
    def _em_params(prec: int, abs_s: float) -> tuple[int, int]:
        """(N, M) for Euler–Maclaurin: N ≳ |s| is what makes the series useful."""
        dps = max(15, int(prec / _LOG2_10) + 5)
        M = max(8, int(0.55 * dps))
        N = max(2 * M, int(abs_s) + 4, dps)
        return N, M

    @classmethod
    def _zeta_iv(cls, sig, tau, prec: int):
        """ζ(σ+iτ) as a complex interval, σ/τ real intervals.  Rigorous.

        Valid for σ > 0 away from the pole at s = 1; this module only ever asks
        for σ ∈ [1/2, 2] at height T > 0, where s = 1 is not in the box.
        """
        s = iv.mpc(sig, tau)
        abs_s = float(_iv_bounds(abs(sig))[1]) + float(_iv_bounds(abs(tau))[1])
        N, M = cls._em_params(prec, abs_s)

        total = iv.mpc(0)
        for n in range(1, N):
            total += iv.exp(-s * iv.log(iv.mpf(n)))
        log_n = iv.log(iv.mpf(N))
        total += iv.exp(-s * log_n) / 2
        total += iv.exp((1 - s) * log_n) / (s - 1)

        poch = s  # (s)_1
        for k in range(1, M + 1):
            c = _bern_coeff(k)
            coeff = iv.mpf(c.numerator) / iv.mpf(c.denominator)
            total += coeff * poch * iv.exp((-s - (2 * k - 1)) * log_n)
            poch = poch * (s + (2 * k - 1)) * (s + 2 * k)  # (s)_{2k+1}

        # |E_{M,N}(s)| <= |(s+2M+1)/(sigma+2M+1)| * |first omitted term|.
        # Every factor is an interval, and taking the interval's upper endpoint
        # gives an upper bound valid for *every* s in the box.  The remainder is
        # then added as a disc, enclosed by a square (which contains the disc).
        c = _bern_coeff(M + 1)
        coeff = iv.mpf(abs(c.numerator)) / iv.mpf(c.denominator)
        first_omitted = coeff * abs(poch) * abs(iv.exp((-s - (2 * M + 1)) * log_n))
        bound = abs(s + (2 * M + 1)) / abs(sig + (2 * M + 1)) * first_omitted
        r = _iv_bounds(bound)[1]
        return total + iv.mpc(iv.mpf([-r, r]), iv.mpf([-r, r]))

    @classmethod
    def _theta_iv(cls, t):
        """θ(t) = Im log Γ(1/4 + it/2) − (t/2) log π as an interval.

        The purely-real case is special-cased: log Γ(1/4) is real, so
        Im log Γ = 0 exactly and θ(0) = 0.  (It also has to be special-cased —
        ``mpmath.libmp.mpci_gamma`` crashes on a complex interval whose
        imaginary part is exactly zero, passing the complex pair where the real
        interval is expected.  Verified against mpmath 1.3.0.)
        """
        half_t = t / 2
        lo, hi = _iv_bounds(half_t)
        if lo == 0 and hi == 0:
            im = iv.mpf(0)
        else:
            im = iv.loggamma(iv.mpc(iv.mpf(1) / 4, half_t)).imag
        return im - half_t * iv.log(iv.pi)

    @classmethod
    def hardy_Z(cls, lo: Fraction, hi: Fraction, prec: int) -> tuple:
        with _iv_prec(prec):
            t = cls._span(lo, hi)
            theta = cls._theta_iv(t)
            z = cls._zeta_iv(iv.mpf(1) / 2, t, prec)
            out = iv.cos(theta) * z.real - iv.sin(theta) * z.imag
            return _iv_bounds(out)

    @classmethod
    def rs_theta(cls, lo: Fraction, hi: Fraction, prec: int) -> tuple:
        with _iv_prec(prec):
            out = cls._theta_iv(cls._span(lo, hi))
            return _iv_bounds(out)

    @classmethod
    def zeta_native(cls, x_lo: Fraction, x_hi: Fraction, y: Fraction, prec: int):
        with _iv_prec(prec):
            return cls._zeta_iv(cls._span(x_lo, x_hi), cls._ival(y), prec)

    @staticmethod
    def native_bounds(z, prec: int) -> tuple:
        return _iv_bounds(z.real) + _iv_bounds(z.imag)

    @staticmethod
    def native_excludes_zero(z, prec: int) -> bool:
        rl, rh, il, ih = _iv_bounds(z.real) + _iv_bounds(z.imag)
        return not (rl <= 0 <= rh and il <= 0 <= ih)

    @staticmethod
    def native_div(zb, za, prec: int):
        with _iv_prec(prec):
            return zb / za

    @staticmethod
    def native_arg_right_half(z, prec: int):
        """Enclosure of Arg z, but only when Re z > 0 is *proven*; else None.

        ``mpmath.iv.atan2`` is the rigorous ``libmp.mpi_atan2``, which rounds its
        endpoints outward (``round_floor`` / ``round_ceiling``); restricting to
        the right half-plane keeps it away from the branch cut entirely.
        """
        with _iv_prec(prec):
            if not z.real.a > 0:
                return None
            return _iv_bounds(iv.atan2(z.imag, z.real))

    @classmethod
    def zeta_box(cls, x_lo: Fraction, x_hi: Fraction, y: Fraction, prec: int) -> tuple:
        return cls.native_bounds(cls.zeta_native(x_lo, x_hi, y, prec), prec)


# ---------------------------------------------------------------------------
# backend selection
# ---------------------------------------------------------------------------

_BACKENDS: dict[str, type] = {"mpmath.iv": _MPIntervalBackend}
if _HAVE_FLINT:  # pragma: no cover - machine dependent
    _BACKENDS["python-flint"] = _FlintBackend

#: The ball-arithmetic engine used by default: ``"python-flint"`` when the
#: Arb-backed wheel imports, otherwise ``"mpmath.iv"``.
BACKEND: str = "python-flint" if _HAVE_FLINT else "mpmath.iv"

#: Why :data:`BACKEND` is what it is — quote this verbatim when reporting.
BACKEND_REASON: str = _FLINT_REASON if _HAVE_FLINT else (
    f"{_FLINT_REASON}; falling back to mpmath's interval context"
)


def available_backends() -> list[str]:
    """Names of every ball-arithmetic backend importable in this interpreter."""
    return sorted(_BACKENDS)


def _pick(backend: str | None):
    if backend is None:
        backend = BACKEND
    try:
        return _BACKENDS[backend]
    except KeyError:
        raise ValueError(
            f"unknown backend {backend!r}; available: {available_backends()}"
        ) from None


# ---------------------------------------------------------------------------
# enclosures of Hardy's Z
# ---------------------------------------------------------------------------


def enclose_Z(t, prec_bits: int = 128, backend: str | None = None) -> tuple:
    """A **rigorous enclosure** ``(lo, hi)`` of Hardy's Z(t): ``lo ≤ Z(t) ≤ hi``.

    ``t`` is converted to its exact rational value first (see :func:`_exact`),
    so the enclosure is of Z at precisely the point the caller named — a float
    argument means the dyadic rational that float really is.

    Z(t) = e^{iθ(t)} ζ(1/2+it) with θ(t) = Im log Γ(1/4+it/2) − (t/2) log π is
    evaluated entirely in ball arithmetic: log Γ, ζ, exp and π all carry their
    own error bars and the product propagates them.  The returned bounds are
    exact mpmath ``mpf`` values (the dyadic endpoints of the ball), so
    ``lo > 0`` and ``hi < 0`` are exact comparisons.

    Measured widths at t = 100 (see :func:`enclosure_width_report`), pinned by
    ``tests/test_rigor.py``:

        bits   python-flint      mpmath.iv
          32     1.9e-08          2.4e-06
          64     3.0e-18          5.6e-16
         128     1.6e-37          3.1e-35
         256     5.5e-76          1.8e-71

    Examples
    --------
    >>> lo, hi = enclose_Z(100.0, 256)          # doctest: +SKIP
    >>> lo < mpmath.siegelz(100) < hi           # doctest: +SKIP
    True
    """
    q = _exact(t)
    return _pick(backend).hardy_Z(q, q, int(prec_bits))


def enclose_rs_theta(t, prec_bits: int = 128, backend: str | None = None) -> tuple:
    """A rigorous enclosure ``(lo, hi)`` of the Riemann–Siegel phase θ(t)."""
    q = _exact(t)
    return _pick(backend).rs_theta(q, q, int(prec_bits))


def proven_sign(
    t,
    prec_bits: int = 64,
    max_escalations: int = 6,
    backend: str | None = None,
) -> int:
    """+1 or −1 if the sign of Z(t) is **proven**; 0 if it cannot be decided.

    The enclosure ``[lo, hi]`` of Z(t) is computed at ``prec_bits``.  If
    ``lo > 0`` the true value is positive — that is a proof, not an estimate.
    If ``hi < 0`` it is negative.  Otherwise the enclosure straddles zero, the
    sign is *unknown*, the precision is doubled and the attempt repeated, up to
    ``max_escalations`` times.  If it still straddles zero the function returns
    **0**: the honest answer, "not decided".

    It never guesses.  At an exact zero of Z no precision suffices and 0 is the
    permanent answer, which is correct — Z really has no sign there.  This is
    the safe failure mode the whole module is built around, and
    ``tests/test_rigor.py`` exercises it by asking for an absurdly low precision.
    """
    adapter = _pick(backend)
    q = _exact(t)
    prec = max(int(prec_bits), 2)
    for _ in range(int(max_escalations) + 1):
        try:
            lo, hi = adapter.hardy_Z(q, q, prec)
        except ArithmeticError:
            # A backend that cannot produce a bound at all has told us nothing;
            # that is "undecided at this precision", not a licence to guess.
            prec *= 2
            continue
        if lo > 0:
            return 1
        if hi < 0:
            return -1
        prec *= 2
    return 0


# ---------------------------------------------------------------------------
# certified sign-change counting
# ---------------------------------------------------------------------------


def _mean_spacing(t: float) -> float:
    """Mean gap between consecutive zero ordinates near height t: 2π/log(t/2π)."""
    t = max(float(t), 10.0)
    return 2.0 * math.pi / math.log(t / (2.0 * math.pi))


def certified_sign_changes(
    t0,
    t1,
    n_samples: int | None = None,
    prec_bits: int = 64,
    max_escalations: int = 6,
    backend: str | None = None,
) -> dict:
    """Count sign changes of Z on [t0, t1] using **proven** signs only.

    Z is sampled on a uniform grid of exact rational abscissae and each sample's
    sign is established by :func:`proven_sign`.  Consecutive samples whose
    proven signs differ bracket a zero of Z — hence a zero of ζ *on the critical
    line*, since |Z| = |ζ(1/2+it)| — and that bracketing is a theorem: Z is
    continuous and really does change sign there.

    Undecided samples do not invalidate the count; they only break the chain.
    The counter compares each proven sign with the **previous proven sign**, so
    a change straddling an undecided point is still counted (there is genuinely
    a zero between them).  The count is therefore always a rigorous *lower
    bound* for the number of critical-line zeros in (t0, t1) — a sign-change
    scan can miss zeros (two in one grid cell), never invent them.

    ``certified`` is True only when **every** sampled sign was proven.

    Returns
    -------
    dict with ``'changes'``, ``'undecided_points'`` (the offending t as floats),
    ``'certified'``, plus ``'t0'``, ``'t1'``, ``'n_samples'``, ``'prec_bits'``,
    ``'max_escalations'``, ``'backend'`` and ``'wall_seconds'``.
    """
    started = time.time()
    adapter = _pick(backend)
    a, b = _exact(t0), _exact(t1)
    if b <= a:
        return {
            "changes": 0,
            "undecided_points": [],
            "certified": True,
            "t0": float(a),
            "t1": float(b),
            "n_samples": 0,
            "prec_bits": int(prec_bits),
            "max_escalations": int(max_escalations),
            "backend": adapter.name,
            "wall_seconds": time.time() - started,
        }
    if n_samples is None:
        step = _mean_spacing(float(b)) / 20.0
        n_samples = int(float(b - a) / step) + 2
    n_samples = max(int(n_samples), 2)

    changes = 0
    undecided: list[float] = []
    last = 0
    for k in range(n_samples):
        t = a + (b - a) * Fraction(k, n_samples - 1)
        s = proven_sign(
            t, prec_bits=prec_bits, max_escalations=max_escalations, backend=adapter.name
        )
        if s == 0:
            undecided.append(float(t))
            continue
        if last != 0 and s != last:
            changes += 1
        last = s

    return {
        "changes": changes,
        "undecided_points": undecided,
        "certified": not undecided,
        "t0": float(a),
        "t1": float(b),
        "n_samples": n_samples,
        "prec_bits": int(prec_bits),
        "max_escalations": int(max_escalations),
        "backend": adapter.name,
        "wall_seconds": time.time() - started,
    }


# ---------------------------------------------------------------------------
# certified N(T) by the argument principle
# ---------------------------------------------------------------------------


def _segment_delta(adapter, xa: Fraction, xb: Fraction, y: Fraction, prec: int, cache: dict):
    """Certified variation of arg ζ along the segment xa → xb at height y.

    Returns ``(lo, hi)`` enclosing the true continuous variation, or ``None`` if
    this segment cannot be certified at this precision (caller subdivides).

    Two conditions are checked, and together they make the answer a theorem:

    1. **ζ has no zero on the segment.**  ζ is enclosed over the whole segment
       at once (the abscissa is an interval, so the enclosure covers every point
       of the segment), and the enclosure is checked to miss the origin.  A
       compact convex set missing 0 lies in an open half-plane through 0 — if it
       contained p and −λp it would contain 0 — so arg varies by strictly less
       than π along the segment: |Δ| < π.
    2. **the quotient lies in the right half-plane.**  With
       q = ζ(xb+iy)/ζ(xa+iy), a proven Re q > 0 gives |Arg q| < π/2 and keeps
       the computation away from the branch cut entirely.  Δ ≡ Arg q (mod 2π),
       and since |Δ| < π and |Arg q| < π/2, necessarily **Δ = Arg q**.

    Subdividing drives q → 1, so both conditions hold on a fine enough grid
    wherever ζ has no zero on the contour.  No "the jump was probably below π"
    heuristic is used anywhere.
    """

    def zval(x: Fraction):
        got = cache.get(x)
        if got is None:
            got = adapter.zeta_native(x, x, y, prec)
            cache[x] = got
        return got

    lo, hi = (xa, xb) if xa <= xb else (xb, xa)
    if not adapter.native_excludes_zero(adapter.zeta_native(lo, hi, y, prec), prec):
        return None
    q = adapter.native_div(zval(xb), zval(xa), prec)
    return adapter.native_arg_right_half(q, prec)


def certified_zero_count(
    T,
    prec_bits: int = 192,
    max_segments: int = 4096,
    backend: str | None = None,
    cross_check: bool = True,
) -> dict:
    """Certified N(T) = #{ρ : ζ(ρ) = 0, 0 < Im ρ < T} by the argument principle.

    The identity used is the exact Riemann–von Mangoldt formula

        N(T) = 1 + θ(T)/π + S(T),     S(T) = (1/π)·Δ arg ζ  along  2 → 2+iT → 1/2+iT

    (see :func:`zeta.zeros.N_of_T` for the contour derivation).  Everything on
    the right is enclosed:

    * **θ(T)** from Arb's / mpmath's interval log Γ;
    * **the vertical leg** 2 → 2+iT analytically: |ζ(2+iy) − 1| ≤ Σ_{n≥2} n^{−2}
      = ζ(2) − 1 = 0.6449… < 1 for *every* real y, so ζ(2+iy) stays inside the
      disc D(1, 0.645), never vanishes, and arg never leaves (−π/2, π/2).  The
      whole leg's variation is therefore the single value arg ζ(2+iT), and the
      constant ζ(2) − 1 < 1 is itself re-verified by ball arithmetic on every
      call rather than trusted;
    * **the horizontal leg** 2 → 1/2 at height T by adaptive subdivision, each
      sub-segment certified by :func:`_segment_delta` — ζ enclosed over the
      whole sub-segment to prove it has no zero there (so |Δ| < π), and the
      endpoint quotient checked to have positive real part (so Δ is exactly the
      principal argument).  No "the jump was probably less than π" heuristic is
      involved; a sub-segment that fails either test is split, and the routine
      reports failure rather than guessing if it runs out of budget.

    The result is an interval enclosing N(T).  N(T) is an integer, so the count
    is **proven** exactly when the interval contains exactly one integer.

    Residual assumptions, stated plainly: the backend's ball arithmetic is
    correct; the Riemann–von Mangoldt identity and Σ_{n≥2} n^{−2} = ζ(2) − 1 are
    correct.  Everything else in the chain is computed with error bars.  No step
    of the computation itself is left uncertified on either backend — but
    ``uncertified_steps`` is returned regardless, empty on success and naming
    the step on failure, and ``certified`` is False whenever it is non-empty.

    Cross-checks are reported under ``'cross_checks'``: mpmath's ``backlunds``
    and ``nzeros`` (fast, accurate, **not** rigorous — flagged
    ``mpmath_rigorous: False``), and on the Arb backend Arb's own
    ``zeta_nzeros``, which is a genuinely independent *rigorous* route to the
    same integer via Turing's method.

    Returns
    -------
    dict with ``'T'``, ``'N_T'`` (int or None), ``'N_T_enclosure'``,
    ``'S_T_enclosure'``, ``'theta_enclosure'``, ``'certified'``,
    ``'uncertified_steps'``, ``'n_segments'``, ``'prec_bits'``, ``'backend'``,
    ``'cross_checks'`` and ``'wall_seconds'``.
    """
    started = time.time()
    adapter = _pick(backend)
    prec = int(prec_bits)
    Tq = _exact(T)
    uncertified: list[str] = []

    if Tq <= 0:
        return {
            "T": float(Tq),
            "N_T": 0,
            "N_T_enclosure": (mp.mpf(0), mp.mpf(0)),
            "S_T_enclosure": (mp.mpf(0), mp.mpf(0)),
            "theta_enclosure": (mp.mpf(0), mp.mpf(0)),
            "certified": True,
            "uncertified_steps": [],
            "n_segments": 0,
            "prec_bits": prec,
            "backend": adapter.name,
            "cross_checks": {},
            "wall_seconds": time.time() - started,
        }

    # --- the lemma behind the vertical leg, re-verified numerically ---------
    z2 = adapter.zeta_box(Fraction(2), Fraction(2), Fraction(0), prec)
    if not (z2[1] - 1 < 1 and z2[0] > 1):
        uncertified.append("vertical-leg lemma |zeta(2+iy)-1| <= zeta(2)-1 < 1 not verified")

    two, half = Fraction(2), Fraction(1, 2)
    cache: dict[Fraction, object] = {}

    # --- vertical leg 2 -> 2+iT --------------------------------------------
    vertical = adapter.native_arg_right_half(adapter.zeta_native(two, two, Tq, prec), prec)
    if vertical is None:
        uncertified.append("arg zeta(2+iT) could not be certified (Re <= 0?)")

    # --- horizontal leg 2 -> 1/2 -------------------------------------------
    n_segments = 0
    deltas: list[tuple] = []
    stack: list[tuple[Fraction, Fraction]] = [(two, half)]
    failed = False
    while stack:
        xa, xb = stack.pop()
        d = _segment_delta(adapter, xa, xb, Tq, prec, cache)
        if d is not None:
            deltas.append(d)
            n_segments += 1
            continue
        if n_segments + len(stack) >= max_segments:
            failed = True
            break
        mid = (xa + xb) / 2
        stack.append((xa, mid))
        stack.append((mid, xb))
    if failed:
        uncertified.append(
            f"horizontal leg not certified within max_segments={max_segments} "
            "(T may sit on a zero ordinate, or prec_bits is too low)"
        )

    theta_lo, theta_hi = adapter.rs_theta(Tq, Tq, prec)

    n_int = None
    s_lo = s_hi = n_lo = n_hi = None
    if vertical is not None and not failed:
        # The outward-rounding interval sum is itself done in mpmath.iv, which
        # is rigorous for +, − and ÷ on both backends.
        with _iv_prec(prec + 32):
            total = iv.mpf([vertical[0], vertical[1]])
            for lo, hi in deltas:
                total = total + iv.mpf([lo, hi])
            s_iv = total / iv.pi
            n_iv = 1 + iv.mpf([theta_lo, theta_hi]) / iv.pi + s_iv
            s_lo, s_hi = _iv_bounds(s_iv)
            n_lo, n_hi = _iv_bounds(n_iv)

    if n_lo is not None:
        # Count the integers in [n_lo, n_hi] *arithmetically*.  Enumerating them
        # would be O(width) — an enclosure a million wide (low prec_bits at a
        # large height) would hang instead of reporting failure — and an
        # unbounded enclosure cannot be enumerated at all.  Exact rational
        # floor/ceil also keeps the endpoints out of mp's working precision,
        # which matters once N(T) exceeds 2**53.
        if not (mp.isfinite(n_lo) and mp.isfinite(n_hi)):
            uncertified.append(
                "N(T) enclosure is unbounded (the backend could not bound a "
                "step); raise prec_bits"
            )
        else:
            k_lo = math.ceil(_exact(n_lo))
            k_hi = math.floor(_exact(n_hi))
            n_cands = k_hi - k_lo + 1
            if n_cands == 1:
                n_int = k_lo
            else:
                uncertified.append(
                    f"N(T) enclosure [{mp.nstr(n_lo, 12)}, {mp.nstr(n_hi, 12)}] "
                    f"contains {max(n_cands, 0)} integers; raise prec_bits"
                )

    checks: dict = {}
    if cross_check:
        if getattr(adapter, "has_arb_nzeros", False):
            try:
                checks["arb_zeta_nzeros"] = adapter.arb_zeta_nzeros(Tq, prec)
                checks["arb_zeta_nzeros_rigorous"] = True
            except Exception as exc:  # pragma: no cover
                checks["arb_zeta_nzeros"] = f"failed: {exc}"
        try:
            with mp.workdps(max(25, int(prec / _LOG2_10))):
                checks["mpmath_backlunds"] = mp.backlunds(mp.mpf(float(Tq)))
                checks["mpmath_nzeros"] = int(mp.nzeros(mp.mpf(float(Tq))))
            checks["mpmath_rigorous"] = False
        except Exception as exc:  # pragma: no cover
            checks["mpmath_nzeros"] = f"failed: {exc}"

    return {
        "T": float(Tq),
        "N_T": n_int,
        "N_T_enclosure": (n_lo, n_hi),
        "S_T_enclosure": (s_lo, s_hi),
        "theta_enclosure": (theta_lo, theta_hi),
        "certified": n_int is not None and not uncertified,
        "uncertified_steps": uncertified,
        "n_segments": n_segments,
        "prec_bits": prec,
        "backend": adapter.name,
        "cross_checks": checks,
        "wall_seconds": time.time() - started,
    }


# ---------------------------------------------------------------------------
# the flagship: certified RH verification up to height T
# ---------------------------------------------------------------------------


#: The run parameters that can change what :func:`verify_rh_certified` returns.
#: They are all in the cache filename *and* re-checked against the file's own
#: contents on load — a filename is a hint, the recorded parameters are the
#: authority.  ``max_escalations`` and ``max_samples`` belong here: at fixed
#: ``prec_bits`` a run with more escalations can certify where a run with none
#: cannot, so leaving them out would let a certified file be replayed for an
#: uncertifiable request — a manufactured ``certified: True``.
_CACHE_KEYS = (
    "T",
    "backend",
    "prec_bits",
    "count_prec_bits",
    "requested_n_samples",
    "max_escalations",
    "max_samples",
)


def _cache_key(
    T: float,
    backend: str,
    prec_bits: int,
    count_bits: int,
    samples,
    max_escalations: int,
    max_samples: int,
) -> dict:
    """The full parameter dict identifying one :func:`verify_rh_certified` run."""
    return {
        "T": float(T),
        "backend": backend,
        "prec_bits": int(prec_bits),
        "count_prec_bits": int(count_bits),
        "requested_n_samples": None if samples is None else int(samples),
        "max_escalations": int(max_escalations),
        "max_samples": int(max_samples),
    }


def _cache_path(key: dict) -> str:
    """``data/rigor_verify_<T>_<backend>_<bits>_<countbits>_<n>_<esc>_<max>.json``.

    Every parameter that can change the answer is in the filename — see
    :data:`_CACHE_KEYS` — so a stale file cannot masquerade as a fresh result
    (house rule: cache keys encode parameters).  The loader additionally
    verifies that the file's *recorded* parameters match, so even a
    hand-renamed or hand-edited file is rejected rather than trusted.
    Derived from ``__file__``; no absolute path is committed.
    """
    tag = "_".join(
        [
            f"{key['T']:g}",
            key["backend"].replace(".", "-"),
            str(key["prec_bits"]),
            str(key["count_prec_bits"]),
            str(key["requested_n_samples"]),
            str(key["max_escalations"]),
            str(key["max_samples"]),
        ]
    )
    return os.path.join(DATA_DIR, f"rigor_verify_{tag}.json")


def _with_floating_comparison(result: dict, Tq: Fraction, compare: bool) -> dict:
    """Attach the *non-rigorous* :func:`zeta.zeros.verify_rh_up_to` result.

    Reported side by side so the reader can see exactly what rigor bought: the
    two should agree on the numbers, and differ only in what may be concluded
    from them.
    """
    if not compare:
        return result
    from zeta.zeros import verify_rh_up_to

    fp = verify_rh_up_to(float(Tq))
    result["floating_point"] = {
        "n_sign_changes": fp["n_sign_changes"],
        "N_T": fp["N_T"],
        "all_on_line": fp["all_on_line"],
        "n_samples": fp["n_samples"],
        "rigorous": False,
    }
    result["agrees_with_floating_point"] = (
        fp["N_T"] == result["N_T"]
        and fp["n_sign_changes"] == result["certified_sign_changes"]
    )
    return result


def verify_rh_certified(
    T,
    prec_bits: int = 64,
    count_prec_bits: int = 192,
    n_samples: int | None = None,
    max_samples: int = 200_001,
    max_escalations: int = 8,
    backend: str | None = None,
    compare_floating: bool = True,
    cache: bool = True,
    verbose: bool = False,
) -> dict:
    """Rigorous counterpart of :func:`zeta.zeros.verify_rh_up_to`.

    Same theorem, no floating-point trust gap.  Let m be the number of sign
    changes of Z on (0, T) established from **proven** signs, and N(T) the
    **certified** zero count from :func:`certified_zero_count`.  Each sign change
    is a zero of ζ on the critical line, the zeros are distinct, so m ≤ N(T)
    always; if m = N(T) then every zero counted by N(T) is one of those
    critical-line sign changes, hence

    * no zero with 0 < γ < T lies off the critical line,
    * no such zero has even order (Z would not change sign there),
    * every such zero is simple.

    In :func:`zeta.zeros.verify_rh_up_to` the same argument is run on ordinary
    mpmath floats, so the conclusion is contingent on every sign evaluation
    being right — overwhelmingly likely, but not proved.  Here both m and N(T)
    are outputs of ball arithmetic: a sign is only counted once its enclosure
    excludes 0, and N(T) only once its enclosure contains a unique integer.

    Honest scope (repo rule): this proves nothing about RH.  It is a statement
    about a finite interval, and by Littlewood's theorem no finite computation
    can be evidence either way (docs/08).

    Rigor is not even slower here.  On the machine this was developed on (an
    Apple-silicon laptop, python-flint backend), the certified route beat the
    floating-point one by more than an order of magnitude — 0.20 s vs 2.6 s at
    T = 100, 0.84 s vs 45 s at T = 300, 5.1 s vs 437 s at T = 1000 — because Arb
    evaluates ζ far faster than mpmath does, and the certified N(T) needs only
    ~20 contour sub-segments.  Those numbers are hardware- and version-specific
    and are **not** pinned by a test; only the mathematics is.

    Returns
    -------
    dict with ``'T'``, ``'certified_sign_changes'``, ``'N_T'``,
    ``'all_on_line'``, ``'certified'``, ``'uncertified_steps'``, ``'backend'``,
    ``'wall_seconds'``, plus ``'undecided_points'``, ``'n_samples'``,
    ``'prec_bits'``, ``'count_prec_bits'``, ``'N_T_enclosure'``,
    ``'cross_checks'``, the run parameters ``'requested_n_samples'``,
    ``'max_escalations'``, ``'max_samples'`` (these seven together are the cache
    key, :data:`_CACHE_KEYS`) and — when ``compare_floating`` —
    ``'floating_point'``, the corresponding non-rigorous result from
    :func:`zeta.zeros.verify_rh_up_to`.

    A result is cached under ``data/rigor_verify_*.json`` keyed by every *call*
    parameter that can change it, and the loader re-checks the parameters
    recorded inside the file before reusing it, so a certificate obtained with
    a generous escalation budget can never be replayed for a stingier request.
    What the key does **not** record is the version of this module or of the
    ball library that produced the file — so a cached certificate is only as
    trustworthy as the checkout that wrote it.  For that reason
    ``data/rigor_verify_*.json`` is gitignored: certificates are claims, not
    data, and a fresh clone recomputes rather than inherits them.  Pass
    ``cache=False`` to force recomputation in place.

    ``wall_seconds`` times the **certified** computation only; the optional
    floating-point comparison is not counted, and a cached result carries the
    wall time of the run that produced it (``from_cache`` says which).
    """
    started = time.time()
    adapter = _pick(backend)
    Tq = _exact(T)
    key = _cache_key(
        float(Tq),
        adapter.name,
        prec_bits,
        count_prec_bits,
        n_samples,
        max_escalations,
        max_samples,
    )
    path = _cache_path(key)
    result = None
    if cache and os.path.isfile(path):
        try:
            with open(path) as fh:
                blob = json.load(fh)
            # A cached certificate is only reusable if it was produced by
            # *exactly* this request.  Anything else — a renamed file, an older
            # schema, a run with different escalation budget — is recomputed.
            if all(blob.get(k) == key[k] for k in _CACHE_KEYS):
                blob["from_cache"] = True
                result = blob
        except Exception:
            result = None
    if result is not None:
        return _with_floating_comparison(result, Tq, compare_floating)

    count = certified_zero_count(Tq, prec_bits=count_prec_bits, backend=adapter.name)
    exact = count["N_T"]

    if n_samples is None:
        step = _mean_spacing(float(Tq)) / 20.0
        n_samples = max(int(float(Tq) / step) + 2, 16)

    scan = certified_sign_changes(
        0,
        Tq,
        n_samples=n_samples,
        prec_bits=prec_bits,
        max_escalations=max_escalations,
        backend=adapter.name,
    )
    while exact is not None and scan["changes"] < exact and scan["n_samples"] < max_samples:
        n_samples = 2 * (scan["n_samples"] - 1) + 1
        if verbose:
            print(
                f"  {scan['n_samples']} samples -> {scan['changes']} proven sign "
                f"changes (need {exact}); refining"
            )
        scan = certified_sign_changes(
            0,
            Tq,
            n_samples=n_samples,
            prec_bits=prec_bits,
            max_escalations=max_escalations,
            backend=adapter.name,
        )

    uncertified = list(count["uncertified_steps"])
    if not scan["certified"]:
        uncertified.append(
            f"{len(scan['undecided_points'])} sampled sign(s) of Z undecided at "
            f"prec_bits={prec_bits} with {max_escalations} escalations"
        )
    all_on_line = exact is not None and scan["changes"] == exact
    if exact is not None and not all_on_line:
        uncertified.append(
            f"only {scan['changes']} proven sign changes found for N(T) = {exact}; "
            "the grid missed zeros (nothing is disproved, nothing is proved)"
        )

    result = {
        "T": float(Tq),
        "certified_sign_changes": scan["changes"],
        "N_T": exact,
        "all_on_line": all_on_line,
        "certified": bool(all_on_line and not uncertified),
        "uncertified_steps": uncertified,
        "backend": adapter.name,
        "wall_seconds": time.time() - started,
        "undecided_points": scan["undecided_points"],
        "n_samples": scan["n_samples"],
        "prec_bits": int(prec_bits),
        "count_prec_bits": int(count_prec_bits),
        # the full cache key, recorded so the loader can verify it (see
        # ``_CACHE_KEYS``) rather than trusting the filename
        "requested_n_samples": key["requested_n_samples"],
        "max_escalations": int(max_escalations),
        "max_samples": int(max_samples),
        "N_T_enclosure": [
            None if v is None else mp.nstr(v, 25) for v in count["N_T_enclosure"]
        ],
        "N_T_enclosure_width": (
            None
            if count["N_T_enclosure"][0] is None
            else float(count["N_T_enclosure"][1] - count["N_T_enclosure"][0])
        ),
        "n_segments": count["n_segments"],
        "cross_checks": {
            k: (str(v) if not isinstance(v, (int, bool, type(None))) else v)
            for k, v in count["cross_checks"].items()
        },
        "from_cache": False,
    }

    if cache:
        try:
            os.makedirs(DATA_DIR, exist_ok=True)
            tmp = path + ".tmp"
            with open(tmp, "w") as fh:
                json.dump(result, fh, indent=1)
            os.replace(tmp, path)
        except Exception:  # pragma: no cover - caching must never break a proof
            pass

    _with_floating_comparison(result, Tq, compare_floating)

    if verbose:
        print(f"verify_rh_certified(T={float(Tq)})  backend={adapter.name}")
        print(f"  certified N(T)              : {exact}")
        print(f"  proven sign changes of Z    : {scan['changes']}  "
              f"({scan['n_samples']} samples, {prec_bits} bits)")
        print(f"  undecided samples           : {len(scan['undecided_points'])}")
        if result["certified"]:
            print(
                f"  ==> PROVEN: all {exact} zeros with 0 < γ < {float(Tq)} are simple "
                "and on the critical line (modulo the correctness of the ball library)."
            )
        else:
            print(f"  ==> NOT certified: {uncertified}")
        print(f"  wall time                   : {result['wall_seconds']:.2f} s")
    return result


# ---------------------------------------------------------------------------
# the cost curve of rigor
# ---------------------------------------------------------------------------


def enclosure_width_report(
    t_values: Sequence,
    prec_bits_list: Sequence[int],
    backend: str | None = None,
) -> list[dict]:
    """How the enclosure width of Z(t) shrinks with working precision.

    One row per (t, prec_bits) pair, in the order ``t`` varies slowest:

    ``'t'``, ``'prec_bits'``, ``'lo'``, ``'hi'``, ``'width'``,
    ``'width_log10'`` (log₁₀ of the width, −inf for an exact ball),
    ``'proven_digits'`` (log₁₀|mid| − log₁₀ width, i.e. how many significant
    digits of Z(t) are *certified*), ``'sign_proven'``, ``'seconds'`` and
    ``'backend'``.

    This is the honest cost curve of rigor: width falls geometrically in the
    bit count, so proving the sign of Z at a point where |Z| ~ 10^{−d} costs
    about 3.33·d extra bits on top of whatever the evaluation itself needs.
    """
    adapter = _pick(backend)
    rows: list[dict] = []
    for t in t_values:
        q = _exact(t)
        for prec in prec_bits_list:
            t0 = time.time()
            try:
                lo, hi = adapter.hardy_Z(q, q, int(prec))
                err = None
            except ArithmeticError as exc:  # pragma: no cover
                lo = hi = None
                err = str(exc)
            elapsed = time.time() - t0
            row = {
                "t": float(q),
                "prec_bits": int(prec),
                "lo": lo,
                "hi": hi,
                "backend": adapter.name,
                "seconds": elapsed,
                "error": err,
            }
            row["width"] = row["width_log10"] = row["proven_digits"] = None
            row["sign_proven"] = False
            if lo is not None:
                with mp.workdps(40):
                    finite = mp.isfinite(lo) and mp.isfinite(hi)
                    width = hi - lo if finite else mp.inf
                    row["width"] = width
                    if not finite:
                        row["width_log10"] = mp.inf
                        row["proven_digits"] = float("-inf")
                    elif width == 0:  # an exactly representable ball
                        row["width_log10"] = mp.mpf("-inf")
                        row["proven_digits"] = float("inf")
                    else:
                        mid = (hi + lo) / 2
                        row["width_log10"] = mp.log10(width)
                        row["proven_digits"] = (
                            float(mp.log10(abs(mid)) - mp.log10(width))
                            if mid != 0
                            else float("-inf")
                        )
                row["sign_proven"] = bool(lo > 0 or hi < 0)
            rows.append(row)
    return rows


# ---------------------------------------------------------------------------
# certified Weil positivity
# ---------------------------------------------------------------------------


def enclose_weil_functional(
    h_cert: Callable,
    g_cert: Callable,
    n_max: int,
    prec_bits: int = 128,
    backend: str | None = None,
) -> tuple:
    """Rigorous enclosure of the Weil functional W(h) = pole + arch + prime.
    
    This function evaluates the arithmetic side of the Riemann-Weil explicit
    formula using full interval/ball arithmetic. The test functions ``h_cert``
    and ``g_cert`` MUST be written to accept and return rigorous intervals
    appropriate for the chosen backend (e.g., ``flint.acb`` or ``mpmath.iv.mpc``).
    
    WARNING: The archimedean integral requires a certified integration backend,
    which is currently only available if ``python-flint`` is installed and
    a certified integration wrapper is implemented. If using ``mpmath.iv``,
    the archimedean term will raise NotImplementedError.
    
    Returns
    -------
    ``(lo, hi)``: An enclosure of W(h) as exact mpmath mpf values.
    """
    adapter = _pick(backend)
    
    if adapter.name == "mpmath.iv":
        raise NotImplementedError(
            "Certified archimedean integral is not implemented for mpmath.iv. "
            "Install python-flint for certified quadrature, or use the float version."
        )
    else:
        raise NotImplementedError(
            "Certified integration for python-flint is pending implementation."
        )


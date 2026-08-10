"""Tests for scripts/61_rung3_mirror.py — the bit-exact mirror of the Lean
rational interval layer used to stage the rung-3 certificate.

The mirror exists so that certificate generation can precompute every box
value in Python and emit it as a literal the Lean kernel then *checks*.  A
wrong mirror value therefore cannot weaken the certificate — the emitted
equality lemma simply fails to compile.  What it can do is waste hours of
kernel time before failing, so the mirror is pinned here two ways:

1. **Soundness against an independent oracle.**  Every box the mirror
   computes must contain the value mpmath computes by a completely
   different route (`Real.log` / `cpow` / complex inverse at dps = 40).
   This is the same "implement, then cross-check against an oracle" habit
   the rest of the suite uses.

2. **The measured dead end** (HANDOFF, 2026-08-10).  Boxed-`s` evaluation
   of the DH partial sum has width that grows like the sum of per-term
   variations — no cancellation — so it can never certify a *lower* bound
   on a segment box, at any subdivision that keeps the term count finite.
   `test_boxed_s_width_cannot_certify_a_lower_bound` pins that with
   numbers, which is why the certificate goes the max-modulus + Cauchy +
   mean-value route instead.  Upper bounds are unaffected (width only
   inflates them), which is exactly what that route needs.
"""

from __future__ import annotations

import importlib.util
import pathlib
from fractions import Fraction as F

import pytest
from mpmath import mp

_MIRROR = pathlib.Path(__file__).resolve().parents[1] / "scripts" / "61_rung3_mirror.py"
_spec = importlib.util.spec_from_file_location("rung3_mirror", _MIRROR)
mirror = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(mirror)

# The oracle zero, as the certificate's rational centre.
CRE = F(808517, 1000000)
CIM = F(85699348, 1000000)

TAYLOR_N = 20
COARSEN_P = 64
KE = 10


def _point(re: F, im: F) -> mirror.C:
    return mirror.C(mirror.iexact(re), mirror.iexact(im))


def _contains(box, lo_val, hi_val=None) -> bool:
    """Interval containment of a real value, in exact/float mixed form."""
    hi_val = lo_val if hi_val is None else hi_val
    return float(box.lo) <= lo_val and hi_val <= float(box.hi)


def test_mirror_logQ_encloses_the_true_log():
    """`logQ n k q` must contain `log q` — the binary reduction, mirrored."""
    with mp.workdps(40):
        for m in (2, 3, 7, 41, 350, 1201):
            k = m.bit_length()
            box = mirror.logQ(TAYLOR_N, k, F(m))
            true = mp.log(m)
            assert _contains(box, float(true)), f"log {m} escaped its box"


def test_log_taylor_order_20_is_too_coarse_for_the_certificate():
    """The parameter trap found before any kernel time was spent.

    `logQ n k q = k·log2I n + log1 n (q/2^k)`, so the box width is dominated
    by `k · width(log2I n) ≈ k · 2^{-n}` — at `n = 20` and `k ≈ 9` that is
    ~1.7e-5, which `dirichletTermBox` amplifies by `‖s‖ ≈ 85.7` into a
    per-term width of ~6e-5.  Summed over the ~500 terms of a rung-3 site
    (weighted by `m^{-σ}`, `Σ ≈ 17`) that is ~2.5e-2 — fifty times the
    certificate's entire `ε' = 5e-4` budget, so *even the centre inequality*
    would fail.  Order 40 costs one longer rational series per term and
    buys eleven orders of magnitude.  Pinned so the next generator run does
    not rediscover it after hours of kernel compute.
    """
    m, k = 350, 350 .bit_length()
    w20 = float((lambda b: b.hi - b.lo)(mirror.logQ(20, k, F(m))))
    w40 = float((lambda b: b.hi - b.lo)(mirror.logQ(40, k, F(m))))
    # the k·log2I term is the whole story
    log2_w = float((lambda b: b.hi - b.lo)(mirror.log2I(20)))
    assert w20 == pytest.approx(k * log2_w, rel=1e-3)
    # order 20 blows the epsilon budget; order 40 does not
    sigma_sum, norm_s, eps = 17.0, 85.7, 5e-4
    assert norm_s * w20 * sigma_sum > 10 * eps
    assert norm_s * w40 * sigma_sum < eps / 1000
    # and that is what the generator uses
    import importlib.util as _ilu
    _gen_spec = _ilu.spec_from_file_location(
        "rung3_gen",
        pathlib.Path(__file__).resolve().parents[1] / "scripts" / "60_rung3_generate.py")
    gen = _ilu.module_from_spec(_gen_spec)
    _gen_spec.loader.exec_module(gen)
    assert gen.TAYLOR_N >= 40


def test_mirror_term_boxes_enclose_the_true_power_at_a_point():
    """`dirichletTermBox` at a degenerate box must contain `m^{-s}` exactly."""
    with mp.workdps(40):
        s = mp.mpc(mp.mpf(CRE.numerator) / CRE.denominator,
                   mp.mpf(CIM.numerator) / CIM.denominator)
        S = _point(CRE, CIM)
        for m in (1, 2, 7, 41, 350):
            box = mirror.dirichletTermBox(TAYLOR_N, COARSEN_P, m.bit_length(),
                                          KE, m, S)
            true = mp.power(m, -s)
            assert _contains(box.re, float(mp.re(true))), f"Re {m}^-s escaped"
            assert _contains(box.im, float(mp.im(true))), f"Im {m}^-s escaped"


def test_mirror_term_boxes_enclose_every_sampled_point_of_a_wide_box():
    """A genuinely wide `S` must enclose `m^{-s}` for every `s` inside it."""
    with mp.workdps(40):
        w = F(1, 1000)
        S = mirror.C(mirror.I(CRE - w, CRE + w), mirror.I(CIM - w, CIM + w))
        for m in (3, 42):
            box = mirror.dirichletTermBox(TAYLOR_N, COARSEN_P, m.bit_length(),
                                          KE, m, S)
            for i in range(5):
                for j in range(5):
                    sre = CRE - w + 2 * w * F(i, 4)
                    sim = CIM - w + 2 * w * F(j, 4)
                    s = mp.mpc(mp.mpf(sre.numerator) / sre.denominator,
                               mp.mpf(sim.numerator) / sim.denominator)
                    true = mp.power(m, -s)
                    assert _contains(box.re, float(mp.re(true)))
                    assert _contains(box.im, float(mp.im(true)))


def test_mirror_complex_inverse_encloses_the_true_reciprocal():
    """`invC` mirrors `1/z = conj z / |z|²` and must enclose the truth."""
    with mp.workdps(40):
        w = F(1, 100)
        S = mirror.C(mirror.I(CRE - w, CRE + w), mirror.I(CIM - w, CIM + w))
        V = mirror.invC(mirror.inv5sBox(S))
        for i in (0, 1, 2):
            sre = CRE - w + w * F(i)
            s = mp.mpc(mp.mpf(sre.numerator) / sre.denominator,
                       mp.mpf(CIM.numerator) / CIM.denominator)
            true = 1 / (5 * (1 - s))
            assert _contains(V.re, float(mp.re(true)))
            assert _contains(V.im, float(mp.im(true)))


def test_mirror_normLower_and_normBound_bracket_the_true_norm():
    """`normLower ≤ ‖z‖ ≤ normBound` for every `z` the box contains."""
    with mp.workdps(40):
        s = mp.mpc(mp.mpf(CRE.numerator) / CRE.denominator,
                   mp.mpf(CIM.numerator) / CIM.denominator)
        S = _point(CRE, CIM)
        box = mirror.dirichletTermBox(TAYLOR_N, COARSEN_P, 6, KE, 41, S)
        true = abs(mp.power(41, -s))
        assert float(mirror.normLower(box)) <= float(true)
        assert float(true) <= float(mirror.normBound(box))


@pytest.mark.slow
def test_boxed_s_width_cannot_certify_a_lower_bound():
    """The recorded dead end, pinned with numbers (HANDOFF, 2026-08-10).

    Boxed-`s` evaluation of the DH partial sum accumulates one variation per
    term with no cancellation, so its width dwarfs the lower-bound headroom
    (~eps' = 5e-4) at any usable box extent — the reason the certificate
    routes lower bounds through Cauchy + the mean value theorem instead, and
    upper bounds (which width only inflates) through boxed evaluation.
    """
    K, eps = 12, 5e-4
    w = F(1, 4096)  # already a very fine boundary subdivision
    S = mirror.C(mirror.I(CRE - w, CRE + w), mirror.iexact(CIM))

    def partial_width(terms: int) -> float:
        acc = mirror.cexact(0, 0)
        for m in range(1, terms):
            acc = mirror.cadd(acc, mirror.term(m, S, TAYLOR_N, COARSEN_P, KE))
        return min(float(acc.re.hi - acc.re.lo), float(acc.im.hi - acc.im.lo))

    width = partial_width(5 * K)
    # measured ~0.04 at 5K = 60 terms and 2w = 1/2048: ~80x the headroom a
    # lower-bound certificate would have to beat, and this is the *easy* end
    assert width > 10 * eps, (
        f"partial-sum box width {width:.3g} at 5K={5 * K} terms, 2w=1/2048 — "
        "if this ever became small the direct lower-bound route would reopen"
    )
    # the wall is structural: per-term variations add, so width grows with K
    assert width > partial_width(5 * (K // 2))

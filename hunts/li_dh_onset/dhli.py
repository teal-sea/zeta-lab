"""The Cauchy route to Li coefficients, pointed at any completed L-function.

Why this file exists rather than a call into ``zeta.li``.  ``zeta.li._li_cauchy``
hard-codes ``zeta.core.xi`` as the integrand and ``zeta.li.RADIUS_MAX`` as the
admissible radius, both of which are statements about zeta's zeros.  The
Davenport-Heilbronn function needs the same pipeline over a different entire
function whose radius bound has to be argued separately.  So the *branch* logic
is imported from ``zeta.li`` unchanged (``_unwrapped_log`` builds the analytic
logarithm and checks the winding number, ``_real_checked`` polices the imaginary
residue against the round-off floor that dividing by r^n creates), and only the
evaluator and the radius argument are new.  Importing rather than copying is
deliberate: it makes "the identical pipeline pointed at xi" a literal statement,
so the positive control in ``run_controls.py`` tests this assembly and not a
paraphrase of it.

Why the radius argument is arithmetic rather than a scan of the whole plane.
Under z = 1 - 1/s the modulus is |z| = |s - 1| / |s|, so |z| <= r describes
exactly the Apollonius disc

    |s - 1/(1 - r^2)|  <=  r/(1 - r^2),

which meets the real axis at 1/(1+r) and 1/(1-r).  Three consequences do all the
work.  A zero with Re s = 1/2 has |s - 1| = |s| and therefore sits on |z| = 1
exactly, so no critical-line zero is ever inside the contour at any r < 1.  A
zero with Re s < 1/2 has |z| > 1.  And a zero with |s| >= 1/(1-r) has
|z| >= 1 - 1/|s| >= r.  So establishing a radius means excluding zeros in one
bounded region with Re s > 1/2 only, which :mod:`radius_scan` does by the
argument principle and which the winding check inside this pipeline then
re-tests on the exact contour used.

Nothing here is evidence about the Riemann Hypothesis.
"""

from __future__ import annotations

import math
import multiprocessing as _mp
from typing import Callable

import mpmath
from mpmath import mp

from zeta.core import xi as _xi
from zeta.epstein import _dh_raw
from zeta.epstein import kappa as _kappa
from zeta.li import _GUARD, _real_checked, _roots_of_unity, _unwrapped_log

__all__ = [
    "apollonius_disc",
    "modulus_floor_for_radius",
    "completed_dh_fast",
    "completed_xi_fast",
    "EVALUATORS",
    "work_digits",
    "node_count",
    "sample_circle",
    "sample_circle_iter",
    "coefficients_from_samples",
    "li_coefficients_cauchy",
]


# ---------------------------------------------------------------------------
# the radius arithmetic
# ---------------------------------------------------------------------------

def apollonius_disc(radius) -> tuple:
    """(centre, disc radius) of {s : |1 - 1/s| <= r}, as plain floats.

    Returned rather than re-derived at each call site because every statement
    this hunt makes about admissibility is a statement about this disc, and a
    second derivation is a second place to get the algebra wrong.
    """
    r = float(radius)
    if not 0 < r < 1:
        raise ValueError("radius must lie strictly between 0 and 1")
    return 1.0 / (1.0 - r * r), r / (1.0 - r * r)


def modulus_floor_for_radius(radius) -> float:
    """1/(1-r): every zero of modulus at least this is outside |z| <= r.

    From |1 - 1/s| >= 1 - 1/|s|.  This is the cheap half of the radius argument
    and it is the half that makes the scan finite.
    """
    r = float(radius)
    return 1.0 / (1.0 - r)


def disc_bounding_box(radius, sigma_cap: float = 2.0) -> tuple:
    """The rectangle that contains the part of the Apollonius disc with
    Re s <= ``sigma_cap``.

    ``sigma_cap`` defaults to 2 because ``zeta.epstein`` pins
    sum_{n>=2} |a_n| n^{-2} < 1, so f has no zero with Re s >= 2 and the disc
    beyond that line needs no scanning.  The caller is expected to re-measure
    that sum rather than take it on trust; :mod:`radius_scan` does.
    """
    c, rad = apollonius_disc(radius)
    left = 1.0 / (1.0 + float(radius))
    if sigma_cap >= c + rad:
        half_height = rad
    else:
        d = c - sigma_cap
        half_height = math.sqrt(max(rad * rad - d * d, 0.0))
    return (left, min(sigma_cap, c + rad), half_height)


# ---------------------------------------------------------------------------
# the evaluators
# ---------------------------------------------------------------------------

def completed_dh_fast(s):
    """F(s) = (pi/5)^{-(s+1)/2} Gamma((s+1)/2) f(s) at the ambient precision.

    ``zeta.epstein.completed_dh`` is the reference and this is not a rewrite of
    its mathematics: it is the same product with the dispatch removed.  The
    reference re-enters ``mp.workdps`` twice per call and, worse for a run that
    makes tens of thousands of calls, hands ``kappa`` a precision that depends on
    the distance from s to 1, so the ``lru_cache`` behind kappa thrashes and each
    evaluation re-derives the constant.  Warm, that difference is measured at
    0.092 s against 0.58 s per evaluation at 142 digits, a factor of six on the
    dominant cost of this hunt.

    The two dispatch branches that are dropped are dropped because the contour
    cannot reach them: every sampling circle used here stays at distance
    r/(1+r) >= 0.33 from the removable point s = 1, and its real part never falls
    below 1/(1+r) > 1/2, so the Gamma poles at s = -1, -3, ... are far away.
    ``run_controls.py`` compares this against ``zeta.epstein.completed_dh`` on the
    actual contour instead of asserting the equivalence.
    """
    return mp.power(mp.pi / 5, -(s + 1) / 2) * mp.gamma((s + 1) / 2) * _dh_raw(s)


def completed_xi_fast(s):
    """Riemann's xi at the ambient precision, the positive control's integrand."""
    return _xi(s, mp.dps)


EVALUATORS: dict[str, Callable] = {"dh": completed_dh_fast, "xi": completed_xi_fast}


# ---------------------------------------------------------------------------
# the two sizing rules, taken from zeta.li and not re-invented
# ---------------------------------------------------------------------------

def work_digits(n_max: int, dps: int, radius) -> int:
    """dps + 2*guard + n_max*log10(1/r): the digits the r^{-n} division costs.

    Identical to the rule inside ``zeta.li._li_cauchy``.  It is quoted here
    rather than imported because the run scripts need the number *before*
    launching, to size a job and to write the estimate into ``RUNS.md``.
    """
    decay = float(mp.log10(1 / mp.mpf(str(radius))))
    return int(math.ceil(dps + 2 * _GUARD + n_max * decay))


def node_count(n_max: int, work: int, radius) -> int:
    """work*ln10/ln(1/r) + n_max + 8, again ``zeta.li``'s rule verbatim.

    The first term drives the aliasing tail Sum_k c_{n+kN} r^{kN} below the
    working round-off; the ``n_max`` shift is because the coefficient that
    aliases onto index n is the one at n + N.
    """
    Rw = mp.mpf(str(radius))
    return int(mp.ceil(work * mp.log(10) / mp.log(1 / Rw))) + n_max + 8


# ---------------------------------------------------------------------------
# sampling, optionally across processes
# ---------------------------------------------------------------------------

_WORKER: dict = {}


def _worker_init(target: str, work: int, radius_str: str, n_points: int) -> None:
    mp.dps = work
    _WORKER.clear()
    _WORKER["fn"] = EVALUATORS[target]
    _WORKER["R"] = mp.mpf(radius_str)
    _WORKER["N"] = n_points
    if target == "dh":
        _kappa(mp.dps)  # warm the lru_cache once per process, not once per call


def _worker_chunk(bounds: tuple) -> list:
    lo, hi = bounds
    fn, R, N = _WORKER["fn"], _WORKER["R"], _WORKER["N"]
    out = []
    for j in range(lo, hi):
        z = R * mp.expjpi(mp.mpf(2 * j) / N)
        v = mp.mpc(fn(1 / (1 - z)))
        out.append((v.real._mpf_, v.imag._mpf_))
    return out


def sample_circle(
    target: str, work: int, radius, n_points: int, processes: int = 1
) -> list:
    """F(1/(1-z)) at the ``n_points`` equispaced nodes of |z| = radius.

    Split across processes because this is where the money goes: the DH
    evaluator is four Hurwitz zeta values at the working precision, and at
    n_max = 2000 the pipeline wants five thousand of them.  Values cross the
    process boundary as mpmath's exact ``_mpf_`` triples, so nothing is rounded
    on the way back and a parallel run and a serial run agree bit for bit
    (checked in ``run_controls.py``).
    """
    radius_str = str(radius)
    if processes <= 1:
        _worker_init(target, work, radius_str, n_points)
        raw = _worker_chunk((0, n_points))
    else:
        step = (n_points + processes - 1) // processes
        chunks = [
            (lo, min(lo + step, n_points)) for lo in range(0, n_points, step)
        ]
        ctx = _mp.get_context("fork")
        with ctx.Pool(
            processes=processes,
            initializer=_worker_init,
            initargs=(target, work, radius_str, n_points),
        ) as pool:
            raw = [row for part in pool.map(_worker_chunk, chunks) for row in part]
    with mp.workdps(work):
        return [
            mp.mpc(mpmath.make_mpf(re), mpmath.make_mpf(im)) for re, im in raw
        ]


def sample_circle_iter(
    target: str, work: int, radius, n_points: int, processes: int, block: int = 64
):
    """Yield (lo, hi, rows) blocks of samples as they complete, in order.

    The reason this exists rather than one big map: compute discipline in this
    repository requires anything over about twenty minutes to checkpoint per
    unit, after a run that reached cell 25 of 100, was preempted, and restarted
    from cell 0 three times.  A block of 64 nodes is the unit here, and the
    caller writes each one to disk as it lands, so a killed run resumes from the
    last block instead of the first.
    """
    radius_str = str(radius)
    chunks = [
        (lo, min(lo + block, n_points)) for lo in range(0, n_points, block)
    ]
    if processes <= 1:
        _worker_init(target, work, radius_str, n_points)
        for lo, hi in chunks:
            yield lo, hi, _worker_chunk((lo, hi))
        return
    ctx = _mp.get_context("fork")
    with ctx.Pool(
        processes=processes,
        initializer=_worker_init,
        initargs=(target, work, radius_str, n_points),
    ) as pool:
        for (lo, hi), rows in zip(chunks, pool.imap(_worker_chunk, chunks)):
            yield lo, hi, rows


# ---------------------------------------------------------------------------
# the extraction
# ---------------------------------------------------------------------------

def _dft_chunk(args: tuple) -> list:
    n_lo, n_hi = args
    vals = _DFT["vals"]
    w = _DFT["w"]
    N = _DFT["N"]
    Rw = _DFT["R"]
    work = _DFT["work"]
    biggest = _DFT["biggest"]
    out = []
    for n in range(n_lo, n_hi):
        acc = mp.fsum(vals[j] * w[(-(j * n)) % N] for j in range(N))
        inv = mp.power(Rw, -n)
        c_n = acc * inv / N
        lam = n * _real_checked(
            c_n, work, _GUARD + 2, f"lambda_{n}", scale=biggest * inv
        )
        out.append(lam._mpf_)
    return out


_DFT: dict = {}


def _dft_init(vals_raw, work, radius_str, n_points, biggest_raw) -> None:
    mp.dps = work
    _DFT.clear()
    _DFT["work"] = work
    _DFT["N"] = n_points
    _DFT["R"] = mp.mpf(radius_str)
    _DFT["vals"] = [
        mp.mpc(mpmath.make_mpf(re), mpmath.make_mpf(im)) for re, im in vals_raw
    ]
    _DFT["w"] = _roots_of_unity(n_points)
    _DFT["biggest"] = mpmath.make_mpf(biggest_raw)


def coefficients_from_samples(
    samples: list, n_max: int, work: int, radius, processes: int = 1
) -> list:
    """lambda_1 .. lambda_n_max from one already-taken circle of samples.

    Separated from :func:`sample_circle` so that the expensive samples can be
    reused: the radius-independence oracle and the main table want different
    n_max off the same circle, and re-sampling to answer a second question is
    how a compute budget disappears.
    """
    radius_str = str(radius)
    with mp.workdps(work):
        vals = _unwrapped_log(samples)
        biggest = max(abs(v) for v in vals)
        raw = [(v.real._mpf_, v.imag._mpf_) for v in vals]
        biggest_raw = biggest._mpf_
    if processes <= 1:
        _dft_init(raw, work, radius_str, len(samples), biggest_raw)
        out = _dft_chunk((1, n_max + 1))
    else:
        step = (n_max + processes - 1) // processes
        chunks = [
            (lo, min(lo + step, n_max + 1)) for lo in range(1, n_max + 1, step)
        ]
        ctx = _mp.get_context("fork")
        with ctx.Pool(
            processes=processes,
            initializer=_dft_init,
            initargs=(raw, work, radius_str, len(samples), biggest_raw),
        ) as pool:
            out = [row for part in pool.map(_dft_chunk, chunks) for row in part]
    with mp.workdps(work):
        return [mpmath.make_mpf(v) for v in out]


def li_coefficients_cauchy(
    target: str,
    n_max: int,
    dps: int = 30,
    radius="0.9",
    processes: int = 1,
    report: dict | None = None,
) -> list:
    """lambda_1 .. lambda_n_max for ``target`` in {"dh", "xi"}, Cauchy route.

    No zero of anything is read.  The winding check inside ``_unwrapped_log`` is
    an argument-principle count over the exact contour, so a nonzero winding is
    this routine refusing to return numbers rather than a nuisance to suppress.
    """
    work = work_digits(n_max, dps, radius)
    n_points = node_count(n_max, work, radius)
    if report is not None:
        report.update(
            {
                "target": target,
                "n_max": n_max,
                "dps": dps,
                "radius": str(radius),
                "work_digits": work,
                "n_points": n_points,
            }
        )
    samples = sample_circle(target, work, radius, n_points, processes=processes)
    out = coefficients_from_samples(samples, n_max, work, radius, processes=processes)
    with mp.workdps(dps):
        return [+v for v in out]

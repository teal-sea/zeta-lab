"""Zero layer: Arb isolation of zeta zeros (route 1), an mpmath bracket check
(route 2), and an mpmath windowed count (route 3, completeness cross-check).

Route 1 is python-flint's ``acb.zeta_zeros`` (Arb's ``acb_dirichlet_zeta_zeros``,
Platt's algorithm as implemented in Arb, with Turing's method for the count),
and ``arb.zeta_nzeros`` for N(T). It returns zeros by index with real part
exactly 1/2, so the index is the completeness statement and it rests on Arb.

Route 2 shares no code with Arb: mpmath's ``siegelz`` (Riemann-Siegel) at the
two ends of each Arb bracket widened to +/- delta must have opposite signs.
That confirms one zero of odd order in each bracket, at float grade (mpmath
``siegelz`` carries no error bound). It does not check completeness.

Route 3 is the independent count this docstring used to list as missing. It
follows KIDA-Nya's method in issue #392 (zeta-audit, ``audit_table.py``,
``check_completeness``): difference mpmath's ``nzeros`` at midpoints between
consecutive ordinates, never at an ordinate itself, and compare with the
number of table rows in the window. It is route-independent float-grade
evidence: a second opinion, not a certificate, and not a replacement for
route 1. The gap is now partially closed. What remains open: route 3 is
sampled, so a hole outside the sampled windows is missed; it is float grade,
so it carries no error bound; and the argument-principle count (the
independent route that could in principle carry enclosures) is unchanged and
still not implemented here. Route 1, through Arb's Turing count, remains the
completeness statement the shards rest on.

Shard driver::

    nice -n 10 .venv/bin/python -u hunts/skewes_enclosure/zero_layer.py \
        --n0 1 --num 100000 --batch 5000 --prec 64 --out <scratch>/shard.json

The JSON holds timings, the shard's partial sums at the parameter sets in
``skewes_terms``, the route-2 sample outcome and the SHA-256 of the zeros as
written (one ``mid +/- rad`` line per zero, not committed).
"""

from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import random
import resource
import sys
import time
from pathlib import Path

import flint
from flint import acb, arb

sys.path.insert(0, str(Path(__file__).resolve().parent))
import skewes_terms as st  # noqa: E402


def arb_zeros(n0: int, num: int, batch: int = 5000, prec: int = 128):
    """Ordinates gamma_{n0} .. gamma_{n0+num-1} as arb balls, plus seconds per batch."""
    old = flint.ctx.prec
    flint.ctx.prec = prec
    try:
        out, times = [], []
        n = n0
        while n < n0 + num:
            k = min(batch, n0 + num - n)
            t = time.perf_counter()
            zs = acb.zeta_zeros(n, k)
            times.append(time.perf_counter() - t)
            for z in zs:
                if not (z.real == arb(1) / 2):
                    raise ValueError(f"zero {n} has real part {z.real}, not exactly 1/2")
                out.append(z.imag)
            n += k
        return out, times
    finally:
        flint.ctx.prec = old


def check_ordered(gammas) -> bool:
    """Consecutive balls are disjoint and increasing (decided on balls)."""
    return all(bool(a < b) for a, b in zip(gammas, gammas[1:]))


def count_below(T: str, prec: int = 128) -> int:
    """N(T) from Arb's Turing count; raises if the ball does not pin an integer."""
    old = flint.ctx.prec
    flint.ctx.prec = prec
    try:
        return int(arb(T).zeta_nzeros().unique_fmpz())
    finally:
        flint.ctx.prec = old


def mpmath_bracket_signs(gamma: arb, delta: str = "1e-8", dps: int = 30) -> bool:
    """Route 2: siegelz(gamma - delta) and siegelz(gamma + delta) differ in sign."""
    import mpmath

    with mpmath.workdps(dps):
        mid = mpmath.mpf(gamma.mid().str(40, radius=False))
        d = mpmath.mpf(delta)
        if not (gamma.rad() < arb(delta)):
            raise ValueError("Arb radius exceeds delta; widen delta")
        a = mpmath.siegelz(mid - d)
        b = mpmath.siegelz(mid + d)
        return bool(a * b < 0)


def _ordinate_str(g) -> str:
    """One ordinate as a decimal string: an arb ball by its midpoint, else str(g)."""
    return g.mid().str(40, radius=False) if isinstance(g, arb) else str(g)


def mpmath_window_count(gammas, start: int, window_rows: int, dps: int = 30) -> dict:
    """Route 3, one window: independent zero count inside ``gammas[start:start+window_rows]``.

    The count is ``nzeros(hi) - nzeros(lo)`` in mpmath, where ``lo`` is the
    midpoint of ``gammas[start - 1]`` and ``gammas[start]`` and ``hi`` is the
    midpoint of ``gammas[start + window_rows - 1]`` and
    ``gammas[start + window_rows]``. Both points lie strictly between
    consecutive ordinates by construction, and this function raises rather
    than evaluate anywhere else: ``nzeros`` at an ordinate itself returns k or
    k - 1 unpredictably (measured here: ``nzeros(gamma_1)`` gives 0 and
    ``nzeros(gamma_3)`` gives 2, while ``nzeros(gamma_10)`` gives 10). The
    method is KIDA-Nya's, from issue #392 and ``check_completeness`` in
    zeta-audit's ``audit_table.py``; the code here is written for this layer.

    ``gammas`` may hold arb balls (their midpoints are read, as in route 2),
    decimal strings, or floats. Only the four boundary ordinates are read, so
    the count is differenced and needs no absolute index: shards that do not
    start at gamma_1 are fine. The result is float grade (mpmath ``nzeros``
    carries no error bound): a second opinion, not a certificate. ``seconds``
    times the two ``nzeros`` calls only.
    """
    import mpmath

    gammas = list(gammas)
    if window_rows < 1:
        raise ValueError("window_rows must be at least 1")
    if not 1 <= start <= len(gammas) - 1 - window_rows:
        raise ValueError(
            f"start {start} with window_rows {window_rows} needs one ordinate "
            f"outside each end of the window in a table of {len(gammas)} rows")
    with mpmath.workdps(dps):
        a, b, c, d = (mpmath.mpf(_ordinate_str(gammas[i])) for i in
                      (start - 1, start, start + window_rows - 1, start + window_rows))
        lo, hi = (a + b) / 2, (c + d) / 2
        if not (a < lo < b and c < hi < d and lo < hi):
            raise ValueError("midpoints are not strictly between consecutive "
                             "ordinates; refusing to evaluate nzeros there")
        t = time.perf_counter()
        inside = int(mpmath.nzeros(hi)) - int(mpmath.nzeros(lo))
        seconds = time.perf_counter() - t
        return {"start": start, "window_rows": window_rows,
                "lo": mpmath.nstr(lo, 20), "hi": mpmath.nstr(hi, 20),
                "table_count": window_rows, "independent_count": inside,
                "agree": inside == window_rows, "seconds": seconds}


def _sampled_starts(n: int, windows: int, window_rows: int) -> list:
    """Window starts spread over a table of n rows (zeta-audit's placement)."""
    hi_start = n - 1 - window_rows
    return sorted({max(1, min(int(n * (k + 1) / (windows + 1)) - window_rows // 2,
                               hi_start))
                   for k in range(windows)})


def check_completeness_mpmath(gammas, windows: int = 3, window_rows: int = 200,
                              dps: int = 30, starts=None) -> dict:
    """Route 3: sampled independent completeness cross-check of a zero table.

    Runs ``mpmath_window_count`` on ``windows`` windows of ``window_rows``
    rows spread over the table (or at the explicit 0-based ``starts``). A
    missing ordinate inside a sampled window makes that window disagree, with
    the independent count one above the table count per missing zero. This is
    sampled evidence: a hole outside the sampled windows is missed, and a
    full sweep costs one pair of ``nzeros`` calls per window. Float grade
    throughout: a second opinion that can catch a missing zero in the sampled
    windows, not a certificate and not a replacement for route 1.
    """
    gammas = list(gammas)
    if windows < 1:
        raise ValueError("windows must be at least 1")
    if len(gammas) < window_rows + 2:
        raise ValueError(f"need at least window_rows + 2 = {window_rows + 2} "
                         f"ordinates, got {len(gammas)}")
    if starts is None:
        starts = _sampled_starts(len(gammas), windows, window_rows)
    if not starts:
        raise ValueError("no windows to check")
    t = time.perf_counter()
    rows = [mpmath_window_count(gammas, s, window_rows, dps) for s in starts]
    return {
        "method": "mpmath.nzeros differenced at midpoints between consecutive ordinates",
        "grade": "float (mpmath, no error bound): a second opinion, not a certificate",
        "coverage": "sampled windows only: a hole outside them is missed",
        "windows": rows,
        "all_agree": all(r["agree"] for r in rows),
        "failures": [r["start"] for r in rows if not r["agree"]],
        "seconds": time.perf_counter() - t,
    }


def count_vs_smooth(gammas, n0: int = 1, dps: int = 30) -> dict:
    """Weak sanity only: total count against the smooth count theta(T)/pi + 1.

    ``gammas`` are gamma_{n0} .. gamma_{n0 + len(gammas) - 1} and T is the last
    ordinate; the implied S(T) is count minus smooth count, and the check is
    |S(T)| < 3. S(T) is ordinarily of size about 1, so this passes with one or
    two zeros missing: it is reported separately from route 3 precisely so the
    two are not conflated (zeta-audit makes the same split). It is not a
    completeness check. The windowed count in ``check_completeness_mpmath``
    is the check that catches a hole.
    """
    import mpmath

    gammas = list(gammas)
    if not gammas:
        raise ValueError("empty table")
    with mpmath.workdps(dps):
        T = mpmath.mpf(_ordinate_str(gammas[-1]))
        smooth = mpmath.siegeltheta(T) / mpmath.pi + 1
        count = n0 + len(gammas) - 1
        s_implied = count - smooth
        return {"T": mpmath.nstr(T, 20), "count": count,
                "smooth_N": mpmath.nstr(smooth, 20),
                "S_implied": mpmath.nstr(s_implied, 20),
                "abs_S_lt_3": bool(abs(s_implied) < 3),
                "grade": "float (mpmath): weak sanity only, not a completeness check"}


def zeros_digest(gammas) -> str:
    h = hashlib.sha256()
    for g in gammas:
        h.update((g.str(45) + "\n").encode())
    return h.hexdigest()


def write_zeros(gammas, path: Path) -> None:
    """The zeros as printed balls, one per line, gzipped; the decompressed bytes
    hash to the shard's ``zeros_sha256``."""
    with gzip.open(path, "wt", encoding="ascii") as f:
        for g in gammas:
            f.write(g.str(45) + "\n")


def run_shard(n0: int, num: int, batch: int, sample: int, seed: int, prec: int = 128,
              omegas=None, zeros_out: Path | None = None) -> dict:
    t0 = time.perf_counter()
    gammas, times = arb_zeros(n0, num, batch, prec)
    t_zeros = time.perf_counter() - t0
    if zeros_out is not None:
        write_zeros(gammas, zeros_out)

    t1 = time.perf_counter()
    sums = {
        "chao_plymen": st.lehman_sum(gammas, st.CHAO_PLYMEN.omega, st.CHAO_PLYMEN.alpha),
        "saouter_demichel": st.lehman_sum(gammas, st.SAOUTER_DEMICHEL.omega,
                                          st.SAOUTER_DEMICHEL.alpha),
    }
    grid = {}
    if omegas:
        grid = {k: v.str(40) for k, v in
                st.lehman_sum_grid(gammas, omegas, st.SAOUTER_DEMICHEL.alpha).items()}
    t_sums = time.perf_counter() - t1

    rng = random.Random(seed)
    picks = sorted(rng.sample(range(num), min(sample, num)))
    t2 = time.perf_counter()
    route2 = {n0 + i: mpmath_bracket_signs(gammas[i]) for i in picks}
    t_route2 = time.perf_counter() - t2

    max_rad = max(g.rad() for g in gammas)
    return {
        "n0": n0,
        "num": num,
        "batch": batch,
        "isolation_prec_bits": prec,
        "first": gammas[0].str(30),
        "last": gammas[-1].str(30),
        "ordered_disjoint": check_ordered(gammas),
        "max_radius": max_rad.str(5),
        "seconds_zeros": t_zeros,
        "seconds_per_batch": times,
        "ms_per_zero": 1e3 * t_zeros / num,
        "seconds_sums": t_sums,
        "partial_sums": {k: v.str(40) for k, v in sums.items()},
        "grid_alpha": st.SAOUTER_DEMICHEL.alpha if omegas else None,
        "grid_sums": grid,
        "route2_sample": {"seed": seed, "size": len(picks),
                          "all_sign_changes": all(route2.values()),
                          "failures": [k for k, v in route2.items() if not v],
                          "seconds": t_route2},
        "zeros_sha256": zeros_digest(gammas),
        "max_rss_kb": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        "python_flint": flint.__version__,
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--n0", type=int, required=True)
    ap.add_argument("--num", type=int, required=True)
    ap.add_argument("--batch", type=int, default=5000)
    ap.add_argument("--sample", type=int, default=200)
    ap.add_argument("--seed", type=int, default=152)
    ap.add_argument("--prec", type=int, default=128)
    ap.add_argument("--omegas", type=Path, help="JSON file with an 'omegas' list (alpha 6e12)")
    ap.add_argument("--zeros-out", type=Path, help="write the zeros here, gzipped")
    ap.add_argument("--out", type=Path, required=True)
    a = ap.parse_args()
    res = run_shard(a.n0, a.num, a.batch, a.sample, a.seed, a.prec,
                    json.loads(a.omegas.read_text())["omegas"] if a.omegas else None,
                    a.zeros_out)
    a.out.write_text(json.dumps(res, indent=1))
    print(json.dumps({k: v for k, v in res.items()
                      if k not in ("seconds_per_batch", "grid_sums")}, indent=1))


if __name__ == "__main__":
    main()

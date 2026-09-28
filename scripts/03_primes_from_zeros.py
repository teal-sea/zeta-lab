#!/usr/bin/env python
"""THE SHOWSTOPPER: reconstruct the primes from the zeros of ζ(s).

Von Mangoldt's explicit formula (1895), for x > 1, with ρ = 1/2 + iγ
running over the non-trivial zeros in conjugate pairs,

    ψ₀(x) = x − Σ_ρ x^ρ/ρ − log 2π − ½·log(1 − x⁻²)
          = x − 2√x Σ_{γ>0} cos(γ·log x − arctan 2γ)/√(1/4+γ²) − log 2π − …

where ψ(x) = Σ_{p^k ≤ x} log p is the Chebyshev prime-power staircase
(ψ₀ = ψ with jumps halved).  Every zero contributes one smooth harmonic in
log x, yet the sum of these waves develops a JUMP of height log p at every
prime power and is flat everywhere else.  The primes are the interference
pattern of the zeros.

The dual view ("the music of the primes"): differentiating in u = log x,
the oscillatory density

    D(u) = −2 Σ_{γ>0} w(γ)·cos(γu)

has a spike at u = log p^k with weight Λ(n)/√n and no spike anywhere else,
so the prime powers can be *detected* from the zeros alone.

This script prints the reconstruction converging, measures the jumps of the
reconstructed staircase at (and away from) prime powers, detects the prime
powers as spectral peaks, and saves a figure of the whole picture.
"""

from __future__ import annotations

import argparse
from pathlib import Path
import math
import time

import numpy as np

from zeta.explicit import (
    convergence_table,
    first_zeros,
    mangoldt,
    prime_spectrum,
    psi_curve,
    psi_staircase,
    psi_true,
    spectrum_peaks,
)

__all__ = ["main"]

# dataviz reference palette (light mode): categorical slots 1-3 + neutral ink
_BLUE, _ORANGE, _AQUA = "#2a78d6", "#eb6834", "#1baf7a"
_INK, _MUTED = "#0b0b0b", "#52514e"


def _get_gammas(n: int) -> np.ndarray:
    """First n zero ordinates from the fastest available cached source."""
    if n <= 1000:
        return first_zeros(n)
    from zeta.statistics import zero_ordinates  # RS scan, cached to T = 1e4

    try:
        return zero_ordinates(n)
    except ValueError as e:
        raise SystemExit(f"error: {e} (or request --zeros <= 10142)") from e


def _prime_powers_upto(x: float) -> list[int]:
    return [n for n in range(2, int(x) + 1) if mangoldt(n) > 0.0]


def section_convergence(x: float, g: np.ndarray) -> None:
    print(f"1)  ψ(x) at x = {x:g} rebuilt from N zero pairs "
          f"(exact ψ({x:g}) = {psi_true(x):.6f})")
    print()
    counts = [c for c in (0, 1, 10, 50, 100, 250, 500, 1000) if c <= g.size]
    if counts[-1] != g.size:
        counts.append(g.size)
    rows = convergence_table(x, g, counts=counts)
    print(f"    {'N zeros':>8} {'γ_max':>10} {'ψ_rec(x)':>14} {'error':>12}")
    print("    " + "-" * 48)
    for r in rows:
        print(f"    {r['n_zeros']:>8} {r['gamma_max']:>10.2f} "
              f"{r['psi_est']:>14.6f} {r['error']:>+12.6f}")
    print()
    print("    The error shrinks as zeros are added: the smooth term x minus a")
    print("    sum of pure cosines is converging to a STAIRCASE.")
    print()


def section_jumps(x: float, g: np.ndarray) -> None:
    h = 0.4
    pps = _prime_powers_upto(x)
    sel = pps[-6:]
    tests: list[int] = []
    for n in sel:
        tests.append(n)
        if n + 1 <= x and mangoldt(n + 1) == 0.0:
            tests.append(n + 1)  # a neighbouring non-prime-power as control
    tests = sorted(set(tests))

    pts = np.array([[n - h, n + h] for n in tests], dtype=float)
    rec = psi_curve(pts.ravel(), g).reshape(pts.shape)
    print(f"2)  Measured jump of the reconstruction across each integer "
          f"(ψ_rec(n+{h}) − ψ_rec(n−{h}), {g.size} zeros)")
    print()
    print(f"    {'n':>5} {'factor':>10} {'true Λ(n)':>10} {'measured':>10}   verdict")
    print("    " + "-" * 56)
    for n, (lo, hi) in zip(tests, rec):
        lam = mangoldt(n)
        jump = hi - lo
        kind = _describe(n)
        verdict = "JUMP  <- prime power" if lam > 0 else "flat  (not a prime power)"
        print(f"    {n:>5} {kind:>10} {lam:>10.4f} {jump:>10.4f}   {verdict}")
    print()
    print("    The cosine sum jumps by log p exactly at the prime powers and is")
    print("    flat in between, the zeros KNOW where the primes are.  (The slight")
    print("    overshoot at the largest primes is Gibbs oscillation at finite N.)")
    print()


def _describe(n: int) -> str:
    m, p = n, 2
    while p * p <= m:
        if m % p == 0:
            k = 0
            while m % p == 0:
                m //= p
                k += 1
            if m == 1:
                return f"{p}^{k}" if k > 1 else "prime"
            return "composite"
        p += 1
    return "prime"


def section_sharpening(x: float, g: np.ndarray) -> None:
    p = max(n for n in _prime_powers_upto(x) if _describe(n) == "prime")
    h = 0.4
    print(f"3)  Watch the edge at the prime p = {p} sharpen as zeros are added")
    print(f"    (true jump: Λ({p}) = log {p} = {math.log(p):.4f})")
    print()
    print(f"    {'N zeros':>8} {'measured jump at p':>20}")
    print("    " + "-" * 30)
    for n_z in (0, 10, 50, 100, 250, g.size):
        vals = psi_curve(np.array([p - h, p + h]), g[:n_z])
        print(f"    {n_z:>8} {vals[1] - vals[0]:>20.4f}")
    print()


def section_spectrum(x: float, g: np.ndarray, n_peaks: int = 20) -> tuple:
    u = np.linspace(0.45, math.log(x) + 0.15, 6000)
    spec = prime_spectrum(g, u, window="gauss")
    peaks = spectrum_peaks(u, spec, n_peaks=n_peaks)
    print(f"4)  \"The music of the primes\": peaks of D(u) = −2Σ w(γ)cos(γu), "
          f"u = log x  ({g.size} zeros)")
    print()
    print(f"    {'peak at x=e^u':>13} {'nearest n':>10} {'kind':>10} "
          f"{'height':>8} {'Λ(n)/√n':>9}   prime power?")
    print("    " + "-" * 64)
    hits = 0
    for pk in sorted(peaks, key=lambda d: d["u"]):
        ok = pk["is_prime_power"]
        hits += ok
        print(f"    {pk['x']:>13.4f} {pk['nearest_n']:>10} "
              f"{_describe(pk['nearest_n']):>10} {pk['height']:>8.4f} "
              f"{pk['lambda_over_sqrt_n']:>9.4f}   {'YES' if ok else 'no'}")
    print()
    print(f"    {hits}/{len(peaks)} detected peaks are prime powers; peak height "
          "approaches Λ(n)/√n.")
    print("    Nothing was told about primes, only the zeros went in.")
    print()
    return u, spec


def make_figure(x: float, g: np.ndarray, u: np.ndarray, spec: np.ndarray,
                path: str) -> None:
    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    xs = np.linspace(2.0, float(x), 2500)
    fig, (ax1, ax2) = plt.subplots(
        2, 1, figsize=(10.5, 8.2), height_ratios=[3, 2], dpi=150
    )
    fig.patch.set_facecolor("#fcfcfb")

    # -- top: the staircase and its reconstructions -------------------------
    ax1.plot(xs, psi_staircase(xs), color="#a9a8a2", lw=3.0,
             label="exact ψ(x) (the primes)", zorder=2,
             solid_joinstyle="miter")
    series = [(10, _BLUE), (100, _ORANGE), (min(g.size, 500), _AQUA)]
    for k, (n_z, col) in enumerate(series):
        ax1.plot(xs, psi_curve(xs, g[:n_z]), color=col, lw=1.3,
                 label=f"{n_z} zeros", zorder=3 + k)
    ax1.set_xlim(2, x)
    ax1.set_ylabel("ψ(x) = Σ log p over prime powers ≤ x")
    ax1.set_title(
        "Chebyshev's prime staircase rebuilt from the zeros of ζ:  "
        "ψ₀(x) = x − Σ_ρ x^ρ/ρ − log 2π − ½log(1−x⁻²)",
        fontsize=11,
    )
    ax1.legend(loc="upper left", frameon=False)
    ax1.grid(True, color="#e6e5e1", lw=0.6)
    ax1.set_axisbelow(True)

    # -- bottom: the dual spectrum ------------------------------------------
    ax2.plot(u, spec, color=_BLUE, lw=1.2)
    y_top = float(spec.max())
    ax2.set_ylim(float(spec.min()) * 1.15, y_top * 1.22)
    last_label_u = -10.0
    for n in _prime_powers_upto(min(x, math.exp(float(u[-1])))):
        un = math.log(n)
        if u[0] <= un <= u[-1]:
            ax2.axvline(un, color="#e6e5e1", lw=0.8, zorder=0)
            if un - last_label_u > 0.045:  # skip labels that would collide
                ax2.annotate(str(n), (un, y_top * 1.10), ha="center",
                             fontsize=7, color=_MUTED)
                last_label_u = un
    ax2.set_xlim(u[0], u[-1])
    ax2.set_xlabel("u = log x       (gray verticals: prime powers)")
    ax2.set_ylabel("D(u) = −2 Σ w(γ) cos(γu)")
    ax2.set_title("The dual view: every spectral peak of the zero-cosines is a "
                  "prime power", fontsize=11, pad=14)
    ax2.grid(True, axis="y", color="#e6e5e1", lw=0.6)
    ax2.set_axisbelow(True)

    for ax in (ax1, ax2):
        ax.set_facecolor("#fcfcfb")
        for side in ("top", "right"):
            ax.spines[side].set_visible(False)
        for side in ("left", "bottom"):
            ax.spines[side].set_color(_MUTED)
        ax.tick_params(colors=_INK, labelsize=9)

    fig.tight_layout()
    fig.savefig(path, facecolor=fig.get_facecolor())
    plt.close(fig)
    print(f"Figure saved: {path}")


def main() -> None:
    parser = argparse.ArgumentParser(
        description=(
            "Reconstruct the Chebyshev prime-power staircase psi(x) from the "
            "non-trivial zeros of zeta via von Mangoldt's explicit formula "
            "psi0(x) = x - sum_rho x^rho/rho - log(2pi) - (1/2)log(1-x^-2): "
            "the jumps of height log p appear at exactly the prime powers as "
            "more zeros are added.  Also runs the dual detection: the spectrum "
            "D(u) = -2 sum cos(gamma*u) peaks precisely at u = log p^k."
        ),
        formatter_class=argparse.ArgumentDefaultsHelpFormatter,
    )
    parser.add_argument("--x", type=float, default=100.0,
                        help="rebuild psi on (2, x]")
    parser.add_argument("--zeros", type=int, default=500,
                        help="number of zero pairs to use (<= 10142)")
    parser.add_argument("--no-figure", action="store_true",
                        help="skip writing the matplotlib figure")
    parser.add_argument("--figure",
                        default=str(Path(__file__).resolve().parent.parent / "figures" / "03_primes_from_zeros.png"),
                        help="output path for the figure")
    args = parser.parse_args()
    if args.x < 5:
        raise SystemExit("error: need --x >= 5")

    t0 = time.time()
    g = _get_gammas(args.zeros)
    print("=" * 78)
    print("PRIMES OUT OF ZEROS: VON MANGOLDT'S EXPLICIT FORMULA, LIVE")
    print("=" * 78)
    print(f"Input: the first {g.size} zeros of ζ  (γ_1 = {g[0]:.6f} … "
          f"γ_{g.size} = {g[-1]:.2f}).  Nothing else.")
    print()
    section_convergence(args.x, g)
    section_jumps(args.x, g)
    section_sharpening(args.x, g)
    u, spec = section_spectrum(args.x, g)
    if not args.no_figure:
        make_figure(args.x, g, u, spec, args.figure)
    print(f"[{time.time() - t0:.1f} s]")


if __name__ == "__main__":
    main()

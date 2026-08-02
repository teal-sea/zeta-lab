"""Publication-quality matplotlib figures for every part of the zeta laboratory.

Each public function builds one self-contained figure telling one mathematical
story, returns the ``matplotlib.figure.Figure``, and optionally saves it via a
``save_path`` argument.  The fourteen figures, in narrative order:

1.  :func:`plot_zeta_critical_line`     — ζ(½+it): Re, Im, |ζ| and the zeros.
2.  :func:`plot_hardy_Z`                — Hardy's Z(t) with sign changes and Gram points.
3.  :func:`plot_zeta_domain_coloring`   — phase portrait of ζ over the critical strip.
4.  :func:`plot_theta_modularity`       — θ(1/x) = √x·θ(x), Poisson summation checked.
5.  :func:`plot_theta_heat_evolution`   — the heat kernel Θ(x,t) relaxing on ℝ/ℤ.
6.  :func:`plot_explicit_formula`       — ψ(x) rebuilt from 0/10/100/500 zeros.
7.  :func:`plot_prime_spectrum`         — −2Σcos(γu): spikes at u = log pᵏ.
8.  :func:`plot_spacing_histogram`      — zero spacings vs GUE (Gaudin) vs Poisson.
9.  :func:`plot_pair_correlation`       — Montgomery's R₂(r) = 1 − (sin πr/πr)².
10. :func:`plot_zero_counting`          — N(T) staircase vs Riemann–von Mangoldt, and S(T).
11. :func:`plot_heatflow_trajectories`  — zeros of H_t under the de Bruijn–Newman flow.
12. :func:`plot_polynomial_root_repulsion` — the elementary heat-flow-on-roots picture.
13. :func:`plot_weil_positivity`        — W(h) ≥ 0 across families; the margin is γ₁.
14. :func:`plot_offline_zero`           — Davenport–Heilbronn's zero OFF the line.

Style
-----
One restrained, colourblind-validated palette is used throughout (categorical
order blue → orange → aqua → …, validated for CVD separation and lightness);
semantic conventions are held fixed across figures:

* **blue**   — empirical zeta data (curves, histograms, trajectories);
* **orange** — the theoretical prediction being compared against (GUE,
  Montgomery, Riemann–von Mangoldt, the Λ(n)/√n comb);
* **muted grey dashed** — null hypotheses / reference levels (Poisson, zero lines);
* **ink**    — exact arithmetic ground truth (the ψ staircase, N(T) staircase).

Figures use ``constrained_layout``, a near-white surface, hairline grids and
labelled axes, and every title states the mathematical claim the figure shows.

All heavy numerical inputs are delegated to the sibling modules
(:mod:`zeta.core`, :mod:`zeta.zeros`, :mod:`zeta.explicit`,
:mod:`zeta.statistics`, :mod:`zeta.heatflow`), whose results are cached under
``data/`` — so regenerating every figure is fast after the first run.  The one
bulk computation done here, the domain-colouring grid of ζ values, is likewise
cached to ``data/``.
"""

from __future__ import annotations

import math
import os
from typing import Sequence

import matplotlib

matplotlib.use("Agg")  # headless: must precede pyplot import

import matplotlib.pyplot as plt  # noqa: E402  (backend must be set first)
import numpy as np  # noqa: E402
from matplotlib.colors import ListedColormap, Normalize, hsv_to_rgb  # noqa: E402
from matplotlib.figure import Figure  # noqa: E402
from matplotlib.lines import Line2D  # noqa: E402

__all__ = [
    "plot_zeta_critical_line",
    "plot_hardy_Z",
    "plot_zeta_domain_coloring",
    "plot_theta_modularity",
    "plot_theta_heat_evolution",
    "plot_explicit_formula",
    "plot_prime_spectrum",
    "plot_spacing_histogram",
    "plot_pair_correlation",
    "plot_zero_counting",
    "plot_heatflow_trajectories",
    "plot_polynomial_root_repulsion",
    "plot_weil_positivity",
    "plot_offline_zero",
]

# --------------------------------------------------------------------------- #
# palette (validated: CVD-safe order, lightness band, chroma floor)
# --------------------------------------------------------------------------- #

_INK = "#0b0b0b"        # primary ink: titles, exact staircases
_SECONDARY = "#52514e"  # axis labels, legends
_MUTED = "#898781"      # ticks, null-hypothesis lines
_GRID = "#e1e0d9"       # hairline grid
_BASELINE = "#c3c2b7"   # axis spines
_SURFACE = "#fcfcfb"    # chart surface

_BLUE = "#2a78d6"       # series 1: empirical zeta data
_ORANGE = "#eb6834"     # series 2: theoretical prediction
_AQUA = "#1baf7a"       # series 3
_RED = "#e34948"        # series 8: "left the real axis" states

#: One-hue sequential ramp (light → dark blue) for ordered families of curves.
_BLUE_RAMP = ("#cde2fb", "#9ec5f4", "#6da7ec", "#3987e5", "#256abf", "#184f95", "#0d366b")

_DATA_DIR = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "data")


# --------------------------------------------------------------------------- #
# shared style helpers
# --------------------------------------------------------------------------- #


def _fig(nrows: int = 1, figsize: tuple[float, float] = (8.0, 4.8),
         height_ratios: Sequence[float] | None = None, sharex: bool = False):
    """A constrained-layout figure on the standard surface; axes always a list."""
    gs = {"height_ratios": list(height_ratios)} if height_ratios else None
    fig, axes = plt.subplots(
        nrows, 1, figsize=figsize, constrained_layout=True, sharex=sharex,
        gridspec_kw=gs,
    )
    fig.set_facecolor(_SURFACE)
    axes = [axes] if nrows == 1 else list(axes)
    for ax in axes:
        ax.set_facecolor(_SURFACE)
    return fig, axes


def _style(ax, xlabel: str | None = None, ylabel: str | None = None,
           title: str | None = None) -> None:
    """Recessive chrome: hairline grid, baseline spines, muted ticks."""
    for side in ("top", "right"):
        ax.spines[side].set_visible(False)
    for side in ("left", "bottom"):
        ax.spines[side].set_color(_BASELINE)
    ax.grid(True, color=_GRID, linewidth=0.6)
    ax.set_axisbelow(True)
    ax.tick_params(colors=_MUTED, labelcolor=_SECONDARY, labelsize=8.5)
    if xlabel:
        ax.set_xlabel(xlabel, color=_SECONDARY, fontsize=9.5)
    if ylabel:
        ax.set_ylabel(ylabel, color=_SECONDARY, fontsize=9.5)
    if title:
        ax.set_title(title, color=_INK, fontsize=11, loc="left", pad=10)


def _legend(ax, loc: str = "best", **kw) -> None:
    ax.legend(frameon=False, fontsize=8.5, labelcolor=_SECONDARY, loc=loc, **kw)


def _finish(fig: Figure, save_path: str | None, dpi: int) -> Figure:
    if save_path:
        d = os.path.dirname(os.path.abspath(save_path))
        os.makedirs(d, exist_ok=True)
        fig.savefig(save_path, dpi=dpi, facecolor=fig.get_facecolor())
    return fig


def _gammas_below(t_max: float) -> np.ndarray:
    """Zero ordinates 0 < γ < t_max from the cached Riemann–Siegel scan."""
    from zeta.statistics import zero_ordinates

    scan_T = 10000.0 if t_max <= 10000.0 else float(t_max)
    g = zero_ordinates(t_max=scan_T)
    return g[g < float(t_max)]


# --------------------------------------------------------------------------- #
# 1. zeta on the critical line
# --------------------------------------------------------------------------- #


def plot_zeta_critical_line(t_max: float = 50.0, n_points: int = 1600,
                            save_path: str | None = None, dpi: int = 160) -> Figure:
    """Re ζ, Im ζ and |ζ| along the critical line s = ½ + it, zeros marked.

    The claim on display: |ζ(½+it)| touches 0 exactly where Re ζ and Im ζ
    vanish *simultaneously* — the nontrivial zeros ρₙ = ½ + iγₙ, whose
    ordinates come from the cached Riemann–Siegel scan (independent of the
    curve, which is evaluated with mpmath's double-precision ``fp.zeta``).

    Parameters
    ----------
    t_max : plot 0 ≤ t ≤ t_max.
    n_points : samples of ζ(½+it) along the line.
    """
    from mpmath import fp

    t = np.linspace(0.0, float(t_max), int(n_points))
    vals = np.array([complex(fp.zeta(complex(0.5, tt))) for tt in t])
    gam = _gammas_below(t_max)

    fig, (ax,) = _fig(figsize=(8.8, 4.6))
    ax.axhline(0.0, color=_BASELINE, linewidth=0.8)
    ax.plot(t, np.abs(vals), color=_INK, linewidth=1.8, label="|ζ(½+it)|")
    ax.plot(t, vals.real, color=_BLUE, linewidth=1.3, label="Re ζ(½+it)")
    ax.plot(t, vals.imag, color=_ORANGE, linewidth=1.3, label="Im ζ(½+it)")
    ax.scatter(gam, np.zeros_like(gam), s=34, facecolor="white", edgecolor=_INK,
               linewidth=1.1, zorder=5, label="zeros ρₙ = ½ + iγₙ")
    if gam.size:
        ax.annotate(f"γ₁ = {gam[0]:.4f}", xy=(gam[0], 0.0), xytext=(gam[0] + 0.6, -1.6),
                    color=_SECONDARY, fontsize=8,
                    arrowprops=dict(arrowstyle="-", color=_BASELINE, lw=0.8))
    _style(ax, xlabel="t  (height on the critical line s = ½ + it)",
           ylabel="value (dimensionless)",
           title="ζ on the critical line: Re and Im vanish together — exactly at the zeros ρₙ = ½ + iγₙ")
    ax.set_xlim(0, t_max)
    _legend(ax, loc="upper left", ncols=2)
    return _finish(fig, save_path, dpi)


# --------------------------------------------------------------------------- #
# 2. Hardy's Z with sign changes and Gram points
# --------------------------------------------------------------------------- #


def plot_hardy_Z(t_max: float = 100.0, save_path: str | None = None,
                 dpi: int = 160) -> Figure:
    """Hardy's Z(t) = e^{iθ(t)} ζ(½+it), its sign changes, and the Gram points.

    Z is *real* for real t with |Z| = |ζ(½+it)|, so every sign change is a
    certificate of a zero on the critical line.  Gram points g_n solve
    θ(g_n) = nπ; Gram's empirical law says the zeros and Gram points
    interlace, i.e. (−1)ⁿ Z(g_n) > 0 (first failure only at n = 126).

    Z is evaluated with the vectorised float64 Riemann–Siegel formula for
    t ≥ 12 (error ≲ 1e-4 there) and with the mpmath implementation
    :func:`zeta.zeros.Z` below t = 12, where the asymptotic series is weak.
    """
    from zeta.statistics import riemann_siegel_z
    from zeta.zeros import Z as Z_mp, gram_point

    t_max = float(t_max)
    step = 0.05
    t_lo = np.arange(0.0, min(12.0, t_max), step)
    z_lo = np.array([float(Z_mp(tt, dps=15)) for tt in t_lo])
    if t_max > 12.0:
        t_hi = np.arange(12.0, t_max, step)
        z_hi = np.asarray(riemann_siegel_z(t_hi), dtype=float)
        t = np.concatenate([t_lo, t_hi])
        z = np.concatenate([z_lo, z_hi])
    else:
        t, z = t_lo, z_lo

    gam = _gammas_below(t_max)
    grams: list[float] = []
    n = -1
    while True:
        g = float(gram_point(n, dps=15))
        if g > t_max:
            break
        grams.append(g)
        n += 1

    fig, (ax,) = _fig(figsize=(9.2, 4.3))
    ax.axhline(0.0, color=_BASELINE, linewidth=0.8)
    ax.plot(t, z, color=_BLUE, linewidth=1.3, label="Z(t)")
    ax.scatter(gam, np.zeros_like(gam), s=30, facecolor="white", edgecolor=_INK,
               linewidth=1.0, zorder=5, label="zero of Z  (= ζ zero on the line)")
    ax.scatter(grams, np.zeros(len(grams)), s=70, marker="|", color=_ORANGE,
               linewidth=1.4, zorder=4, label="Gram point g_n  (θ(g_n) = nπ)")
    _style(ax, xlabel="t", ylabel="Z(t)  (real by construction)",
           title="Hardy's Z(t) = e^{iθ(t)}ζ(½+it) is real: each sign change certifies a zero on the line;"
                 " Gram points interlace them")
    ax.set_xlim(0, t_max)
    _legend(ax, loc="upper left", ncols=3)
    return _finish(fig, save_path, dpi)


# --------------------------------------------------------------------------- #
# 3. domain colouring of zeta over the critical strip
# --------------------------------------------------------------------------- #


def _zeta_grid(re_range: tuple[float, float], im_range: tuple[float, float],
               nx: int, ny: int, cache: bool) -> np.ndarray:
    """Complex ζ values on a grid, cached to ``data/`` (fp.zeta ≈ 40 µs/point)."""
    from mpmath import fp

    r0, r1 = float(re_range[0]), float(re_range[1])
    i0, i1 = float(im_range[0]), float(im_range[1])
    path = os.path.join(
        _DATA_DIR, f"domain_coloring_{r0:g}_{r1:g}_{i0:g}_{i1:g}_{nx}x{ny}.npz"
    )
    if cache and os.path.exists(path):
        with np.load(path) as fh:
            box = fh["box"]
            if tuple(box) == (r0, r1, i0, i1) and fh["Z"].shape == (ny, nx):
                return fh["Z"]
    xs = np.linspace(r0, r1, nx)
    ys = np.linspace(i0, i1, ny)
    Z = np.empty((ny, nx), dtype=complex)
    for j, y in enumerate(ys):
        for i, x in enumerate(xs):
            try:
                Z[j, i] = complex(fp.zeta(complex(x, y)))
            except (ValueError, ZeroDivisionError, OverflowError):
                Z[j, i] = np.nan  # the pole s = 1, if the grid lands on it
    if cache:
        os.makedirs(_DATA_DIR, exist_ok=True)
        np.savez_compressed(path, Z=Z, box=np.array([r0, r1, i0, i1]))
    return Z


def plot_zeta_domain_coloring(re_range: tuple[float, float] = (-7.5, 4.5),
                              im_range: tuple[float, float] = (-3.0, 45.0),
                              nx: int = 360, ny: int = 560,
                              save_path: str | None = None, dpi: int = 160,
                              cache: bool = True) -> Figure:
    """Domain colouring (phase portrait) of ζ(s) over the critical strip.

    Encoding — the standard one for complex phase, which is genuinely cyclic:

    * **hue**  = arg ζ(s), full colour wheel per 2π;
    * **brightness** = |ζ(s)| via L = 1 − 1/(1+|ζ|^0.28): zeros are *black*,
      the pole at s = 1 is *white*;
    * faint rings mark |ζ| doubling contours (fractional part of log₂|ζ|).

    Every point where all hues meet in a black dot is a zero.  The figure shows
    the trivial zeros marching down the negative real axis at −2, −4, −6 and
    every nontrivial zero sitting on Re s = ½ — dead centre of the strip
    0 ≤ Re s ≤ 1 — which is the Riemann Hypothesis as a picture.

    The ζ grid (mpmath ``fp.zeta``) is cached to ``data/`` keyed by the window
    and resolution, so re-plotting is instant.
    """
    Z = _zeta_grid(re_range, im_range, int(nx), int(ny), cache)

    with np.errstate(divide="ignore", invalid="ignore", over="ignore"):
        mag = np.abs(Z)
        h = (np.angle(Z) / (2.0 * np.pi)) % 1.0
        L = 1.0 - 1.0 / (1.0 + mag**0.28)          # 0 at zeros → 1 at the pole
        band = np.log2(mag)
        band = band - np.floor(band)                # fractional part ∈ [0,1)
        ring = 0.90 + 0.10 * band                   # subtle modulus contours
        V = np.clip((L * ring) ** 0.62, 0.0, 1.0)   # gamma-lift keeps midtones bright
        S = 0.82 * (1.0 - L**5)                     # desaturate toward the pole
    bad = ~np.isfinite(mag)
    h[bad], S[bad], V[bad] = 0.0, 0.0, 1.0          # pole cell → white
    rgb = hsv_to_rgb(np.dstack([h, S, V]))

    fig, (ax,) = _fig(figsize=(6.6, 8.2))
    ax.imshow(rgb, origin="lower", aspect="auto",
              extent=(re_range[0], re_range[1], im_range[0], im_range[1]),
              interpolation="nearest")
    for x, ls, lw in ((0.0, "--", 0.9), (1.0, "--", 0.9), (0.5, "-", 0.8)):
        ax.axvline(x, color="white", linestyle=ls, linewidth=lw, alpha=0.85)

    gam = _gammas_below(im_range[1])
    if im_range[0] < 0:
        gam_all = np.concatenate([gam, -gam[gam < -im_range[0]]])
    else:
        gam_all = gam
    ax.scatter(np.full(gam_all.size, 0.5), gam_all, s=42, facecolor="none",
               edgecolor="white", linewidth=1.1, zorder=5)
    triv = np.arange(-2.0, math.floor(re_range[0]) - 1.0, -2.0)
    triv = triv[triv >= re_range[0]]
    ax.scatter(triv, np.zeros_like(triv), s=42, facecolor="none",
               edgecolor="white", linewidth=1.1, zorder=5)
    ax.scatter([1.0], [0.0], s=70, marker="*", facecolor="white",
               edgecolor=_INK, linewidth=0.5, zorder=6)

    handles = [
        Line2D([], [], marker="o", mfc="none", mec=_INK, ls="none", ms=7,
               label="zero of ζ (black in the portrait)"),
        Line2D([], [], marker="*", mfc="white", mec=_INK, ls="none", ms=10,
               label="pole at s = 1 (white)"),
        Line2D([], [], color=_MUTED, ls="--", lw=1, label="strip edges Re s = 0, 1"),
        Line2D([], [], color=_MUTED, ls="-", lw=1, label="critical line Re s = ½"),
    ]
    leg = ax.legend(handles=handles, loc="upper left", fontsize=8,
                    labelcolor=_SECONDARY, framealpha=0.9, facecolor=_SURFACE,
                    edgecolor=_BASELINE)
    leg.set_zorder(7)

    phase = np.linspace(-0.5, 0.5, 256) % 1.0   # same map as the image: arg/2π mod 1
    wheel = hsv_to_rgb(np.dstack([phase, np.full_like(phase, 0.82),
                                  np.full_like(phase, 0.88)]))[0]
    sm = plt.cm.ScalarMappable(cmap=ListedColormap(wheel), norm=Normalize(-np.pi, np.pi))
    cb = fig.colorbar(sm, ax=ax, orientation="horizontal", fraction=0.045,
                      pad=0.06, aspect=35)
    cb.set_ticks([-np.pi, 0.0, np.pi])
    cb.set_ticklabels(["−π", "0", "π"])
    cb.set_label("hue = arg ζ(s);  brightness = |ζ(s)| (black → zero, white → pole)",
                 color=_SECONDARY, fontsize=8.5)
    cb.ax.tick_params(colors=_MUTED, labelcolor=_SECONDARY, labelsize=8)
    cb.outline.set_edgecolor(_BASELINE)

    ax.tick_params(colors=_MUTED, labelcolor=_SECONDARY, labelsize=8.5)
    for side in ("top", "right", "left", "bottom"):
        ax.spines[side].set_color(_BASELINE)
    ax.set_xlabel("Re s", color=_SECONDARY, fontsize=9.5)
    ax.set_ylabel("Im s", color=_SECONDARY, fontsize=9.5)
    ax.set_title("Phase portrait of ζ(s): trivial zeros at −2, −4, −6 …;  every nontrivial zero\n"
                 "on Re s = ½, dead centre of the critical strip (that is RH)",
                 color=_INK, fontsize=11, loc="left", pad=10)
    return _finish(fig, save_path, dpi)


# --------------------------------------------------------------------------- #
# 4. theta modularity
# --------------------------------------------------------------------------- #


def plot_theta_modularity(x_min: float = 0.15, x_max: float = 6.0,
                          n_points: int = 300, n_defect: int = 90,
                          save_path: str | None = None, dpi: int = 160) -> Figure:
    """θ(1/x)/√x laid over θ(x): Jacobi's modular relation, then its defect.

        θ(x) = Σ_{n∈ℤ} e^{−πn²x}  satisfies  θ(1/x) = √x · θ(x)   (x > 0),

    which is Poisson summation applied to a Gaussian — and the single identity
    from which Riemann's functional equation ξ(s) = ξ(1−s) descends.  Both
    sides are *summed directly* (:func:`zeta.core.theta` never uses the
    relation internally), so the overlay is evidence, not a tautology.  The
    lower panel shows |θ(1/x) − √x θ(x)| computed at 30 significant digits:
    it sits at the round-off floor (≲ 10⁻⁴⁵), i.e. the identity is exact.
    """
    from zeta.core import theta, theta_modular_defect

    xs = np.geomspace(float(x_min), float(x_max), int(n_points))
    lhs = np.array([float(theta(x, dps=20)) for x in xs])
    rhs = np.array([float(theta(1.0 / x, dps=20)) / math.sqrt(x) for x in xs])

    xd = np.geomspace(float(x_min), float(x_max), int(n_defect))
    defect = np.array([abs(float(theta_modular_defect(x, dps=30))) for x in xd])
    defect = np.maximum(defect, 1e-60)  # exact zeros would break the log axis

    fig, (ax0, ax1) = _fig(nrows=2, figsize=(7.8, 5.8), height_ratios=(2.4, 1.0),
                           sharex=True)
    ax0.plot(xs, lhs, color=_BLUE, linewidth=2.4, label="θ(x), summed directly")
    ax0.plot(xs, rhs, color=_ORANGE, linewidth=1.4, linestyle=(0, (5, 4)),
             label="θ(1/x)/√x, summed independently")
    ax0.set_xscale("log")
    _style(ax0, ylabel="θ  (dimensionless)",
           title="Poisson summation as a picture: θ(1/x) = √x·θ(x) — two independent sums, one curve")
    _legend(ax0, loc="upper right")

    worst = float(defect.max())
    ax1.scatter(xd, defect, s=9, color=_BLUE, zorder=3)
    ax1.set_yscale("log")
    ax1.set_ylim(1e-60, 1e-30)
    ax1.set_xticks([0.2, 0.5, 1.0, 2.0, 5.0])
    ax1.set_xticklabels(["0.2", "0.5", "1", "2", "5"])
    ax1.tick_params(axis="x", which="minor", labelbottom=False)
    _style(ax1, xlabel="x  (log scale)", ylabel="|θ(1/x) − √x θ(x)|")
    ax1.annotate(f"worst defect {worst:.1e} at 30 working digits — pure round-off"
                 " (points on the bottom edge computed exactly 0)",
                 xy=(0.02, 0.82), xycoords="axes fraction", color=_SECONDARY, fontsize=8.5)
    return _finish(fig, save_path, dpi)


# --------------------------------------------------------------------------- #
# 5. heat evolution on the circle
# --------------------------------------------------------------------------- #


def plot_theta_heat_evolution(times: Sequence[float] = (0.0008, 0.002, 0.005, 0.012, 0.03, 0.08),
                              n_points: int = 481,
                              save_path: str | None = None, dpi: int = 160) -> Figure:
    """The heat kernel Θ(x,t) on the circle ℝ/ℤ at several times — the PDE picture.

        Θ(x,t) = Σ_{n∈ℤ} e^{−4π²n²t} e^{2πinx}   solves   ∂ₜΘ = ∂ₓ²Θ,  Θ(·,0⁺) = δ₀.

    A spike of heat spreads and relaxes to the uniform equilibrium Θ ≡ 1; the
    total heat ∫₀¹ Θ dx = 1 (the n = 0 Fourier mode) is conserved exactly.
    This Θ is the heat-kernel avatar of the Jacobi θ: Θ(0,t) = θ(4πt), and its
    small-t/large-t duality *is* the modular relation of the previous figure.
    Values come from the spectral sum :func:`zeta.core.theta_heat`.
    """
    from zeta.core import theta_heat

    ts = sorted(float(t) for t in times)
    xs = np.linspace(-0.5, 0.5, int(n_points))
    ramp_idx = np.linspace(1, len(_BLUE_RAMP) - 1, len(ts)).round().astype(int)

    fig, (ax,) = _fig(figsize=(7.8, 4.9))
    ax.axhline(1.0, color=_MUTED, linewidth=1.0, linestyle="--")
    masses = []
    for k, t in enumerate(ts):
        u = np.array([float(theta_heat(x, t, dps=12)) for x in xs])
        masses.append(float(np.trapezoid(u, xs)))
        ax.plot(xs, u, color=_BLUE_RAMP[ramp_idx[k]], linewidth=1.7,
                label=f"t = {t:g}")
    ax.annotate("equilibrium Θ ≡ 1", xy=(0.335, 1.0), xytext=(0.30, 2.1),
                color=_SECONDARY, fontsize=8.5,
                arrowprops=dict(arrowstyle="-", color=_BASELINE, lw=0.8))
    worst = max(abs(m - 1.0) for m in masses)
    ax.annotate(f"heat is conserved: ∫₀¹Θ dx = 1 at every t (checked to {worst:.1e})",
                xy=(0.02, 0.955), xycoords="axes fraction", color=_SECONDARY, fontsize=8.5)
    _style(ax, xlabel="x  (position on the circle ℝ/ℤ, period 1)",
           ylabel="temperature Θ(x, t)",
           title="Heat on the circle: Θ(x,t) = Σₙ e^{−4π²n²t}e^{2πinx} solves ∂ₜΘ = ∂ₓ²Θ —\n"
                 "a δ-spike relaxing to uniform, mass conserved")
    _legend(ax, loc="upper right", title="time t", title_fontsize=8.5)
    ax.set_xlim(-0.5, 0.5)
    return _finish(fig, save_path, dpi)


# --------------------------------------------------------------------------- #
# 6. the explicit formula: psi from the zeros
# --------------------------------------------------------------------------- #


def plot_explicit_formula(x_max: float = 100.0,
                          zero_counts: Sequence[int] = (0, 10, 100, 500),
                          n_points: int = 2400,
                          save_path: str | None = None, dpi: int = 160) -> Figure:
    """Chebyshev's ψ staircase versus von Mangoldt's explicit formula.

        ψ₀(x) = x − Σ_ρ x^ρ/ρ − log 2π − ½ log(1 − x⁻²)

    Each conjugate pair ρ = ½ ± iγ contributes one harmonic
    2√x·cos(γ log x − arg ρ)/|ρ|; the figure superposes the partial sums over
    the first N zeros for each N in ``zero_counts`` on top of the *exact*
    arithmetic staircase ψ(x) = Σ_{pᵏ≤x} log p.  With N = 0 only the smooth
    terms survive; as N grows the waves interfere into the jumps at the prime
    powers — the primes reconstructed from the zeros.
    """
    from zeta.explicit import psi_curve, psi_staircase

    counts = sorted(int(c) for c in zero_counts)
    xs = np.linspace(2.0, float(x_max), int(n_points))
    exact = psi_staircase(xs)

    fig, (ax,) = _fig(figsize=(8.8, 5.2))
    ax.plot(xs, exact, color=_INK, linewidth=1.6,
            label="ψ(x) exact  (jump log p at every pᵏ)", zorder=5)
    ramp_idx = np.linspace(1, len(_BLUE_RAMP) - 1, len(counts)).round().astype(int)
    for k, N in enumerate(counts):
        approx = psi_curve(xs, N)
        ax.plot(xs, approx, color=_BLUE_RAMP[ramp_idx[k]], linewidth=1.25,
                label=f"explicit formula, first {N} zero{'s' if N != 1 else ''}")
    _style(ax, xlabel="x", ylabel="ψ(x) = Σ_{pᵏ ≤ x} log p",
           title="Von Mangoldt's explicit formula  ψ₀(x) = x − Σ_ρ x^ρ/ρ − log 2π − ½log(1−x⁻²):\n"
                 "every zero adds one harmonic — the staircase of primes emerges from the zeros")
    _legend(ax, loc="upper left")
    ax.set_xlim(2.0, x_max)
    return _finish(fig, save_path, dpi)


# --------------------------------------------------------------------------- #
# 7. the prime spectrum
# --------------------------------------------------------------------------- #


def plot_prime_spectrum(n_zeros: int = 500, x_max: float = 50.0,
                        n_points: int = 6000, window: str = "gauss",
                        save_path: str | None = None, dpi: int = 160) -> Figure:
    """"The music of the primes": the zero-side spike train D(u) = −2Σ w(γ)cos(γu).

    Differentiating the explicit formula in u = log x turns the ψ staircase
    into a comb: the purely oscillatory part of the density of prime powers,

        D(u) = −2 Σ_{γ>0} w(γ) cos(γu),

    has a spike at u = log pᵏ of height Λ(pᵏ)/√pᵏ — and nowhere else.  The
    orange stems are that *prediction* drawn from the primes alone; the blue
    curve is built from the zeros alone.  They agree peak by peak.
    """
    from zeta.explicit import mangoldt, prime_spectrum

    u = np.linspace(math.log(1.5), math.log(float(x_max)), int(n_points))
    D = prime_spectrum(int(n_zeros), u, window=window)

    stems = [(n, math.log(n), mangoldt(n) / math.sqrt(n))
             for n in range(2, int(x_max) + 1) if mangoldt(n) > 0.0]

    fig, (ax,) = _fig(figsize=(9.2, 4.7))
    ax.axhline(0.0, color=_BASELINE, linewidth=0.8)
    for i, (n, un, h) in enumerate(stems):
        ax.vlines(un, 0.0, h, color=_ORANGE, linewidth=1.5, alpha=0.95, zorder=3,
                  label="predicted comb: height Λ(pᵏ)/√pᵏ at u = log pᵏ" if i == 0 else None)
        ax.scatter([un], [h], s=14, color=_ORANGE, zorder=4)
        ax.annotate(str(n), xy=(un, h), xytext=(0, 5 + 8 * (i % 2)),
                    textcoords="offset points", ha="center",
                    color=_SECONDARY, fontsize=7)
    ax.plot(u, D, color=_BLUE, linewidth=1.1, zorder=2,
            label=f"D(u) = −2Σ w(γ)cos(γu), first {int(n_zeros)} zeros ('{window}' taper)")
    _style(ax, xlabel="u = log x   (spikes at log 2, log 3, log 4, log 5, …)",
           ylabel="spectral density D(u)",
           title="The music of the primes: a cosine sum over the zeros alone spikes exactly at\n"
                 "u = log pᵏ with height Λ(pᵏ)/√pᵏ — the primes are the spectrum of the zeros")
    top = max(h for _, _, h in stems) if stems else 1.0
    ax.set_ylim(min(-0.12, float(D.min()) * 1.2), top * 1.45)
    _legend(ax, loc="upper right")
    ax.set_xlim(u[0] - 0.02, u[-1] + 0.06)
    return _finish(fig, save_path, dpi)


# --------------------------------------------------------------------------- #
# 8. spacing histogram vs GUE vs Poisson
# --------------------------------------------------------------------------- #


def plot_spacing_histogram(t_max: float = 10000.0, bins: int = 40,
                           save_path: str | None = None, dpi: int = 160) -> Figure:
    """Nearest-neighbour spacings of the unfolded zeros vs GUE and Poisson.

    Ordinates are unfolded to unit mean density by the exact smooth counting
    function, γ̃ = θ(γ)/π, and consecutive gaps sₙ = γ̃ₙ₊₁ − γ̃ₙ are histogrammed
    against

    * the exact N → ∞ GUE law (Gaudin distribution, p = E″(0;s) from the
      sine-kernel Fredholm determinant),
    * the 2×2 Wigner surmise p(s) = (32/π²)s²e^{−4s²/π}, and
    * the Poisson law e^{−s} of uncorrelated points.

    The p(s) ~ s² vanishing at s = 0 is quadratic *level repulsion*: the zeros
    behave like eigenvalues of a random Hermitian matrix, not like darts.
    """
    from zeta.statistics import (gue_spacing_exact, nearest_neighbour_spacings,
                                 poisson_spacing, wigner_surmise_gue)

    g = _gammas_below(t_max)
    s = nearest_neighbour_spacings(g)
    grid = np.linspace(0.0, 3.2, 400)

    fig, (ax,) = _fig(figsize=(7.6, 4.9))
    dens, edges = np.histogram(s, bins=int(bins), range=(0.0, 3.2), density=True)
    centers = 0.5 * (edges[:-1] + edges[1:])
    width = edges[1] - edges[0]
    ax.bar(centers, dens, width=width * 0.9, color=_BLUE_RAMP[1], zorder=2,
           label=f"zeta zeros: {s.size} spacings below T = {t_max:g}")
    ax.plot(grid, gue_spacing_exact(grid), color=_ORANGE, linewidth=2.0, zorder=4,
            label="GUE, exact (Gaudin: p = E″ of the sine kernel)")
    ax.plot(grid, wigner_surmise_gue(grid), color=_AQUA, linewidth=1.4,
            linestyle=":", zorder=4, label="Wigner surmise (32/π²)s²e^{−4s²/π}")
    ax.plot(grid, poisson_spacing(grid), color=_MUTED, linewidth=1.4,
            linestyle="--", zorder=3, label="Poisson e^{−s} (uncorrelated null)")
    ax.annotate("p(s) → 0 like s²:\nlevel repulsion", xy=(0.12, 0.12),
                xytext=(0.42, 0.28), color=_SECONDARY, fontsize=8.5,
                arrowprops=dict(arrowstyle="->", color=_SECONDARY, lw=0.9))
    _style(ax, xlabel="unfolded spacing s   (⟨s⟩ = 1 by construction, γ̃ = θ(γ)/π)",
           ylabel="probability density p(s)",
           title="Zeros repel like GUE eigenvalues: their spacing law is Gaudin's, not Poisson's")
    _legend(ax, loc="upper right")
    ax.set_xlim(0, 3.2)
    return _finish(fig, save_path, dpi)


# --------------------------------------------------------------------------- #
# 9. pair correlation vs Montgomery
# --------------------------------------------------------------------------- #


def plot_pair_correlation(t_max: float = 10000.0, r_max: float = 3.0,
                          bins: int = 60, save_path: str | None = None,
                          dpi: int = 160) -> Figure:
    """Empirical pair correlation of the zeros vs Montgomery's R₂(r) = 1 − (sin πr/πr)².

    Montgomery (1973) conjectured — and Dyson recognised as the GUE two-point
    function — that the unfolded zeros have pair correlation
    R₂(r) = 1 − (sin πr / πr)².  The *correlation hole* at r = 0 is the
    repulsion of the previous figure seen through every pair, not just
    neighbours; a Poisson process would sit flat at R₂ ≡ 1.
    """
    from zeta.statistics import montgomery_prediction, pair_correlation

    g = _gammas_below(t_max)
    r, R2 = pair_correlation(g, r_max=float(r_max), bins=int(bins))
    grid = np.linspace(0.0, float(r_max), 500)

    fig, (ax,) = _fig(figsize=(7.8, 4.7))
    ax.axhline(1.0, color=_MUTED, linewidth=1.2, linestyle="--",
               label="Poisson (uncorrelated): R₂ ≡ 1")
    ax.plot(grid, montgomery_prediction(grid), color=_ORANGE, linewidth=2.0,
            zorder=4, label="Montgomery–GUE:  1 − (sin πr / πr)²")
    ax.plot(r, R2, color=_BLUE, linewidth=0.9, alpha=0.55, zorder=3)
    ax.scatter(r, R2, s=16, color=_BLUE, zorder=5,
               label=f"zeta zeros below T = {t_max:g} ({g.size} zeros, unfolded)")
    ax.annotate("correlation hole:\nzeros never crowd", xy=(0.08, 0.05),
                xytext=(0.35, 0.22), color=_SECONDARY, fontsize=8.5,
                arrowprops=dict(arrowstyle="->", color=_SECONDARY, lw=0.9))
    _style(ax, xlabel="unfolded pair separation r", ylabel="pair correlation R₂(r)",
           title="Montgomery's pair correlation: every pair of zeros avoids coincidence exactly as\n"
                 "GUE eigenvalues do — R₂(r) = 1 − (sin πr/πr)²")
    _legend(ax, loc="lower right")
    ax.set_xlim(0, r_max)
    ax.set_ylim(-0.05, 1.35)
    return _finish(fig, save_path, dpi)


# --------------------------------------------------------------------------- #
# 10. N(T) staircase, Riemann-von Mangoldt, S(T)
# --------------------------------------------------------------------------- #


def plot_zero_counting(t_max: float = 200.0, save_path: str | None = None,
                       dpi: int = 160) -> Figure:
    """The zero-counting staircase N(T) vs the Riemann–von Mangoldt law, and S(T).

        N(T) = θ(T)/π + 1 + S(T),        S(T) = (1/π) arg ζ(½ + iT).

    Top: the exact integer staircase (one step per zero ordinate) hugs the
    smooth main term (T/2π)log(T/2π) − T/2π + 7/8 to within a fraction of a
    step.  Bottom: the difference S(T) — computed here as
    N(T) − 1 − θ(T)/π with the *exact* θ — oscillates around zero with |S| < 1
    at these heights while jumping by +1 across every ordinate.  S is O(log T)
    yet is precisely what makes N(T) an integer.
    """
    from zeta.statistics import riemann_siegel_theta
    from zeta.zeros import riemann_von_mangoldt

    t_max = float(t_max)
    g = _gammas_below(t_max)
    T = np.linspace(5.0, t_max, 3000)
    smooth = np.array([riemann_von_mangoldt(x) for x in T])
    S = np.searchsorted(g, T) - 1.0 - riemann_siegel_theta(T) / np.pi

    fig, (ax0, ax1) = _fig(nrows=2, figsize=(8.8, 6.0), height_ratios=(2.2, 1.0),
                           sharex=True)
    steps_x = np.concatenate([[0.0], g, [t_max]])
    steps_y = np.concatenate([[0.0], np.arange(1, g.size + 1), [float(g.size)]])
    ax0.step(steps_x, steps_y, where="post", color=_INK, linewidth=1.5,
             label="N(T): exact count of zeros with 0 < γ < T", zorder=4)
    ax0.plot(T, smooth, color=_ORANGE, linewidth=1.8, zorder=3,
             label="Riemann–von Mangoldt main term (T/2π)log(T/2π) − T/2π + 7/8")
    ax0.annotate(f"N({t_max:g}) = {g.size}", xy=(0.985, 0.06), xycoords="axes fraction",
                 ha="right", color=_SECONDARY, fontsize=9)
    _style(ax0, ylabel="N(T)  (number of zeros)",
           title="Riemann–von Mangoldt:  N(T) = θ(T)/π + 1 + S(T) — the staircase of zeros hugs the\n"
                 "smooth law; the leftover wiggle is S(T)")
    _legend(ax0, loc="upper left")

    ax1.axhline(0.0, color=_MUTED, linewidth=1.0, linestyle="--")
    ax1.plot(T, S, color=_BLUE, linewidth=0.9,
             label="S(T) = N(T) − 1 − θ(T)/π  = (1/π) arg ζ(½+iT)")
    _style(ax1, xlabel="height T", ylabel="S(T)")
    _legend(ax1, loc="upper left")
    ax1.set_xlim(0, t_max)
    return _finish(fig, save_path, dpi)


# --------------------------------------------------------------------------- #
# 11. de Bruijn-Newman heat-flow trajectories
# --------------------------------------------------------------------------- #


def plot_heatflow_trajectories(t_values: Sequence[float] = (-0.4, -0.2, 0.0, 0.2, 0.4, 0.6),
                               n_zeros: int = 10, z_max: float = 105.0,
                               save_path: str | None = None, dpi: int = 160) -> Figure:
    """Zeros of H_t under the backward heat flow — the de Bruijn–Newman picture.

        H_t(z) = ∫₀^∞ e^{tu²} Φ(u) cos(zu) du,      H₀(z) = Ξ(z/2)/8,

    so at t = 0 the real zeros are exactly z = 2γₙ.  H_t satisfies
    ∂H/∂t = −∂²H/∂z² (backward heat equation): *increasing* t makes the real
    zeros repel — every gap widens, and the minimum gap (lower panel) grows
    monotonically.  Decreasing t is the attracting direction; zeros can only
    leave the real axis by first colliding, which is what happens below the
    de Bruijn–Newman constant Λ (RH ⟺ Λ = 0, and Rodgers–Tao proved Λ ≥ 0).
    Trajectories come from :func:`zeta.heatflow.track_zeros` (cached).
    """
    from zeta.heatflow import track_zeros

    res = track_zeros(list(t_values), z_max=float(z_max), n_zeros=int(n_zeros),
                      dps=None)
    ts = res["t_values"]
    zs = res["zeros"]  # (n_t, n_zeros)

    fig, (ax0, ax1) = _fig(nrows=2, figsize=(8.2, 6.2), height_ratios=(2.6, 1.0),
                           sharex=True)
    ax0.axvline(0.0, color=_MUTED, linewidth=1.0, linestyle="--")
    i0 = int(np.argmin(np.abs(ts)))
    for k in range(zs.shape[1]):
        ax0.plot(ts, zs[:, k], color=_BLUE, linewidth=1.4, marker="o",
                 markersize=3.2, label="zeros of H_t" if k == 0 else None)
    ax0.annotate("t = 0:  H₀ = Ξ(z/2)/8 — zeros at z = 2γₙ",
                 xy=(0.0, float(zs[i0, -1])), xytext=(8, 6),
                 textcoords="offset points", color=_SECONDARY, fontsize=8.5)
    ax0.annotate(f"z = 2γ₁ = {zs[i0, 0]:.2f}", xy=(0.0, float(zs[i0, 0])),
                 xytext=(8, -11), textcoords="offset points",
                 color=_SECONDARY, fontsize=8.5)
    _style(ax0, ylabel="position z of the real zeros of H_t",
           title="The de Bruijn–Newman flow  ∂H/∂t = −∂²H/∂z²:  for t > 0 the zeros of H_t repel;\n"
                 "collisions (→ complex pairs) can only happen for t < Λ, and RH ⟺ Λ = 0")
    _legend(ax0, loc="center left")

    ax1.plot(ts, res["min_gap"], color=_ORANGE, linewidth=1.7, marker="o",
             markersize=3.6, label="minimum gap between consecutive zeros")
    _style(ax1, xlabel="heat-flow time t", ylabel="min gap")
    ax1.annotate("monotone in t: repulsion", xy=(0.62, 0.18),
                 xycoords="axes fraction", color=_SECONDARY, fontsize=8.5)
    _legend(ax1, loc="upper left")
    return _finish(fig, save_path, dpi)


# --------------------------------------------------------------------------- #
# 12. polynomial root repulsion
# --------------------------------------------------------------------------- #


def plot_polynomial_root_repulsion(roots: Sequence[float] = (-3.0, -1.0, 0.5, 2.0, 4.5),
                                   t_min: float = -1.1, t_max: float = 0.7,
                                   n_t: int = 181, save_path: str | None = None,
                                   dpi: int = 160) -> Figure:
    """The Λ story in miniature: heat flow on a real polynomial's roots.

    Flow p(x) = Π(x − rᵢ) by p_t = exp(−t d²/dx²) p — the same sign convention
    as H_t.  The roots then obey the repulsive Coulomb dynamics

        drᵢ/dt = +2 Σ_{j≠i} 1/(rᵢ − rⱼ),

    so for t > 0 they spread apart, and running backwards (t < 0) they attract:
    at the first collision a pair leaves the real axis as a complex-conjugate
    pair (red).  That collision time is this toy model's "Λ".  Data from
    :func:`zeta.heatflow.polynomial_heat_flow`, which also verifies the ODE
    against exact coefficient evolution.
    """
    from zeta.heatflow import polynomial_heat_flow

    ts = np.linspace(float(t_min), float(t_max), int(n_t))
    res = polynomial_heat_flow(list(roots), ts)
    tv = res["t_values"]
    rr = res["roots_exact"]  # (n_t, n) complex
    is_real = np.abs(rr.imag) < 1e-8

    fig, (ax0, ax1) = _fig(nrows=2, figsize=(8.4, 6.2), height_ratios=(2.4, 1.0),
                           sharex=True)
    ax0.axvline(0.0, color=_MUTED, linewidth=1.0, linestyle="--")
    tt = np.broadcast_to(tv[:, None], rr.shape)
    ax0.scatter(tt[is_real], rr.real[is_real], s=5, color=_BLUE, zorder=3)
    ax0.scatter(tt[~is_real], rr.real[~is_real], s=5, color=_RED, zorder=4)
    coll = res["collision_t"]
    if coll is not None:
        ax0.axvline(coll, color=_RED, linewidth=1.0, linestyle=":")
        ax0.annotate(f"first collision ≈ {coll:.3f}\n(this model's 'Λ')",
                     xy=(coll, float(np.nanmax(rr.real)) * 0.55), xytext=(6, 0),
                     textcoords="offset points", color=_SECONDARY, fontsize=8.5)
    handles = [
        Line2D([], [], marker="o", color=_BLUE, ls="none", ms=5, label="real roots"),
        Line2D([], [], marker="o", color=_RED, ls="none", ms=5,
               label="Re of a complex-conjugate pair (left the axis)"),
    ]
    ax0.legend(handles=handles, frameon=False, fontsize=8.5, labelcolor=_SECONDARY,
               loc="upper left")
    _style(ax0, ylabel="root position (real part)",
           title="Heat flow exp(−t d²/dx²) on a polynomial:  drᵢ/dt = +2Σ 1/(rᵢ−rⱼ) — roots repel\n"
                 "for t > 0; run backwards they collide and escape into ℂ, exactly like H_t below Λ")

    ax1.plot(tv, res["min_gap"], color=_BLUE, linewidth=1.6,
             label="min gap of the real roots")
    ax1.plot(tv, res["max_abs_imag"], color=_RED, linewidth=1.6,
             label="max |Im root|  (> 0 ⇔ off the real axis)")
    ax1.axhline(0.0, color=_BASELINE, linewidth=0.8)
    _style(ax1, xlabel="heat-flow time t", ylabel="gap / |Im|")
    _legend(ax1, loc="upper right")
    err = res["max_ode_error"]
    ax1.annotate(f"ODE vs exact coefficient flow: max deviation {err:.1e}",
                 xy=(0.30, 0.80), xycoords="axes fraction",
                 color=_SECONDARY, fontsize=8)
    return _finish(fig, save_path, dpi)


# --------------------------------------------------------------------------- #
# 13. Weil positivity across test-function families
# --------------------------------------------------------------------------- #


def plot_weil_positivity(gaussian_points: int = 7, fejer_points: int = 5,
                         dps: int = 20, save_path: str | None = None,
                         dpi: int = 160) -> Figure:
    """The Weil functional W(h) over positive-type families: ≥ 0, and why barely.

    **Weil positivity criterion**: RH ⟺ W(h) = Σ_ρ h(γ_ρ) ≥ 0 for every
    admissible h of positive type.  W is computed here from the *arithmetic*
    side of the explicit formula (pole + archimedean − primes; no zeros
    anywhere), via :func:`zeta.weil.positivity_probe`, which escalates the
    working precision until every plotted sign is certified.

    Top: the Gaussian family h(r) = e^{−ar²}.  As a grows, h concentrates on
    the zero-free gap (−γ₁, γ₁) and W collapses *exponentially* along the
    prediction 2e^{−aγ₁²} — the margin of positivity is controlled by the
    single lowest zero γ₁ = 14.1347… (on the log axis the RH boundary W = 0
    is infinitely far below: approached, never attained).  Bottom: the Fejér
    family on a *linear* axis with the W = 0 line drawn — b²·W hovers about
    Σ_γ γ⁻² (≈ 0.023, of which 1/γ₁² alone is ~22%), safely above zero.

    Honest scope (docs/08): observed positivity reflects the verified zeros
    and is not evidence for RH.
    """
    from zeta.weil import GAMMA1, positivity_probe

    g_rows = positivity_probe("gaussian", n_points=int(gaussian_points), dps=dps)
    f_rows = positivity_probe("fejer", n_points=int(fejer_points), dps=dps)
    ga = np.array([r["param"] for r in g_rows])
    gW = np.array([float(r["W"]) for r in g_rows])
    fb = np.array([r["param"] for r in f_rows])
    fWb2 = np.array([float(r["W"]) * b * b for r, b in zip(f_rows, fb)])
    certified = all(r["positive"] for r in g_rows + f_rows)

    from zeta.statistics import zero_ordinates

    sum_inv_g2 = float(np.sum(zero_ordinates(t_max=10000.0) ** -2.0))

    fig, (ax0, ax1) = _fig(nrows=2, figsize=(8.2, 6.4), height_ratios=(2.2, 1.2))

    aa = np.geomspace(ga.min(), ga.max(), 400)
    ax0.plot(aa, 2.0 * np.exp(-aa * GAMMA1**2), color=_ORANGE, linewidth=2.0,
             zorder=3, label="2·exp(−a·γ₁²) — the first zero alone")
    ax0.plot(ga, gW, color=_BLUE, linewidth=1.1, alpha=0.55, zorder=4)
    ax0.scatter(ga, gW, s=26, color=_BLUE, zorder=5,
                label="W(h), arithmetic side (no zeros used); every sign certified > 0")
    ax0.set_xscale("log")
    ax0.set_yscale("log")
    ax0.annotate("W = 0 (the RH boundary) is the log-axis floor at −∞:\n"
                 "the margin collapses like 2·exp(−a·γ₁²) but never closes",
                 xy=(0.03, 0.10), xycoords="axes fraction",
                 color=_SECONDARY, fontsize=8.5)
    _style(ax0, xlabel="Gaussian parameter a   (h(r) = exp(−a·r²), log scale)",
           ylabel="W(h)  (log scale)",
           title="Weil positivity, measured:  W(h) = Σ_ρ h(γ_ρ) stays ≥ 0 over every family probed —\n"
                 "and its collapse toward 0 is controlled by the lowest zero γ₁ = 14.1347…")
    _legend(ax0, loc="upper right")

    ax1.axhline(0.0, color=_MUTED, linewidth=1.2, linestyle="--",
                label="W = 0 — where a counterexample to RH would live")
    ax1.axhline(sum_inv_g2, color=_ORANGE, linewidth=1.6, zorder=3,
                label=f"Σ_γ γ⁻² = {sum_inv_g2:.4f} (partial, γ < 10⁴; 1/γ₁² is 22% of it)")
    ax1.plot(fb, fWb2, color=_BLUE, linewidth=1.1, alpha=0.55, zorder=4)
    ax1.scatter(fb, fWb2, s=26, color=_BLUE, zorder=5,
                label="b²·W(h) for Fejér h(r) = (sin br/br)²")
    ax1.set_ylim(-0.008, max(float(fWb2.max()), sum_inv_g2) * 1.75)
    _style(ax1, xlabel="Fejér parameter b", ylabel="b²·W(h)")
    ax1.legend(frameon=True, fontsize=8.5, labelcolor=_SECONDARY, loc="upper right",
               framealpha=0.9, facecolor=_SURFACE, edgecolor=_BASELINE)
    if not certified:  # pragma: no cover — would indicate a bug upstream
        ax0.annotate("WARNING: an uncertified sign slipped through", xy=(0.35, 0.5),
                     xycoords="axes fraction", color=_RED, fontsize=10)
    return _finish(fig, save_path, dpi)


# --------------------------------------------------------------------------- #
# 14. the Davenport-Heilbronn off-line zero (the counterexample, as a picture)
# --------------------------------------------------------------------------- #


def _dh_grid(re_range: tuple[float, float], im_range: tuple[float, float],
             nx: int, ny: int, cache: bool) -> np.ndarray:
    """Complex Davenport–Heilbronn f values on a grid, cached to ``data/``.

    Bulk evaluation uses a vectorised Euler–Maclaurin Hurwitz zeta
    (float64; N scaled to the window height, 8 Bernoulli terms) in

        f(s) = 5^{−s}[ζ(s,1/5) + κ·ζ(s,2/5) − κ·ζ(s,3/5) − ζ(s,4/5)],

    with κ from :func:`zeta.epstein.kappa` (derived, not remembered).  The
    grid — fresh or from cache — is cross-checked against the mpmath-backed
    :func:`zeta.epstein.dh_f` at three interior points; relative disagreement
    above 1e-8 raises ``ArithmeticError`` (measured on the default window:
    ~1e-12, i.e. far below one pixel of the colour encoding).
    """
    from mpmath import mp

    from zeta.epstein import dh_f, kappa

    r0, r1 = float(re_range[0]), float(re_range[1])
    i0, i1 = float(im_range[0]), float(im_range[1])
    path = os.path.join(
        _DATA_DIR, f"dh_domain_coloring_{r0:g}_{r1:g}_{i0:g}_{i1:g}_{nx}x{ny}.npz"
    )
    F = None
    if cache and os.path.exists(path):
        with np.load(path) as fh:
            if tuple(fh["box"]) == (r0, r1, i0, i1) and fh["F"].shape == (ny, nx):
                F = fh["F"]
    if F is None:
        k = float(kappa(20))
        xs = np.linspace(r0, r1, nx)
        ys = np.linspace(i0, i1, ny)
        S = (xs[None, :] + 1j * ys[:, None]).ravel()
        n_terms = max(128, int(1.6 * max(abs(i0), abs(i1))))
        combo = np.zeros_like(S)
        for a_num, c in ((1, 1.0), (2, k), (3, -k), (4, -1.0)):
            a = a_num / 5.0
            hz = np.zeros_like(S)
            for n in range(n_terms):          # Σ_{n<N} (n+a)^{−s}, chunked
                hz += (n + a) ** (-S)
            Na = n_terms + a
            hz += Na ** (1.0 - S) / (S - 1.0) + 0.5 * Na ** (-S)
            bern = {2: 1 / 6, 4: -1 / 30, 6: 1 / 42, 8: -1 / 30,
                    10: 5 / 66, 12: -691 / 2730, 14: 7 / 6, 16: -3617 / 510}
            rising = S.copy()                 # (s)_1; then (s)_{2k−1} iteratively
            for kk in range(1, 9):
                hz += (bern[2 * kk] / math.factorial(2 * kk)
                       * rising * Na ** (-S - (2 * kk - 1)))
                rising = rising * (S + 2 * kk - 1) * (S + 2 * kk)
            combo += c * hz
        F = (5.0 ** (-S) * combo).reshape(ny, nx)
        if cache:
            os.makedirs(_DATA_DIR, exist_ok=True)
            np.savez_compressed(path, F=F, box=np.array([r0, r1, i0, i1]))
    # mandatory cross-check against the arbitrary-precision implementation
    xs = np.linspace(r0, r1, nx)
    ys = np.linspace(i0, i1, ny)
    for (ix, iy) in ((nx // 3, ny // 4), (2 * nx // 3, ny // 2), (nx // 2, 4 * ny // 5)):
        ref = complex(dh_f(mp.mpc(xs[ix], ys[iy]), dps=20))
        err = abs(complex(F[iy, ix]) - ref) / max(abs(ref), 1e-300)
        if not err < 1e-8:
            raise ArithmeticError(
                f"dh grid disagrees with zeta.epstein.dh_f at "
                f"({xs[ix]:.3f}, {ys[iy]:.3f}): rel err {err:.2e}"
            )
    return F


def _dh_line_zeros(t0: float, t1: float) -> list[float]:
    """Ordinates of the sign changes of Z_f on [t0, t1] (bisected to ~1e-4)."""
    from mpmath import mp

    from zeta.epstein import Z_dh

    lo, hi = float(t0), float(t1)
    n = max(int((hi - lo) / 0.06) + 2, 8)
    ts = np.linspace(lo, hi, n)
    vals = [float(Z_dh(mp.mpf(t), dps=12)) for t in ts]
    out = []
    for a, b, va, vb in zip(ts[:-1], ts[1:], vals[:-1], vals[1:]):
        if va == 0.0 or (va > 0) == (vb > 0):
            continue
        x0, x1, v0 = a, b, va
        while x1 - x0 > 1e-4:
            xm = 0.5 * (x0 + x1)
            vm = float(Z_dh(mp.mpf(xm), dps=12))
            if vm == 0.0:
                x0 = x1 = xm
            elif (vm > 0) == (v0 > 0):
                x0, v0 = xm, vm
            else:
                x1 = xm
        out.append(0.5 * (x0 + x1))
    return out


def plot_offline_zero(re_range: tuple[float, float] = (-0.75, 1.75),
                      im_range: tuple[float, float] = (83.0, 88.5),
                      nx: int = 240, ny: int = 340,
                      save_path: str | None = None, dpi: int = 160,
                      cache: bool = True) -> Figure:
    """Phase portrait of Davenport–Heilbronn's f around its OFF-line zero.

    Same encoding as :func:`plot_zeta_domain_coloring` (hue = arg f,
    brightness = |f|, black dots are zeros) on the strip window that contains

        ρ = 0.80851718… + 85.69934848…·i,       Re ρ − ½ = 0.3085…,

    the classical off-critical-line zero (located and verified to 50 digits
    by :mod:`zeta.epstein`; Spira 1994 lists 0.808517 + 85.699348i).  f has a
    Riemann-type functional equation F(s) = F(1−s) — perfect mirror symmetry
    about Re s = ½, visibly forcing the mirror partner 1 − ρ̄ — and yet the
    circled pair sits well off the line, while f's genuine line zeros (white)
    carry on above and below.  Symmetry alone cannot give RH: what f lacks is
    the Euler product (docs/08 §4.1, docs/09 gate #3).

    Grid values come from :func:`_dh_grid` (cached; cross-checked against the
    arbitrary-precision ``dh_f`` on every call), line zeros from a sign-change
    scan of ``Z_dh``.
    """
    from zeta.epstein import OFFLINE_ZERO_IM, OFFLINE_ZERO_RE

    F = _dh_grid(re_range, im_range, int(nx), int(ny), cache)
    rho_re, rho_im = float(OFFLINE_ZERO_RE), float(OFFLINE_ZERO_IM)

    with np.errstate(divide="ignore", invalid="ignore", over="ignore"):
        mag = np.abs(F)
        h = (np.angle(F) / (2.0 * np.pi)) % 1.0
        L = 1.0 - 1.0 / (1.0 + mag**0.28)
        band = np.log2(mag)
        band = band - np.floor(band)
        ring = 0.90 + 0.10 * band
        V = np.clip((L * ring) ** 0.62, 0.0, 1.0)
        S = 0.82 * (1.0 - L**5)
    rgb = hsv_to_rgb(np.dstack([h, S, V]))

    fig, (ax,) = _fig(figsize=(6.6, 8.0))
    ax.imshow(rgb, origin="lower", aspect="auto",
              extent=(re_range[0], re_range[1], im_range[0], im_range[1]),
              interpolation="nearest")
    for x, ls, lw in ((0.0, "--", 0.9), (1.0, "--", 0.9), (0.5, "-", 0.8)):
        ax.axvline(x, color="white", linestyle=ls, linewidth=lw, alpha=0.85)

    line_zeros = _dh_line_zeros(im_range[0], im_range[1])
    ax.scatter(np.full(len(line_zeros), 0.5), line_zeros, s=46, facecolor="none",
               edgecolor="white", linewidth=1.2, zorder=5)
    pair = [(rho_re, rho_im), (1.0 - rho_re, rho_im)]
    ax.scatter([p[0] for p in pair], [p[1] for p in pair], s=210, facecolor="none",
               edgecolor=_RED, linewidth=2.2, zorder=6)
    ax.annotate("ρ = 0.8085… + 85.6993…i\nRe ρ − ½ = +0.3085:  OFF the line",
                xy=(rho_re, rho_im), xytext=(0.985, 0.30), textcoords="axes fraction",
                ha="right", color="white", fontsize=8.5,
                arrowprops=dict(arrowstyle="->", color="white", lw=0.9))
    ax.annotate("mirror 1 − ρ̄\n(forced by F(s) = F(1−s))",
                xy=(1.0 - rho_re, rho_im), xytext=(0.015, 0.36),
                textcoords="axes fraction", color="white", fontsize=8.5,
                arrowprops=dict(arrowstyle="->", color="white", lw=0.9))

    handles = [
        Line2D([], [], marker="o", mfc="none", mec=_RED, ls="none", ms=9, mew=2,
               label="the off-line pair ρ, 1 − ρ̄  (RH is FALSE for f)"),
        Line2D([], [], marker="o", mfc="none", mec=_INK, ls="none", ms=7,
               label="zeros of f on the critical line (sign changes of Z_f)"),
        Line2D([], [], color=_MUTED, ls="-", lw=1, label="critical line Re s = ½"),
        Line2D([], [], color=_MUTED, ls="--", lw=1, label="strip edges Re s = 0, 1"),
    ]
    leg = ax.legend(handles=handles, loc="upper left", fontsize=8,
                    labelcolor=_SECONDARY, framealpha=0.9, facecolor=_SURFACE,
                    edgecolor=_BASELINE)
    leg.set_zorder(7)

    phase = np.linspace(-0.5, 0.5, 256) % 1.0
    wheel = hsv_to_rgb(np.dstack([phase, np.full_like(phase, 0.82),
                                  np.full_like(phase, 0.88)]))[0]
    sm = plt.cm.ScalarMappable(cmap=ListedColormap(wheel), norm=Normalize(-np.pi, np.pi))
    cb = fig.colorbar(sm, ax=ax, orientation="horizontal", fraction=0.045,
                      pad=0.06, aspect=35)
    cb.set_ticks([-np.pi, 0.0, np.pi])
    cb.set_ticklabels(["−π", "0", "π"])
    cb.set_label("hue = arg f(s);  brightness = |f(s)| (black → zero)",
                 color=_SECONDARY, fontsize=8.5)
    cb.ax.tick_params(colors=_MUTED, labelcolor=_SECONDARY, labelsize=8)
    cb.outline.set_edgecolor(_BASELINE)

    ax.tick_params(colors=_MUTED, labelcolor=_SECONDARY, labelsize=8.5)
    for side in ("top", "right", "left", "bottom"):
        ax.spines[side].set_color(_BASELINE)
    ax.set_xlabel("Re s", color=_SECONDARY, fontsize=9.5)
    ax.set_ylabel("Im s", color=_SECONDARY, fontsize=9.5)
    ax.set_title("Perfect mirror symmetry, zero OFF the line: Davenport–Heilbronn's f satisfies\n"
                 "F(s) = F(1−s) exactly — and RH fails for it.  Symmetry alone cannot give RH",
                 color=_INK, fontsize=11, loc="left", pad=10)
    return _finish(fig, save_path, dpi)

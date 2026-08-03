"""Publication-quality matplotlib figures for every part of the zeta laboratory.

Each public function builds one self-contained figure telling one mathematical
story, returns the ``matplotlib.figure.Figure``, and optionally saves it via a
``save_path`` argument.  The twenty figures, in narrative order:

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
15. :func:`plot_certified_enclosures`   — Z(t) inside rigorous bands that shrink with precision.
16. :func:`plot_li_coefficients`        — λ_n ≥ 0 against the RH-predicted growth.
17. :func:`plot_jensen_roots`           — Jensen-polynomial roots, all real, on the line.
18. :func:`plot_finite_field_rh`        — Frobenius eigenvalues on |α| = √p: RH, proved.
19. :func:`plot_sato_tate`              — a_p/(2√p) over all curves vs the semicircle.
20. :func:`plot_mertens`                — M(x)/√x, the random walk that misled a century.

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
:mod:`zeta.statistics`, :mod:`zeta.heatflow`, :mod:`zeta.rigor`,
:mod:`zeta.li`, :mod:`zeta.finitefield`, :mod:`zeta.criteria`),
whose results are cached under
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
    "plot_certified_enclosures",
    "plot_li_coefficients",
    "plot_jensen_roots",
    "plot_finite_field_rh",
    "plot_sato_tate",
    "plot_mertens",
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
    working precision until every plotted sign sits above its estimated noise
    floor.  That is a floating-point verdict, not a ball-arithmetic
    certificate — :func:`plot_certified_enclosures` is what the latter looks
    like.

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
    resolved = all(r["positive"] for r in g_rows + f_rows)

    from zeta.statistics import zero_ordinates

    sum_inv_g2 = float(np.sum(zero_ordinates(t_max=10000.0) ** -2.0))

    fig, (ax0, ax1) = _fig(nrows=2, figsize=(8.2, 6.4), height_ratios=(2.2, 1.2))

    aa = np.geomspace(ga.min(), ga.max(), 400)
    ax0.plot(aa, 2.0 * np.exp(-aa * GAMMA1**2), color=_ORANGE, linewidth=2.0,
             zorder=3, label="2·exp(−a·γ₁²) — the first zero alone")
    ax0.plot(ga, gW, color=_BLUE, linewidth=1.1, alpha=0.55, zorder=4)
    ax0.scatter(ga, gW, s=26, color=_BLUE, zorder=5,
                label="W(h), arithmetic side (no zeros used); every sign resolved > 0")
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
    if not resolved:  # pragma: no cover — would indicate a bug upstream
        ax0.annotate("WARNING: a sign stayed inside the noise floor", xy=(0.35, 0.5),
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


# --------------------------------------------------------------------------- #
# 15. certified enclosures of Hardy's Z
# --------------------------------------------------------------------------- #


def plot_certified_enclosures(t_min: float = 10.0, t_max: float = 40.0,
                              n_points: int = 260,
                              band_bits: Sequence[int] = (12, 16, 20),
                              width_bits: Sequence[int] = (8, 16, 32, 64, 128, 256),
                              width_t: Sequence[float] = (30.0, 100.0),
                              backend: str | None = None,
                              save_path: str | None = None, dpi: int = 160) -> Figure:
    """Rigorous enclosures of Z(t): the bands are theorems, and they shrink with precision.

    Ball arithmetic returns a pair lo ≤ hi with the *guarantee* lo ≤ Z(t) ≤ hi
    (:func:`zeta.rigor.enclose_Z`), so a band that misses zero is a **proof** of
    the sign of Z there, and a sign change between two proven signs is a proved
    zero of ζ on the critical line.

    Top: the band at each of ``band_bits`` working precisions, drawn around the
    curve.  The bands are nested — every enclosure contains the true value, so a
    higher-precision band lies inside a lower-precision one — and at these
    deliberately crude precisions the outermost is wide enough to *see*.  Where
    the coarse band straddles 0 the sign of Z is **not decided**; those samples
    are marked, and they occur only where the grid lands close enough to a zero
    that a band of that width cannot exclude 0.  Increasing the precision
    shrinks the band and decides them — except at a true zero, where no
    precision ever will, because Z genuinely has no sign there and 0 ("not
    decided") is the correct permanent answer.

    Bottom: the cost curve.  Width falls geometrically in the bit count — the
    dashed reference is a pure 2^{−bits} law — so proving the sign of Z where
    |Z| ~ 10^{−d} costs about 3.33·d bits on top of the evaluation itself.

    Honest scope (docs/08): a certificate over a finite interval is still a
    statement about a finite interval, and is not evidence for RH.
    """
    from zeta.rigor import BACKEND, enclose_Z

    t = np.linspace(float(t_min), float(t_max), int(n_points))
    bits = sorted(int(b) for b in band_bits)

    def _band(prec: int) -> tuple[np.ndarray, np.ndarray]:
        lo = np.empty(t.size)
        hi = np.empty(t.size)
        for i, tt in enumerate(t):
            try:
                a, b = enclose_Z(float(tt), prec, backend=backend)
                lo[i], hi[i] = float(a), float(b)
            except (ArithmeticError, ValueError):  # pragma: no cover - crude precision
                lo[i], hi[i] = -np.inf, np.inf
        return lo, hi

    bands = {b: _band(b) for b in bits}
    lo_ref, hi_ref = _band(128)
    z = 0.5 * (lo_ref + hi_ref)
    coarse_lo, coarse_hi = bands[bits[0]]
    undecided = (coarse_lo <= 0.0) & (coarse_hi >= 0.0)

    fig, (ax0, ax1) = _fig(nrows=2, figsize=(9.0, 6.6), height_ratios=(2.3, 1.3))
    ax0.axhline(0.0, color=_BASELINE, linewidth=0.9)
    ramp = (_BLUE_RAMP[1], _BLUE_RAMP[3], _BLUE_RAMP[5])
    for k, b in enumerate(bits):
        lo, hi = bands[b]
        ax0.fill_between(t, lo, hi, color=ramp[k % len(ramp)],
                         alpha=0.55 if k == 0 else 0.85, linewidth=0, zorder=2 + k,
                         label=f"enclosure at {b} bits  (median width "
                               f"{np.median(hi - lo):.1e})")
    ax0.plot(t, z, color=_INK, linewidth=1.1, zorder=6, label="Z(t) (128-bit enclosure)")
    if undecided.any():
        ax0.scatter(t[undecided], np.zeros(int(undecided.sum())), s=26, color=_RED,
                    zorder=7, marker="x",
                    label=f"sign NOT proven at {bits[0]} bits "
                          f"({int(undecided.sum())} of {t.size} samples)")
    _style(ax0, ylabel="Z(t)  (real by construction)",
           title="Every band is a theorem: lo ≤ Z(t) ≤ hi, guaranteed.  A band that misses 0 PROVES the\n"
                 "sign; the crosses mark the samples where the crudest band still straddles 0")
    ax0.set_xlim(t_min, t_max)
    span = float(np.nanmax(hi_ref) - np.nanmin(lo_ref))
    ax0.set_ylim(float(np.nanmin(lo_ref)) - 0.12 * span,
                 float(np.nanmax(hi_ref)) + 0.55 * span)
    _legend(ax0, loc="upper right", ncols=2)

    ref_t = float(list(width_t)[0])
    styles = ((_BLUE, "o", "-", 1.6), (_AQUA, "s", "--", 1.2))
    for j, tt in enumerate(width_t):
        widths = []
        for b in width_bits:
            try:
                a, c = enclose_Z(float(tt), int(b), backend=backend)
                widths.append(float(c - a))
            except (ArithmeticError, ValueError):  # pragma: no cover
                widths.append(np.nan)
        colour, marker, ls, lw = styles[j % len(styles)]
        ax1.plot(list(width_bits), widths, marker=marker, markersize=4.2, linewidth=lw,
                 linestyle=ls, color=colour,
                 label=f"width of the enclosure at t = {tt:g}")
        if j == 0:
            ref_t = float(tt)
    b0 = float(min(width_bits))
    w0 = None
    try:
        a, c = enclose_Z(ref_t, int(b0), backend=backend)
        w0 = float(c - a)
    except (ArithmeticError, ValueError):  # pragma: no cover
        w0 = 1.0
    grid = np.array(sorted(float(b) for b in width_bits))
    ax1.plot(grid, w0 * 2.0 ** (-(grid - b0)), color=_MUTED, linestyle="--",
             linewidth=1.2, label="pure 2^(−bits) reference")
    ax1.set_yscale("log")
    _style(ax1, xlabel="working precision (bits)", ylabel="enclosure width",
           title=f"The cost of rigour, measured (backend: {BACKEND if backend is None else backend})")
    _legend(ax1, loc="upper right")
    return _finish(fig, save_path, dpi)


# --------------------------------------------------------------------------- #
# 16. Li coefficients against the RH-predicted growth
# --------------------------------------------------------------------------- #


def plot_li_coefficients(n_max: int = 200, dps: int = 25,
                         save_path: str | None = None, dpi: int = 160) -> Figure:
    """Li's criterion in a picture: λ_n ≥ 0, and the growth RH predicts.

    **THEOREM** (Li 1997; Bombieri–Lagarias 1999): RH ⟺ λ_n ≥ 0 for every
    n ≥ 1, where λ_n = (1/(n−1)!)·dⁿ/dsⁿ[s^{n−1} log ξ(s)]|_{s=1}, computed here
    by :func:`zeta.li.li_positivity_scan` from a Cauchy pass around a circle
    (no zeros are used).

    Top: λ_n with the RH-predicted asymptotic (n/2)(log n − log 2π + γ − 1) + 1
    overlaid — the leading term is derived from the smooth zero density.
    Middle: the same for small n on a scale where the RH boundary λ = 0 is
    visible; λ₁ = 0.0231 is the closest any coefficient comes to it.
    Bottom: λ_n minus the asymptotic.  The residual does **not** settle to a
    constant — its envelope grows, which is what an O(√n log n) oscillation (the
    resonance of the individual zeros) looks like.  The measured envelope is
    printed in the panel rather than asserted.

    Honest scope (docs/08): every λ_n here is positive, and that is *not*
    evidence for RH — the criterion quantifies over all n, and by Littlewood's
    theorem no finite range can settle it.  A single negative λ_n would refute
    RH outright.
    """
    from zeta.li import li_positivity_scan

    rows = li_positivity_scan(int(n_max), dps=int(dps))
    n = np.array([r["n"] for r in rows], dtype=float)
    lam = np.array([float(r["lambda_n"]) for r in rows])
    asym = np.array([r["asymptotic"] for r in rows])
    resid = lam - asym
    n_small = min(20, int(n_max))
    cut = min(50, int(n_max))
    env_small = float(np.max(np.abs(resid[n <= cut])))
    env_all = float(np.max(np.abs(resid)))

    fig, (ax0, ax1, ax2) = _fig(nrows=3, figsize=(8.4, 8.2),
                                height_ratios=(2.1, 1.3, 1.3))
    ax0.plot(n, asym, color=_ORANGE, linewidth=2.0, zorder=3,
             label="RH prediction  (n/2)(log n − log 2π + γ − 1) + 1")
    ax0.plot(n, lam, color=_BLUE, linewidth=1.3, zorder=4, label="λ_n (Cauchy route, no zeros used)")
    ax0.axhline(0.0, color=_MUTED, linewidth=1.1, linestyle="--",
                label="λ = 0 — the RH boundary")
    _style(ax0, ylabel="λ_n",
           title="Li's criterion: RH ⟺ λ_n ≥ 0 for every n.  The computed λ_n track the growth RH\n"
                 "predicts — and every one of them is positive")
    _legend(ax0, loc="upper left")

    mask = n <= n_small
    ax1.axhline(0.0, color=_MUTED, linewidth=1.2, linestyle="--")
    ax1.plot(n[mask], lam[mask], color=_BLUE, linewidth=1.2, zorder=4)
    ax1.scatter(n[mask], lam[mask], s=26, color=_BLUE, zorder=5, label="λ_n")
    ax1.annotate(f"λ₁ = {lam[0]:.6f} — the closest\napproach to the boundary",
                 xy=(float(n[0]), float(lam[0])), xytext=(0.10, 0.62),
                 textcoords="axes fraction", color=_SECONDARY, fontsize=8.5,
                 arrowprops=dict(arrowstyle="->", color=_SECONDARY, lw=0.9))
    _style(ax1, ylabel="λ_n  (small n)",
           title=f"Zoom on n ≤ {n_small}: the margin above λ = 0 that RH is about")
    _legend(ax1, loc="upper left")

    ax2.axhline(0.0, color=_MUTED, linewidth=1.2, linestyle="--")
    ax2.plot(n, resid, color=_AQUA, linewidth=1.1, zorder=4,
             label="λ_n − asymptotic")
    ax2.annotate(f"envelope: ±{env_small:.2f} for n ≤ {cut}, ±{env_all:.2f} by "
                 f"n = {int(n_max)}\n"
                 "— growing, i.e. an oscillation, not a constant offset",
                 xy=(0.03, 0.08), xycoords="axes fraction", color=_SECONDARY, fontsize=8.5)
    _style(ax2, xlabel="n", ylabel="residual",
           title="The residual oscillates (the individual zeros resonating), so the +1 constant\n"
                 "in the asymptotic is not separable from it at these n")
    _legend(ax2, loc="upper left")
    return _finish(fig, save_path, dpi)


# --------------------------------------------------------------------------- #
# 17. Jensen polynomial roots: hyperbolicity, visible
# --------------------------------------------------------------------------- #


def plot_jensen_roots(d_values: Sequence[int] = (2, 3, 4, 6, 8, 10, 12),
                      n: int = 1, n_compare: int = 12, dps: int = 30,
                      save_path: str | None = None, dpi: int = 160) -> Figure:
    """The roots of the Jensen polynomials J^{d,n} — all real, all on the line.

    With 8·ξ(½+z) = Σ γ(n) z^{2n}/n! and J^{d,n}(X) = Σ_j C(d,j) γ(n+j) Xʲ,
    **Pólya's criterion** says RH ⟺ every J^{d,n} is *hyperbolic* (all roots
    real).  Top panel: one row per degree d, each dot a root of J^{d,n} in the
    normalised variable (:func:`zeta.li.jensen_polynomial` with
    ``normalise=True``, an X ↦ sX rescaling that leaves hyperbolicity
    untouched).  Every root sits on the real line and they are well separated —
    that separation is what "comfortably hyperbolic" looks like.  All roots are
    negative, as they must be: w = z² sends a zero ½ ± iγ of ξ to w = −γ², and
    γ(n) > 0 for every n forces it by Descartes' rule.

    Bottom: how far from real, quantified.  The largest |Im root| relative to
    the largest |root| is plotted against d, together with the tolerance
    10^{−dps/2} that the root-finder verdict uses.  At the defaults the measured
    values land between about 10^{−110} and 10^{−250}, i.e. a hundred orders of
    magnitude or more below that tolerance, so the verdict is nowhere near a
    close call — and it is confirmed independently by an exact Sturm-sequence
    count in ℚ[X] (``method="both"`` in :func:`zeta.li.is_hyperbolic`).  The
    worst value actually plotted is quoted in the panel title.

    Honest scope (docs/08): one non-hyperbolic J^{d,n} would refute RH; a table
    of hyperbolic ones is "no violation found", never support.
    """
    from zeta.li import is_hyperbolic, jensen_polynomial, xi_taylor_coefficients

    ds = [int(d) for d in d_values]
    d_max = max(ds)
    gammas = xi_taylor_coefficients(max(int(n), int(n_compare)) + d_max + 1, dps=int(dps))

    def _info(d: int, shift: int) -> dict:
        coeffs = jensen_polynomial(d, shift, dps=int(dps), gammas=gammas, normalise=True)
        return is_hyperbolic(coeffs, dps=int(dps), method="both")

    infos = {d: _info(d, int(n)) for d in ds}

    fig, (ax0, ax1) = _fig(nrows=2, figsize=(8.6, 6.6), height_ratios=(2.2, 1.3))
    ax0.axvline(0.0, color=_BASELINE, linewidth=1.0)
    for k, d in enumerate(ds):
        roots = np.array([float(r.real) if hasattr(r, "real") else float(r)
                          for r in infos[d]["roots"]])
        colour = _BLUE_RAMP[min(k, len(_BLUE_RAMP) - 1)]
        ax0.plot(roots, np.full(roots.size, float(d)), color=colour, linewidth=0.8,
                 alpha=0.5, zorder=2)
        ax0.scatter(roots, np.full(roots.size, float(d)), s=32, color=_BLUE,
                    edgecolor="white", linewidth=0.6, zorder=4)
    ax0.set_yticks(ds)
    all_real = all(inf["hyperbolic"] for inf in infos.values())
    exact_ok = all(inf["n_real_exact"] == inf["degree"] for inf in infos.values())
    ax0.annotate(f"every root real: {all_real}   (exact Sturm count = degree: {exact_ok})\n"
                 f"smallest relative root gap here: "
                 f"{min(inf['min_gap'] for inf in infos.values() if inf['degree'] > 1):.4f}",
                 xy=(0.03, 0.06), xycoords="axes fraction", color=_SECONDARY, fontsize=8.5)
    _style(ax0, xlabel=f"root of J^(d,{int(n)}) in the normalised variable",
           ylabel="degree d",
           title="Hyperbolicity, visible: every root of every Jensen polynomial lies on the real\n"
                 "line (and to the left of 0, since w = z² sends a zero ½ ± iγ of ξ to w = −γ²)")

    tol = 10.0 ** (-int(dps) / 2.0)
    floor = 1e-320
    plotted: list[float] = []
    for shift, colour, marker in ((int(n), _BLUE, "o"), (int(n_compare), _AQUA, "s")):
        vals = []
        for d in ds:
            inf = infos[d] if shift == int(n) else _info(d, shift)
            vals.append(max(float(inf["max_rel_imag"]), floor))
        plotted.extend(vals)
        ax1.plot(ds, vals, color=colour, linewidth=1.4, marker=marker, markersize=4.5,
                 label=f"max |Im root| / max |root|,  n = {shift}")
    ax1.axhline(tol, color=_ORANGE, linewidth=1.6, linestyle="--",
                label=f"root-finder tolerance 10^(−dps/2) = {tol:.0e}")
    ax1.set_yscale("log")
    worst = max(plotted)
    ax1.set_ylim(min(plotted) * 1e-2, tol * 1e6)
    _style(ax1, xlabel="degree d", ylabel="relative |Im root|",
           title=f"…and not by a narrow margin: the largest relative |Im root| plotted is "
                 f"{worst:.0e},\nagainst a tolerance of {tol:.0e}")
    _legend(ax1, loc="upper right")
    return _finish(fig, save_path, dpi)


# --------------------------------------------------------------------------- #
# 18. the proven critical line: Frobenius eigenvalues on |alpha| = sqrt(p)
# --------------------------------------------------------------------------- #


def plot_finite_field_rh(primes: Sequence[int] = (13, 101, 503, 1009),
                         dps: int = 25, save_path: str | None = None,
                         dpi: int = 160) -> Figure:
    """RH where it is a THEOREM: Frobenius eigenvalues on the circle |α| = √p.

    For E : y² = x³ + ax + b over F_p the zeta numerator is 1 − a_p T + p T² =
    (1 − αT)(1 − ᾱT) with α + ᾱ = a_p and αᾱ = p, so RH for E is |α| = √p,
    equivalently the Hasse bound |a_p| ≤ 2√p.  Every point plotted is an
    eigenvalue of Frobenius for some curve mod p — one per *distinct* trace,
    taken over **all** p² − p nonsingular curves via
    :func:`zeta.finitefield.traces_mod_p` — and every one lands on its circle.

    Left: the α-plane, with the circle |α| = √p drawn for each p.  Right: the
    same eigenvalues in s-coordinates.  Substituting T = p^{−s} sends a
    numerator root T₀ = 1/α to s = log(α)/log(p), so
    Re(s) = log|α|/log p = log √p / log p = **exactly ½**.  The √ in the
    point-count bound *is* the ½ in Re(s) = ½.  The strip edges Re s = 0, 1 are
    drawn for scale: the points do not merely cluster near the middle line,
    they are on it, by a theorem (Hasse 1934, Weil 1948, Deligne 1974).

    Note the vertical extent on the right: Im(s) = ±arg(α)/log p is defined only
    modulo 2π/log p, because p^{−s} is periodic.  These zeros live on a
    *circle*, not a line — precisely the structure Spec Z is missing (docs/11).

    Nothing here is evidence for RH over the integers: Z ⊗_Z Z = Z, so there is
    no surface E × E on which to run Weil's positivity argument.
    """
    from mpmath import mp

    from zeta.finitefield import traces_mod_p

    ps = [int(p) for p in primes]
    colours = (_BLUE, _ORANGE, _AQUA, "#7b5ea7", _RED)

    fig, axes = plt.subplots(1, 2, figsize=(11.0, 5.4), constrained_layout=True)
    fig.set_facecolor(_SURFACE)
    for ax in axes:
        ax.set_facecolor(_SURFACE)
    ax0, ax1 = axes

    worst_re = 0.0
    n_points = 0
    for k, p in enumerate(ps):
        traces = np.unique(np.asarray(traces_mod_p(p)))
        colour = colours[k % len(colours)]
        with mp.workdps(int(dps) + 10):
            alphas = [mp.mpc(mp.mpf(int(a)) / 2,
                             mp.sqrt(mp.mpf(4 * p - int(a) * int(a))) / 2)
                      for a in traces]
            logp = mp.log(p)
            re_s = [float(mp.re(mp.log(z) / logp)) for z in alphas]
            im_s = [float(mp.im(mp.log(z) / logp)) for z in alphas]
            worst_re = max(worst_re, max(abs(r - 0.5) for r in re_s))
        xs = np.array([float(mp.re(z)) for z in alphas])
        ys = np.array([float(mp.im(z)) for z in alphas])
        n_points += 2 * xs.size

        phi = np.linspace(0.0, 2.0 * np.pi, 400)
        r = math.sqrt(p)
        ax0.plot(r * np.cos(phi), r * np.sin(phi), color=colour, linewidth=1.1,
                 alpha=0.55, zorder=2)
        ax0.scatter(np.concatenate([xs, xs]), np.concatenate([ys, -ys]), s=16,
                    color=colour, zorder=4)
        ax0.text(0.0, r * 1.015, f"p = {p},  √p = {r:.3f}", ha="center", va="bottom",
                 color=colour, fontsize=8.0, zorder=6,
                 bbox=dict(facecolor=_SURFACE, edgecolor="none", alpha=0.85, pad=1.0))
        ax1.scatter(re_s + re_s, im_s + [-v for v in im_s], s=16, color=colour,
                    zorder=4,
                    label=f"p = {p}: {2 * xs.size} eigenvalues, |α| = √p = {r:.3f}")

    lim = 1.14 * math.sqrt(max(ps))
    ax0.set_xlim(-lim, lim)
    ax0.set_ylim(-lim, lim)
    ax0.set_aspect("equal")
    _style(ax0, xlabel="Re α", ylabel="Im α",
           title="The α-plane: αᾱ = p exactly, so every\neigenvalue is on the circle |α| = √p")

    ax1.axvline(0.0, color=_MUTED, linewidth=1.0, linestyle="--")
    ax1.axvline(1.0, color=_MUTED, linewidth=1.0, linestyle="--")
    ax1.axvline(0.5, color=_INK, linewidth=1.4, zorder=3)
    ax1.set_xlim(-0.08, 1.08)
    measured = (f"below the last digit\nreturned at dps = {int(dps)}"
                if worst_re == 0.0 else f"{worst_re:.1e}\nat dps = {int(dps)}")
    ax1.annotate("Re(s) = ½ — not approximately,\n"
                 f"exactly: max |Re s − ½| is\n{measured}",
                 xy=(0.5, 0.0), xytext=(0.55, 0.05), textcoords="axes fraction",
                 color=_SECONDARY, fontsize=8.5)
    _style(ax1, xlabel="Re s   (strip edges 0 and 1 dashed)", ylabel="Im s = ±arg(α)/log p",
           title="s-coordinates (T = p^−s): the proven critical\nline, with all "
                 f"{n_points} eigenvalues on it")
    _legend(ax1, loc="upper left")
    return _finish(fig, save_path, dpi)


# --------------------------------------------------------------------------- #
# 19. vertical Sato-Tate: the semicircle in the proven universe
# --------------------------------------------------------------------------- #


def plot_sato_tate(p_values: Sequence[int] = (503, 4001), n_bins: int = 20,
                   save_path: str | None = None, dpi: int = 160) -> Figure:
    """a_p/(2√p) over ALL curves mod p, against the semicircle (2/π)√(1−x²).

    This is the "GUE statistics" of the universe where RH is proved.  Every
    normalised trace lies in [−1, 1] — that containment *is* RH for the curve —
    and as p → ∞ the empirical distribution over all p² − p nonsingular curves
    converges to the semicircle.  **THEOREM** (Birch 1968, via the
    Eichler–Selberg trace formula): this is *vertical* Sato–Tate, fixed p and
    all curves, not the horizontal conjecture (one curve, varying p) that needed
    Taylor et al. 2008–11.  Data from
    :func:`zeta.finitefield.sato_tate_histogram` (cached under ``data/``).

    Convergence is slow and, in the sup norm at fixed bin count, not even
    monotone in p — with the traces confined to the ~4√p integers of the Hasse
    interval, each bin holds only ~0.1·2√p lattice points and the lattice lands
    differently for every p.  The measured sup deviations are printed in the
    legend rather than smoothed over.  The *moments* converge far faster, and
    the second one is exact: Σ a_p² = (p−1)²(p+1) for every prime.
    """
    from zeta.finitefield import sato_tate_histogram

    ps = sorted(int(p) for p in p_values)
    fig, (ax,) = _fig(figsize=(8.4, 5.0))
    grid = np.linspace(-1.0, 1.0, 500)
    ax.plot(grid, (2.0 / math.pi) * np.sqrt(np.maximum(0.0, 1.0 - grid ** 2)),
            color=_ORANGE, linewidth=2.2, zorder=6,
            label="semicircle (2/π)√(1 − x²) — the p → ∞ law")

    last = None
    peak = 0.0
    for k, p in enumerate(ps):
        h = sato_tate_histogram(p, n_bins=int(n_bins))
        last = h
        mids = np.asarray(h["bin_midpoints"])
        dens = np.asarray(h["density"])
        peak = max(peak, float(dens.max()))
        width = float(mids[1] - mids[0]) if mids.size > 1 else 2.0 / int(n_bins)
        label = (f"p = {p}: all {h['n_curves']:,} curves  "
                 f"(sup dev {h['sup_deviation']:.4f})")
        if k == len(ps) - 1:
            ax.bar(mids, dens, width=width * 0.92, color=_BLUE_RAMP[1], zorder=2,
                   label=label)
        else:
            ax.step(mids, dens, where="mid", color=_BLUE, linewidth=1.3, zorder=4,
                    label=label)

    ax.axvline(-1.0, color=_MUTED, linewidth=1.1, linestyle="--")
    ax.axvline(1.0, color=_MUTED, linewidth=1.1, linestyle="--",
               label="|a_p| = 2√p — the Hasse bound.  Nothing is ever outside it")
    if last is not None:
        ax.annotate(f"⟨x²⟩ = {last['moments'][0]:.7f} vs the limit 0.25;\n"
                    f"Σa_p² = (p−1)²(p+1) exactly: "
                    f"{last['second_moment_exact'] == last['second_moment_closed_form']}\n"
                    f"Hasse violations: {last['hasse_violations']}",
                    xy=(0.015, 0.66), xycoords="axes fraction",
                    color=_SECONDARY, fontsize=8.5)
    _style(ax, xlabel="normalised trace  a_p / (2√p)",
           ylabel="probability density",
           title="Vertical Sato–Tate: the traces of Frobenius over every curve mod p fill the\n"
                 "semicircle — and never leave [−1, 1], because there RH is a theorem")
    ax.set_xlim(-1.15, 1.15)
    ax.set_ylim(0.0, peak * 1.45 if peak > 0 else 1.0)
    _legend(ax, loc="upper right")
    return _finish(fig, save_path, dpi)


# --------------------------------------------------------------------------- #
# 20. the Mertens random walk
# --------------------------------------------------------------------------- #


def plot_mertens(limit: int = 10 ** 6, x_min: int = 100, n_points: int = 4000,
                 save_path: str | None = None, dpi: int = 160) -> Figure:
    """M(x)/√x — the random walk that made a false conjecture look true.

    M(x) = Σ_{n≤x} μ(n).  **THEOREM**: RH ⟺ M(x) = O(x^{½+ε}) for every ε > 0.
    **THEOREM** (Odlyzko–te Riele 1985): the *strong* Mertens conjecture
    |M(x)| < √x is **FALSE** — limsup M(x)/√x > 1.06 and liminf < −1.009 — and
    the disproof is non-constructive: no counterexample is known and the bounds
    on the first one are astronomical.

    Top: the walk M(x) itself, μ(n) summed by :func:`zeta.criteria.mertens_array`.
    Bottom: M(x)/√x on a logarithmic x-axis with the ±1 lines the conjecture
    claimed could never be crossed.  Over every x reachable by a sieve the ratio
    stays far inside them — which is exactly the picture that convinced people
    for a century, and is therefore the standing demonstration that this kind of
    plot is not evidence.  Nothing here says anything about RH (docs/08).

    The ratio panel starts at ``x_min`` (default 100) because the first few x
    are degenerate rather than informative: M(1) = 1 puts the ratio at exactly 1
    and M(5) = −2 at −2/√5 = −0.894, neither of which says anything about the
    growth of M.  The extremes quoted are those of the plotted range.
    """
    from zeta.criteria import mertens_array

    limit = int(limit)
    x_min = max(1, int(x_min))
    M = mertens_array(limit)
    idx = np.unique(np.geomspace(x_min, limit, int(n_points)).astype(np.int64))
    x = idx.astype(np.float64)
    m = M[idx].astype(np.float64)
    ratio = m / np.sqrt(x)
    dense = np.arange(1, limit + 1)
    stride = max(1, dense.size // int(n_points))
    xd = dense[::stride]
    md = M[1:][::stride]

    span = np.arange(x_min, limit + 1, dtype=np.float64)
    ratio_all = M[x_min:limit + 1] / np.sqrt(span)
    hi = int(np.argmax(ratio_all)) + x_min
    lo = int(np.argmin(ratio_all)) + x_min

    fig, (ax0, ax1) = _fig(nrows=2, figsize=(8.8, 6.4), height_ratios=(1.4, 1.6))
    ax0.axhline(0.0, color=_BASELINE, linewidth=0.9)
    ax0.plot(xd, md, color=_INK, linewidth=0.8,
             label=f"M(x) = Σ_{{n≤x}} μ(n),  M({limit:g}) = {int(M[limit])}")
    _style(ax0, ylabel="M(x)",
           title="The Möbius random walk M(x), and the ratio the Mertens conjecture bounded")
    _legend(ax0, loc="upper left")

    ax1.axhline(0.0, color=_BASELINE, linewidth=0.9)
    for sign in (1.0, -1.0):
        ax1.axhline(sign, color=_MUTED, linewidth=1.3, linestyle="--",
                    label=("|M(x)| = √x — the strong Mertens conjecture, DISPROVED "
                           "(Odlyzko–te Riele 1985)" if sign > 0 else None))
    ax1.plot(x, ratio, color=_BLUE, linewidth=0.9, label="M(x)/√x")
    ax1.scatter([hi, lo], [ratio_all[hi - x_min], ratio_all[lo - x_min]], s=34,
                facecolor="white", edgecolor=_RED, linewidth=1.3, zorder=6,
                label=f"extremes for x ≥ {x_min:,}: {ratio_all[lo - x_min]:+.4f} at "
                      f"x = {lo:,}, {ratio_all[hi - x_min]:+.4f} at x = {hi:,}")
    ax1.set_xscale("log")
    ax1.set_ylim(-1.85, 1.80)
    ax1.annotate("the limsup exceeds 1.06 and the liminf is below −1.009 — somewhere.\n"
                 "No x that any sieve can reach shows it: this plot is the reason the\n"
                 "conjecture was believed, not a reason to believe anything.",
                 xy=(0.03, 0.03), xycoords="axes fraction", color=_SECONDARY, fontsize=8.5)
    _style(ax1, xlabel=f"x  (log scale, from {x_min:,})", ylabel="M(x)/√x",
           title="RH ⟺ M(x) = O(x^{½+ε}) [THEOREM].  |M(x)| < √x [FALSE] — and no "
                 "counterexample is known")
    _legend(ax1, loc="upper right")
    return _finish(fig, save_path, dpi)

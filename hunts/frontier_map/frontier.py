"""The frontier map: unconditional critical-line proportions vs bandwidth.

Context. The August 2026 paper "More than two thirds of the zeros of the
Riemann zeta function lie on the critical line" makes Montgomery's
pair-correlation argument unconditional by restricting Weil's Hermitian form
to a finite Gabor family at bandwidth lambda <= 1. For a window v >= 0 on
[-1/2, 1/2] the scale-free functional (paper eq. 7.3, generalised to any
admissible form factor F exactly as in hunts/wide_search/xiprime.py) is

    1/c_lambda(v) = [ int v^2 + lambda iint F(lambda(s-s')) v v ]
                    / ( lambda (int v)^2 ),

and the proportions of simple-on-line and distinct zeros it delivers are
H = 2 - 1/c and Hd = (1 + H)/2. The method has exactly one dial, lambda,
capped at 1 by the Rudnick-Sarnak / Montgomery support restriction
(paper Prop. 5.6 and section 7.5(a)); its section 7.5(a) also notes the
certificate is empty for lambda <= 1/2.

This module computes the whole landscape H(lambda) for the two kernels the
machinery accepts unconditionally — Montgomery's F (zeta) and
Farmer-Gonek-Lee's F_1 (xi') — and assembles it, together with the ceilings
and prior-art bars that box the method in, into one machine-readable map and
one figure. The optimiser is `hunts/wide_search/xiprime.optimise`, reused
rather than forked; its zeta control reproduces the paper's Theorem D to 10
digits (wide_search/RESULTS-xiprime.md).

The independent cross-check. For zeta the paper solves the variational
problem in closed form (eq. 7.4):

    c*_lambda = sqrt(2) tan(theta) / (1 + theta tan(theta)),
    theta = lambda / sqrt(2),

so the numeric curve can be compared against an analytic one at every
lambda, not only at the lambda = 1 endpoint. The closed form was not used
anywhere in the optimiser's construction.

Run from the repo root:

    .venv/bin/python hunts/frontier_map/frontier.py            # print the map
    .venv/bin/python hunts/frontier_map/frontier.py --json     # + frontier_map.json
    .venv/bin/python hunts/frontier_map/frontier.py --figure   # + figures/frontier_map.png
"""

from __future__ import annotations

import json
import math
import sys
from pathlib import Path
from typing import Any

_HERE = Path(__file__).resolve().parent
_REPO_ROOT = _HERE.parents[1]
_WIDE_SEARCH = _REPO_ROOT / "hunts" / "wide_search"
for p in (str(_WIDE_SEARCH), str(_REPO_ROOT)):
    if p not in sys.path:
        sys.path.insert(0, p)

from xiprime import optimise  # noqa: E402  (hunts/wide_search/xiprime.py)


# --------------------------------------------------------------------------
# the closed form (paper eq. 7.4) — the independent route for the zeta curve
# --------------------------------------------------------------------------


def zeta_H_closed(lam: float) -> float:
    """H(lambda) for zeta from the paper's closed-form optimum, eq. (7.4).

    c*_lambda = sqrt(2) tan(theta) / (1 + theta tan(theta)), theta = lam/sqrt(2);
    at lam = 1 this is the Montgomery-Taylor constant, H = 0.6725007...
    """
    theta = lam / math.sqrt(2.0)
    t = math.tan(theta)
    c = math.sqrt(2.0) * t / (1.0 + theta * t)
    return 2.0 - 1.0 / c


# --------------------------------------------------------------------------
# the computed landscape
# --------------------------------------------------------------------------


def landscape(
    kernel: str,
    lams: list[float] | None = None,
    n_basis: int = 14,
    n_r: int = 320,
    n_s: int = 320,
) -> list[dict[str, float]]:
    """Optimal H and Hd at each bandwidth, by the wide_search optimiser."""
    if lams is None:
        lams = [round(0.05 * k, 2) for k in range(1, 21)]  # 0.05 .. 1.00
    rows = []
    for lam in lams:
        r = optimise(lam=lam, kernel=kernel, n_basis=n_basis, n_r=n_r, n_s=n_s)
        rows.append({"lambda": lam, "H": r["H"], "Hd": r["Hd"]})
    return rows


def onset(kernel: str, lo: float = 0.4, hi: float = 0.9, tol: float = 1e-10) -> float:
    """The bandwidth lambda_0 where the certificate first delivers H > 0.

    Bisection on the optimal H(lambda), which is monotone increasing in
    lambda (the pair term enters as lambda F(lambda .), and enlarging the
    band only enlarges the feasible family; monotonicity is also measured,
    not assumed — see probe.py).
    """

    def h(lam: float) -> float:
        return optimise(lam=lam, kernel=kernel)["H"]

    h_lo, h_hi = h(lo), h(hi)
    if not (h_lo < 0.0 < h_hi):
        raise ValueError(f"onset not bracketed on [{lo}, {hi}]: H = {h_lo}, {h_hi}")
    while hi - lo > tol:
        mid = 0.5 * (lo + hi)
        if h(mid) > 0.0:
            hi = mid
        else:
            lo = mid
    return 0.5 * (lo + hi)


# --------------------------------------------------------------------------
# the fixed points of the map: ceilings, bars, walls — data, with sources
# --------------------------------------------------------------------------

#: Every entry is (value, source, standing caveat or ""). "paper" is the
#: 10 Aug 2026 PDF; line numbers refer to the pdftotext -layout rendering
#: that hunts/wide_search/HANDOFF.md pins.
REFERENCE_BARS: dict[str, dict[str, Any]] = {
    "zeta": {
        "levinson_1974": {
            "value": 1.0 / 3.0,
            "kind": "prior art (Levinson's method)",
            "source": "Levinson 1974, via paper section 1.2",
            "caveat": "",
        },
        "conrey_1989": {
            "value": 0.4088,
            "kind": "prior art (Levinson's method)",
            "source": "Conrey 1989 'more than two fifths', via paper section 1.2",
            "caveat": "",
        },
        "przz_2020": {
            "value": 5.0 / 12.0,
            "kind": "prior art (Levinson's method); standing record 2020-2026",
            "source": "Pratt-Robles-Zaharescu-Zeindler 2020, via paper section 1.2",
            "caveat": "",
        },
        "paper_theorem_D": {
            "value": 0.6725007037,
            "kind": "attained by the mapped method at lambda = 1",
            "source": "paper Theorem D; reproduced to 10 digits by "
            "hunts/wide_search/xiprime.py",
            "caveat": "",
        },
        "bandwidth_one_ceiling": {
            "value": 0.68185,
            "kind": "ceiling for configuration-by-configuration certificates "
            "on bandwidth-one data",
            "source": "paper Remark 1.1; enclosure data recomputed in "
            "hunts/wide_search/pair_ceiling.py",
            "caveat": "the published N=256 law delivers the ceiling only for "
            "certificates with |r'(1)| + int|r''| <= 8.38043; the bare "
            "uniform sentence elides this (RESULTS-pair-ceiling.md)",
        },
        "montgomery_taylor_on_RH": {
            "value": 0.6725,
            "kind": "RH-conditional comparison",
            "source": "Montgomery-Taylor 1975, via paper section 1.2",
            "caveat": "conditional on RH; same constant, which is the point",
        },
        "cgdl_2020_on_RH": {
            "value": 0.6792,
            "kind": "RH-conditional comparison (SDP majorants, F outside [-1,1])",
            "source": "Chirre-Goncalves-de Laat 2020, via paper section 1.2",
            "caveat": "conditional; operates outside the bandwidth-one regime "
            "the ceiling is scoped to",
        },
    },
    "xiprime": {
        "paper_remark_7_3_flat": {
            "value": 0.85838,
            "kind": "attained by the mapped method (flat window)",
            "source": "paper Remark 7.3",
            "caveat": "",
        },
        "paper_remark_7_3_quartic": {
            "value": 0.86864,
            "kind": "attained by the mapped method (quartic window)",
            "source": "paper Remark 7.3",
            "caveat": "",
        },
        "sharp_constant_wide_search": {
            "value": 0.86864150052976706411,
            "kind": "attained: the solved variational optimum at lambda = 1",
            "source": "hunts/wide_search/RESULTS-xiprime.md",
            "caveat": "an optimisation of the paper's functional with "
            "Farmer-Gonek's form factor, not a new theorem",
        },
        "wu_2015_on_line": {
            "value": 0.86957,
            "kind": "prior-art bar (on the line, without simplicity)",
            "source": "Wu 2015 section 3, via paper Remark 7.3",
            "caveat": "counts zeros merely on the line; the mapped method's "
            "number carries simplicity, so the comparison is the paper's own",
        },
        "conrey_1989_xiprime": {
            "value": 0.79874,
            "kind": "prior-art bar (simple and on the line)",
            "source": "paper Remark 7.3, attributed there to Conrey 1989",
            "caveat": "wide_search could not locate this figure in Conrey 1989, "
            "whose stated results concern zeta; carried as the paper's "
            "attribution, not this tree's (RESULTS-xiprime.md)",
        },
        "fgl_2014_on_RH": {
            "value": 0.8584,
            "kind": "RH-conditional comparison",
            "source": "Farmer-Gonek-Lee 2014 Cor. 1.3, via paper Remark 7.3",
            "caveat": "conditional on RH",
        },
        "cgdl_2020_xiprime_on_RH": {
            "value": 0.8825,
            "kind": "RH-conditional comparison",
            "source": "Chirre-Goncalves-de Laat 2020 Cor. 7, via paper Remark 7.3",
            "caveat": "conditional on RH",
        },
    },
}

#: paper Remark 1.1: bandwidths the same route would need for higher
#: proportions — the structural wall, verbatim from the source.
STRUCTURAL_WALL = [
    {"target": 0.70, "required_bandwidth": 1.04},
    {"target": 0.80, "required_bandwidth": 1.26},
    {"target": 0.90, "required_bandwidth": 1.70},
]

#: The lanes that are open or blocked, with the coordinates measured here
#: or in wide_search. Kept as data so RESULTS and the JSON cannot drift.
OPEN_LANES = [
    {
        "name": "zeta: attained-to-ceiling interval",
        "interval": [0.6725007037, 0.68185],
        "status": "open",
        "note": "the scalar-moment joint-window LP collapses to the left "
        "endpoint (RESULTS-pair-ceiling.md); what remains is the full-data "
        "LP over marked periodic configurations",
    },
    {
        "name": "xiprime: shortfall to Wu's on-line bar",
        "interval": [0.86864150052976706411, 0.86957],
        "status": "closed negatively at lambda = 1",
        "note": "no admissible window reaches Wu; short by 9.285e-4 "
        "(RESULTS-xiprime.md). The method's number carries simplicity, "
        "which Wu's does not.",
    },
    {
        "name": "xi^(kappa), kappa >= 2",
        "interval": None,
        "status": "blocked",
        "note": "Bian 2008 has no closed form for F_kappa and no tail bound; "
        "the 11-term truncations fail at the lambda = 1 optimum "
        "(RESULTS-higher-derivatives.md)",
    },
    {
        "name": "lambda > 1",
        "interval": None,
        "status": "walled",
        "note": "needs pair-correlation input beyond the Rudnick-Sarnak / "
        "Montgomery range (Hardy-Littlewood-strength prime pairs); "
        "paper Remark 1.1 and section 7.5(a)",
    },
]


# --------------------------------------------------------------------------
# assembly
# --------------------------------------------------------------------------


def build_map(
    lams: list[float] | None = None,
    with_onsets: bool = True,
) -> dict[str, Any]:
    """Compute the landscape for both kernels and assemble the full map."""
    zeta_rows = landscape("zeta", lams)
    xi_rows = landscape("xiprime", lams)
    closed = [
        {"lambda": r["lambda"], "H": zeta_H_closed(r["lambda"])} for r in zeta_rows
    ]
    cross = max(
        abs(a["H"] - b["H"]) for a, b in zip(zeta_rows, closed)
    )
    out: dict[str, Any] = {
        "landscape": {"zeta": zeta_rows, "xiprime": xi_rows},
        "zeta_closed_form": closed,
        "closed_form_max_deviation": cross,
        "reference_bars": REFERENCE_BARS,
        "structural_wall": STRUCTURAL_WALL,
        "open_lanes": OPEN_LANES,
    }
    if with_onsets:
        out["onset"] = {
            "zeta": onset("zeta"),
            "xiprime": onset("xiprime"),
        }
    return out


def render_figure(m: dict[str, Any], path: Path) -> None:
    """The map as one picture: two curves, the bars, the ceiling, the wall."""
    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    fig, ax = plt.subplots(figsize=(9.0, 6.0))

    zl = [r["lambda"] for r in m["landscape"]["zeta"]]
    zH = [r["H"] for r in m["landscape"]["zeta"]]
    xl = [r["lambda"] for r in m["landscape"]["xiprime"]]
    xH = [r["H"] for r in m["landscape"]["xiprime"]]
    cf = [r["H"] for r in m["zeta_closed_form"]]

    ax.plot(zl, zH, "-", color="#1f5fa8", lw=2.0, label=r"$\zeta$: optimal $H(\lambda)$ (numeric)")
    ax.plot(zl, cf, "--", color="#7fb2e5", lw=1.2, label=r"$\zeta$: closed form, paper eq. (7.4)")
    ax.plot(xl, xH, "-", color="#b0413e", lw=2.0, label=r"$\xi'$: optimal $H(\lambda)$ (numeric)")

    bars = m["reference_bars"]
    ax.axhline(bars["zeta"]["przz_2020"]["value"], color="#666666", lw=0.9, ls=":")
    ax.axhline(bars["zeta"]["bandwidth_one_ceiling"]["value"], color="#1f5fa8", lw=0.9, ls="-.")
    ax.axhline(bars["xiprime"]["wu_2015_on_line"]["value"], color="#b0413e", lw=0.9, ls="-.")
    ax.text(0.03, 5.0 / 12.0 + 0.006, "PRZZ 2020 record 5/12 (Levinson line)", fontsize=8, color="#555555")
    ax.text(0.03, 0.68185 + 0.006, "bandwidth-one ceiling 0.68185 (Remark 1.1)", fontsize=8, color="#1f5fa8")
    ax.text(0.03, 0.86957 + 0.006, "Wu 2015 on-line bar 0.86957", fontsize=8, color="#b0413e")

    if "onset" in m:
        offsets = {"zeta": (10, -12), "xiprime": (-78, -26)}
        for k, col in (("zeta", "#1f5fa8"), ("xiprime", "#b0413e")):
            lam0 = m["onset"][k]
            ax.plot([lam0], [0.0], "o", ms=5, color=col)
            ax.annotate(
                rf"$\lambda_0 = {lam0:.4f}$",
                (lam0, 0.0),
                textcoords="offset points",
                xytext=offsets[k],
                fontsize=8,
                color=col,
            )

    ax.plot([1.0], [zH[-1]], "s", color="#1f5fa8", ms=6)
    ax.annotate("0.6725007", (1.0, zH[-1]), textcoords="offset points", xytext=(-62, 4), fontsize=8, color="#1f5fa8")
    ax.plot([1.0], [xH[-1]], "s", color="#b0413e", ms=6)
    ax.annotate("0.8686415", (1.0, xH[-1]), textcoords="offset points", xytext=(-62, 4), fontsize=8, color="#b0413e")

    ax.axvspan(1.0, 1.75, color="#f2e8e8", zorder=0)
    for w in m["structural_wall"]:
        ax.plot([w["required_bandwidth"]], [w["target"]], "x", color="#8a5a5a", ms=7)
        ax.annotate(
            f"{w['target']:.2f} needs $\\lambda\\approx{w['required_bandwidth']}$",
            (w["required_bandwidth"], w["target"]),
            textcoords="offset points",
            xytext=(5, -3),
            fontsize=8,
            color="#8a5a5a",
        )
    ax.text(
        1.37, 0.08,
        "beyond known pair correlation\n(Hardy–Littlewood strength required)",
        fontsize=8, color="#8a5a5a", ha="center",
    )

    ax.axhline(0.0, color="black", lw=0.6)
    ax.axvline(1.0, color="#444444", lw=0.9)
    ax.set_xlim(0.0, 1.75)
    ax.set_ylim(-0.25, 1.0)
    ax.set_xlabel(r"bandwidth $\lambda$")
    ax.set_ylabel("proportion of zeros, simple and on the critical line")
    ax.set_title(
        "The frontier map: unconditional proportions from bandwidth-one pair correlation\n"
        "(curves computed here; bars and wall from the 10 Aug 2026 paper — a map of a method, "
        "not evidence about RH)",
        fontsize=10,
    )
    ax.legend(loc="lower right", fontsize=8)
    ax.grid(alpha=0.25)
    fig.tight_layout()
    fig.savefig(path, dpi=160)
    plt.close(fig)


def main(argv: list[str]) -> None:
    m = build_map()
    print(f"closed-form cross-check, max |numeric - eq.(7.4)| over the zeta curve: "
          f"{m['closed_form_max_deviation']:.3e}")
    print(f"onset lambda_0:  zeta {m['onset']['zeta']:.6f}   xiprime {m['onset']['xiprime']:.6f}")
    for kern in ("zeta", "xiprime"):
        last = m["landscape"][kern][-1]
        print(f"at the wall lambda=1, {kern}: H = {last['H']:.10f}, Hd = {last['Hd']:.10f}")
    for lane in m["open_lanes"]:
        iv = lane["interval"]
        span = f"[{iv[0]:.7f}, {iv[1]:.7f}]" if iv else "-"
        print(f"lane: {lane['name']:45s} {lane['status']:28s} {span}")
    if "--json" in argv:
        out = _HERE / "frontier_map.json"
        out.write_text(json.dumps(m, indent=2, default=float) + "\n", encoding="utf-8")
        print(f"wrote {out.relative_to(_REPO_ROOT)}")
    if "--figure" in argv:
        fig_path = _REPO_ROOT / "figures" / "frontier_map.png"
        render_figure(m, fig_path)
        print(f"wrote {fig_path.relative_to(_REPO_ROOT)}")


if __name__ == "__main__":
    main(sys.argv[1:])

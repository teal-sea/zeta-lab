"""Figures for the chroma/hue hunt. Reads the results_*.json the probes wrote.

Writes four PNGs into figures/:
  chroma_hue_wheels.png       the two injective wheels, and the four collapsed ones
  chroma_hue_consonance.png   exhaustive-search score distribution, fifths marked
  chroma_hue_perceptual.png   HSL hues in OKLab, and the spectral octave
  chroma_hue_spectrum.png     dissonance MDS spectrum by Fourier mode, three measures
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402
import numpy as np  # noqa: E402

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import colorspace as cs  # noqa: E402
import pc  # noqa: E402

FIG = HERE.parents[1] / "figures"
NAMES = ["C", "C#", "D", "D#", "E", "F", "F#", "G", "G#", "A", "A#", "B"]
N = 12


def hue_rgb(h_deg, L=0.7):
    c = cs.max_chroma_in_gamut(L, h_deg) * 0.95
    return np.clip(cs.oklab_to_srgb(cs.oklch_to_oklab(L, c, h_deg)), 0, 1)


def wheels():
    fig, axes = plt.subplots(2, 3, figsize=(10, 7), subplot_kw={"aspect": "equal"})
    for ax, k in zip(axes.flat, [1, 5, 2, 3, 4, 6]):
        ax.set_title(f"wheel k = {k}: x -> {k}x" + ("  (chromatic)" if k == 1 else "  (fifths)" if k == 5 else f"  ({N // np.gcd(k, N)} hues)"))
        for x in range(N):
            ang = 2 * np.pi * x / N
            h = (360.0 * k * x / N) % 360
            ax.add_patch(plt.Circle((np.cos(ang), np.sin(ang)), 0.16, color=hue_rgb(h)))
            ax.text(np.cos(ang) * 1.32, np.sin(ang) * 1.32, NAMES[x], ha="center", va="center", fontsize=9)
        ax.set_xlim(-1.5, 1.5)
        ax.set_ylim(-1.5, 1.5)
        ax.axis("off")
    fig.suptitle("Z_12 painted by its characters. Pitch classes sit in chromatic order; colour is hue 30k·x degrees (OKLCH, L = 0.7).")
    fig.tight_layout()
    fig.savefig(FIG / "chroma_hue_wheels.png", dpi=130)
    plt.close(fig)


def consonance():
    d = json.load(open(HERE / "results_consonance.json"))
    fig, axes = plt.subplots(1, 3, figsize=(12, 3.6))
    for ax, (name, r) in zip(axes, d["measures"].items()):
        h = r["exhaustive_hist_0.001"]
        xs = np.array([float(k) for k in h])
        ys = np.array([h[k] for k in h], dtype=float)
        ax.bar(xs, ys, width=0.004, color="0.6")
        ax.set_yscale("log")
        ax.axvline(r["fifths"], color="C3", label=f"fifths {r['fifths']:.3f} (argmax)")
        ax.axvline(r["chromatic"], color="C0", label=f"chromatic {r['chromatic']:.3f}")
        ax.set_title(f"{name}: all {d['evaluated']:,} canonical bijections")
        ax.set_xlabel("Spearman(hue distance, dissonance)")
        ax.legend(fontsize=8)
    fig.tight_layout()
    fig.savefig(FIG / "chroma_hue_consonance.png", dpi=130)
    plt.close(fig)


def perceptual():
    p = json.load(open(HERE / "results_perceptual.json"))
    s = json.load(open(HERE / "results_spectrum.json"))
    fig, axes = plt.subplots(1, 2, figsize=(11, 5))
    ax = axes[0]
    ax.set_aspect("equal")
    for rec in p["hsl_wheel"]["oklch"]:
        L, C, h = rec
        ax.plot([0, C * np.cos(np.radians(h))], [0, C * np.sin(np.radians(h))], color=hue_rgb(h), lw=3)
    for i, rec in enumerate(p["hsl_wheel"]["oklch"]):
        L, C, h = rec
        ax.text(1.15 * C * np.cos(np.radians(h)), 1.15 * C * np.sin(np.radians(h)), f"HSL {30 * i}°", fontsize=7, ha="center")
    ax.set_title("The 12 HSL hues in the OKLab chroma plane\n(equal 30° HSL steps land 6.5° to 61° apart)")
    ax.set_xlabel("a")
    ax.set_ylabel("b")
    ax = axes[1]
    pts = s["pitch_class_light"]
    nm = [r["nm"] for r in pts]
    hue = [r["oklch_hue"] for r in pts]
    ax.plot(range(len(pts)), hue, "k-", lw=1)
    for i, (l, h) in enumerate(zip(nm, hue)):
        ax.plot(i, h, "o", color=hue_rgb(h), ms=12)
        ax.annotate(f"{l:.0f} nm", (i, h), textcoords="offset points", xytext=(0, 9), ha="center", fontsize=7)
    ax.set_xlabel("equal-tempered semitone step of light frequency from 660 nm")
    ax.set_ylabel("OKLCH hue (degrees)")
    ax.set_title(f"Monochromatic light, 12-TET steps across {s['window_semitones']:.1f} semitones\n(hue span {s['hue_span_deg']:.0f}°, steps {min(s['hue_steps_deg_per_semitone']):.0f}° to {max(s['hue_steps_deg_per_semitone']):.0f}°)")
    fig.tight_layout()
    fig.savefig(FIG / "chroma_hue_perceptual.png", dpi=130)
    plt.close(fig)


def spectrum():
    fig, ax = plt.subplots(figsize=(7, 3.8))
    meas = pc.dissonance_measures(N)
    w = 0.25
    for i, (name, m) in enumerate(meas.items()):
        D = pc.circulant_from_ic(m)
        J = np.eye(N) - np.ones((N, N)) / N
        B = -0.5 * J @ (D**2) @ J
        lam = np.real(np.fft.fft(B[0]))[1:7]
        lam = lam / np.abs(lam).max()
        ax.bar(np.arange(1, 7) + (i - 1) * w, lam, width=w, label=name)
    ax.axhline(0, color="k", lw=0.5)
    ax.set_xlabel("Fourier mode k (the wheel x -> kx)")
    ax.set_ylabel("MDS eigenvalue (scaled to max |λ| = 1)")
    ax.set_title("Classical MDS of a transposition-invariant dissonance is diagonal in Fourier modes.\nMode 5 (fifths) wins; mode 1 (chromatic) is the anti-consonant direction.")
    ax.legend()
    fig.tight_layout()
    fig.savefig(FIG / "chroma_hue_spectrum.png", dpi=130)
    plt.close(fig)


if __name__ == "__main__":
    wheels()
    consonance()
    perceptual()
    spectrum()
    print("figures written to", FIG)

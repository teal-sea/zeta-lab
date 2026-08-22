"""The wave version: pitch classes as equal-tempered steps across the visible
octave of light, mapped to the hue of monochromatic light.

Visible light runs from about 400 THz (750 nm) to 790 THz (380 nm), a ratio of
1.97, so the visible band is one octave to within 2 percent. Newton used that
to cut the spectrum into seven colours matching the diatonic scale. This probe
takes the same idea literally: frequency f_k = 400 THz * 2^(k/12), k = 0..11,
and asks what hue geometry the eye assigns to those twelve lights.

CIE 1931 colour matching functions are approximated by the multi-lobe
Gaussian fit of Wyman, Sloan and Shirley (2013). The fit is checked against
three facts it was not tuned to here: the equal-energy white lands at
chromaticity (1/3, 1/3), the luminous efficiency peaks near 555 nm, and the
dominant wavelengths of the sRGB primaries come out near 611, 549 and 464 nm.
The hue angles below are good to a few degrees, which is all the argument uses.
Writes results_spectrum.json.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
import colorspace as cs  # noqa: E402

C_LIGHT = 299_792_458.0


def _g(lam, mu, s1, s2):
    s = np.where(lam < mu, s1, s2)
    return np.exp(-0.5 * ((lam - mu) / s) ** 2)


def cmf(lam):
    """(xbar, ybar, zbar) at wavelength(s) lam in nm, Wyman et al. 2013 fit."""
    lam = np.asarray(lam, dtype=float)
    x = 1.056 * _g(lam, 599.8, 37.9, 31.0) + 0.362 * _g(lam, 442.0, 16.0, 26.7) - 0.065 * _g(lam, 501.1, 20.4, 26.2)
    y = 0.821 * _g(lam, 568.8, 46.9, 40.5) + 0.286 * _g(lam, 530.9, 16.3, 31.1)
    z = 1.217 * _g(lam, 437.0, 11.8, 36.0) + 0.681 * _g(lam, 459.0, 26.0, 13.8)
    return np.stack([x, y, z], axis=-1)


def xy(XYZ):
    s = XYZ.sum(axis=-1, keepdims=True)
    return (XYZ / s)[..., :2]


def dominant_wavelength(XYZ_colour, white_xy, lams):
    """Wavelength where the ray white -> colour meets the spectral locus (2D)."""
    c = xy(np.asarray(XYZ_colour))
    d = c - white_xy
    d /= np.linalg.norm(d)
    locus = xy(cmf(lams))
    v = locus - white_xy
    vn = v / np.linalg.norm(v, axis=1, keepdims=True)
    return float(lams[int(np.argmax(vn @ d))])


def main():
    lams = np.arange(380.0, 780.0, 0.5)
    out = {}
    # checks on the fit
    ee = cmf(lams).sum(axis=0)
    out["check_equal_energy_xy"] = [round(float(v), 4) for v in xy(ee)]
    out["check_ybar_peak_nm"] = float(lams[int(np.argmax(cmf(lams)[:, 1]))])
    white = xy(cs.srgb_to_xyz([1.0, 1.0, 1.0]))
    out["check_dominant_wavelengths_sRGB"] = {
        k: dominant_wavelength(cs.srgb_to_xyz(v), white, lams)
        for k, v in {"R": [1, 0, 0], "G": [0, 1, 0], "B": [0, 0, 1]}.items()
    }
    # the visible octave, physically
    out["visible_octaves_380_750nm"] = round(float(np.log2(750 / 380)), 4)
    # the window where the fit is trustworthy and hue is monotone in wavelength
    lo_nm, hi_nm = 420.0, 660.0
    out["window_nm"] = [lo_nm, hi_nm]
    out["window_octaves"] = round(float(np.log2(hi_nm / lo_nm)), 4)
    out["window_semitones"] = round(float(12 * np.log2(hi_nm / lo_nm)), 2)

    def hue_of(nm):
        row = cmf(nm)
        return cs.oklab_to_oklch(cs.xyz_to_oklab(row / max(row[1], 1e-9) * 0.2))[2]

    f0 = C_LIGHT / (hi_nm * 1e-9)
    ks = np.arange(0, int(np.floor(out["window_semitones"])) + 1)
    freqs = f0 * 2 ** (ks / 12)
    lam_k = C_LIGHT / freqs * 1e9
    hues = [hue_of(l) for l in lam_k]
    steps = [((hues[i + 1] - hues[i] + 180) % 360) - 180 for i in range(len(hues) - 1)]
    out["pitch_class_light"] = [
        {"k": int(k), "THz": round(float(f) / 1e12, 1), "nm": round(float(l), 1), "oklch_hue": round(h, 1)}
        for k, f, l, h in zip(ks, freqs, lam_k, hues)
    ]
    out["hue_steps_deg_per_semitone"] = [round(s, 1) for s in steps]
    out["hue_span_deg"] = round(float(sum(steps)), 1)
    out["hue_step_max_over_min_abs"] = round(max(abs(s) for s in steps) / min(abs(s) for s in steps), 2)
    fine = [hue_of(l) for l in np.arange(lo_nm, hi_nm + 0.5, 1.0)]
    unwrapped = np.degrees(np.unwrap(np.radians(fine)))
    out["spectral_locus_oklch_hue_every_20nm"] = [round(h, 1) for h in fine[::20]]
    out["hue_vs_wavelength_sign_changes_in_window"] = int(np.sum(np.diff(np.sign(np.diff(unwrapped))) != 0))
    out["spectral_hue_range_deg"] = round(float(abs(unwrapped[-1] - unwrapped[0])), 1)
    out["non_spectral_purple_arc_deg"] = round(360.0 - out["spectral_hue_range_deg"], 1)
    Path(__file__).with_name("results_spectrum.json").write_text(json.dumps(out, indent=1))
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()

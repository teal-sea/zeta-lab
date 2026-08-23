"""Colour-space conversions for the chroma/hue hunt, hand-rolled so nothing here
depends on a package the venv does not carry.

Three spaces, one difference formula:

* sRGB (IEC 61966-2-1) <-> linear RGB <-> CIE XYZ (D65).
* CIELAB (CIE 1976) with the D65 white, and the CIEDE2000 difference formula
  (Sharma, Wu, Dalal 2005). `SHARMA_PAIRS` carries published test pairs so the
  formula is pinned, not remembered.
* OKLab / OKLCH (Ottosson 2020), the perceptual space whose hue angle the
  hunt treats as "perceptual hue".

HSL hue is the naive encoding the hunt compares against. Everything is numpy
float64; nothing here is precision-critical in the mpmath sense.
"""

from __future__ import annotations

import numpy as np

# --- sRGB <-> linear <-> XYZ (D65) -----------------------------------------

_M_RGB2XYZ = np.array(
    [
        [0.4124564, 0.3575761, 0.1804375],
        [0.2126729, 0.7151522, 0.0721750],
        [0.0193339, 0.1191920, 0.9503041],
    ]
)
_M_XYZ2RGB = np.linalg.inv(_M_RGB2XYZ)
WHITE_D65 = np.array([0.95047, 1.0, 1.08883])


def srgb_to_linear(c):
    c = np.asarray(c, dtype=float)
    return np.where(c <= 0.04045, c / 12.92, ((c + 0.055) / 1.055) ** 2.4)


def linear_to_srgb(c):
    c = np.asarray(c, dtype=float)
    return np.where(c <= 0.0031308, 12.92 * c, 1.055 * np.power(np.clip(c, 0, None), 1 / 2.4) - 0.055)


def srgb_to_xyz(rgb):
    return srgb_to_linear(rgb) @ _M_RGB2XYZ.T


def xyz_to_srgb(xyz):
    return linear_to_srgb(np.asarray(xyz, dtype=float) @ _M_XYZ2RGB.T)


def in_gamut(rgb, tol=1e-6):
    rgb = np.asarray(rgb, dtype=float)
    return bool(np.all(rgb >= -tol) and np.all(rgb <= 1 + tol))


# --- HSL --------------------------------------------------------------------


def hsl_to_srgb(h_deg, s=1.0, l=0.5):
    """Standard HSL -> sRGB. ``h_deg`` in degrees."""
    h = (h_deg % 360.0) / 60.0
    c = (1 - abs(2 * l - 1)) * s
    x = c * (1 - abs(h % 2 - 1))
    m = l - c / 2
    i = int(h) % 6
    r, g, b = [(c, x, 0), (x, c, 0), (0, c, x), (0, x, c), (x, 0, c), (c, 0, x)][i]
    return np.array([r + m, g + m, b + m])


# --- CIELAB -----------------------------------------------------------------


def _f_lab(t):
    d = 6 / 29
    return np.where(t > d**3, np.cbrt(t), t / (3 * d * d) + 4 / 29)


def xyz_to_lab(xyz, white=WHITE_D65):
    xyz = np.asarray(xyz, dtype=float)
    fx, fy, fz = _f_lab(xyz / white).T if xyz.ndim > 1 else _f_lab(xyz / white)
    L = 116 * fy - 16
    a = 500 * (fx - fy)
    b = 200 * (fy - fz)
    return np.stack([L, a, b], axis=-1)


def srgb_to_lab(rgb):
    return xyz_to_lab(srgb_to_xyz(rgb))


def ciede2000(lab1, lab2):
    """CIEDE2000 colour difference (Sharma, Wu, Dalal 2005), kL = kC = kH = 1."""
    L1, a1, b1 = (float(v) for v in lab1)
    L2, a2, b2 = (float(v) for v in lab2)
    C1 = np.hypot(a1, b1)
    C2 = np.hypot(a2, b2)
    Cbar = (C1 + C2) / 2
    G = 0.5 * (1 - np.sqrt(Cbar**7 / (Cbar**7 + 25.0**7)))
    a1p = (1 + G) * a1
    a2p = (1 + G) * a2
    C1p = np.hypot(a1p, b1)
    C2p = np.hypot(a2p, b2)

    def hp(a, b):
        if a == 0 and b == 0:
            return 0.0
        return np.degrees(np.arctan2(b, a)) % 360.0

    h1p = hp(a1p, b1)
    h2p = hp(a2p, b2)
    dLp = L2 - L1
    dCp = C2p - C1p
    if C1p * C2p == 0:
        dhp = 0.0
    else:
        dh = h2p - h1p
        if dh > 180:
            dh -= 360
        elif dh < -180:
            dh += 360
        dhp = dh
    dHp = 2 * np.sqrt(C1p * C2p) * np.sin(np.radians(dhp / 2))
    Lbp = (L1 + L2) / 2
    Cbp = (C1p + C2p) / 2
    if C1p * C2p == 0:
        hbp = h1p + h2p
    else:
        s = h1p + h2p
        if abs(h1p - h2p) <= 180:
            hbp = s / 2
        elif s < 360:
            hbp = (s + 360) / 2
        else:
            hbp = (s - 360) / 2
    T = (
        1
        - 0.17 * np.cos(np.radians(hbp - 30))
        + 0.24 * np.cos(np.radians(2 * hbp))
        + 0.32 * np.cos(np.radians(3 * hbp + 6))
        - 0.20 * np.cos(np.radians(4 * hbp - 63))
    )
    dtheta = 30 * np.exp(-(((hbp - 275) / 25) ** 2))
    RC = 2 * np.sqrt(Cbp**7 / (Cbp**7 + 25.0**7))
    SL = 1 + 0.015 * (Lbp - 50) ** 2 / np.sqrt(20 + (Lbp - 50) ** 2)
    SC = 1 + 0.045 * Cbp
    SH = 1 + 0.015 * Cbp * T
    RT = -np.sin(np.radians(2 * dtheta)) * RC
    return float(
        np.sqrt((dLp / SL) ** 2 + (dCp / SC) ** 2 + (dHp / SH) ** 2 + RT * (dCp / SC) * (dHp / SH))
    )


#: (Lab1, Lab2, dE00) from Sharma, Wu & Dalal (2005), Table 1. Used by the test
#: to pin ``ciede2000``; any pair the implementation disagrees with is a defect.
SHARMA_PAIRS = [
    ((50.0000, 2.6772, -79.7751), (50.0000, 0.0000, -82.7485), 2.0425),
    ((50.0000, 3.1571, -77.2803), (50.0000, 0.0000, -82.7485), 2.8615),
    ((50.0000, 2.8361, -74.0200), (50.0000, 0.0000, -82.7485), 3.4412),
    ((50.0000, -1.3802, -84.2814), (50.0000, 0.0000, -82.7485), 1.0000),
    ((50.0000, -1.1848, -84.8006), (50.0000, 0.0000, -82.7485), 1.0000),
    ((50.0000, -0.9009, -85.5211), (50.0000, 0.0000, -82.7485), 1.0000),
    ((50.0000, 0.0000, 0.0000), (50.0000, -1.0000, 2.0000), 2.3669),
    ((50.0000, -1.0000, 2.0000), (50.0000, 0.0000, 0.0000), 2.3669),
    ((50.0000, 2.4900, -0.0010), (50.0000, -2.4900, 0.0009), 7.1792),
    ((50.0000, 2.4900, -0.0010), (50.0000, -2.4900, 0.0010), 7.1792),
    ((50.0000, 2.4900, -0.0010), (50.0000, -2.4900, 0.0011), 7.2195),
    ((50.0000, 2.4900, -0.0010), (50.0000, -2.4900, 0.0012), 7.2195),
    ((50.0000, -0.0010, 2.4900), (50.0000, 0.0009, -2.4900), 4.8045),
    ((50.0000, -0.0010, 2.4900), (50.0000, 0.0010, -2.4900), 4.8045),
    ((50.0000, -0.0010, 2.4900), (50.0000, 0.0011, -2.4900), 4.7461),
    ((50.0000, 2.5000, 0.0000), (50.0000, 0.0000, -2.5000), 4.3065),
    ((50.0000, 2.5000, 0.0000), (73.0000, 25.0000, -18.0000), 27.1492),
    ((50.0000, 2.5000, 0.0000), (61.0000, -5.0000, 29.0000), 22.8977),
    ((50.0000, 2.5000, 0.0000), (56.0000, -27.0000, -3.0000), 31.9030),
    ((50.0000, 2.5000, 0.0000), (58.0000, 24.0000, 15.0000), 19.4535),
    ((50.0000, 2.5000, 0.0000), (50.0000, 3.1736, 0.5854), 1.0000),
    ((50.0000, 2.5000, 0.0000), (50.0000, 3.2972, 0.0000), 1.0000),
    ((50.0000, 2.5000, 0.0000), (50.0000, 1.8634, 0.5757), 1.0000),
    ((50.0000, 2.5000, 0.0000), (50.0000, 3.2592, 0.3350), 1.0000),
    ((60.2574, -34.0099, 36.2677), (60.4626, -34.1751, 39.4387), 1.2644),
    ((63.0109, -31.0961, -5.8663), (62.8187, -29.7946, -4.0864), 1.2630),
    ((61.2901, 3.7196, -5.3901), (61.4292, 2.2480, -4.9620), 1.8731),
    ((35.0831, -44.1164, 3.7933), (35.0232, -40.0716, 1.5901), 1.8645),
    ((22.7233, 20.0904, -46.6940), (23.0331, 14.9730, -42.5619), 2.0373),
    ((36.4612, 47.8580, 18.3852), (36.2715, 50.5065, 21.2231), 1.4146),
    ((90.8027, -2.0831, 1.4410), (91.1528, -1.6435, 0.0447), 1.4441),
    ((90.9257, -0.5406, -0.9208), (88.6381, -0.8985, -0.7239), 1.5381),
    ((6.7747, -0.2908, -2.4247), (5.8714, -0.0985, -2.2286), 0.6377),
    ((2.0776, 0.0795, -1.1350), (0.9033, -0.0636, -0.5514), 0.9082),
]


# --- OKLab ------------------------------------------------------------------

_M1 = np.array(
    [
        [0.8189330101, 0.3618667424, -0.1288597137],
        [0.0329845436, 0.9293118715, 0.0361456387],
        [0.0482003018, 0.2643662691, 0.6338517070],
    ]
)
_M2 = np.array(
    [
        [0.2104542553, 0.7936177850, -0.0040720468],
        [1.9779984951, -2.4285922050, 0.4505937099],
        [0.0259040371, 0.7827717662, -0.8086757660],
    ]
)


def xyz_to_oklab(xyz):
    lms = np.asarray(xyz, dtype=float) @ _M1.T
    return np.cbrt(lms) @ _M2.T


def oklab_to_xyz(lab):
    lms_ = np.asarray(lab, dtype=float) @ np.linalg.inv(_M2).T
    return (lms_**3) @ np.linalg.inv(_M1).T


def srgb_to_oklab(rgb):
    return xyz_to_oklab(srgb_to_xyz(rgb))


def oklab_to_srgb(lab):
    return xyz_to_srgb(oklab_to_xyz(lab))


def oklch_to_oklab(L, C, h_deg):
    h = np.radians(h_deg)
    return np.array([L, C * np.cos(h), C * np.sin(h)])


def oklab_to_oklch(lab):
    L, a, b = (float(v) for v in lab)
    return L, float(np.hypot(a, b)), float(np.degrees(np.arctan2(b, a)) % 360.0)


def max_chroma_in_gamut(L, h_deg, tol=1e-6):
    """Largest OKLCH chroma at (L, h) whose sRGB image stays inside the gamut."""
    lo, hi = 0.0, 0.5
    while hi - lo > tol:
        mid = (lo + hi) / 2
        if in_gamut(oklab_to_srgb(oklch_to_oklab(L, mid, h_deg))):
            lo = mid
        else:
            hi = mid
    return lo

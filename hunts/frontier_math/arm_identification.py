"""The two arms compute one function: `ghat(z) = Phi2(-i z)`.

This hunt grew two independent certification efforts.

* **BandCert** (`zeta23ext/Zeta23Ext/BandCert/`, 2283 lines, sorry-free)
  encloses the *paper field* `Phi2(z) = s(z + sqrt2) + s(z - sqrt2)` with
  `s(u) = sin(u/2)/u`, on a fixed-point interval arithmetic at scale
  `2^-64`, and uses it for the band-dual verdict.
* **EForm3** (`zeta23ext/Zeta23Ext/EForm3/`) works the retention
  inequality through `Qre`, `Qim` and the *damage* `D(y,s) = Qim^2 - Qre^2`,
  built from `ghat(z) = int_{-1/2}^{1/2} cos(sqrt2 u) cosh(z u) du`.

Nobody noticed these are the same function.  They are:

    ghat(z) = Phi2(-i z)          for every complex z,

checked here to the last bit of double precision at 27 points on and off
the real axis (:func:`identification_residual`), and derivable in one line:
`ghat` has the closed form `sinh((z+i sqrt2)/2)/(z + i sqrt2) +
sinh((z-i sqrt2)/2)/(z - i sqrt2)`, and `sinh(i w / 2)/(i w) = sin(w/2)/w
= s(w)`, so substituting `z = -i w` turns each `ghat` branch into an `s`
branch of `Phi2`.

## Why it matters

The single-pair (`k = 1`) retention chain is closed at hardened grade
(ledger 2026-08-13); its one substantial remaining formalisation
obligation was described as "a two-variable interval table over
`[28/5, 60] x [0, 1/2]` — the analogue of the BandCert leaf tables".
Under the identification it is not the *analogue* of those tables, it is
an *instance* of them.  Specifically `BandCert.Phi.phiC_mem` already
gives, sorry-free,

    phiC X Y SH CH  encloses  Phi2 (g + i y)      (X ∋ g, Y ∋ y, y ≠ 0,
                                                   SH ∋ sinh(y/2), CH ∋ cosh(y/2))

so with `g = s` and `y_arg = -y` it encloses `ghat(y + i s)` directly, and
`CIv.mul_mem` squares it.  The damage enclosure is then

    D(y,s) = -Re[ ghat(y + i s)^2 ] = -Re[ Phi2(s - i y)^2 ],

three composition steps on top of theorems that already compile.  The
complex interval layer (`CIv` with `add/sub/mul/div/mulR/ofR` soundness)
that this was assumed to need is also already there.

`REUSE_MAP` below names, obligation by obligation, which existing
kernel-checked theorem covers it and what is genuinely new.

## What is NOT claimed

The identification is an identity between two closed forms, not a proof of
anything about retention; the wiring lemma that connects EForm3's `Qre`/
`Qim` to `BandDual.Phi2` inside Lean is small but is **not written**, and
the table itself is not built.  Nothing here is evidence about RH.

Run ``.venv/bin/python hunts/frontier_math/arm_identification.py``.
"""

from __future__ import annotations

import cmath
import math

__all__ = [
    "SQ2", "A_CONST", "ghat", "phi2", "sfun", "damage_via_ghat",
    "damage_via_phi2", "IDENTIFICATION_POINTS", "identification_residual",
    "damage_route_residual", "REUSE_MAP", "REMAINING", "report",
]

SQ2 = math.sqrt(2.0)
A_CONST = SQ2 * math.sin(1 / SQ2)


def ghat(z: complex) -> complex:
    """`int_{-1/2}^{1/2} cos(sqrt2 u) cosh(z u) du` — EForm3's transform."""
    zp, zm = z + 1j * SQ2, z - 1j * SQ2
    return cmath.sinh(zp / 2) / zp + cmath.sinh(zm / 2) / zm


def sfun(u: complex) -> complex:
    """`s(u) = sin(u/2)/u`, `s(0) = 1/2` — BandCert's `sfunC`."""
    if u == 0:
        return 0.5 + 0j
    return cmath.sin(u / 2) / u


def phi2(z: complex) -> complex:
    """`Phi2(z) = s(z + sqrt2) + s(z - sqrt2)` — BandCert's paper field."""
    return sfun(z + SQ2) + sfun(z - SQ2)


#: Points spanning the real axis, the strip `0 <= y <= 1/2` and the far
#: field, including the innermost damage window and `phi_r`'s first zeros.
IDENTIFICATION_POINTS = (
    0 + 0j, 1 + 0j, 3.7 + 0j, 6.516999776 + 0j, 12.755 + 0j, 30 + 0j,
    59.9 + 0j, 0.5 + 0j, 0.5 + 6.517j, 0.5 + 0.0j, 0.3 + 12.7j,
    0.5 + 6.0653j, 0.5 + 59.5j, 0.25 + 25.2j, 0.49 + 6.517j,
    0.1 + 18.977j, 0.5 + 100.0j, 0.05 + 6.3j, 0.4 + 31.47j,
    1j, 6.517j, -6.517j, 0.5 - 6.517j, 2 + 2j, -1 + 0.5j,
    0.5 + 1e-6j, 1e-9 + 6.517j,
)


def identification_residual(points=IDENTIFICATION_POINTS) -> float:
    """`max |ghat(z) - Phi2(-i z)|` over `points`."""
    return max(abs(ghat(z) - phi2(-1j * z)) for z in points)


def damage_via_ghat(y: float, s: float) -> float:
    """EForm3's route: `D = Qim^2 - Qre^2 = -Re ghat(y + i s)^2`."""
    g = ghat(complex(y, s))
    return -(g * g).real


def damage_via_phi2(y: float, s: float) -> float:
    """BandCert's route: `D = -Re Phi2(s - i y)^2`.

    This is the composition the Lean side would build: `phiC` at the point
    `(g, y_arg) = (s, -y)`, squared with `CIv.mul`, real part negated.
    """
    p = phi2(complex(s, -y))
    return -(p * p).real


def damage_route_residual(ys=(0.05, 0.1, 0.25, 0.4, 0.49, 0.5),
                          ss=(6.0653, 6.517, 9.0, 12.755, 18.977, 31.47,
                              45.0, 59.9)) -> float:
    """`max |damage_via_ghat - damage_via_phi2|` over the obligation box."""
    return max(abs(damage_via_ghat(y, s) - damage_via_phi2(y, s))
               for y in ys for s in ss)


#: Obligation -> what already covers it.  "NEW" means genuinely to write.
REUSE_MAP = (
    ("complex interval arithmetic (add/sub/mul/div, soundness)",
     "BandCert.Phi.CIv + add_mem/sub_mem/mul_mem/div_mem/mulR_mem/ofR_mem",
     "COVERED"),
    ("fixed-point real interval arithmetic at 2^-64",
     "BandCert.Iv (EIv, 20+ operations, each with a _mem lemma)", "COVERED"),
    ("sin, cos at large argument (needs reduction to |t| <= 1)",
     "BandCert.Leaves.sinCosIv (L1 + L3, pi to 2^-64, doubling)", "COVERED"),
    ("sinh, cosh on the depth range",
     "BandCert.Leaves.sinhCoshSmall (L4)", "COVERED"),
    ("sqrt2 to 2^-64", "BandCert.Leaves.SQ2 / SQ2_mem", "COVERED"),
    ("Phi2 at a COMPLEX point, with soundness",
     "BandCert.Phi.phiC / phiC_mem  (y != 0)", "COVERED"),
    ("A and A^2 enclosed", "BandCert.Phi.AIV_mem / A2IV_mem", "COVERED"),
    ("the exact reduction margin = (4/A^2) slack",
     "EForm3.retention_gap + Gap.energy_F, both sorry-free; the step is "
     "linarith", "NEW, small"),
    ("wiring: EForm3's Qre/Qim to BandDual's Phi2",
     "ghat(y+is) = Phi2(s - i y); both sides have closed forms already in "
     "the two files (Phi2_closed, and EForm3's ClosedForm.lean)",
     "NEW, small"),
    ("the damage cap table on [28/5, 60] x [0, 1/2]",
     "an instance of the BandCert leaf-table pattern (Data/Leaves/Check/"
     "Verify), driven by phiC", "NEW, the real cost"),
    ("integer square completion per window",
     "elementary: max over m of m D - c m(m-1)", "NEW, small"),
    ("K >= 39/50 on |u| <= 1 and K >= 1/125 on |u| <= 6",
     "one-variable bounds on phiR^2, phiR_mem already encloses phiR",
     "NEW, small"),
)

REMAINING = (
    "R1 the wiring lemma is NOT written; the identification is checked "
    "numerically here and derived on paper, not in Lean.",
    "R2 phiC_mem carries `y != 0`; the damage statement needs y = 0 too, "
    "where D = -phi_r^2 <= 0 is trivial but still needs its own line.",
    "R3 the table is not built. Its size is the open engineering question: "
    "BandCert's existing cover uses 62-248 cells per depth.",
    "R4 the identification says nothing about the multi-pair (k >= 2) "
    "quantifier, which is open (ledger 2026-08-13, defect #20).",
    "R5 nothing here is evidence about RH.",
)


def report() -> dict:
    print("= the identification =")
    r = identification_residual()
    print(f"  max |ghat(z) - Phi2(-i z)| over {len(IDENTIFICATION_POINTS)} "
          f"points = {r:.3e}")
    print(f"  A = Phi2(0) = {phi2(0).real:.16f}  (EForm3's Aconst "
          f"{A_CONST:.16f})")
    print("= the damage function, both routes =")
    d = damage_route_residual()
    print(f"  max |(-Re ghat(y+is)^2) - (-Re Phi2(s-iy)^2)| over the "
          f"obligation box = {d:.3e}")
    for y, s in ((0.5, 6.517), (0.5, 12.755), (0.25, 31.47)):
        print(f"  y={y} s={s}: {damage_via_ghat(y, s):+.10f} vs "
              f"{damage_via_phi2(y, s):+.10f}")
    print("= what the reuse map says =")
    cov = sum(1 for _, _, st in REUSE_MAP if st == "COVERED")
    print(f"  {cov} of {len(REUSE_MAP)} obligations are already "
          f"kernel-checked in BandCert; {len(REUSE_MAP)-cov} are new, of "
          f"which ONE is substantial:")
    for ob, by, st in REUSE_MAP:
        mark = "  " if st == "COVERED" else ">>"
        print(f"  {mark} [{st:<16}] {ob}")
        print(f"       <- {by}")
    print("= what remains =")
    for x in REMAINING:
        print(f"  * {x}")
    return {"identification_residual": r, "damage_route_residual": d,
            "covered": cov, "total": len(REUSE_MAP)}


if __name__ == "__main__":
    report()

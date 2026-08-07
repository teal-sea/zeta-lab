"""Gate 4, made into a number: a decision statistic for the Euler product.

`docs/09` §5 asks four questions of any proposed ontology for RH. Gate 3
(the counterexample gate) and Gate 4 (the Euler product must be structural)
are both stated qualitatively — "where exactly does Davenport–Heilbronn fail
to embed?", "the primes must be the points". This module turns that pair
into something a candidate can be *measured* against.

The statistic.  For a Dirichlet series f(s) = Σ aₙn^{−s} with a₁ = 1, write
its logarithmic derivative as −f′/f = Σ bₙn^{−s} (obtained by convolution:
aₙ log n = Σ_{m|n} b_m a_{n/m}).  Define

    D(f) = Σ_{n composite, not a prime power} bₙ²/n
           ────────────────────────────────────────
           Σ_{n a prime power}               bₙ²/n

with the 1/n weight chosen to match the zero-side atom energy of
`zeta/quasicrystal.py`, where atom weight goes like bₙ/√n.

**D = 0 if and only if f has an Euler product**, and this is an equivalence
rather than a heuristic.  One direction: an Euler product makes log f a sum
of independent local terms, so −f′/f is supported on prime powers.  The
other: if b is supported on prime powers then log f = Σ_{p,m} c_{p^m}p^{−ms}
splits as Σ_p (local series), and exponentiating gives the product.  So D is
a genuine decision procedure for Gate 4, computable from coefficients alone
with no zeros, no ξ-phases and no counting functions — which is exactly the
provenance restriction of §5.1's Requirement A.

Measured (`factorization_report`):

| function | D | status |
| --- | --- | --- |
| ζ | 1.2e-32 | Euler product |
| L(χ) quadratic mod 3, 4, 5 | ~1e-32 | Euler product |
| Davenport–Heilbronn | 0.979 | no Euler product |
| the c = ½ real-part combination | 0.825 | no Euler product |

The Euler-product rows are zero to float64 rounding; anything below ~1e-20
is zero at this precision.

**And the control, which is the point.**  A nonzero D means nothing on its
own until you know what a *generic* non-factoring sequence scores.  Against
a null of random real coefficient sequences with DH's shape (period 5,
a₁ = 1, a₅ = 0), the null median is 1.33 with a 5–95% band of 0.53–4.31, and
**Davenport–Heilbronn lands at the 27th percentile — squarely typical**.
DH is not an exotic near-miss to factorization; it is an unremarkable member
of the class of things that do not factor.  A candidate ontology that
"almost" produces an Euler product would have to score orders of magnitude
below this null, not merely nonzero.

**What this does not do.**  It tests factorization, not RH.  An Euler
product is not known to imply RH — that implication is substantially GRH.
Nothing here is evidence for RH (`docs/08`).

A related blindness worth stating, because it bounds every ordinate-based
probe including `zeta/quasicrystal.py`: the zeros of ζ(s−δ) are the points
δ+½+iγ with **the same ordinates γ**.  Any statistic computed from ordinates
alone is therefore identical for ζ and for a shifted function whose zeros lie
nowhere near Re s = ½.  Ordinate probes read arithmetic; they cannot read the
position of the critical line.  That is why the coefficient-side statistic
here is the one that carries the Gate 4 content.

Everything here is *accurate*, not *certified* (see `zeta/rigor.py`).
"""

from __future__ import annotations

from typing import Any, Sequence

import numpy as np

__all__ = [
    "DEFAULT_N_MAX",
    "ZERO_THRESHOLD",
    "periodic_coefficients",
    "log_derivative_coefficients",
    "factorization_defect",
    "euler_product_panel",
    "null_distribution",
    "factorization_report",
    "dh_family_coefficients",
    "kappa_landscape",
]

DEFAULT_N_MAX = 80
# Below this, D is zero to float64 rounding: an exact Euler product scores
# ~1e-32 here because the composite b_n are ~1e-16 and enter squared.
ZERO_THRESHOLD = 1e-20

# kappa of the Davenport-Heilbronn function.  Re-derived on demand by
# zeta.epstein.kappa; the literal is a test reference only, per house rule.
KAPPA_REF = 0.28407904384041227


def periodic_coefficients(values: Sequence[float], n_max: int = DEFAULT_N_MAX) -> np.ndarray:
    """aₙ from one period, indexed 1..n_max (index 0 unused)."""
    q = len(values)
    a = np.zeros(n_max + 1)
    for n in range(1, n_max + 1):
        a[n] = float(values[(n - 1) % q])
    return a


def log_derivative_coefficients(
    a: Sequence[float], n_max: int = DEFAULT_N_MAX
) -> np.ndarray:
    """bₙ with −f′/f = Σ bₙn^{−s}, by Dirichlet convolution.

    Same recursion as ``zeta.quasicrystal.dh_log_derivative_coefficients``,
    at float rather than mpmath precision — this one is for bulk statistics
    (house rule: numpy for bulk, mpmath where precision is critical).  The
    two are checked against each other on DH in the tests.
    """
    a = np.asarray(a, dtype=float)
    if a[1] == 0:
        raise ValueError("a_1 must be nonzero (normalize the series first)")
    b = np.zeros(n_max + 1)
    for n in range(1, n_max + 1):
        s = a[n] * np.log(n)
        for m in range(1, n):
            if n % m == 0:
                s -= b[m] * a[n // m]
        b[n] = s / a[1]
    return b


def factorization_defect(
    a: Sequence[float], n_max: int = DEFAULT_N_MAX
) -> float:
    """D(f): composite-supported energy of −f′/f over prime-power energy.

    Zero exactly when f has an Euler product (see module docstring for both
    directions of the equivalence).
    """
    from .explicit import mangoldt

    b = log_derivative_coefficients(a, n_max)
    pp = 0.0
    comp = 0.0
    for n in range(2, n_max + 1):
        energy = b[n] ** 2 / n
        if mangoldt(n) > 0:
            pp += energy
        else:
            comp += energy
    return float(comp / pp) if pp > 0 else float("inf")


def euler_product_panel(n_max: int = DEFAULT_N_MAX) -> dict[str, dict[str, Any]]:
    """D for a panel of functions whose factorization status is known.

    The Euler-product members are the calibration: a statistic that did not
    return zero for ζ and for the quadratic characters would be measuring
    something other than factorization.
    """
    members = {
        "zeta": ([1.0], True),
        "L quadratic mod 3": ([1, -1, 0], True),
        "L quadratic mod 4": ([1, 0, -1, 0], True),
        "L quadratic mod 5": ([1, -1, -1, 1, 0], True),
        "DH real-part combination (c=1/2)": ([1, 0, 0, -1, 0], False),
        "Davenport-Heilbronn": ([1, KAPPA_REF, -KAPPA_REF, -1, 0], False),
    }
    out = {}
    for name, (period, has_euler) in members.items():
        d = factorization_defect(periodic_coefficients(period, n_max), n_max)
        out[name] = {
            "defect": d,
            "has_euler_product": has_euler,
            "verdict_correct": bool((d < ZERO_THRESHOLD) == has_euler),
        }
    return out


def null_distribution(
    n_samples: int = 400, seed: int = 7, n_max: int = DEFAULT_N_MAX
) -> dict[str, Any]:
    """D for random real sequences with Davenport–Heilbronn's shape.

    Period 5, a₁ = 1, a₅ = 0, the three free slots drawn standard normal.
    This is what "does not factor" looks like generically, and it is the
    only thing that makes a nonzero D interpretable.
    """
    rng = np.random.default_rng(seed)
    vals = []
    for _ in range(int(n_samples)):
        v = rng.normal(size=3)
        a = periodic_coefficients([1.0, v[0], v[1], v[2], 0.0], n_max)
        vals.append(factorization_defect(a, n_max))
    arr = np.array(vals)
    return {
        "n_samples": int(n_samples),
        "seed": int(seed),
        "median": float(np.median(arr)),
        "p05": float(np.percentile(arr, 5)),
        "p95": float(np.percentile(arr, 95)),
        "samples": arr,
    }


def factorization_report(
    n_max: int = DEFAULT_N_MAX, n_samples: int = 400, seed: int = 7
) -> dict[str, Any]:
    """Panel + null + where Davenport–Heilbronn sits inside the null."""
    panel = euler_product_panel(n_max)
    null = null_distribution(n_samples, seed, n_max)
    dh = panel["Davenport-Heilbronn"]["defect"]
    pct = float(100.0 * (null["samples"] < dh).mean())
    return {
        "panel": {k: {kk: vv for kk, vv in v.items()} for k, v in panel.items()},
        "null_median": null["median"],
        "null_p05": null["p05"],
        "null_p95": null["p95"],
        "dh_defect": dh,
        "dh_percentile_in_null": pct,
        "all_verdicts_correct": all(v["verdict_correct"] for v in panel.values()),
        "dh_is_typical": bool(null["p05"] < dh < null["p95"]),
        "verdict": (
            "D is a decision statistic for Gate 4: exactly zero iff f has an "
            "Euler product, computed from coefficients alone (no zeros, no "
            "xi-phases) as Requirement A demands. Davenport-Heilbronn scores "
            f"{dh:.3f}, the {pct:.0f}th percentile of a matched null of "
            "non-factoring sequences -- typical, not an exotic near-miss. "
            "Tests factorization, NOT RH; an Euler product is not known to "
            "imply RH (docs/08, docs/09)."
        ),
    }


# ----------------------------------------------------------------------
# Is the functional equation's kappa special for factorization?
# ----------------------------------------------------------------------

def dh_family_coefficients(t: float, n_max: int = DEFAULT_N_MAX) -> np.ndarray:
    """The one-parameter family aₙ = [1, t, −t, −1, 0], periodic mod 5.

    Davenport–Heilbronn is the member at t = κ, where κ is *forced* by the
    functional equation F(s) = F(1−s) (re-derived by linear solve on every
    call in ``zeta.epstein.kappa``).  Factorization is a different functional
    of the same coefficients, so this family is the natural place to ask
    whether the two constraints know about each other.
    """
    return periodic_coefficients([1.0, float(t), -float(t), -1.0, 0.0], n_max)


def kappa_landscape(
    t_values: Sequence[float] | None = None, n_max: int = DEFAULT_N_MAX
) -> dict[str, Any]:
    """D along the DH family, and whether κ sits anywhere distinguished on it.

    Measured:

    * D is **exactly even** in t.  That is structural rather than lucky —
      t ↦ −t conjugates the underlying character, and conjugation cannot
      change whether something factors.
    * The family minimum is at **t = 0** with D = 0.825 (the real-part
      combination), and **no member of the family factors**: D never comes
      near zero anywhere on it.
    * At κ = 0.284079 the defect is 0.979 with slope dD/dt = **+1.154**.
      κ is *not* a critical point; it sits on a plain upslope.

    So the functional equation pins κ exactly and says nothing whatever about
    the Euler product.  This is `docs/09` Gate 2 — "symmetry alone is
    provably insufficient" — as a measurement rather than an assertion: one
    can slide t along the family, destroying the functional equation at every
    point but κ, without ever gaining or losing factorization.

    Does not test RH.  Everything here is *accurate*, not *certified*.
    """
    from .epstein import kappa as _kappa_derived

    kappa = float(_kappa_derived(30))
    if t_values is None:
        t_values = np.linspace(-3.0, 3.0, 241)
    ts = np.asarray(t_values, dtype=float)
    ds = np.array(
        [factorization_defect(dh_family_coefficients(t, n_max), n_max) for t in ts]
    )

    h = 1e-4
    slope = (
        factorization_defect(dh_family_coefficients(kappa + h, n_max), n_max)
        - factorization_defect(dh_family_coefficients(kappa - h, n_max), n_max)
    ) / (2 * h)

    i_min = int(np.argmin(ds))
    d_kappa = factorization_defect(dh_family_coefficients(kappa, n_max), n_max)
    return {
        "kappa": kappa,
        "t_values": ts,
        "defects": ds,
        "defect_at_kappa": float(d_kappa),
        "slope_at_kappa": float(slope),
        "kappa_is_critical_point": bool(abs(slope) < 1e-3),
        "min_defect": float(ds[i_min]),
        "argmin_t": float(ts[i_min]),
        "family_ever_factors": bool((ds < ZERO_THRESHOLD).any()),
        "verdict": (
            "kappa is forced by the functional equation and is NOT a critical "
            f"point of the factorization defect (slope {slope:+.3f}); no "
            "member of the family factors, and the family minimum sits at "
            "t=0 with D=0.825, still far from zero. The functional equation "
            "and the Euler product are independent constraints -- docs/09 "
            "Gate 2, 'symmetry alone is provably insufficient', measured."
        ),
    }

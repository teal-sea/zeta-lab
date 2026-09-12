"""Attack on the mechanism stated in `hunts/epp_herglotz/MISSION.md`.

Nothing here is a result.  The mechanism claims that Euler-product positivity
(`Lambda(n) >= 0`) plus the functional equation composes into
`Re (xi'/xi) >= 0` on `Re s > 1/2`, which is equivalent to RH.  This file
tries to destroy that claim.

The attack instrument is the **symmetric shifted product**

    W_a(s) = zeta(s+a) zeta(s-a),      Xi_a(s) = xi(s+a) xi(s-a),   a real

which is built here because it carries, by construction, every hypothesis the
mechanism uses:

* an exact `s -> 1-s` functional equation for the completed function,
  `Xi_a(1-s) = Xi_a(s)`, with `Xi_a(1/2+it)` real;
* a *scalar* Euler product, `prod_p (1-p^{-s-a})^{-1} (1-p^{-s+a})^{-1}`,
  which neither standing rival of `zeta.epstein.battery` has;
* non-negative log-derivative coefficients,
  `Lambda_{W_a}(n) = Lambda(n) (n^a + n^{-a}) >= 0`, which is the
  mechanism's load-bearing hypothesis (EPP);
* real, non-negative, multiplicative Dirichlet coefficients;

and for which RH is false unconditionally: the zeros of `Xi_a` are the points
`rho +- a`, and Hardy's theorem puts infinitely many `rho` on `Re s = 1/2`, so
infinitely many zeros of `Xi_a` sit on `Re s = 1/2 + a` and `Re s = 1/2 - a`.
No assumption about zeta is needed for that sentence.

Run: `.venv/bin/python hunts/epp_herglotz/probe.py`
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

import mpmath
from mpmath import mp

_REPO_ROOT = Path(__file__).resolve().parents[2]
if str(_REPO_ROOT) not in sys.path:  # pragma: no cover - import bootstrap
    sys.path.insert(0, str(_REPO_ROOT))

from zeta.core import xi  # noqa: E402
from zeta.epstein import battery, count_zeros_box  # noqa: E402

#: The shift used throughout.  a = 1/4 keeps the zeros of `W_a` inside the
#: critical strip (they sit on Re s = 1/4 and Re s = 3/4) and keeps the
#: Dirichlet series convergent for Re s > 5/4.
SHIFT = mpmath.mpf(1) / 4

#: zeta's first ordinate, used only as a place to look.
GAMMA_1 = mpmath.mpf("14.134725141734693790")


# ---------------------------------------------------------------------------
# the two functions, and their log-derivatives by two independent routes
# ---------------------------------------------------------------------------


def xi_log_derivative_explicit(s, dps: int = 30):
    """`xi'/xi(s)` from the explicit split `G + zeta'/zeta`."""
    with mp.workdps(dps + 10):
        s = mp.mpmathify(s)
        g = 1 / s + 1 / (s - 1) - mp.log(mp.pi) / 2 + mp.digamma(s / 2) / 2
        z = mp.zeta(s, derivative=1) / mp.zeta(s)
        return +(g + z)


def xi_direct(s, dps: int = 30):
    """`xi(s) = (1/2) s (s-1) pi^{-s/2} Gamma(s/2) zeta(s)`, from mpmath alone.

    `zeta.core.xi` rounds its return to the requested `dps`, which makes a
    difference quotient of it unusable; this is the same function written so
    that `mp.diff` can see full working precision.  The two are compared
    against each other in stage A.
    """
    with mp.workdps(dps + 10):
        s = mp.mpmathify(s)
        return +(s * (s - 1) / 2 * mp.pi ** (-s / 2) * mp.gamma(s / 2) * mp.zeta(s))


def xi_log_derivative_numeric(s, dps: int = 30):
    """`xi'/xi(s)` by numerical differentiation of :func:`xi_direct`."""
    with mp.workdps(dps + 20):
        s = mp.mpmathify(s)
        f = lambda z: xi_direct(z, dps=dps + 20)
        d = mp.diff(f, s, method="quad", radius=mp.mpf(1) / 4)
        return +(d / f(s))


def archimedean_part(s, dps: int = 30):
    """`G(s) = 1/s + 1/(s-1) - (1/2)log pi + (1/2)psi(s/2)`."""
    with mp.workdps(dps + 10):
        s = mp.mpmathify(s)
        return +(1 / s + 1 / (s - 1) - mp.log(mp.pi) / 2 + mp.digamma(s / 2) / 2)


def prime_part(s, dps: int = 30):
    """`A(s) = sum_n Lambda(n) n^{-s} = -zeta'/zeta(s)`."""
    with mp.workdps(dps + 10):
        s = mp.mpmathify(s)
        return +(-mp.zeta(s, derivative=1) / mp.zeta(s))


def completed_shift(s, a=SHIFT, dps: int = 30):
    """`Xi_a(s) = xi(s+a) xi(s-a)`."""
    with mp.workdps(dps + 10):
        s = mp.mpmathify(s)
        return +(xi(s + a, dps=dps + 10) * xi(s - a, dps=dps + 10))


def shift_log_derivative(s, a=SHIFT, dps: int = 30):
    """`Xi_a'/Xi_a(s) = xi'/xi(s+a) + xi'/xi(s-a)`."""
    with mp.workdps(dps + 10):
        s = mp.mpmathify(s)
        return +(xi_log_derivative_explicit(s + a, dps=dps + 10)
                 + xi_log_derivative_explicit(s - a, dps=dps + 10))


def shift_prime_part(s, a=SHIFT, dps: int = 30):
    """`A_a(s) = sum_n Lambda(n)(n^a + n^{-a}) n^{-s} = -W_a'/W_a(s)`."""
    with mp.workdps(dps + 10):
        s = mp.mpmathify(s)
        return +(prime_part(s + a, dps=dps + 10) + prime_part(s - a, dps=dps + 10))


def shift_archimedean_part(s, a=SHIFT, dps: int = 30):
    with mp.workdps(dps + 10):
        s = mp.mpmathify(s)
        return +(archimedean_part(s + a, dps=dps + 10)
                 + archimedean_part(s - a, dps=dps + 10))


# ---------------------------------------------------------------------------
# Dirichlet coefficients, and the log-derivative coefficients from them
# ---------------------------------------------------------------------------


def shift_coefficient(n: int, a=SHIFT, dps: int = 30):
    """`b_n = sum_{de=n} d^{-a} e^{a}`, the Dirichlet coefficients of `W_a`."""
    with mp.workdps(dps + 10):
        total = mp.mpf(0)
        for d in range(1, n + 1):
            if n % d == 0:
                total += mp.mpf(d) ** (-a) * mp.mpf(n // d) ** a
        return +total


def log_derivative_coefficients(coefficient, n_max: int, dps: int = 30):
    """`Lambda_F(n)` for `n <= n_max`, from the Dirichlet coefficients alone.

    Uses `b_n log n = sum_{d | n} Lambda_F(d) b_{n/d}` with `b_n = a_n / a_1`,
    so an interface whose `a_1` is not 1 (Epstein counts units) is normalised
    rather than rejected.  This route never sees an Euler product; it only
    sees coefficients, which is the point.
    """
    with mp.workdps(dps + 15):
        a1 = mp.mpmathify(coefficient(1))
        if a1 == 0:
            raise ValueError("a_1 = 0: the log-derivative recursion is undefined")
        b = [mp.mpf(0)] * (n_max + 1)
        for n in range(1, n_max + 1):
            b[n] = mp.mpmathify(coefficient(n)) / a1
        lam = [mp.mpf(0)] * (n_max + 1)
        for n in range(2, n_max + 1):
            acc = b[n] * mp.log(n)
            for d in range(2, n):
                if n % d == 0:
                    acc -= lam[d] * b[n // d]
            lam[n] = acc
        return [+x for x in lam]


def von_mangoldt(n: int):
    """`Lambda(n)`, by trial division; small `n` only."""
    m, p = n, 2
    while p * p <= m:
        if m % p == 0:
            e = 0
            while m % p == 0:
                m //= p
                e += 1
            return mp.log(p) if m == 1 else mp.mpf(0)
        p += 1
    return mp.log(n) if n > 1 else mp.mpf(0)


# ---------------------------------------------------------------------------
# stage A: the target, measured rather than assumed
# ---------------------------------------------------------------------------


def stage_a(dps: int = 30) -> dict:
    """`Re xi'/xi` vanishes on the critical line, and is positive to its right.

    Both are consequences of `F(1-s) = -F(s)` and the paired Hadamard sum, so
    this stage is a check on the arithmetic of the mechanism's first sentence,
    not evidence for anything.
    """
    out: dict = {}
    probe_s = mp.mpc("0.8", "3")
    out["log_derivative_route_defect"] = mp.nstr(
        abs(xi_log_derivative_explicit(probe_s, dps=dps)
            - xi_log_derivative_numeric(probe_s, dps=dps)), 6)
    out["xi_vs_xi_direct_defect"] = mp.nstr(
        abs(xi(probe_s, dps=dps) - xi_direct(probe_s, dps=dps)), 6)

    on_line = []
    for t in ("1", "5", "14.5", "30", "77.3"):
        val = xi_log_derivative_explicit(mp.mpc("0.5", t), dps=dps)
        on_line.append(float(abs(mp.re(val))))
    out["max_abs_re_on_critical_line"] = max(on_line)

    grid = []
    for sigma in ("0.5001", "0.55", "0.7", "0.9", "1.0", "1.5", "3.0"):
        for t in ("0.3", "2", "7", "14.134725", "21.5", "40", "60"):
            val = xi_log_derivative_explicit(mp.mpc(sigma, t), dps=dps)
            grid.append((sigma, t, float(mp.re(val))))
    out["grid_points"] = len(grid)
    out["min_re_right_of_line"] = min(g[2] for g in grid)
    out["argmin_right_of_line"] = [g for g in grid if g[2] == out["min_re_right_of_line"]][0][:2]
    mirrored = []
    for sigma in ("0.4999", "0.3", "0.1"):
        for t in ("2", "14.134725", "40"):
            mirrored.append(float(mp.re(xi_log_derivative_explicit(mp.mpc(sigma, t), dps=dps))))
    out["max_re_left_of_line"] = max(mirrored)
    return out


# ---------------------------------------------------------------------------
# stage B: the rival, and every hypothesis the mechanism uses
# ---------------------------------------------------------------------------


def stage_b(a=SHIFT, dps: int = 30, n_max: int = 60) -> dict:
    """`W_a` carries the functional equation, the Euler product and EPP."""
    out: dict = {"shift": mp.nstr(a, 10)}

    fe = []
    for s in (mp.mpc("0.3", "2"), mp.mpc("0.9", "17"), mp.mpc("-1.2", "5.5"),
              mp.mpc("2.4", "-8")):
        d = completed_shift(s, a=a, dps=dps) - completed_shift(1 - s, a=a, dps=dps)
        scale = abs(completed_shift(s, a=a, dps=dps))
        fe.append(float(abs(d) / scale) if scale else float(abs(d)))
    out["max_relative_fe_defect"] = max(fe)

    imag = []
    for t in ("2", "9.5", "14.134725", "31"):
        v = completed_shift(mp.mpc("0.5", t), a=a, dps=dps)
        imag.append(float(abs(mp.im(v)) / abs(v)))
    out["max_relative_imag_on_line"] = max(imag)

    coeffs = [shift_coefficient(n, a=a, dps=dps) for n in range(1, n_max + 1)]
    out["min_dirichlet_coefficient"] = float(min(coeffs))
    out["coefficient_1"] = float(coeffs[0])
    out["coefficient_growth_n60_over_d60"] = float(coeffs[-1] / 12)

    lam = log_derivative_coefficients(
        lambda n: shift_coefficient(n, a=a, dps=dps), n_max, dps=dps)
    closed = [mp.mpf(0)] + [
        von_mangoldt(n) * (mp.mpf(n) ** a + mp.mpf(n) ** (-a)) for n in range(1, n_max + 1)
    ]
    out["max_lambda_recursion_vs_closed_form"] = float(
        max(abs(lam[n] - closed[n]) for n in range(2, n_max + 1)))
    out["min_lambda_W"] = float(min(lam[2:]))
    out["min_lambda_zeta"] = float(min(
        log_derivative_coefficients(lambda n: mp.mpf(1), n_max, dps=dps)[2:]))

    with mp.workdps(dps + 10):
        s = mp.mpc("2.5", "1.5")
        prod = mp.mpf(1)
        p = 2
        primes = []
        while len(primes) < 400:
            if all(p % q for q in primes if q * q <= p):
                primes.append(p)
            p += 1
        for q in primes:
            prod *= 1 / ((1 - mp.mpf(q) ** (-s - a)) * (1 - mp.mpf(q) ** (-s + a)))
        direct = mp.zeta(s + a) * mp.zeta(s - a)
        out["euler_product_defect_400_primes"] = float(abs(prod - direct) / abs(direct))
    return out


# ---------------------------------------------------------------------------
# stage C: the kill: the rival violates the conclusion
# ---------------------------------------------------------------------------


def stage_c(a=SHIFT, dps: int = 30) -> dict:
    """`Xi_a` has zeros off its own critical line, and `Re Xi_a'/Xi_a` goes negative."""
    out: dict = {}

    zero = mp.mpc(mp.mpf("0.5") + a, GAMMA_1)
    out["claimed_off_line_zero"] = [mp.nstr(mp.re(zero), 12), mp.nstr(mp.im(zero), 20)]
    out["abs_completed_at_claimed_zero"] = mp.nstr(
        abs(completed_shift(zero, a=a, dps=dps)), 6)
    out["abs_completed_at_line_same_height"] = mp.nstr(
        abs(completed_shift(mp.mpc("0.5", GAMMA_1), a=a, dps=dps)), 6)
    out["distance_from_critical_line"] = float(a)

    box = count_zeros_box(mp.mpc("0.1", "10"), mp.mpc("0.9", "25"), dps=20,
                          fn=lambda z: completed_shift(z, a=a, dps=20))
    out["box_zero_count_0.1_0.9_x_10_25"] = int(round(float(box)))

    signs = []
    prev = None
    n_samples = 900
    for k in range(n_samples + 1):
        t = 10 + (25 - 10) * mp.mpf(k) / n_samples
        v = mp.re(completed_shift(mp.mpc("0.5", t), a=a, dps=15))
        s = 1 if v > 0 else -1
        if prev is not None and s != prev:
            signs.append(float(t))
        prev = s
    out["line_sign_changes_10_25"] = len(signs)

    on_line = []
    for t in ("2", "9.5", "14.134725141734694", "31"):
        on_line.append(float(abs(mp.re(shift_log_derivative(mp.mpc("0.5", t), a=a, dps=dps)))))
    out["max_abs_re_log_derivative_on_line"] = max(on_line)

    negatives = []
    for dsig in ("0.001", "0.01", "0.05", "0.12"):
        s = mp.mpc(mp.mpf("0.5") + a - mp.mpf(dsig), GAMMA_1)
        negatives.append((dsig, float(mp.re(shift_log_derivative(s, a=a, dps=dps)))))
    out["re_log_derivative_left_of_off_line_zero"] = negatives
    out["min_re_log_derivative_right_of_line"] = min(v for _, v in negatives)
    return out


# ---------------------------------------------------------------------------
# stage D: the positivity the mechanism runs on is shared by the rival
# ---------------------------------------------------------------------------


def _min_toeplitz_eigenvalue(phi, offsets, dps: int = 25) -> float:
    with mp.workdps(dps):
        n = len(offsets)
        rows = []
        for j in range(n):
            rows.append([phi(offsets[j] - offsets[k]) for k in range(n)])
        m = mp.matrix(rows)
        eigs = mp.eigsy(mp.matrix([[mp.re(m[i, j]) for j in range(n)] for i in range(n)])) \
            if all(abs(mp.im(m[i, j])) < mp.mpf(10) ** (-dps + 5)
                   for i in range(n) for j in range(n)) else None
        if eigs is None:
            eigs = mp.eighe(m)
        return float(min(eigs[0] if isinstance(eigs, tuple) else eigs))


def stage_d(a=SHIFT, dps: int = 25) -> dict:
    """Bochner positivity of the prime side, for zeta and for the rival."""
    out: dict = {}
    offsets = [mp.mpf(x) for x in ("0", "0.7", "1.9", "3.3", "5.1", "8.4", "13.0")]
    sigma = mp.mpf("2.5")

    out["toeplitz_min_eigenvalue_zeta"] = _min_toeplitz_eigenvalue(
        lambda d: prime_part(mp.mpc(sigma, d), dps=dps), offsets, dps=dps)
    out["toeplitz_min_eigenvalue_shift"] = _min_toeplitz_eigenvalue(
        lambda d: shift_prime_part(mp.mpc(sigma, d), a=a, dps=dps), offsets, dps=dps)

    arch = []
    for t in ("10", "50", "200", "1000"):
        s = mp.mpc("0.6", t)
        arch.append((t,
                     float(mp.re(archimedean_part(s, dps=dps))),
                     float(mp.re(shift_archimedean_part(s, a=a, dps=dps)))))
    out["re_archimedean_zeta_vs_shift"] = arch
    return out


# ---------------------------------------------------------------------------
# stage E: gate #3, on the mechanism's load-bearing hypothesis
# ---------------------------------------------------------------------------


def claim_euler_product_positivity(iface, n_max: int = 40, dps: int = 25) -> bool:
    """EPP: the log-derivative coefficients `Lambda_F(n)` are all `>= 0`.

    Read from the interface's Dirichlet coefficients only, through the
    recursion in :func:`log_derivative_coefficients`.  A rival whose `a_1` is
    zero has no log-derivative Dirichlet series in this normalisation at all;
    the claim is reported as not holding, and stage E records separately that
    the reason was undefined rather than negative, because those are different
    facts and collapsing them would flatter the claim.
    """
    return epp_detail(iface, n_max=n_max, dps=dps)["holds"]


def epp_detail(iface, n_max: int = 40, dps: int = 25) -> dict:
    tol = mp.mpf(10) ** (-dps + 8)
    try:
        lam = log_derivative_coefficients(iface["coefficient"], n_max, dps=dps)
    except ValueError as exc:
        return {"holds": False, "status": f"undefined: {exc}", "min_lambda": None,
                "first_negative_n": None}
    negatives = [n for n in range(2, n_max + 1) if lam[n] < -tol]
    return {
        "holds": not negatives,
        "status": "non-negative" if not negatives else "negative coefficient present",
        "min_lambda": float(min(lam[2:])),
        "first_negative_n": negatives[0] if negatives else None,
    }


def stage_e(dps: int = 25, truncations: tuple[int, ...] = (40, 200)) -> dict:
    """Gate #3 on EPP, at two truncations, because the verdict depends on one.

    The claim is a statement about *all* `n`; a run can only read finitely
    many.  At `n <= 40` the principal Epstein form of discriminant -23 has no
    negative log-derivative coefficient and the battery reports the claim as
    shared with a rival that violates RH.  Its first negative coefficient is
    at `n = 48`.  A coefficient claim taken through the battery therefore
    carries its truncation as part of the claim, and this stage records both
    readings rather than the flattering one.
    """
    from zeta.epstein import dh_interface, epstein_interface, zeta_interface

    out: dict = {}
    for n_max in truncations:
        verdict = battery(
            lambda iface, _n=n_max: claim_euler_product_positivity(iface, n_max=_n, dps=dps),
            dps=dps,
        )
        out[f"battery_n_max_{n_max}"] = {
            k: (list(v) if isinstance(v, tuple) else v) for k, v in verdict.items()
        }
    detail = {}
    for iface in (zeta_interface(dps), dh_interface(dps),
                  epstein_interface((2, 1, 3), dps), epstein_interface((1, 1, 6), dps)):
        detail[iface["name"]] = epp_detail(iface, n_max=max(truncations), dps=dps)
    detail["shifted_product_W_a"] = epp_detail(
        {"coefficient": lambda n: shift_coefficient(n, dps=dps)}, n_max=max(truncations),
        dps=dps)
    out["detail_at_n_max"] = max(truncations)
    out["detail"] = detail
    return out


# ---------------------------------------------------------------------------
# stage F: what the composition step would have to supply
# ---------------------------------------------------------------------------


def stage_f(dps: int = 30) -> dict:
    """What the composition step would have to supply, in numbers.

    Three facts, in order of how much they cost the mechanism.

    1.  On the critical line the inequality the mechanism must prove,
        `Re A <= Re G`, is an **equality**: that is what `Re F = 0` on the
        line means.  The margin is zero on the whole boundary of the region.
    2.  Just inside, the margin is `Re F(1/2+eps+it) = sum_rho (eps)/|s-rho|^2`,
        so it is linear in `eps` with slope the zero-counting data itself.
        Measured here by the ratio `Re F / eps` against the direct sum over
        the first ordinates.
    3.  EPP alone bounds the prime side only by the triangle inequality
        `|A| <= sum Lambda(n) n^{-sigma}`, which diverges at `sigma = 1/2`.
        Cut at the approximate-functional-equation length `N ~ sqrt(t/2pi)`
        the bound is `~ 2 sqrt(N)`, against a target of `(1/2) log(t/2pi)`.
        The ratio is how much cancellation the mechanism still owes after
        EPP has been used.
    """
    out: dict = {}

    with mp.workdps(dps):
        margins = []
        for t in ("7", "20", "50"):
            row = {"t": t}
            for eps in ("1e-3", "1e-5", "1e-7"):
                s = mp.mpc(mp.mpf("0.5") + mp.mpf(eps), t)
                row[f"ReF/eps at eps={eps}"] = float(
                    mp.re(xi_log_derivative_explicit(s, dps=dps)) / mp.mpf(eps))
            margins.append(row)
        out["margin_slope"] = margins

        ledger = []
        primes_lambda = {}
        n_top = 4096
        for n in range(2, n_top + 1):
            lam = von_mangoldt(n)
            if lam != 0:
                primes_lambda[n] = lam
        for t_exp in (3, 4, 6, 8):
            t = mp.mpf(10) ** t_exp
            n_cut = int(mp.floor(mp.sqrt(t / (2 * mp.pi))))
            if n_cut > n_top:
                continue
            triangle = mp.fsum(v / mp.sqrt(n) for n, v in primes_lambda.items() if n <= n_cut)
            actual = abs(mp.fsum(v * mp.mpf(n) ** (mp.mpc(-0.5, -t))
                                 for n, v in primes_lambda.items() if n <= n_cut))
            target = mp.log(t / (2 * mp.pi)) / 2
            ledger.append({
                "t": f"1e{t_exp}",
                "cut_N": n_cut,
                "triangle_bound_from_EPP": float(triangle),
                "actual_partial_sum_modulus": float(actual),
                "archimedean_target": float(target),
                "triangle_over_target": float(triangle / target),
            })
        out["cancellation_ledger"] = ledger
    return out


def stage_g(dps: int = 25, n_zeros: int = 300) -> dict:
    """The margin slope, recomputed from the ordinates by a disjoint route.

    Stage F measured `Re F(1/2+eps+it)/eps` from the explicit split
    `G + zeta'/zeta`.  Here the same number is assembled from the zeros
    themselves, `sum_{gamma>0} [ (t-gamma)^{-2} + (t+gamma)^{-2} ]`, using
    mpmath's `zetazero` as the independent implementation.  Agreement is the
    statement that the mechanism's margin *is* the zero-counting data, which
    is the reason no bound with slack can prove the inequality.
    """
    with mp.workdps(dps):
        t = mp.mpf(7)
        partial = {}
        total = mp.mpf(0)
        for k in range(1, n_zeros + 1):
            g = mp.im(mp.zetazero(k))
            total += 1 / (t - g) ** 2 + 1 / (t + g) ** 2
            if k in (10, 50, 100, 300):
                partial[f"first_{k}_ordinates"] = float(total)
        last = mp.im(mp.zetazero(n_zeros))
        # tail with the Riemann-von Mangoldt density log(u/2pi)/(2pi)
        tail = mp.quad(
            lambda u: (1 / (t - u) ** 2 + 1 / (t + u) ** 2) * mp.log(u / (2 * mp.pi)) / (2 * mp.pi),
            [last, mp.inf])
        f_route = mp.re(xi_log_derivative_explicit(mp.mpc("0.5000001", t), dps=dps)) / mp.mpf("1e-7")
        return {
            "t": "7",
            "zero_side_partial_sums": partial,
            "last_ordinate_used": float(last),
            "density_tail_estimate": float(tail),
            "zero_side_total_with_tail": float(total + tail),
            "F_route_value": float(f_route),
        }


def main() -> None:
    results = {
        "A_target": stage_a(),
        "B_rival_hypotheses": stage_b(),
        "C_kill": stage_c(),
        "D_shared_positivity": stage_d(),
        "E_gate3": stage_e(),
        "F_cancellation_ledger": stage_f(),
        "G_margin_from_zeros": stage_g(),
    }
    path = Path(__file__).resolve().parent / "results.json"
    path.write_text(json.dumps(results, indent=2, default=str), encoding="utf-8")
    print(json.dumps(results, indent=2, default=str))


if __name__ == "__main__":
    main()

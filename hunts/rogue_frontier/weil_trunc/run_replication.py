"""Replication gates against the printed numbers in the sources.

Every closed form in galerkin.py is validated here against direct quadrature
or an independent oracle BEFORE the grid experiments trust it.  Emits
``replication.json``.  Run from the repo root:

    .venv/bin/python hunts/rogue_frontier/weil_trunc/run_replication.py
"""

from __future__ import annotations

import json
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.getcwd())

from mpmath import mp  # noqa: E402

import galerkin as G  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = {}


def log(*a):
    print(*a, flush=True)


def worked_example_vector(t):
    """The G2 s2.3 vector: v in H_0(4) cap P_4(13), (v2,v3,v4)=(1,0,-3)/sqrt2."""
    L = t.L
    beta = L / (4 * mp.pi)
    s2 = mp.sqrt(2)
    v2, v3, v4 = 1 / s2, mp.mpf(0), -3 / s2
    A = mp.matrix([[1, s2], [1 / beta**2, s2 / (1 + beta**2)]])
    b = mp.matrix(
        [
            -s2 * (v2 + v3 + v4),
            -s2 * (v2 / (4 + beta**2) + v3 / (9 + beta**2) + v4 / (16 + beta**2)),
        ]
    )
    sol = mp.lu_solve(A, b)
    return [sol[0], sol[1], v2, v3, v4]


# ---------------------------------------------------------------------------
# Gate A: archimedean closed forms vs direct quadrature, zeta and DH
# ---------------------------------------------------------------------------


def gate_A():
    log("== Gate A: closed-form archimedean entries vs direct quadrature ==")
    res = {}
    with mp.workdps(40):
        for kind, a in (("zeta", mp.mpf(1) / 4), ("dh", mp.mpf(3) / 4)):
            c, N = 13, 3
            t = G.Truncation(c, N, kind=kind)
            L = t.L

            def rho(y):
                # sum_j exp(-2(j+a) y) = e^{-2ay} / (1 - e^{-2y})
                return mp.e ** (-2 * a * y) / (1 - mp.e ** (-2 * y))

            def q(n, m, y):
                if n == m:
                    return 2 * (1 - y / L) * mp.cos(2 * mp.pi * n * y / L)
                return (
                    mp.sin(2 * mp.pi * m * y / L) - mp.sin(2 * mp.pi * n * y / L)
                ) / (mp.pi * (n - m))

            worst_off = mp.mpf(0)
            for (n, m) in [(0, 1), (1, 2), (1, 3), (-2, 3)]:
                direct = -mp.quad(lambda y: rho(y) * q(n, m, y), [0, L / 7, L])
                closed = t.entry(n, m) - t.w02(n, m) + (
                    t._sgn(t._P, m) - t._sgn(t._P, n)
                ) / (mp.pi * (n - m))
                worst_off = max(worst_off, abs(direct - closed))
            # diagonal: -WR(n,n) per SOURCE.md s2 item 3 (from CCM (3.15))
            if kind == "zeta":
                ctil = mp.quad(
                    lambda y: (mp.e ** (y / 2) - 1) / (2 * mp.sinh(y)), [0, L]
                )
                worst_diag = mp.mpf(0)
                for n in range(N + 1):
                    wr = (
                        (mp.euler + mp.log(4 * mp.pi))
                        - mp.log((mp.e**L + 1) / (mp.e**L - 1))
                        + 2 * ctil
                        + mp.quad(lambda y: rho(y) * (q(n, n, y) - 2), [0, L / 7, L])
                    )
                    worst_diag = max(worst_diag, abs(-wr - t._archdiag[n]))
                res["zeta_diag_vs_ccm315_quadrature"] = float(worst_diag)
            res[f"{kind}_offdiag_vs_quadrature"] = float(worst_off)
    # DH diagonal has no CCM reference; it is validated by the T-ladder in
    # Gate E and the r-space tail identity below.
    log("   ", res)
    assert res["zeta_offdiag_vs_quadrature"] < 1e-35
    assert res["zeta_diag_vs_ccm315_quadrature"] < 1e-33
    assert res["dh_offdiag_vs_quadrature"] < 1e-35
    OUT["gate_A"] = res


# ---------------------------------------------------------------------------
# Gate B: the G2 s2.3 worked example and lambda_min at (13, 4)
# ---------------------------------------------------------------------------


def gate_B():
    log("== Gate B: worked example (13,4) and lambda_min ==")
    with mp.workdps(50):
        t = G.Truncation(13, 4)
        E = t.even_matrix()
        v = worked_example_vector(t)
        quad = mp.fsum(v[i] * E[i, j] * v[j] for i in range(5) for j in range(5))
        target = mp.mpf("0.049968414571096979730")
        dev = abs(quad - target)
        ev, vecs = G.eigsy_sorted(E)
        lam = ev[0]
        # pole identity: 2 g_v(i/2) = <v, W02 v>, on a NON pole-neutral vector
        w = [mp.mpf(1), mp.mpf("0.3"), -mp.mpf("0.7"), mp.mpf("0.11"), mp.mpf("0.5")]
        gv = G.g_even(w, t.L)
        pole_lhs = 2 * gv(mp.mpc(0, mp.mpf(1) / 2))
        W = mp.matrix(5)
        W[0, 0] = t.w02(0, 0)
        for k in range(1, 5):
            W[0, k] = W[k, 0] = mp.sqrt(2) * t.w02(0, k)
        for j in range(1, 5):
            for k in range(j, 5):
                W[j, k] = W[k, j] = t.w02(j, k) + t.w02(j, -k)
        pole_rhs = mp.fsum(w[i] * W[i, j] * w[j] for i in range(5) for j in range(5))
        pole_dev = abs(pole_lhs - pole_rhs)
        # pole-neutrality of the worked-example vector
        pn = mp.fsum(v[i] * W[i, j] * v[j] for i in range(5) for j in range(5))
    res = {
        "quad_value": mp.nstr(quad, 25),
        "printed": "0.049968414571096979730",
        "abs_dev_from_printed": float(dev),
        "lambda_min_even": float(lam),
        "printed_lambda_min": 9.7e-15,
        "pole_identity_dev": float(pole_dev),
        "worked_vector_pole_term": float(pn),
        "worked_vector": [mp.nstr(x, 12) for x in v],
    }
    log("   ", json.dumps(res, indent=2))
    assert dev < mp.mpf("2e-21")
    assert abs(lam / mp.mpf(9.7e-15) - 1) < 0.01
    assert pole_dev < mp.mpf("1e-40")
    OUT["gate_B"] = res


# ---------------------------------------------------------------------------
# Gate C: finite-T eigenvalue flow at (13, 4) vs G2 Figure 2
# ---------------------------------------------------------------------------


def gate_C():
    log("== Gate C: finite-T lambda_min flow at (13,4) vs G2 Fig 2 ==")
    targets = {11: -1.9e-2, 14: -5.3e-7, 18: -3.9e-10}
    res = {}
    with mp.workdps(30):
        t = G.Truncation(13, 4)
        for T, tgt in targets.items():
            E = G.total_matrix_T(t, T)
            ev, _ = G.eigsy_sorted(E)
            res[str(T)] = {"lambda_min": float(ev[0]), "printed": tgt}
            log(f"    T={T}: lambda_min={mp.nstr(ev[0], 4)} (printed {tgt})")
    for T, tgt in targets.items():
        got = res[str(T)]["lambda_min"]
        assert abs(got / tgt - 1) < 0.08, (T, got, tgt)
    OUT["gate_C"] = res


# ---------------------------------------------------------------------------
# Gate D: the finite dictionary (zero-side sum) vs G2 Table 1
# ---------------------------------------------------------------------------


def gate_D():
    log("== Gate D: zero-side dictionary sums vs G2 Table 1 ==")
    zeros = json.load(open("data/zeros_1000.json"))["zeros"]  # dps 30, read-only
    printed = {
        32: ("0.049967509", -9.1e-7),
        64: ("0.049968326", -8.8e-8),
        128: ("0.049968406", -7.9e-9),
        256: ("0.049968413", -6.5e-10),
        512: ("0.049968414", -4.7e-11),
    }
    res = {}
    with mp.workdps(40):
        t = G.Truncation(13, 4)
        v = worked_example_vector(t)
        gv = G.g_even(v, t.L)
        target = mp.mpf("0.049968414571096979730")
        vals = []
        s = mp.mpf(0)
        gammas = [mp.mpf(z) for z in zeros[:512]]
        for i, gm in enumerate(gammas, start=1):
            s += 2 * gv(gm)
            if i in printed:
                resid = s - target
                vals.append((i, s, resid))
                res[str(i)] = {
                    "partial_sum": mp.nstr(s, 12),
                    "printed_partial": printed[i][0],
                    "raw_residual": float(resid),
                    "printed_residual": printed[i][1],
                }
                log(
                    f"    M={i}: sum={mp.nstr(s, 10)} (printed {printed[i][0]}) "
                    f"resid={mp.nstr(resid, 3)} (printed {printed[i][1]:.1e})"
                )
    for i in printed:
        got = res[str(i)]["raw_residual"]
        assert abs(got / printed[i][1] - 1) < 0.1, (i, got)
    OUT["gate_D"] = res


# ---------------------------------------------------------------------------
# Gate E: T-route vs closed form, zeta (29,6) and DH (13,3), tail-matched
# ---------------------------------------------------------------------------


def _tail_offdiag(t, n, T, a, logqpi, nper=250):
    """(1/pi^2) int_T^inf h(r) S(r,n,L) dr, period-chunked + remainder bound.

    Returns (value, remainder_bound): nper full periods are integrated
    directly; beyond R = T + nper*p the smooth part is integrated to
    infinity and the oscillatory part is bounded by one integration by
    parts, |int_R^inf h(r) n rho cos(Lr)/(r^2-b^2) dr| <= 2 h(R) n rho
    / (L (R^2 - b^2)) (h increasing slower than the 1/r^2 decay).
    """
    L = t.L
    rho = 2 * mp.pi / L
    b = rho * n
    p = 2 * mp.pi / L

    def h(r):
        return mp.re(mp.psi(0, mp.mpc(a, r / 2))) - logqpi

    def f(r):
        return h(r) * n * rho * (1 - mp.cos(L * r)) / (r * r - b * b)

    R = T + nper * p
    pts = [T + k * p for k in range(nper + 1)]
    val = mp.quad(f, pts)
    rem_smooth = mp.quad(lambda r: h(r) * n * rho / (r * r - b * b), [R, mp.inf])
    rem_osc_bound = 2 * h(R) * n * rho / (L * (R * R - b * b))
    return (val + rem_smooth) / mp.pi**2, rem_osc_bound / mp.pi**2


def gate_E():
    log("== Gate E: source route + analytic tail = closed form ==")
    res = {}
    with mp.workdps(20):
        for kind, a, logqpi, c, N, ns in (
            ("zeta", mp.mpf(1) / 4, mp.log(mp.pi), 29, 6, (1, 4, 6)),
            ("dh", mp.mpf(3) / 4, mp.log(mp.pi / 5), 13, 3, (1, 3)),
        ):
            t = G.Truncation(c, N, kind=kind)
            T = 60
            pv, pd = G.arch_matrix_T(c, N, T, kind=kind)
            worst = mp.mpf(0)
            worst_bound = mp.mpf(0)
            for n in ns:
                closed = t._S[n]  # int sin(om_n y) rho_a
                # source route value: psi_{R,inf}(n) = S_n / pi (checked
                # numerically; both odd in n, psi(0) = S_0 = 0), so compare
                # pi * (pv[n] + tail) with S_n
                tail, bound = _tail_offdiag(t, n, T, a, logqpi)
                lhs = mp.pi * (pv[n] + tail)
                worst = max(worst, abs(lhs - closed))
                worst_bound = max(worst_bound, mp.pi * bound)
            res[f"{kind}_c{c}_N{N}_offdiag_worst"] = float(worst)
            res[f"{kind}_c{c}_N{N}_remainder_bound"] = float(worst_bound)
            log(f"    {kind} (c={c}, N={N}): worst |route+tail - closed| = "
                f"{mp.nstr(worst, 3)} (osc remainder bound {mp.nstr(worst_bound, 3)})")
            assert worst < worst_bound + mp.mpf("1e-6"), (kind, worst)
    OUT["gate_E"] = res


# ---------------------------------------------------------------------------
# Gate F: DH kappa closed form vs the lab's derived value
# ---------------------------------------------------------------------------


def gate_F():
    log("== Gate F: DH kappa closed form vs zeta.epstein ==")
    from zeta import epstein

    with mp.workdps(50):
        k_closed = G.dh_kappa()
        k_ref = mp.mpf(epstein.KAPPA_REF)
        dev = abs(k_closed - k_ref)
        k_derived = epstein.kappa(dps=45)
        dev2 = abs(k_closed - k_derived)
    res = {
        "kappa_closed_form": mp.nstr(k_closed, 40),
        "kappa_ref": epstein.KAPPA_REF,
        "abs_dev_ref": float(dev),
        "abs_dev_derived": float(dev2),
    }
    log("   ", json.dumps(res, indent=2))
    assert dev < mp.mpf("1e-39")
    OUT["gate_F"] = res


# ---------------------------------------------------------------------------
# Gate G: diagonal constants via the r-space representation (zeta control
# with known answer, then DH with the same machinery)
# ---------------------------------------------------------------------------


def gate_G():
    log("== Gate G: diagonal entries from (1/pi) int_0^inf h(r) Ghat_nn dr ==")
    res = {}
    with mp.workdps(20):
        for kind, a, logqpi in (
            ("zeta", mp.mpf(1) / 4, mp.log(mp.pi)),
            ("dh", mp.mpf(3) / 4, mp.log(mp.pi / 5)),
        ):
            c, n = 13, 1
            t = G.Truncation(c, 2, kind=kind)
            L = t.L
            om = 2 * mp.pi * n / L

            def h(r):
                return mp.re(mp.psi(0, mp.mpc(a, r / 2))) - logqpi

            def ghat(r):
                sm = mp.sin(L * (r - om) / 2)
                sp = mp.sin(L * (r + om) / 2)
                return (2 / L) * (sm * sm / (r - om) ** 2 + sp * sp / (r + om) ** 2)

            p = 2 * mp.pi / L
            R = 2000
            nper = int(mp.ceil(R / p))
            pts = [min(k * p, R) for k in range(nper + 1)]
            val = mp.quad(lambda r: h(r) * ghat(r), pts) / mp.pi
            # tail bound: |ghat| <= (2/L)(1/(r-om)^2 + 1/(r+om)^2), h(r) <=
            # log r for r >= 7 (both integrated numerically to infinity)
            bound = (
                mp.quad(
                    lambda r: mp.log(r)
                    * (2 / L)
                    * (1 / (r - om) ** 2 + 1 / (r + om) ** 2),
                    [R, mp.inf],
                )
                / mp.pi
            )
            closed = t._archdiag[n]
            dev = abs(val - closed)
            res[f"{kind}_diag_n1_rspace_dev"] = float(dev)
            res[f"{kind}_diag_n1_tail_bound"] = float(bound)
            log(
                f"    {kind}: r-space={mp.nstr(val, 8)} closed={mp.nstr(closed, 8)} "
                f"dev={mp.nstr(dev, 3)} (tail bound {mp.nstr(bound, 3)})"
            )
            assert dev < bound + mp.mpf("1e-4"), (kind, dev, bound)
    OUT["gate_G"] = res


# ---------------------------------------------------------------------------
# Gate H: sharp validation of the DH archimedean diagonal via the
# difference kernel d(r) = Re psi(3/4+ir/2) - Re psi(1/4+ir/2), which
# decays like 1/r^2, so the identity
#   archdiag_dh(n) = archdiag_zeta(n) + log 5 + (1/2pi) int_R d(r) Ghat_nn
# can be checked to ~1e-12 with a finite window.  This matters because a
# uniform error eps in the DH diagonal constant would shift every DH
# eigenvalue by exactly eps (Weyl), and the DH lambda_min floor we measure
# is ~1e-10; the gate must therefore beat 1e-10 decisively.
# ---------------------------------------------------------------------------


def gate_H():
    log("== Gate H: DH diagonal at 1e-12 via the difference kernel ==")
    res = {}
    with mp.workdps(30):
        c = 13
        tz = G.Truncation(c, 2, kind="zeta")
        td = G.Truncation(c, 2, kind="dh")
        L = tz.L
        p = 2 * mp.pi / L
        R = 10000

        def d(r):
            return mp.re(
                mp.psi(0, mp.mpc(mp.mpf(3) / 4, r / 2))
                - mp.psi(0, mp.mpc(mp.mpf(1) / 4, r / 2))
            )

        for n in (0, 1):
            om = 2 * mp.pi * n / L

            def ghat(r, om=om):
                if n == 0:
                    s = mp.sin(L * r / 2)
                    return (4 / L) * s * s / (r * r)
                sm = mp.sin(L * (r - om) / 2)
                sp = mp.sin(L * (r + om) / 2)
                return (2 / L) * (sm * sm / (r - om) ** 2 + sp * sp / (r + om) ** 2)

            nper = int(mp.ceil(R / p))
            pts = [min(k * p, R) for k in range(1, nper + 1)]
            pts = [mp.mpf(0)] + pts
            integ = mp.quad(lambda r: d(r) * ghat(r), pts) / mp.pi  # (1/2pi)*2 (even)
            # tail: |d| <= dbound/r^2 with dbound from the last node;
            # |ghat| <= (2/L)(1/(r-om)^2 + 1/(r+om)^2)
            dbound = abs(d(R)) * R * R * mp.mpf("1.1")
            tail_bound = (
                dbound
                * (2 / L)
                * mp.quad(
                    lambda r: (1 / (r * r)) * (1 / (r - om) ** 2 + 1 / (r + om) ** 2),
                    [R, mp.inf],
                )
                / mp.pi
            )
            lhs = td._archdiag[n]
            rhs = tz._archdiag[n] + mp.log(5) + integ
            dev = abs(lhs - rhs)
            res[f"n{n}_dev"] = float(dev)
            res[f"n{n}_tail_bound"] = float(tail_bound)
            log(
                f"    n={n}: |archdiag_dh - (archdiag_zeta + log5 + integral)| = "
                f"{mp.nstr(dev, 3)} (tail bound {mp.nstr(tail_bound, 3)})"
            )
            assert dev < tail_bound + mp.mpf("1e-12"), (n, dev, tail_bound)
    OUT["gate_H"] = res


# ---------------------------------------------------------------------------


def main():
    t0 = time.time()
    gate_A()
    gate_B()
    gate_C()
    gate_D()
    gate_E()
    gate_F()
    gate_G()
    gate_H()
    OUT["elapsed_s"] = round(time.time() - t0, 1)
    with open(os.path.join(HERE, "replication.json"), "w") as f:
        json.dump(OUT, f, indent=1)
    log(f"ALL GATES PASSED in {OUT['elapsed_s']}s -> replication.json")


if __name__ == "__main__":
    main()

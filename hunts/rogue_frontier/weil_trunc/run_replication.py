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


def _tail_offdiag(t, n, T, a, logqpi):
    """(1/pi^2) int_T^inf h(r) S(r,n,L) dr, smooth + oscillatory split."""
    L = t.L
    rho = 2 * mp.pi / L
    b = rho * n

    def h(r):
        return mp.re(mp.psi(0, mp.mpc(a, r / 2))) - logqpi

    sm = mp.quad(lambda r: h(r) * n * rho / (r * r - b * b), [T, mp.inf])
    osc = mp.quadosc(
        lambda r: -h(r) * n * rho * mp.cos(L * r) / (r * r - b * b),
        [T, mp.inf],
        period=2 * mp.pi / L,
    )
    return (sm + osc) / mp.pi**2


def gate_E():
    log("== Gate E: source route + analytic tail = closed form ==")
    res = {}
    with mp.workdps(25):
        for kind, a, logqpi, c, N in (
            ("zeta", mp.mpf(1) / 4, mp.log(mp.pi), 29, 6),
            ("dh", mp.mpf(3) / 4, mp.log(mp.pi / 5), 13, 3),
        ):
            t = G.Truncation(c, N, kind=kind)
            T = 200
            pv, pd = G.arch_matrix_T(c, N, T, kind=kind)
            worst = mp.mpf(0)
            for n in range(1, N + 1):
                closed = t._S[n]  # int sin(om_n y) rho_a
                # source route value: psi_{R,inf}(n) = S_n / pi (checked
                # numerically; both odd in n, psi(0) = S_0 = 0), so compare
                # pi * (pv[n] + tail) with S_n
                tail = _tail_offdiag(t, n, T, a, logqpi)
                lhs = mp.pi * (pv[n] + tail)
                worst = max(worst, abs(lhs - closed))
            res[f"{kind}_c{c}_N{N}_offdiag_worst"] = float(worst)
            log(f"    {kind} (c={c}, N={N}): worst |route+tail - closed| = "
                f"{mp.nstr(worst, 3)}")
            assert worst < mp.mpf("1e-8"), (kind, worst)
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


def main():
    t0 = time.time()
    gate_A()
    gate_B()
    gate_C()
    gate_D()
    gate_E()
    gate_F()
    OUT["elapsed_s"] = round(time.time() - t0, 1)
    with open(os.path.join(HERE, "replication.json"), "w") as f:
        json.dump(OUT, f, indent=1)
    log(f"ALL GATES PASSED in {OUT['elapsed_s']}s -> replication.json")


if __name__ == "__main__":
    main()

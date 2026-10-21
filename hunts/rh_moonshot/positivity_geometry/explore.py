"""Print the tables behind NOTES.md (writes nothing to disk).

Run from the worktree root:
    .venv/bin/python hunts/rh_moonshot/positivity_geometry/explore.py [section ...]

Sections: curves, fakes, windows, quadratic, rivals (default: all).
"""

from __future__ import annotations

import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
for p in (str(HERE), str(ROOT)):
    if p not in sys.path:
        sys.path.insert(0, p)

import frobenius_span as fs  # noqa: E402

#: (f, p) with y^2 = f(x), f highest degree first. Genus 1 and genus 2 test curves.
CURVES = [
    ((1, 0, 3, 5), 101),  # docs/11's example, N_1 only at this size
    ((1, 0, 1, 1), 5),
    ((1, 0, 2, 3), 7),
    ((1, 0, -1, 0), 11),  # y^2 = x^3 - x, supersingular at p = 11
    ((1, 0, 1, 6), 13),
    ((1, 0, 0, 0, -1, 1), 5),  # genus 2
    ((1, 0, 0, 0, 1, 3), 7),
    ((1, 0, 2, 0, 1, 3), 11),
    ((1, 0, 0, 1, 0, 2), 13),
]


def section_curves(n_max: int = 4) -> None:
    print("== curves: brute-force counts, Weil polynomial, Hodge index on the Frobenius span ==")
    for f, p in CURVES:
        if p > 13:
            continue
        g = fs._check_curve_poly(f, p)
        t0 = time.time()
        N = fs.point_counts(f, p, n_max)
        P = fs.weil_polynomial(p, N, g)
        pred = fs.counts_from_weil_polynomial(p, P, n_max)
        ratios = [float(r) for r in fs.eigenvalue_moduli_ratio(p, P)]
        cs = fs.castelnuovo_severi_margins(p, N, g, n_max)
        rep = fs.hodge_index_report(p, N, g, window=n_max + 1)
        sym = fs.hodge_index_report(p, N, g, window=n_max // 2, symmetric=True)
        print(
            f"f={f} p={p} g={g} N={[N[n] for n in range(1, n_max + 1)]} P={P} "
            f"rational_ok={pred == N} |alpha|/sqrt(q)={['%.15f' % r for r in ratios]} "
            f"CS_margins={cs} full={rep['full_inertia']} proj={rep['projected_inertia']} "
            f"sym={sym['full_inertia']} ({time.time() - t0:.2f}s)"
        )


GENUS1_FAKES = [(5, 5), (5, -5), (7, 6), (7, 7), (11, 7), (11, 10), (13, 8), (13, 13)]


def section_fakes(d_max: int = 60) -> None:
    print("== genus-1 fakes: Z(T) = (1 - aT + qT^2)/((1-T)(1-qT)) with a^2 > 4q ==")
    for q, a in GENUS1_FAKES:
        N = fs.fake_genus1_counts(q, a, d_max)
        b = fs.closed_point_counts(N, d_max)
        D0 = fs.fake_genus1_threshold(q, a)
        P = [1, -a, q]
        ratios = [float(r) for r in fs.eigenvalue_moduli_ratio(q, P)]
        rep2 = fs.hodge_index_report(q, N, 1, window=2)
        rep5 = fs.hodge_index_report(q, N, 1, window=5)
        print(
            f"q={q} a={a} fe={fs.is_self_reciprocal(q, P)} |alpha|/sqrt(q)={['%.6f' % r for r in ratios]} "
            f"min b_d (d<={d_max})={min(b)} b_1..6={b[:6]} D0={D0} "
            f"full(w=2)={rep2['full_inertia']} full(w=5)={rep5['full_inertia']}"
        )


def section_windows() -> None:
    print("== genus-2 fakes: one honest factor, one fake factor; smallest refusing window ==")
    q = 5
    for a1 in range(-4, 5):
        for a2 in (5, -5):
            P = fs.poly_mul([1, -a1, q], [1, -a2, q])
            N = fs.counts_from_polynomial(q, P, 40)
            try:
                b = fs.closed_point_counts(N, 40)
            except ArithmeticError:
                b = None
            first = None
            for w in range(2, 9):
                if not fs.hodge_index_report(q, N, 2, window=w)["hodge_index_holds"]:
                    first = w
                    break
            cs = fs.castelnuovo_severi_margins(q, N, 2, 40)
            first_cs = next((n + 1 for n, m in enumerate(cs) if m < 0), None)
            print(
                f"a1={a1:+d} a2={a2:+d} P={P} min b_d(d<=40)={None if b is None else min(b)} "
                f"first refusing window={first} first failing 2x2 minor (Delta, G_n): n={first_cs}"
            )


def section_quadratic(d_max: int = 40) -> None:
    print("== quadratic-character Euler products over F_q(t) ==")
    for f, p in CURVES[1:5]:
        ram = fs.curve_ramification(f, p)
        N1 = fs.count_points(f, p, 1)
        P = [1, -(p + 1 - N1), p]
        res = fs.quadratic_euler_decomposition(P, p, ram, d_max)
        print(f"honest f={f} p={p} ram={ram} failure={res['failure']} conductor_ok={res['conductor_ok']}")
    for q, a in GENUS1_FAKES:
        P = [1, -a, q]
        rows = []
        for conf in fs.ramification_configurations(4):
            res = fs.quadratic_euler_decomposition(P, q, conf, d_max)
            rows.append((conf, res["failure"]))
        print(f"fake q={q} a={a}: " + "; ".join(f"{c}->{f}" for c, f in rows))


def section_rivals() -> None:
    print("== number-field rival table (G1: Lambda >= 0 on prime powers; G2: one pole) ==")
    t0 = time.time()
    table = fs.nf_rival_table(n_max=60, dps=30)
    for name, row in table.items():
        print(name, {k: v for k, v in row.items()})
    print(f"({time.time() - t0:.1f}s)")


SECTIONS = {
    "curves": section_curves,
    "fakes": section_fakes,
    "windows": section_windows,
    "quadratic": section_quadratic,
    "rivals": section_rivals,
}

if __name__ == "__main__":
    wanted = sys.argv[1:] or list(SECTIONS)
    for name in wanted:
        SECTIONS[name]()

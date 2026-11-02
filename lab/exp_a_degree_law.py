"""Experiment A: HVG degree law of unfolded zeta-zero gaps vs i.i.d., shuffled and GUE nulls.

Run: lab/.venv/bin/python lab/exp_a_degree_law.py
Writes lab/results/exp_a.json and prints the table.

Every sequence is cut into consecutive segments of SEG gaps, the HVG is built per segment,
TRIM nodes are dropped at each segment end, and degrees >= KMAX are pooled. The error bar
on each fraction is the spread across segments divided by sqrt(segments), because the
degrees of neighbouring nodes are correlated and a binomial error would be too small.

Nulls:
* i.i.d.: the theorem P(k) = (1/3)(2/3)^(k-2), and the zeta gaps shuffled (same marginal,
  correlations destroyed): a planted control, it must match the theorem or the code is wrong.
* GUE, route 1: the beta = 2 Hermite tridiagonal ensemble (Dumitriu-Edelman), n = 4002,
  central half of the spectrum, unfolded by the exact integrated semicircle.
* GUE, route 2: the repo's dense sampler zeta.statistics.gue_eigenvalues + unfold_gue,
  n = 1000, central half, compared at a shorter segment length it can supply.
"""
import json
import sys
import time
from pathlib import Path

import numpy as np
from scipy.linalg import eigvalsh_tridiagonal

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent))
import hvg  # noqa: E402
from zeta.statistics import gue_eigenvalues, riemann_siegel_theta, unfold_gue  # noqa: E402

KMAX = 13
TRIM = 25


def zeta_gaps(t_max: int) -> np.ndarray:
    g = np.load(HERE / "data" / f"zeros_T{t_max}.npz")["gammas"]
    return np.diff(riemann_siegel_theta(g) / np.pi)


def gue_tridiag_gaps(n: int, rng: np.random.Generator, bulk: float = 0.5) -> np.ndarray:
    """Unfolded bulk gaps of one beta = 2 Hermite matrix (semicircle radius 2 sqrt(n))."""
    d = rng.normal(0.0, np.sqrt(2.0), n) / np.sqrt(2.0)
    e = np.sqrt(rng.chisquare(2.0 * np.arange(n - 1, 0, -1))) / np.sqrt(2.0)
    lam = eigvalsh_tridiagonal(d, e)
    x = np.clip(lam / (2.0 * np.sqrt(n)), -1.0, 1.0)
    count = n * (0.5 + (x * np.sqrt(1.0 - x * x) + np.arcsin(x)) / np.pi)
    lo, hi = int(n * (0.5 - bulk / 2)), int(n * (0.5 + bulk / 2))
    return np.diff(count[lo:hi])


def gue_dense_gaps(n: int, seed: int, bulk: float = 0.5) -> np.ndarray:
    u = np.sort(unfold_gue(gue_eigenvalues(n, seed=seed), n))
    lo, hi = int(n * (0.5 - bulk / 2)), int(n * (0.5 + bulk / 2))
    return np.diff(u[lo:hi])


def segment_fractions(seqs, seg: int) -> tuple[np.ndarray, int]:
    """Per-segment degree fractions (rows) over all sequences; returns (F, gaps_dropped)."""
    rows, dropped = [], 0
    for s in seqs:
        nseg = s.size // seg
        dropped += s.size - nseg * seg
        for i in range(nseg):
            deg, _, _ = hvg.degrees(s[i * seg:(i + 1) * seg])
            h = hvg.degree_histogram(hvg.interior(deg, TRIM), KMAX).astype(float)
            rows.append(h / h.sum())
    if not rows:
        raise RuntimeError("no complete segment: every gap was dropped")
    return np.asarray(rows), dropped


def summary(F: np.ndarray) -> dict:
    return {
        "segments": int(F.shape[0]),
        "p": F.mean(axis=0).tolist(),
        "se": (F.std(axis=0, ddof=1) / np.sqrt(F.shape[0])).tolist(),
    }


def compare(a: dict, b: dict) -> list:
    pa, sa, pb, sb = (np.asarray(a[k]) for k in ("p", "se"))  if False else (
        np.asarray(a["p"]), np.asarray(a["se"]), np.asarray(b["p"]), np.asarray(b["se"]))
    z = (pa - pb) / np.sqrt(sa ** 2 + sb ** 2)
    return z.tolist()


def main() -> int:
    t0 = time.time()
    rng = np.random.default_rng(20261102)
    out = {"kmax_pooled": KMAX, "trim": TRIM, "seed": 20261102}

    zg = zeta_gaps(100000)
    out["zeta_gaps"] = int(zg.size)
    out["zeta_mean_gap"] = float(zg.mean())
    shuffled = rng.permutation(zg)

    print('zeta loaded', zg.size, 'gaps', flush=True)
    tri = [gue_tridiag_gaps(4002, rng) for _ in range(300)]
    print('GUE tridiag done', round(time.time() - t0, 1), 's', flush=True)
    out["gue_tridiag_gaps"] = int(sum(s.size for s in tri))
    out["gue_tridiag_mean_gap"] = float(np.mean(np.concatenate(tri)))
    dense = [gue_dense_gaps(1000, seed=1000 + i) for i in range(80)]
    print('GUE dense done', round(time.time() - t0, 1), 's', flush=True)
    out["gue_dense_gaps"] = int(sum(s.size for s in dense))
    out["gue_dense_mean_gap"] = float(np.mean(np.concatenate(dense)))

    k = np.arange(KMAX + 1)
    iid = hvg.iid_degree_law(k)
    iid[KMAX] = 1.0 - iid[:KMAX].sum()
    out["iid_law"] = iid.tolist()

    tables = {}
    for seg in (2000, 400):
        Fz, dz = segment_fractions([zg], seg)
        Fs, _ = segment_fractions([shuffled], seg)
        Ft, dt = segment_fractions(tri, seg)
        row = {
            "zeta": summary(Fz), "zeta_dropped_gaps": dz,
            "shuffled": summary(Fs),
            "gue_tridiag": summary(Ft), "gue_tridiag_dropped_gaps": dt,
        }
        if seg <= 400:
            Fd, dd = segment_fractions(dense, seg)
            row["gue_dense"] = summary(Fd)
            row["gue_dense_dropped_gaps"] = dd
            row["z_tridiag_vs_dense"] = compare(row["gue_tridiag"], row["gue_dense"])
        row["z_zeta_vs_gue"] = compare(row["zeta"], row["gue_tridiag"])
        zi = {"p": iid.tolist(), "se": [0.0] * (KMAX + 1)}
        row["z_zeta_vs_iid"] = compare(row["zeta"], zi)
        row["z_shuffled_vs_iid"] = compare(row["shuffled"], zi)
        tables[str(seg)] = row

    # height dependence inside T <= 1e5: first and second halves of the zeta sequence
    half = zg.size // 2
    F1, _ = segment_fractions([zg[:half]], 2000)
    F2, _ = segment_fractions([zg[half:]], 2000)
    out["height_halves"] = {"low": summary(F1), "high": summary(F2),
                            "z_high_vs_low": compare(summary(F2), summary(F1))}
    out["tables"] = tables
    out["seconds"] = round(time.time() - t0, 1)

    res = HERE / "results"
    res.mkdir(exist_ok=True)
    (res / "exp_a.json").write_text(json.dumps(out, indent=1))

    t = tables["2000"]
    print(f"zeta gaps {out['zeta_gaps']} (mean {out['zeta_mean_gap']:.5f}); GUE tridiag gaps "
          f"{out['gue_tridiag_gaps']} (mean {out['gue_tridiag_mean_gap']:.5f}); dense "
          f"{out['gue_dense_gaps']} (mean {out['gue_dense_mean_gap']:.5f}); {out['seconds']} s")
    print(f"segments of 2000: zeta {t['zeta']['segments']}, GUE {t['gue_tridiag']['segments']}, "
          f"dropped zeta gaps {t['zeta_dropped_gaps']}")
    print(" k   iid      shuffled  zeta     GUE      z(zeta-iid) z(shuf-iid) z(zeta-GUE) z(hi-lo)")
    for kk in range(2, KMAX + 1):
        print(f"{kk:2d}{'+' if kk == KMAX else ' '} {iid[kk]:.5f}  {t['shuffled']['p'][kk]:.5f}   "
              f"{t['zeta']['p'][kk]:.5f}  {t['gue_tridiag']['p'][kk]:.5f}  "
              f"{t['z_zeta_vs_iid'][kk]:9.1f}  {t['z_shuffled_vs_iid'][kk]:9.1f}  "
              f"{t['z_zeta_vs_gue'][kk]:9.1f}  {out['height_halves']['z_high_vs_low'][kk]:7.1f}")
    t4 = tables["400"]
    print("segments of 400, z(zeta-GUE tridiag) and z(tridiag-dense) for k=2..8:",
          [round(v, 1) for v in t4["z_zeta_vs_gue"][2:9]],
          [round(v, 1) for v in t4["z_tridiag_vs_dense"][2:9]])
    return 0


if __name__ == "__main__":
    sys.exit(main())

"""Gap-distribution LP retained from the withdrawn zeta transplant.

Generalises Cheer-Goldston's 5-bucket argument (cg_transplant.py) to an LP
over the empirical distribution of consecutive distinct on-line gap lengths,
with chain levels. The cross-mass between on-line zeros decomposes over
DISJOINT pair classes -- pairs j apart in the on-line ordering ("level j") --
so per-class floors add with no double counting:

  level 1: every consecutive gap of length u is a pair at distance u; the
           discovery LP uses a sampled bin minimum.
  level j >= 2, within a cell I of a fixed partition: among nu gaps, if n_I
           lie in I, at least j*n_I - (j-1)*nu chains of j consecutive gaps
           are all in I (the CG device, level 2 = their N2); each is a pair
           at distance in j*I, kernel floor min g over j*I.

Improvements over CG's printed argument, each floor-raising:
  - fine level-1 bins (their A/B buckets are two coarse bins);
  - boundary slack represented by ``ellR``; after eliminating it, the length
    condition is the conservative inequality total internal length <= 1;
  - chain levels 2 and 3 over a partition whose boundaries are optimised;
  - census bootstrap iterated to its fixed point: the floor improves the
    simple-zero bound, which raises the census nu_on, which raises the floor.

The adversary minimises an ordered-real-configuration floor. The former claim
that this floor could be inserted additively into the unconditional zeta
counting argument was withdrawn after Gate 0 failed. See
``CLEAN-KILL-REPORT.md``. SciPy output is discovery data, not an exact lower
object.

Controls: with CG's two-bucket structure this reproduces their floor
(cg_transplant.py holds that calibration); the lambda_2 -> 2*lambda_1
lesion; a bin-width ladder.

Run from the repo root:  .venv/bin/python hunts/frontier_math/gap_lp.py
"""

from __future__ import annotations

import numpy as np
from scipy.optimize import linprog

from cg_transplant import H_PAPER, MT_CONST, _GTable, g_kernel, lambda_roots


def finite_linear_chain_floor(n_gaps: int, n_in_cell: int, level: int) -> int:
    """Exact finite endpoint-aware lower bound for all-in-cell chains."""

    return max(0, level * n_in_cell - (level - 1) * n_gaps - (level - 1))


def gap_floor(nu, boundaries, U=3.0, h=0.01, levels=(2, 3), table=None):
    """LP floor for census density nu; partition cells from `boundaries`.

    boundaries: increasing cell edges inside (0, U); cells are the intervals
    between consecutive edges (plus (0, first) and (last, U)).
    Variables: mu_i >= 0 per level-1 bin; ell_i (length carried by bin i);
    R >= 0 (gaps > U, length ell_R >= U*R); t_{c,j} >= 0 chain counts.
    """
    if table is None:
        table = _GTable(hi=4.0 * U)
    # snap cell boundaries onto the bin grid: a bin straddling a cell edge
    # would otherwise be credited to one cell wholesale, and the chain
    # count n_I could overcount reality (caught by the h-ladder control).
    b = np.unique(np.round(np.asarray(boundaries, float) / h) * h)
    b = b[(b > h / 2) & (b < U - h / 2)]
    edges = np.concatenate([[0.0], b, [U]])
    nbins = int(round(U / h))
    lo = h * np.arange(nbins)
    hi = lo + h
    gmin_bin = np.array([table.minimum(a, b) for a, b in zip(lo, hi)])
    cells = [(edges[k], edges[k + 1]) for k in range(len(edges) - 1)]
    bin_cell = np.searchsorted(edges, (lo + hi) / 2) - 1

    nlev = len(levels)
    ncell = len(cells)
    # variables: mu (nbins), ell (nbins), R, ellR, t (ncell*nlev)
    nv = 2 * nbins + 2 + ncell * nlev
    iv_mu = 0
    iv_ell = nbins
    iv_R = 2 * nbins
    iv_ellR = 2 * nbins + 1
    iv_t = 2 * nbins + 2

    cobj = np.zeros(nv)
    cobj[iv_mu:iv_mu + nbins] = gmin_bin
    for ci, (a, b) in enumerate(cells):
        for li, j in enumerate(levels):
            cobj[iv_t + ci * nlev + li] = table.minimum(j * a, j * b)

    Aeq = np.zeros((2, nv))
    beq = np.zeros(2)
    Aeq[0, iv_mu:iv_mu + nbins] = 1.0
    Aeq[0, iv_R] = 1.0
    beq[0] = nu                       # census
    Aeq[1, iv_ell:iv_ell + nbins] = 1.0
    Aeq[1, iv_ellR] = 1.0
    beq[1] = 1.0                      # ellR absorbs boundary and long-gap slack

    rows = []
    rhs = []
    for i in range(nbins):            # ell_i within bin-edge bounds
        r = np.zeros(nv); r[iv_ell + i] = 1.0; r[iv_mu + i] = -hi[i]
        rows.append(r); rhs.append(0.0)
        r = np.zeros(nv); r[iv_ell + i] = -1.0; r[iv_mu + i] = lo[i]
        rows.append(r); rhs.append(0.0)
    r = np.zeros(nv); r[iv_ellR] = -1.0; r[iv_R] = U
    rows.append(r); rhs.append(0.0)   # ell_R >= U * R
    # Asymptotic chain floors. The exact finite count loses at most j-1
    # endpoint chains; finite_linear_chain_floor records that regression.
    for ci in range(ncell):           # t >= j n_c - (j-1) nu + o(1)
        sel = (bin_cell == ci)
        for li, j in enumerate(levels):
            r = np.zeros(nv)
            r[iv_mu:iv_mu + nbins][sel] = j
            r[iv_t + ci * nlev + li] = -1.0
            rows.append(r); rhs.append((j - 1) * nu)
    Aub = np.array(rows)
    bub = np.array(rhs)

    res = linprog(cobj, A_ub=Aub, b_ub=bub, A_eq=Aeq, b_eq=beq,
                  bounds=[(0, None)] * nv, method="highs")
    return float(res.fun) if res.success else None


def optimise_boundaries(nu, n_edges=3, table=None, seed=2, iters=400,
                        U=3.0, h=0.01, levels=(2, 3)):
    """Random-restart local search over partition boundaries."""
    lam = lambda_roots(2)
    rng = np.random.default_rng(seed)
    if table is None:
        table = _GTable(hi=4.0 * U)
    best = (0.0, None)
    base = np.array([1.0, lam[0] + 0.15, 2.0][:n_edges])
    for it in range(iters):
        if it == 0:
            cand = base.copy()
        else:
            src = best[1] if best[1] is not None else base
            cand = np.sort(np.clip(src + rng.normal(0, 0.12, size=n_edges),
                                   0.2, U - 0.05))
        if np.any(np.diff(cand) < 0.02):
            continue
        fl = gap_floor(nu, cand, U=U, h=h, levels=levels, table=table)
        if fl is not None and fl > best[0]:
            best = (fl, cand)
    return best


def bootstrap(nu0=H_PAPER, rounds=6, **kw):
    """Iterate: floor -> improved H -> improved census -> floor."""
    nu = nu0
    hist = []
    for _ in range(rounds):
        fl, edges = optimise_boundaries(nu, **kw)
        Hnew = H_PAPER + 2.0 * fl
        hist.append((nu, fl, Hnew, edges))
        if Hnew - nu < 1e-12:
            break
        nu = Hnew
    return hist


if __name__ == "__main__":
    table = _GTable(hi=12.0)
    print("conditional check (nu = 0.83625; CG's bucket floor was 0.00012638):")
    fl, edges = optimise_boundaries(0.83625, table=table)
    print(f"  gap-LP floor = {fl:.8f} at boundaries {np.round(edges, 4)}"
          f"  -> conditional H >= {2 - (MT_CONST - 2 * fl):.7f}  (CG: 0.6727534)")

    print("withdrawn transplant arithmetic with bootstrap:")
    for nu, fl, Hn, ed in bootstrap(table=table):
        print(f"  census nu = {nu:.7f}: floor = {fl:.8f} "
              f"(boundaries {np.round(ed, 4)}) -> H >= {Hn:.7f}")

    print("ladder (bin width h):")
    _, ed = optimise_boundaries(H_PAPER, table=table, iters=150)
    for h in (0.02, 0.01, 0.005):
        print(f"  h = {h}: floor = {gap_floor(H_PAPER, ed, h=h, table=table):.10f}")

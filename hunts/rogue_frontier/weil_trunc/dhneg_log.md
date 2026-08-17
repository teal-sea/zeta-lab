# dhneg: progress log

Goal: first (c, N) where the DH truncated Weil form acquires a negative
eigenvalue, enclosure-checked, with zeta control and localization evidence.
Data: `dhneg_scan.json` (checkpointed per point). Drivers: `dhneg_scan.py`,
`dhneg_confirm.py`, `dhneg_localize.py`.

## Session 2026-08-17

### Groundwork (before any scan)

Off-line pair (zeta.epstein, pinned): rho = 0.80851718245663738555 +
85.69934848537759217193 i, so delta = beta - 1/2 = 0.30851718..., gamma_off =
85.699348... The quadruple {rho, 1-rho, conj} enters the zero-side dictionary
as 4 Re g_v(gamma_off - i delta).

On-line landscape (data/dh_zeros_online_T120.json, 64 zeros to T=120):

- 43 on-line ordinates below 85.699.
- Local spacing near t=85.7 is ~1.5 (mean density (1/2pi) log(5t/2pi) =
  0.672/unit at t=85.7), EXCEPT a 4.54-wide gap between 83.109 and 87.647.
  The off-line ordinate sits inside that gap. So a band-limited beam of
  width ~2pi/L placed in the gap touches no on-line zero within +-2.2.

### Regime reasoning (what (c, N) should first expose the pair)

Three requirements interact:

1. Band reach: the even-sector test functions F_v have resonances at
   z = 2 pi k / L, k <= N; to place mass at gamma_off the band edge
   2 pi N / L must exceed 85.7. That gives N > 13.64 L: N > 35 (c=13),
   N > 46 (c=29), N > 52.5 (c=47). The whole existing positive grid
   (N <= 32, c <= 47) has band edge <= 52.2 < 85.7: it never reached the
   off-line ordinate at all. The N=32 truncation was indeed too coarse.
2. Amplification: the quadruple term carries the analytic-continuation
   factor ~ e^{delta L} = c^{0.3085} (|sin(zL/2)| ~ e^{delta L/2}/2 off the
   axis). Small: 2.2 at c=13, 3.3 at c=47. So negativity is not free; the
   on-line positive terms near the beam must be suppressed.
3. Suppression capacity: a positive-type band-limited g (hat g >= 0 on R,
   type L) can vanish on reals only at density L/(2pi) per unit (real zeros
   come doubled), vs on-line density 0.672/unit near t=85.7; equality at
   L = 4.22, c ~ 68. BUT the 4.5-wide gap at 85.7 relaxes this: the beam
   needs to null neighbors only outside the gap, so the practical threshold
   should sit well below c=68. Expect first negativity at moderate c once
   N crosses the band-reach line ~ 13.64 L with some margin for beam
   shaping.

Probe first: N-ladders (pivot-sign LDL in balls: one factorization at Nmax
gives n_neg for every principal N at once) at c in {13, 19, 29, 37, 47},
Nmax = 96; then bisect c downward.

### First timing probe (before the systematic scan)

c=47, N=96, prec=600: assembly 0.2 s, even LDL 0.1 s, inertia (95, 2)
conclusive: TWO negative eigenvalues. eig on the N=64 principal submatrix:
lam_min ~ -0.316 (not small). So the transition is somewhere at N <= 64 for
c=47, and the negative value is O(0.1), far above the 1e-38 positive floor
at N=32. A float scout cross-check (independent mpmath route) is mandatory
before believing this; scheduled next.

# CHALLENGE (circularity): spectral_operator

Hunt #150, mechanism 5. Circularity challenger, 2026-10-26, branch
`hunt/rh-moonshot-challenge-circularity`. This session did not build the construction and
edited none of its files. It read `NOTES.md` and `spo_common.py` as committed at
`2c94035de` (merged here at `d89c63d6d`) and scored them against the rubric pre-registered
in `MISSION.md` (section "Challenge-phase scoring rubric", 2026-10-26).

Files here: `circ_spo.py` (a run-time provenance trap around the builder's definition path,
a planted control, and the spectrum by a second eigensolver),
`test_spectral_operator_challenge_circularity.py` (9 tests), this page.

Grades as in `MISSION.md`. Nothing written here is kernel-checked.

## Verdict

**The builder's disposition stands: the self-adjointness step is arithmetic-free and
already in print; the RH content is link (3), which is `ccm_arithmetic`'s step 2 and
unresolved.** No hidden use of RH, GRH or the zeros was found. The provenance claim is
confirmed by an independent method that is stronger than the builder's:

- **P1 (provenance, verified at run time).** The builder's check is a text scan of the six
  `DEFINITION` functions, the `BallTruncation` class and two `ccm_common` helpers
  (`test_spectral_operator.py` lines 52-58). A text scan does not see module-level helpers
  those call, module constants they could read, or files they open; in particular
  `wp_common`, imported by `spo_common`, carries DH's off-line ordinates as module
  constants (`GAMMA_OFF`, `DELTA_OFF`, `GAMMA_OFF2`, `DELTA_OFF2`, `wp_common.py` lines
  45-50). This session ran the builder's whole definition path (`prec_for`, `sectors`,
  `ground`, `xi_full`, `operator`) for zeta and DH at (c, N) = (13, 12) and (13, 16) with:
  traps on mpmath's `zetazero`, `siegelz`, `siegeltheta`, `grampoint` and `nzeros` (on
  `mp` and on the module), on Arb's `zeta_zero`, `zeta_zeros` and `zeta_nzeros`, on every
  public function of `zeta.zeros`, on `zeta.core.xi`, `zeta.core.rs_theta` and
  `zeta.statistics.riemann_siegel_theta`; the four DH constants replaced by values that
  record and refuse any use; and every file open logged. Result: **no trap fired, no
  poisoned constant was touched, no file was opened**, for zeta and for DH. The planted
  control, the builder's comparison routine `zeta_ordinates` under the same traps, is
  caught (`mpmath.zetazero`).

  **Every constant and table, at the coordinator's request.** Tables: the file-open log
  records no file opened at all on the definition path (no zero list, no `xi_cache`, no
  `data/` file). Constants: a fresh interpreter that imports `spo_common` and runs a
  (13, 8) cell for zeta and DH loads exactly five modules from `hunts/` or `zeta/`:
  `spo_common`, `ccm_common`, `enclosures`, `galerkin`, `wp_common` (no `zeta.*` module
  at all). A literal scan of their source reads every decimal with four or more places,
  in code, strings or comments, and compares it, to 1e-6 relative, with the first 200
  zeta ordinates, with those ordinates rescaled to the operator's variable
  s = z L / (2 pi) at c = 13 and 60, and with the known off-line zeros of DH and Epstein
  (1,1,6). It finds 4 such literals, all module-level constants: `wp_common.GAMMA_OFF` and
  `DELTA_OFF` (DH), `ccm_common.EPSTEIN_OFF` (Epstein), plus `ccm_common`'s aliases
  `DH_GAMMA_OFF` and `DH_DELTA_OFF`. Every one of them was poisoned for the run, together
  with `wp_common.GAMMA_OFF2` and `DELTA_OFF2` (DH's second off-line zero, poisoned by
  name), and none was touched for zeta or for DH; the wider first pass also poisoned
  `zeta.epstein.OFFLINE_ZERO_RE`, `_IM` and `zeta.weil.GAMMA1`, with the same null
  result. (A first version of the scan
  listed the modules loaded in its own process, which included `zeta.*` modules the
  challenger's script had imported; there it found 19 literals, every extra one a
  docstring or comment or one of the poisoned constants above. The fresh-interpreter list
  is the right one.) The scan finds a
  planted `SECRET = 14.1347251417` in a scratch module (test). Provenance: clean, by three
  methods (the builder's text scan, run-time traps with poisoned constants and logged
  file opens, and the literal scan). The 4.3e-41 agreement with the zeros is therefore
  not zero-importing: the operator is built from the primes up to c, the archimedean
  place and the pole, and the zeros it reproduces are an output.
- **P2 (the arithmetic-free step is published).** Connes and van Suijlekom prove the
  real-zeros statement for any real distribution under simplicity, isolation and
  evenness (arXiv 2511.23257, Commun. Math. Phys. 406 (2025) 312), and CCM's operator
  inherits real spectrum from it. The NOTES' located obstruction ("self-adjointness
  holds for DH exactly as for zeta") is that published fact observed on DH. It is
  correct, and it is not new.
- **P3 (a second eigensolver agrees).** mpmath's `eig` on D' (the builder uses Arb's
  `acb_mat.eig` and the secular equation): at (13, 16) the largest imaginary part is
  1.8e-45 for zeta and 7.3e-58 for DH, and zeta's lowest positive eigenvalue is
  14.1347251417347, against gamma_1 = 14.134725141734694 (difference -8.5e-16 at this
  small band).

## Scorecard

1. **Disposition.** Restricted class obstructed **for the self-adjointness step** (the
   theorem is Connes and van Suijlekom's, whose hypotheses are met by every even-simple
   real distribution, DH included, as the NOTES measure); **unresolved** for the
   mechanism, whose open step is link (3). This agrees with NOTES section 7.
2. **Grade per step.**
   - Even-simplicity of the truncated form T (Arb LDL^T inertia, every pivot
     conclusive): hardened for the truncated matrix. Agreed. Like `ccm_arithmetic`'s
     lambda_1, this is band-level: by interlacing, the window form's infimum lies below
     every band-N value, so even-simplicity at (c, N) says nothing about the window form
     (see `ccm_arithmetic/challenge/CHALLENGE_circularity.md`, C1). The NOTES do not
     claim otherwise.
   - Self-adjointness of D'' for W = T - eps_N: cited (CCM Lemma "key"), checked
     numerically (builder, 1e-60). Agreed.
   - Real spectrum: measured on two eigensolvers (builder's Arb `eig`, this session's
     mpmath `eig`).
   - Spectrum against zeta's zeros (to 4.6e-40 for 46 zeros at (60, 100)): measured,
     against mpmath's on-line zeros. Agreed.
   - Link (3), convergence: unproved; no grade.
   - Composite: measured, as the NOTES say (section 8).
3. **The Euler-product step.** Named: link (3), the convergence (NOTES section 4). Tested
   on DH only: its real spectrum places eigenvalues in the gap where its off-line pair
   sits (measured). Epstein (1,1,6), W_{1/4} and zeta(s - delta) were not run. The NOTES'
   remark that their operators would be self-adjoint wherever even-simple is the cited
   theorem, not a computation.
4. **Finite stand-ins.** Seven cells, c <= 60, N <= 200, compared to at most the first 100
   zeros. None is offered as uniform; the NOTES say every (c, N) is a different finite
   operator and nothing is uniform (section 5). Agreed. At (13, 200) the operator stops
   tracking the zeros near the 50th to 60th, which the NOTES report.
5. **Novelty search.** The builder claims none (the construction and its accuracy are
   CCM's). This session's queries, web search, 2026-10-26:
   (a) "Connes Consani Moscovici zeta spectral triples self-adjoint rank one perturbation
   scaling operator spectrum real any distribution criticism obstruction Hilbert-Polya":
   A. Connes, C. Consani, H. Moscovici, *Zeta Spectral Triples*, arXiv 2511.22755 (2025;
   listed for an EMS lecture-notes volume, 2026), and Connes's page
   https://alainconnes.org/2026/07/zeta-spectral-triples/; Connes and Moscovici, *The UV
   prolate spectrum matches the zeros of zeta*, PNAS (2022); no published critique or
   obstruction found.
   (b) "Connes van Suijlekom arXiv 2511.23257 lowest eigenvalue simple even
   eigenfunction Fourier transform only real zeros" (from the earlier unit): A. Connes
   and W. D. van Suijlekom, *Quadratic Forms, Real Zeros and Echoes of the Spectral
   Action*, Commun. Math. Phys. 406 (2025) 312: the theorem behind P2.
   (c) From the earlier unit: A. Groskin, *High-Precision Approximation of Riemann Zeros
   via the Truncated Weil Form*, arXiv 2605.20224 (2026), a public implementation of the
   Galerkin matrix, convergence called open. No rival (DH) test of the CCM operator was
   found in print.
   arXiv listing search, zbMATH and the Lean Zulip archive were not browsed.
6. **Rivals on complete hypotheses.**
   - DH: meets the hypotheses of the self-adjointness theorem (even-simple, hardened on
     three cells) and has real spectrum: a rival passing a shared lemma, so no verdict on
     the whole; it fails link (3) at its off-line pair (measured).
   - Epstein (1,1,6), W_{1/4}: not run; excludes nothing.
   - zeta(s - delta): not run; excludes nothing. It would lack the functional equation
     about Re s = 1/2 that makes the Weil distribution's even sector the right one.
7. **Circularity.** None. The definition reads c, N, the precision, Lambda(n) for n <= c,
   the digamma function and the pole (P1, verified at run time); zeros enter only the
   comparison section, after the spectrum is computed (NOTES section 2, confirmed by the
   planted control). The target (a self-adjoint operator whose spectrum is the zeros)
   would imply RH by reality of the spectrum; no step assumes RH.

## Run manifest

```runmanifest
id: rh_moonshot-spectral_operator-2026-10-26-challenge-circularity
hunt: rh_moonshot
started: 2026-10-26T14:30+00:00
finished: 2026-10-26T16:09+00:00
ran:
  - .venv/bin/python hunts/rh_moonshot/spectral_operator/challenge/circ_spo.py
  - .venv/bin/python -m pytest -q -n0 hunts/rh_moonshot/spectral_operator
outcome: provenance confirmed at run time with traps on every zero source, every zero-like module constant on the path poisoned, file opens logged (none) and a literal scan of every path module, no hit for zeta or DH and both planted controls caught; self-adjointness is Connes-van Suijlekom's arithmetic-free theorem; link (3) unresolved
artifacts:
  - hunts/rh_moonshot/spectral_operator/challenge/circ_spo.py
  - hunts/rh_moonshot/spectral_operator/challenge/test_spectral_operator_challenge_circularity.py
  - hunts/rh_moonshot/spectral_operator/challenge/CHALLENGE_circularity.md
```

Compute: about 55 s of one core for the script (most of it computing 200 zeta ordinates for the scan). Times are read from the clock, except
`started`, which is approximate (to about 5 minutes).

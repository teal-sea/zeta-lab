# DH: the Davenport-Heilbronn refusal gate, design and status

**Status (2026-10-26, later the same day): built and preregistered.** The
literature record is `DH_LITERATURE.md`, the gate code is `dh_gate.py` with
`test_dh_gate.py`, and the preregistration is `DH_GATE_PREREG.md`, committed
before the run (commit 2ba8cbba3). **The gate was run as preregistered:
the clean pipeline PASSes (four zero boxes refused, each with decided winding
1; two controls decided 0), and both must-catch faults (`one_corner`,
`main_terms_only`) are caught** (`../RUNS.md`, E7; `dh_gate_results.json`). Steps 3 to 5 below were
done differently from the plan written earlier the same day:

- Step 3: the literature has no explicit-remainder Riemann-Siegel formula for
  L-functions, and the measured sharp residual is not a smooth function of p.
  The correction C is therefore the difference between the sharp sums and
  Rubinstein's smoothed split (`dh.F_split`). It is an exact identity at t = 0;
  at t > 0 it goes through hunt #61's enclosure of H.
- Step 4: there is no DH analogue of Theorem 1.3. On DH the pipeline evaluates
  H itself in balls, so E = 0.
- Step 5: `dh_gate.dh_barrier` is `effective.barrier_rectangle`'s rule with the
  function swapped.

What follows is the plan as first written. Nothing here is a statement about
any de Bruijn-Newman constant.

## What the gate is for

Every sweep or barrier run of this evaluator on zeta is gated (`EVALUATOR.md`,
`../REDUCTION.md` part D, `../MISSION.md` scope) on one control. The same
pipeline, run on the Davenport-Heilbronn function, must refuse to declare a
zero-free region where DH's heat flow still has a non-real zero. DH has
zeta's functional-equation shape and real coefficients but no Euler product,
and its Riemann hypothesis is false. A pipeline that would pass DH where DH
has zeros is not reading anything zeta-specific, and a pass on zeta would
then mean nothing.

## The numbers the gate is built on, cited and not recomputed

- **Lambda_DH is not 0.2304.** Hunt #61 (`hunts/lambda_dh_bounds/`, read-only
  from here; the reading course is `docs/29`) gives the bracket
  0.2304 < Lambda_DH <= 0.7696992583210755065522 in the wide frame of Polymath
  15, which is this evaluator's frame. 0.2304 = 4 x 36/625 is the floor. It
  comes from a winding count of 1 for the narrow-frame flow at t = 36/625, over
  a box whose interior has Im z >= 3/1024, which that hunt grades *decided*
  (python-flint at 420 bits, an mpmath second witness;
  `hunts/lambda_dh_bounds/SEPARATION.md`, its `winding_results.json` and
  `crosscheck_dhflow_results.json`). The factor 4 between the frames is
  derived in its `FRAME.md`: z = 2 z_n, t = 4 t_n. The earlier wording here
  ("Lambda_DH = 0.2304, quoted from the task") was wrong: 0.2304 is a lower
  bound.
- **The consequence the gate uses.** Since Lambda_DH > 0.2304, any run of the
  pipeline on DH that would output Lambda_DH <= t0 + y0^2/2 < 0.2304 is false,
  so it must fail at some step. Hunt #61 also locates a zero of the
  narrow-frame flow at t = 0.0576 near z_n = 240.3451714460939 +
  0.01018313776460141 i (its measured locating pass). In this evaluator's frame
  that is z of about 480.6903 + 0.0204 i at t = 0.2304, inside the region
  x >= 200 of Theorem 1.3.

## Conventions (`dh.py`)

f(s) = sum a_n n^{-s}, with a_n = 1, kappa, -kappa, -1, 0 for n = 1 to 5 mod 5;
F(s) = (pi/5)^{-(s+1)/2} Gamma((s+1)/2) f(s); H_0(z) = F((1 + iz)/2); and H_t is
its backward heat flow, evaluated as
int F((1 + iz)/2 + sqrt(t) v) e^{-v^2}/sqrt(pi) dv. kappa is derived by one
linear solve of F(s) = F(1 - s), and never typed in. The main terms are the
termwise Gaussian average of the approximate functional equation, exactly the
shape of Polymath's (ft-def) with DH's Gamma factor:
M_t(s) = exp((t/4) alpha(s)^2) M(s), alpha = M'/M, b_n = exp((t/4) log^2 n),
and A_t + B_t = M_t(s_-) sum a_n b_n n^{-s_-*} + M_t(s_+) sum a_n b_n n^{-s_+*}.

## Plan and status

1. **The function and an oracle: done.** Measured in `test_dh.py`:
   - kappa comes out real to 1e-44 and agrees with `zeta.epstein.KAPPA_REF` to
     1e-38, and with the closed form, which is used only as an observation.
   - The functional-equation defect is below 1e-40 at three points. A kappa
     perturbed by 1e-6 breaks it (lesion).
   - H_0 is real on the real axis.
   - H_0 vanishes at the lab's pinned off-line zero (`zeta.epstein`, Spira's
     0.808517 + 85.699348i), mapped to z = 2 gamma + i(2 sigma - 1), to 1e-18
     of its size 0.3 above.
   - **The frame, checked by an independent route.** Gauss-Hermite quadrature
     over mpmath's Hurwitz-based F, which shares no code with hunt #61's
     `DHFlow`, vanishes at 2 z_n and t = 0.2304 to 1e-10 of its size at
     y = 0.3. The same numbers read in the wrong frame (z_n at t_n) are not a
     zero (lesion).
2. **The main terms: done, and measured not to see the zeros on their own.**
   At t = 0, |H - (A + B)|/|B| stays below 1.1 (5x/(4 pi))^{-1/4} on eight
   points from x = 300 to 10^4. It oscillates (0.011 to 0.22 there), as
   zeta's C_0(p) correction does, and the scale is that of a Riemann-Siegel
   correction. At both gate zeros, the t = 0 one at x of about 171.4 (N = 8)
   and the t = 0.2304 one at x of about 480.7 (N = 13), |A + B|/|B| is still
   0.25 to 0.28. So a pipeline that used the main terms with error terms
   smaller than that would declare those points zero-free. This is the
   behaviour the gate exists to catch, observed at the level of the
   approximation.
3. **A correction term C_t for DH: next.** For zeta, C_t comes from the
   Riemann-Siegel remainder at the cutoff N. For f = c L(s, chi) + conj(c)
   L(s, conj chi) with chi mod 5, the remainder depends on the residue of N
   mod 5 as well as on the fractional position. The route: derive it by the
   contour argument of Polymath's Section 5 applied to the Hurwitz
   representation, fit it first against the measured residuals of step 2 (the
   oracle is cheap at x below 10^4), then use it. The literature on
   Riemann-Siegel formulas for Dirichlet L-functions has not been searched or
   pinned yet. That search comes before any derivation is written.
4. **Error bounds for DH: after 3.** These are analogues of e_A, e_B, e_C of
   Theorem 1.3 with |a_n| <= 1 and the conductor 5 in the Gamma factor. They
   are the lab's derivation, and unreviewed until reviewed. While that holds,
   a passing gate says only that the pipeline is not trivially permissive. It
   does not lend the zeta run any grade it lacks.
5. **The pipeline on DH: after 4.** `barrier_rectangle` and the sweep in
   `effective.py` are written for zeta. They will take the function as a
   parameter only when step 4 gives DH everything they need. No interface is
   built before that (`CLAUDE.md`, design discipline).
6. **What the gate cannot test.** The sweep's lower bound for zeta is
   Euler-mollified (Section 8.5), and DH has no Euler product. The DH run can
   therefore exercise the barrier, the error terms and an unmollified triangle
   bound, but not the mollifier itself. Input 2 of `../REDUCTION.md` part D
   stays zeta-specific and is not tested by this gate. That is recorded here so
   that a passing gate is not read as covering it.

## Gate condition, to be fixed before the gate is run

The pipeline is run on DH at (t0, y0) with t0 + y0^2/2 < 0.2304. Start with
t0 = 0.2304 and y0 in {0.01, 0.02}, over the rectangle
[480.19, 481.19] x [y0, 1] that contains the wide-frame image of hunt #61's
box. It **passes the gate** if it reports no winding number, or reports
winding 1, or fails its sweep inequality somewhere. It **fails the gate** if
it declares the rectangle zero-free. A failed gate blocks every zeta sweep.
An inconclusive DH computation excludes nothing (`CLAUDE.md`, the battery
rule). Before running, this condition is to be preregistered in `../RUNS.md`
together with the cost estimate.

## Cost

Measured on the shared box under load (`../RUNS.md`, E5): main terms take
milliseconds (N = 13 at x of about 480); the oracle takes 0.1 to 7 s a point at
t = 0 (x = 300 to 10^5) and about 15 s a point at t = 0.2304 with 80
Gauss-Hermite nodes. `test_dh.py` runs in about 50 s on one core.

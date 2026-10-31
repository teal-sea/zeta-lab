# Conceptual map and research triage

Inspection base: `6a9aa8fd4074ea23868c1c547168c0c773185781`, fetched on
2026-09-04. This is a map of inspected interfaces and selected proofs, not an
audit of every theorem in the repository. The ranking records research
judgment during reconnaissance, not a preregistered quantitative score.

## The mathematical machine

The classical zeta arm turns arithmetic into analysis: theta and Poisson
summation give the functional equation; the explicit formula translates zeros
back into primes; heat deformation turns zero positions into a dynamical
question. Li coefficients, exact Sturm tests of Jensen polynomials, Weil
functionals, and elementary equivalence criteria are alternative probes of
the same object. Finite-field curves supply a comparison universe with
genuine Frobenius spectra. Most of this is reconstruction of known theory,
not a claim of original mathematics. `zeta/rigor.py` adds enclosure-carrying
numerics, while the independent Lean arm establishes symbolic statements.

The counterexample machinery is not merely another collection of functions.
Davenport-Heilbronn and the Epstein examples separate functional-equation
symmetry from Euler-product arithmetic. The inverse-spectral and moment
surrogate failures explain why reconstructing a spectrum or reproducing
heavy tails is insufficient. The off-line zero localization and the DH heat
deformation program are substantive analytic/computational chains of their
own. The prime-zeta program shows another useful distinction: its main
rightmost-zero threshold was rediscovered prior art, while connecting the
general almost-periodic theorem to an existing conjecture remained useful.

The simple-zero chain begins with Alpöge-Furman, not with this laboratory.
Their explicit formula and prime-side asymptotics control the trace and
Frobenius norm of a finite Weil form. Inertia charges conjugate off-line
pairs; multiplicity-aware rank-trace inequalities then give a simple-on-line
proportion. Their Montgomery-Taylor window supplies the base constant H.
The lab imports those analytic facts. The Ainta-style extension retains a
spectral defect instead of discarding it, turns local kernel overlap into
block defect, pinches blocks, averages offsets, and solves one scalar
inequality. `StableRankTrace.Psi_eq_gc_two_add_one` identifies the new-looking
defect as an upstream scalar function shifted by one. That is an actual
composition of proof paths, already accomplished before this run.

In `lean/bridge`, S2 and S6-S16 have proofs; finite floor S10 remains a
hypothesis in the generic theorem. The three- and four-point developments
discharge their specific S10 inputs. This makes the formal machinery more
general than those individual unconditional instances. Conversely, variable
windows, position-dependent pressures, uncapped Gram profiles, and the
band-aware competitor extension go beyond this bridge's present interface.
Their analytic deductions and computational candidates are ahead of this
lab's formalization. `family_wall` bounds the fixed-window capped family;
its ceiling is not a bound on the enlarged competitor family.

The older gap-census transplant is a different chain. Its exact incidence
laws, finite rational floor, and pair-energy inequality are reusable pieces;
joint retention is not obtained by adding independently valid single-pair
bounds. The signed cross interactions in `PROOF-LEDGER.md` are mathematical
obstructions, not missing implementation. `outband_intake` also names a real
interface uncertainty: positivity of the published weighted form factor
does not by itself establish every pair-density constraint used by its LP.
Its predicted gains should remain class values until that identification is
proved.

The Fredholm/xi-prime arm solves another optimization problem. Its kernel is
the Farmer-Gonek-Lee F1 rather than the Montgomery-Taylor |s-t| kernel.
Classical energy Cauchy-Schwarz gives the ambient upper bound. The original
work is showing that the optimizer is positive and radially decreasing,
then constructing admissible endpoint tapers approaching it. The registered
Lean conclusion is an exact variational closure statement. It does not
itself assert a numerical zeta or xi-prime zero proportion. Coercivity and
residual bounds are transferable; numerical constants and source hypotheses
are not interchangeable between the two kernels.

Other live mathematical subjects include prime-simplex/factorial induction
lemmas, Hardy-Ramanujan/Mertens arguments, smooth pair-sum sets for Erdős
126, Krenn-Gu polynomial matching obstructions, the affine-plane extension
obstruction for Erdős 617, and minimum-overlap/Bloch/spherical optimization.
The Krenn-Gu records distinguish an exhaustive orbit cover of selected
supported matchings from an invalid restriction of all edge variables to
orbit-constant values. That distinction is especially relevant here:
averaging is safe for our convex coefficient problem, not for arbitrary
nonlinear polynomial feasibility.

`ontology` proposes and classifies conjectures; it is not an oracle for
novelty. `dossier` separates kinds of evidence. The live harness ledgers
preserve dead ends and audits; the general harness framework lost its own
experiment and is retired. Branch history contains integrated bridge work,
recovered O9 tables, rescued matching/support searches, and competing
out-of-band readings. Their existence is not evidence that the recorded
mathematical gaps closed. Current files and later corrections take priority
over old branch summaries.

## Ranked candidates

Rank uses qualitative probability of a correct substantive outcome,
mathematical significance, and reusability. No numerical probability or score
is claimed to be calibrated. A decisive negative outcome counts as success.

| Rank | Proposed claim or experiment | Why it might work; existing inputs | Fast falsifier | Significance if successful | Difficulty; path |
|---|---|---|---|---|---|
| 1 | Reversal closure plus a finite mixed adversary gives a rigorous bound on all pair-weight/pressure choices, exposing whether asymmetric gains are real. | The objective is linear in coefficients, the domain and span budgets are reversal-invariant, and saved cut vectors can be combined by exact weak duality. Uses `amtopa_ceiling`, the bridge's gap bookkeeping, and the symmetry lesson from Krenn-Gu. | Any failure of reversal to preserve the actual feasible set; or a verified upper bound that leaves the reported target feasible. | Can eliminate a whole optimization target and reduce the coefficient search without changing its optimum. High reusability across pressure certificates. | Moderate; analytic + optimization + numerical verification. **Attacked below.** |
| 2 | Build a joint odd/even-lag spectral-defect certificate instead of compressing all overlaps to one energy. | Odd-lag graphs are bipartite; the band profile uses graph coloring. Combine `StableRankTrace`, S14 pinching, and the competitor's band-aware profile. | Small PSD unit-diagonal matrices violate the proposed joint bound, or optimization always selects a scalar endpoint. | Potential stronger simple-zero construction and a reusable matrix inequality. | High; analytic + SDP. Competitor primary source already identifies multi-lag work, so no priority claim. |
| 3 | Determine whether the out-of-band LP's entire feasible class follows unconditionally from the actual zero-side formula. | `configuration_lp.py` uses real pair densities while the source has a weighted form on complex zero differences. Incidence and DH controls supply adversaries. | One admissible off-line configuration breaks the translation of a purported constraint. | Either legitimizes a new information source or closes a costly false route. | High; analytic + computational. |
| 4 | Use coercive residuals to give an exact quantitative stability bound for near-optimal windows and guide coupled window/certificate optimization. | `Pub1` already bounds the inverse operator and supplies a positive optimizer. Energy orthogonality identifies the quotient loss. | The desired window objective is not the same operator, or the claimed gain is just classical quadratic completion. | Reusable error estimates and principled parameter compression; limited novelty. | Moderate; analytic + formal. |
| 5 | Strengthen the capped block lemma by retaining fixed trace and total Gram energy. | S12 discards trace information when one eigenvalue exceeds two. | Find the same sharp envelope in the competitor record. | Removes an artificial cap, but only useful as original work if not already known. | Moderate; analytic. **Killed as a new direction:** AMTOPA already uses precisely this envelope. |
| 6 | Use the DH strip-to-time and zero-localization modules to sharpen an explicit deformation bound with a shared tail lemma. | Existing zero-free half-plane estimates and argument-principle enclosures consume related tails. | A tail constant loses its uniformity at large height or the normalization changes by four. | A concrete non-zeta heat-flow bound and reusable interval analysis. | High; analytic + enclosure arithmetic. |
| 7 | Exploit simultaneous base-point S-unit equations to constrain collision fibers, not total solution counts. | Erdős 126 support arms already supply injections and show why ordinary exponential S-unit bounds are too weak. | A family has many base-point equations but retains the same large fiber. | Potential genuine number-theoretic progress beyond a coefficient improvement. | Very high; analytic/combinatorial, low present probability. |
| 8 | Quantify how many old edges must change before an affine-plane coloring can admit one additional vertex. | Erdős 617's proof forces disjoint blockers to contain intersecting lines; matching/orbit machinery may classify small repairs. | A small recoloring counterexample defeats the proposed stability threshold. | A structural restriction on counterexamples; does not settle the full coloring problem. | High; combinatorial + SAT. |

## What the lab already knew implicitly

The saved pressure adversaries already contain an obstruction to a later
reported target, but their reflected copies were not enforced. The missing
operation is mathematical closure of the test set under a known symmetry.
It costs no new gap search. The main result of this run is the explicit
finite witness extracted from that observation, not a claim to have invented
symmetrization.

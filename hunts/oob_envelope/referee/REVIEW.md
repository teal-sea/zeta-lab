1. **PASS, ordinary derivation:** the support lemma holds for complex and odd L2 functions, including frequency 2L; the pole term is unchanged (§2).
2. **PASS with stated scope, ordinary derivation:** Q >= R_H and the finite-cosine reduction survive; tail constants and quadrature must be recomputed (§3).
3. **PASS after repair, ordinary derivation:** b447f0d fixes the all-N estimate and analytic-strip scope; original defects are retained in §4.
4. **PASS, hardened numerical step:** two CC/Arb resolutions give R_H >= 1.1579e-17 on the full even sector at L=4/5, with explicit quadrature, tail and coupling bounds (§5).
5. **PASS, controls with separate grades:** K1 passes from both enclosures; independent DH K2 at two resolutions, K3 and all three planted lesions pass at measured grade (§6).

# Independent referee review, 2026-09-27

Primary verdict: **the corrected L=4/5 even-sector bound survives independent
review and all five approved units pass**. The
composite Q bound combines an independently reviewed ordinary derivation
with a hardened numerical step. It is not kernel-checked. The L=1.19
positivity claim remains UNRESOLVED; Stage A midpoint evidence does not
bound the whole form.

## 1. Inputs, independence, and boundary

Read the referee brief, `hunts/oob_envelope/MISSION.md`, repository mandate,
and the computational-mathematics method reference. There is no
`referee/MISSION.md`; the brief points to the hunt-level mission.

Pinned reviewed material:

| input | revision | use |
|---|---|---|
| theory RESULTS | `e62cac5`, plus changes through `9f5bbc3a7c46cb6a97947a700cff5c568e2f3a74` | full prose proof, not implementation |
| numerics RESULTS | `ed52a32ed49ce3fcb4ab7189b7a8b7eb1f4db234` | interim claim and budgets |
| envelope and initial hardened result | `57ef234` | original exact-rational witness and reported output |
| hardened control result | `ed52a32`, `harden_L08_T100_sine16_control.json` | shifted LDL decisions and full-space accounting |
| final readback | theory `fa6f450d57e94fab7fb3c931cf7f6c3afc07b337`; numerics `b9a25bae89c55471444def8e1b5cb2f9b5eac798` | later caveats, K2 and Stage A status; no author code read |
| repair readback | theory `b447f0dab4c9fda3e2d66ece2cc7da043781e332`; numerics `3132b7daa5b54d9c4141f0e144bc9dc262a2855f` | repaired all-N proof and scope; corrected full-space endpoint |
| final reporting correction | numerics `f779b27` | removes invalid two-sided bracket at L=1.19; ordinary monotonicity check accepted |
| Zhu | [arXiv:2608.24827v2](https://arxiv.org/html/2608.24827v2), §§1–5 and parity statement | primary-source convention and reduction check |
| DH normalization and old negative control | `hunts/rogue_frontier/weil_trunc/SOURCE.md` §4 and `dhneg_log.md` in this checkout | rival definition and reproduction target |

The later theory revision fixes two earlier defects: it allows an empty
positivity interval, and it assumes a uniform bound on component sizes in
Proposition 2.2. Those repairs are not charged against the current version.
The first final readback added only caveats and numerical status changes.
The subsequent repair readback changes the proof and endpoint as detailed
below. The rejected original claims remain recorded with their revisions.

No theory, numerics, or rival implementation was read or imported. Only their
prose and result data were read. The new implementation shares python-flint
with the numerical lane, so it is independent in construction and
quadrature, not in its arithmetic library. This is a separate model-family
review; model independence alone is not evidence of correctness.

`git fetch origin` completed. The advertised research-session `list_sessions`
tool is not exposed here; read-only Orca terminal listing and git worktree
listing confirmed the sibling lanes. No messages, code, or state were
written to those lanes. All new files are in this referee scope.

**No numerical computation, test, verifier, reducer, or build has run locally.**
The approved Modal batch uses source commit `c65c66e`; RUNS.md records every
unit. Source reading, git inspection, data extraction, file writing, hashing
and Modal orchestration are the only local operations.
The initial no-compute-on-Ghost instruction is retained; the later reminder
of a local resource allowance has not been used to launch local work.

All mathematical checks in §§2–4 and §7 are ordinary derivations by this
referee, not numerical tests or kernel checks. They are subject to external
review. Reported author numbers retain their original attribution.

## 2. Claim card and support lemma

The object is the Hermitian form on `W_L = L2([-L,L]; C)`, with zero extension,
`F(t)=integral f(x) exp(itx) dx`, and prime powers satisfying `log n < 2L`.
The pole contribution for general complex f is

    F(i/2) conjugate(F(-i/2)) + F(-i/2) conjugate(F(i/2))
      = 2 |integral f cosh(x/2)|^2 - 2 |integral f sinh(x/2)|^2.

The real-even numerical claim uses only the first term. Applying it to all
complex functions would need the odd-sector numerical bound as well.

For `g(x)=integral f(y) conjugate(f(y-x)) dy`, Cauchy-Schwarz and translation
continuity give continuous g. Its overlap vanishes for `|x| >= 2L`, including
the endpoints, whose intersection is a null set. Plancherel gives
`|F|^2 in L1`. For a finite measure mu supported outside the open band,
absolute Fubini then gives

    integral |F(t)|^2 H(t) dt = 2 pi integral g(-lambda) dmu(lambda) = 0.

This proof uses neither parity nor reality of f. It also proves the
polarized matrix-entry identity. It does not set a truncated integral over
`[0,T]` to zero. The pole term is independent of H and is never evaluated
by substituting a nonreal argument into H. **PASS.**

The stated lemma is for finite-measure transforms. The mission's broader
wording about arbitrary bounded almost-periodic functions is not literally
the same class. For Bohr almost-periodic functions the same conclusion can
be extended using uniform trigonometric approximants preserving the
spectrum, but that extension is not needed for this finite-cosine witness.

## 3. Modified reduction and infinite tail

Dependency chain:

    exact prime-power list and rational H
      -> nonnegative kernel decomposition -> P_L - H <= S
    support lemma + correct pole + archimedean lower envelope
      -> Q >= R_H
    enclosed leading block + tail deviation + coupling norm
      -> full-space lower bound.

Zhu's Lemma 3.1 was read in the primary source. Its recurrence and Binet
remainder yield the required envelope for `t >= 15/4`. Subtracting `P_L-H`
and using Parseval gives the proposed inequality without losing H inside
the retained interval. Complex f require the full-line formula; parity
splitting recovers the two half-line sector formulas.

The linear-algebra implication is

    lambda_min(R_H) >= min(lambda0, beta - eps_D) - eps_B.

It needs both the tail block and the off-diagonal block. A positive leading
block alone is insufficient. Gershgorin and the Schur test remain valid,
but every entry majorant must use `max |a-P_L+H-beta|` on the real interval.
The pole contribution must be accounted for separately. A single exact
rescaling of the *total* old error budget, including the pole part, is not
an identity; it may be a conservative bound if justified.

The theory correctly notices the missing `T/pi` in the source's displayed
supremum-based entry estimate. The independent implementation retains it.
This is a source display defect, not a refutation of the split inequality.

For the actual finite H the ellipse integrand is analytic inside the
digamma poles. Its majorant must include `sum |b_lambda| cosh(delta lambda)`.
The numerical report specifies this and a radius in every retained entry.
That specification is mathematically appropriate. The JSON does not expose
the matrix entries or those radii, so its `pd: true` flags cannot independently
verify the implementation's error insertion.

**PASS as an ordinary analytic reduction for the finite-cosine witness.**
The independent even-sector execution now passes at L=4/5 (§5); this is not
a validation of the author's unseen source or a uniform statement in L.

## 4. Original proof defects and reviewed repairs

### 4.1 Finite-N estimate in Theorem 2

The equality of infima is supported by the completion construction once N
is sufficiently large for the finite list of prime-power exponents. The
theorem nevertheless quantifies over every `N >= 1` for its sharper cosine
error bound. The proof only establishes its key estimate when
`m*pi/(2N+2) <= pi`.

An exact symbolic counterexample to that intermediate inequality is
`N=1, m=8`: the weights are supported on `{-1,0,1}`, so `rho_N(8)=0`, whereas
`cos(pi*m/(2N+2))=cos(2*pi)=1`. Thus the displayed assertion
`1-rho_N(m) <= 1-cos(...)` would say `1 <= 0`. Such an exponent occurs when
`L > 4 log 2`.

This refutes the unrestricted intermediate estimate, not the duality
identity or the claimed asymptotic rate. A sufficient repair is
`2N >= max m` for the cosine estimate. Alternatively, the quadratic error
estimate can be justified for every m by zero-extending the weight vector v:

    2(1-rho_N(m)) = ||v-shift^m(v)||^2 / ||v||^2
                  <= m^2 ||v-shift(v)||^2 / ||v||^2
                  = 2m^2(1-cos(pi/(2N+2))).

The entire displayed two-stage inequality, as printed for all N, is not
established. **FAIL at the identified proof step; repairable restriction.**

### 4.2 General H need not be analytic

Finite total variation of mu supplies a bounded continuous H on the real
line. It does not supply a strip extension or a finite value of
`integral exp(delta |lambda|) d|mu|`. Consequently §1.5(b)'s ellipse method
needs a finite trigonometric sum or an explicit exponential-moment
hypothesis. The support lemma, real-axis tail estimates, and split inequality
do not need this additional hypothesis. The actual sine-degree-16 witness
satisfies it. **FAIL for an unrestricted transfer of the quadrature method;
no defect in the actual finite H.**

### 4.3 Threshold asymptotic inherited from the source

The table's claim that the threshold sentence is unchanged inherits a
source slip. If `T1=2*pi*exp(S)` and `T0` solves beta=0, then
`T0 log(T0/T1)=1`. Expanding gives
`T0-T1=1-1/(2T1)+O(T1^-2)`, not an additive `O(T1^-1)` difference.
The relative scale and all uses of the exact beta formula survive.

### 4.4 Extended-value notation and remaining theory

Proposition 1.3 writes `Q - integral_tail` on all W_L. Both terms can be
infinite. Use its bounded multiplier/time-operator expression to define
R', and define B directly by its capped multiplier, or initially restrict
to the finite form domain and extend. The domination argument survives
this repair; `infinity-infinity` is not a definition.

The completion induction, weak duality, continuous-measure tail argument,
and model-operator asymptotic proof were inspected. No additional decisive
gap was identified, subject to the above corrections and the stated PNT
input. This is not a numerical reproduction of their tables. The sampled
finite-component census does not prove component exhaustion. Novelty,
record comparisons, and the exact Liu-source translation are not independently
cleared by this review; their external-source status remains conditional.

The theory worker's later `fa6f450` progress note independently acknowledges
the extended-value definition problem, an even/full-space sector mismatch
in the essential-spectrum argument, the missing odd-sector citation for
the T=150 bracket, and an overstatement that a better joint H can help only
when the envelope threshold binds. These are valid caveats. In particular,
`R_H <= R' <= B_T` gives a common lower limit on operating heights, not a
proof that optimizing H cannot help above that limit. The essential-spectrum
argument on the even subspace needs the symmetrization/modulation step
written out; it is not supplied by a complex modulation that leaves that
subspace. None of these ancillary claims is needed for the L=0.8 split bound.

### Repair readback at b447f0d

The revised theorem uses `1-rho_N(m)` and the shift-norm quadratic bound
for every N, restricting the cosine comparison to `m <= 2N+1`. That closes
the N=1, m=8 defect. The strip hypothesis now distinguishes finite measures
from finite cosine sums or exponential moments; the actual witness qualifies.
The threshold expansion and pole-versus-symbol rescaling are corrected.
The bounded-symbol definitions remove the infinity subtraction, and the
even symmetrization of the modulation sequence supplies the missing weakly
null sequence. The two-sector citation and sampled component census caveat
are now explicit. These changes pass ordinary analytic review. The phrase
that every difference has a bounded integrand should exclude the displayed
`Q-B_T`, which the revised proof correctly treats as extended nonnegative.
No numerical or kernel-checked grade is claimed for these repairs.

## 5. Numerical claim at L=4/5

The target is the exact rational `sine:16` witness, `T=100`, and the first
96 even Legendre modes. A different basis of the same size would usually
be a different Ritz problem, so this review keeps the subspace and changes
the quadrature and transform evaluation instead.

The inspected author control JSON reports:

| quantity | reported value or decision | referee status |
|---|---|---|
| S | `388813211679889/250000000000000` | independently reconstructed and covered by an Arb kernel decomposition in both leading units |
| leading shift `1.158e-17` | positive pivots | reproduced by both CC/Arb units |
| leading shift `1.1585e-17` | one negative pivot | reproduced by both CC/Arb units |
| largest quadrature error | about `5.764e-44` | reported, not independently bounded at this value |
| tail deviation | about `2.757e-95` | alternative independent bound below `2.256e-95` |
| coupling | about `3.030e-44` | nonzero; must be subtracted |

The original numerics RESULTS at ed52a32, lines 17–20 and 22–24, assert the exact full-space endpoint
`1.158e-17`. The displayed
two-block proof only yields `1.158e-17 - eps_B` when the leading shift is
that same number. The JSON's decimal `lower_bound` rounds away this loss;
its `lower_bound_arb` is a ball, not a lower endpoint equal to its midpoint.
It could be possible to prove an extra leading-block margin and recover the
claimed endpoint, but that extra margin is not given by a boolean LDL pass.

**The literal endpoint is unsupported by the stated accounting.** A candidate
safe outward-rounded replacement is `1.1579e-17`, conditional on the reported
enclosures being valid. This observation does not allege that the true
minimum is below `1.158e-17`.

**Repair accepted at 3132b7d:** RESULTS now subtracts `eps_B` explicitly and
states the safe endpoint `1.1579e-17`, on the even sector. It also corrects
the H=0 calibration to `1.0199e-17`. The new endpoint serialization is
reported edited but unrun; no author code was read and this review does not
validate that edit. The independent replay described next closes the
corrected scientific enclosure through a separate quadrature implementation.

The new implementation encloses the same frozen witness with a two-atom
kernel decomposition, reassembles the same 96-mode form, and tests both
reported shifts. It uses its own independently derived quadrature error
bound. It cannot confirm the author's exact quoted quadrature radius merely
by obtaining the same final sign. The distinction will be retained in the
post-run verdict.

### Independent 96-mode results

Both approved units completed on source commit `c65c66e`, without a code
repair or rerun. The exact rational frozen envelope passed the independent
two-atom Arb proof in each unit. Both shifted LDL tests decided the same
bracket as the author: the exact leading block satisfies
`1.158e-17 < lambda_min(A) < 1.1585e-17`. The upper test has a negative pivot
at index 36, after positive earlier pivots. The measured midpoint Ritz value
is `1.1583402660085778616489630627792930825e-17` at the displayed precision;
the two result files store the same longer decimal string.

| independent bound | CC degree 160, 512 bits | CC degree 192, 640 bits |
|---|---|---|
| entry quadrature radius, rounded upward | `< 1.186e-54` | `< 6.685e-67` |
| matrix operator quadrature error, rounded upward | `< 1.139e-52` | `< 6.418e-65` |
| tail block deviation | `< 2.256e-95` | `< 2.256e-95` |
| leading-to-tail coupling norm | `< 1.621e-46` | `< 1.621e-46` |
| coupling-subtracted full even-sector bound | `> 1.1579e-17` | `> 1.1579e-17` |
| K1 comparison with `2.27e-17` | PASS | PASS |

The stored balls justify these outward decimal summaries. Each matrix
contains the quadrature radius in every entry and carries series and Arb
arithmetic errors. The exact dyadic midpoint/radius lower triangles,
preassembly budgets, LDL decisions and results were downloaded from the
durable volume and their hashes checked against each manifest. RUNS.md
records the app IDs, paths, terminal states and hashes.

The independent full-sector bound follows from
`min(1.158e-17, beta-eps_D)-eps_B`, with the interval comparison against
`1.1579e-17` passing in both runs. This is an enclosure-carrying numerical
step conditional on the explicit ordinary analytic bounds in §7, which
were reviewed here. Together with the reviewed reduction, it yields the
same lower bound for Q on real even functions. It supplies no independent
odd-sector numerical bound.

The result JSON's top-level `grade: measured` describes its midpoint
eigenanalysis; the separate LDL and `full_space_evidence` fields carry the
enclosure claim. Eigenvalue-string agreement is corroboration, not the
proof of the full-sector bound. These runs independently reproduce the
author's eigenvalue bracket and corrected endpoint, not every author GL
entry or its quoted `eps_Q_max`: their implementation was not inspected,
and a high-precision author matrix is not part of the supplied evidence.

## 6. Controls and lesions

| obligation | evidence and rationale | independent outcome |
|---|---|---|
| K1 | independent full even-sector bounds are below the supplied `2.27e-17` ceiling | PASS in both leading units; no Ritz value is used as a whole-form lower bound |
| K2 | DH coefficients on all integers, conductor 5, odd gamma factor, no pole, H=0 | PASS measured at both resolutions; negative Q and R witnesses, independent scalar agreement |
| K3 | ordinary support proof; complex, odd, constant and boundary tests | PASS measured in overlap and frequency representations at two cutoffs |
| in-band lesion | normalized constant f gives defect `1/32` at `2L-1/20` | PASS measured: nonzero defect recovered in both representations |
| one-prime sign lesion | admissibility alone cannot catch it | PASS measured: negating p=2 correction makes its per-prime envelope negative |
| dropped power | removing 4 changes the form on the window | PASS: shared inventory gate rejects it; measured constant-window defect is positive |

The brief's instruction that any mutant remaining positive proves a broken
pipeline needs a precise interpretation. An altered form can genuinely
remain positive. For example, reversing an out-of-band correction does not
break orthogonality. The proper failure is rejection of an invalid support,
envelope, or defining-coefficient claim. A positive eigenvalue alone is not
a lesion detector. These checks target the corresponding broken obligation.

K3 also has an independent frequency-side check on complex polynomial
windows with a squared endpoint taper, plus an odd window. Three integrations
by parts give `|F(t)| <= B/|t|^3`, where
`B=|f''(L)|+|f''(-L)|+integral |f'''|`. The omitted two-sided integral,
normalized by 2pi, is at most `||H||_infinity B^2/(5pi T^5)`.
The code measures finite integrals at two cutoffs and reports these tail
majorants. For the in-band constant-window lesion it uses the slower explicit
`2/(pi L T)` tail bound. Floating quadrature errors remain unvalidated, so
this check is measured rather than an enclosure claim.

For the constant window test, deleting the n=4 term changes the normalized
form by `log(2)*(1-log(4)/(2L)) > 0`. This is an exact derived expression;
its numerical value is independently reproduced below. The independent DH control also
checks the non-prime-power identity `Lambda_DH(6)=(1+kappa^2)log(6)`.

K2's reference uses `width=log(47)` and hence this hunt's half-width
`L=log(47)/2`, with 65 even Fourier modes. The target negative value near
`-0.3163` is old measured evidence, not a result of this review. A refusal
caused only by resource exhaustion will not count as a K2 pass.

At `b9a25ba`, the numerical lane reports a completed Modal K2 run: the
legitimate envelope gate returns no positive bound; forced-beta runs are
explicitly invalid-envelope lesions. That is a useful gate-rejection
control, not an independent validation of the whole enclosure pipeline.
This referee's two independent negative-witness and reduction checks pass
below, with their measured grade retained.

**Independent controls execution, source c65c66e:** Modal app
`ap-NhsIKRPPAvEgmNaQlKQZDY` completed the `controls` unit in 5.6466 seconds.
The reconstructed unpadded sine-16 sum is
`1.555252826719554395156823327133059661505079595438460442661392472215115356514794825835`;
the exact frozen sum includes the two constant paddings and passes the
independent moment/residual checks. These are measured results; the Arb
envelope check belongs to the leading units.

K3 gives zero computed overlap on all ten complex/odd/constant test windows
at every out-of-band frequency, including the boundary. The in-band
constant-window defect is `0.03125`. Both finite-frequency resolutions pass
their measured analytic-tail comparison. The one-prime sign flip gives a
negative envelope witness `-3.163357475943...`; dropping n=4 is rejected by
the shared support gate and gives defect `0.092580913162...` on the constant
test. All three lesions are detected. This is a measured PASS for K3 and
lesions, not a matrix enclosure. Manifest and result were downloaded from
the volume; their source/result hashes agree with the local artifacts.

For DH, Binet's formula at `3/4+it/2` bounds the archimedean deficit by
`1/(9t)+3/(2t^2) <= 1/t` for `t >= 15/4`. Thus the proposed H=0 reduction
uses `beta=log(5T/(2pi))-1/T-sum 2|Lambda_DH(n)|/sqrt(n)`, without borrowing
the zeta pole or prime-power-only coefficient support. The first independent
unit `dh512` passes: Q on the recovered witness is `-0.31630285307629097`,
R is `-0.7314173097418135`, and scalar adaptive evaluation gives
`-0.7314173097417971`. The negative beta also blocks a positive whole-form
bound. This is measured negative-witness evidence, not just a resource or
undecided-enclosure rejection.

The final `dh768` unit also passes: Q is `-0.31630285307558303`, R is
`-0.7314173097420369`, and the scalar adaptive value is
`-0.7314173097419605`. Both resolutions recover the large negative witness
and refuse a positive bound. Their saved witness vectors and result hashes
were checked against volume readback. No positivity inference relies merely
on the runner's hardcoded `positive_result: false`: the acceptance gate
requires the observed negative Q and R values, domination, and scalar/matrix
agreement. K2 is a measured PASS, not an interval proof of the DH integrals.

### Supervisor's later L=1.19 evidence update

The supervisor reports that app `ap-mucAZVkQ7RThKhLbUB9CuN` stopped, with
nine unit JSON objects and `stageA_L119_reduced.json` on volume
`oob-envelope-stages`. At N=360, T=500, the midpoint eigenvalue is reported
as `5.775648793894534e-48`; interval LDL has `n_neg=null`,
`undecided=306`, and no quadrature, tail, or coupling bounds.

Disposition: **UNRESOLVED, measured midpoint only. No support-2.38 positivity
result.** This is the supervisor's evidence, accepted as reported; no Modal
retrieval or reducer was run by this referee. It changes neither the L=0.8
endpoint objection nor the outstanding independent checks.

**New reporting defect at `b9a25ba`:** the Stage A discussion says the
published upper bounds at L=1.1 and L=1.2 bracket the floor at L=1.19, and
that the reduced value must lie between them. This does not follow.
Monotonicity and an upper bound U at L=1.2 do not imply
`lambda*(1.19) >= U`. Only the larger-window infimum itself supplies a
lower comparison, not its upper bound. The L=1.1 upper bound does give a
necessary upper ceiling on a valid L=1.19 lower bound. Remove the claimed
two-sided bracket and the words asserting necessity of lying between the
two upper bounds. No contradiction with the reported midpoint is claimed.
**Repair accepted at f779b27:** the final numerics text keeps only the
one-sided ceiling and explicitly withdraws the false bracket. The independent
L=4/5 verdict does not settle L=1.19.

## 7. Independent numerical budget derivation and execution

The live consumer is the same 96-mode claim. There is no general framework.
`independent.py` contains the implementation; `run_modal.py` dispatches
single units only. The formulas below are ordinary derivations supporting
the verifier. Both leading units now carry their interval evaluations;
numerical agreement does not replace these analytic derivations.

For a sine kernel of degree D use weights
`a_j=sin(pi(j+1)/(D+2))`, `j=0,...,D`, and normalized correlations rho_k.
At this window, p=2 has two low moments and p=3 has one. Put

    u=log(2)/(sqrt(2)*rho_1), v=log(2)/(2*rho_2),
    M2=(v+sqrt(v^2+8u^2))/2, cos(theta2)=-u/M2,
    M3=log(3)/(sqrt(3)*rho_1), theta3=pi.

Two equal atoms at plus/minus theta give the required low coefficients
after convolution with the nonnegative sine kernel. High cosine
coefficients are `2 M_p rho_k cos(k theta_p)`. Compare each exact rational
frozen coefficient with that construction, and charge the L1 difference
against the frozen constant's slack. No sampled nonnegativity is used by
the proposed zeta enclosure path.

For transforms use the spherical-Bessel power series, with term ratio
`-x^2/[2(k+1)(2n+2k+3)]`. After its absolute ratio is below 1/2, bound the
uncomputed tail by twice the absolute next term. Seed two consecutive high
orders with such balls and recur downward. The pole uses the same series
with positive signs at x=L/2. There is no floating input snap or unbounded
recurrence seed error. A separate `j0=sinc(x)` overlap check is included.

For panels of width h=1/2 choose rho=1+sqrt(2). The ellipse has imaginary
height 1/4 and real extent h/sqrt(2). The digamma arguments have real part
at least 1/8. From
`psi(z)=-gamma-1/z+sum_{k>=1} z/[k(k+z)]`, a conservative majorant follows
from `|psi(z)| <= 1+8+2|z|`. The program uses `|z| <= T+2`.

If an integrand has ellipse bound M, Chebyshev coefficient bounds and
Lobatto aliasing give interpolation error at most
`4 M rho^-q/(rho-1)`. Integrating over a panel gives at most h times this
quantity. Each matrix entry gets the sum over all panels as an actual
radius. This is Clenshaw-Curtis, independent of the authors' Gauss rule.

For tails let `n0=2N` and

    a_n=sqrt(2L(2n+1))*(LT)^n/(2n+1)!!.

The ratio `a_(n+2)/a_n` has a decreasing geometric majorant r after the
cut. Thus `sum_tail a_n^2 <= a_n0^2/(1-r^2) = U`. Completeness gives
`sum_lead |F_n(t)|^2 <= 2L`. With `K=(T/pi) max_real |a-P+H-beta|`,

    eps_D <= K U,
    eps_B <= K sqrt(2L U) + 2 sqrt((L+sinh L) V),

where V bounds the squared pole tail using the same majorant with x=L/2
and an extra factor exp(L/2). The even pole is positive in the tail block.
These are alternative operator-norm bounds to the author's Gershgorin/Schur
constants. The two independent-quadrature executions close that implication.

The real archimedean multiplier is monotone in |t|, by differentiating its
convergent digamma series. Its absolute value on [0,T] is bounded by the
two endpoints, giving a sharper real-axis budget than the ellipse budget.

The verifier records the enclosed matrix before LDL, then both shifted
decisions, eps_Q, eps_D, eps_B, and an outward-safe full-space endpoint.
Failure or uncertainty at any gate remains inconclusive. Both independent
resolution units completed and passed before the numerical verdict changed.

## 8. Approved execution gate

The supervisor approved the exact five bounded Modal units in `RUNS.md`,
sequentially with a $0.15 allowance and a stop on first failure or inconclusive
gate. RUNS.md now includes a conservative derivation: CC degrees 160 and 192
give matrix quadrature errors below `2e-49` and `2e-61`. The remote units
check and save their actual budgets before assembling the matrix. This
resolves the degree-selection concern analytically and now by both Arb
executions. All five units completed with gate true; every app is stopped,
all required artifacts are durable and read back, and there were no failures,
inconclusive gates or reruns. See RUNS.md for the complete execution record.

Remaining scope limits: the author GL implementation and its exact quoted
quadrature radius were not independently audited; this review proves the
corrected L=4/5 result through the new CC route. Symbolic steps remain
ordinary reviewed derivations. K2/K3/lesions remain measured controls. The
prior-art survey retains the source-verification limits noted in §4.
At L=1.19, unresolved interval signs and absent quadrature, tail and coupling
bounds still block any whole-form positivity verdict. No new paid unit is
requested by this completed review.

1. **PASS, ordinary derivation:** the support lemma holds for complex and odd L2 functions, including frequency 2L; the pole term is unchanged (§2).
2. **PASS with stated scope, ordinary derivation:** Q >= R_H and the finite-cosine reduction survive; tail constants and quadrature must be recomputed (§3).
3. **FAIL as written, repairable proof details:** the all-N cosine estimate exceeds its valid range; the general measure class lacks an analytic-strip hypothesis (§4).
4. **UNRESOLVED, numerical claim:** the 96-mode enclosure has not been independently executed; the displayed full-space endpoint omits the nonzero coupling subtraction (§5).
5. **UNRESOLVED, controls:** reported K1 is consistent; independent K1/K2/K3 and planted-lesion executions await supervisor approval (§6).

# Independent referee review, 2026-09-27

Primary verdict: **incomplete, with the independent numerical enclosure and
controls still missing**. No counterexample to the finite-cosine reduction
was found in this analytic pass. The numerical conclusion is not promoted.

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
| Zhu | [arXiv:2608.24827v2](https://arxiv.org/html/2608.24827v2), §§1–5 and parity statement | primary-source convention and reduction check |
| DH normalization and old negative control | `hunts/rogue_frontier/weil_trunc/SOURCE.md` §4 and `dhneg_log.md` in this checkout | rival definition and reproduction target |

The later theory revision fixes two earlier defects: it allows an empty
positivity interval, and it assumes a uniform bound on component sizes in
Proposition 2.2. Those repairs are not charged against the current version.
The final readback added no change to the theory RESULTS text or the L=0.8
endpoint claim. It did add the caveats and numerical status changes below.

No theory, numerics, or rival implementation was read or imported. Only their
prose and result data were read. The new implementation shares python-flint
with the numerical lane, so it is independent in construction and
quadrature, not in its arithmetic library. This is a separate model-family
review; model independence alone is not evidence of correctness.

`git fetch origin` completed. The advertised research-session `list_sessions`
tool is not exposed here; read-only Orca terminal listing and git worktree
listing confirmed the sibling lanes. No messages, code, or state were
written to those lanes. All new files are in this referee scope.

**No numerical computation, test, verifier, reducer, or build has run in this
review.** Source reading, git inspection, data extraction, and file writing
are the only local operations. Numerical code below is prepared, unexecuted.
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

**PASS as an ordinary analytic reduction for the finite-cosine witness;
execution-level validation remains UNRESOLVED.**

## 4. Proof details requiring correction

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

## 5. Numerical claim at L=4/5

The target is the exact rational `sine:16` witness, `T=100`, and the first
96 even Legendre modes. A different basis of the same size would usually
be a different Ritz problem, so this review keeps the subspace and changes
the quadrature and transform evaluation instead.

The inspected author control JSON reports:

| quantity | reported value or decision | referee status |
|---|---|---|
| S | `388813211679889/250000000000000` | frozen exact witness; independent proof prepared |
| leading shift `1.158e-17` | positive pivots | reported, not replayed |
| leading shift `1.1585e-17` | one negative pivot | reported, not replayed |
| largest quadrature error | about `5.764e-44` | reported, not independently bounded at this value |
| tail deviation | about `2.757e-95` | reported, independent alternative bound prepared |
| coupling | about `3.030e-44` | nonzero; must be subtracted |

Numerics RESULTS lines 17–20 and 22–24 assert the exact full-space endpoint
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

The new implementation encloses the same frozen witness with a two-atom
kernel decomposition, reassembles the same 96-mode form, and tests both
reported shifts. It uses its own, deliberately larger, quadrature error
bound. It cannot confirm the author's exact quoted quadrature radius merely
by obtaining the same final sign. The distinction will be retained in the
post-run verdict.

## 6. Controls and lesions

| obligation | current evidence | required independent execution |
|---|---|---|
| K1 | reported full-space bound is below the supplied `2.27e-17` ceiling | compare the independently obtained full-space bound, not a Ritz value used as a lower bound |
| K2 | unfinished at ed52a32; b9a25ba reports a Modal gate-rejection control, discussed below | reconstruct DH coefficients on all integers, conductor 5, odd gamma factor, no pole, H=0; reproduce the negative witness and evaluate the reduced form on it |
| K3 | ordinary support proof passes | deterministic random complex step functions, an odd step function, endpoint and every H frequency; compute exact overlap integrals numerically |
| in-band lesion | normalized constant f gives defect `1/32` at `2L-1/20`, by direct overlap | recover that nonzero defect |
| one-prime sign lesion | admissibility alone cannot catch it | negate p=2's correction and find failure of its per-prime nonnegative polynomial |
| dropped power | removing 4 changes the form on the window | fail the prime-power inventory gate and detect the missing time-domain shift |

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
its numerical evaluation is still pending. The independent DH control also
checks the non-prime-power identity `Lambda_DH(6)=(1+kappa^2)log(6)`.

K2's reference uses `width=log(47)` and hence this hunt's half-width
`L=log(47)/2`, with 65 even Fourier modes. The target negative value near
`-0.3163` is old measured evidence, not a result of this review. A refusal
caused only by resource exhaustion will not count as a K2 pass.

At `b9a25ba`, the numerical lane reports a completed Modal K2 run: the
legitimate envelope gate returns no positive bound; forced-beta runs are
explicitly invalid-envelope lesions. That is a useful gate-rejection
control, not an independent validation of the whole enclosure pipeline.
This referee's own negative-witness and reduction checks remain unrun.

For DH, Binet's formula at `3/4+it/2` bounds the archimedean deficit by
`1/(9t)+3/(2t^2) <= 1/t` for `t >= 15/4`. Thus the proposed H=0 reduction
uses `beta=log(5T/(2pi))-1/T-sum 2|Lambda_DH(n)|/sqrt(n)`, without borrowing
the zeta pole or prime-power-only coefficient support. This derivation has
not yet been numerically checked.

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

## 7. Independent numerical budget derivation, unexecuted

The live consumer is the same 96-mode claim. There is no general framework.
`independent.py` contains the implementation; `run_modal.py` dispatches
single units only. The formulas below are ordinary derivations supporting
the proposed verifier and have not yet been checked numerically.

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
constants. They prove the same two-block implication if the execution closes.

The real archimedean multiplier is monotone in |t|, by differentiating its
convergent digamma series. Its absolute value on [0,T] is bounded by the
two endpoints, giving a sharper real-axis budget than the ellipse budget.

The verifier records the enclosed matrix before LDL, then both shifted
decisions, eps_Q, eps_D, eps_B, and an outward-safe full-space endpoint.
Failure or uncertainty at any gate remains inconclusive. The two independent
resolution units must both complete before declaring the reproduction done.

## 8. Approved execution gate

The supervisor approved the exact five bounded Modal units in `RUNS.md`,
sequentially with a $0.15 allowance and a stop on first failure or inconclusive
gate. RUNS.md now includes a conservative derivation: CC degrees 160 and 192
give matrix quadrature errors below `2e-49` and `2e-61`. The remote units
check and save their actual budgets before assembling the matrix. This
resolves the degree-selection concern analytically, not yet by execution.
Until the outputs exist, the numerical and control verdicts stay UNRESOLVED.

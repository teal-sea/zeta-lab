# CLAIMS — the ledger

Every claim this run touched, whether the run generated it or the repository
already carried it. A claim with no disposition is an unfinished claim, not a
true one.

## Disposition vocabulary

| disposition | meaning |
| --- | --- |
| REJECTED | attacked and destroyed; the negation is now the better bet |
| KNOWN | true, and already in the literature or already in this tree |
| TRIVIAL | true, and follows immediately from a definition |
| MALFORMED | not a statement with a truth value as posed |
| INCONCLUSIVE | attacked, still standing, but the attack was not decisive |
| EMPIRICALLY SUPPORTED | measured, with controls, at floating precision |
| RIGOROUSLY COMPUTED | every step carried an enclosure (`zeta/rigor.py` only) |
| FORMALLY VERIFIED | kernel-checked by Lean with zero `sorry` |
| NOVELTY UNRESOLVED | survives attack; prior-art search inconclusive |
| SURVIVOR | survives attack, controls, replication and prior-art search |

"The director thinks this is correct" is not a disposition and may not be used.

## Ledger

Each entry: ID → origin → generating context → dependencies → evidence →
counterexample attempts → controls → replications → knownness → formal status →
objections → confidence → disposition.

*(entries are appended by the run; see `docs/25-the-director-run.md` for the
narrative and `GRAVEYARD.md` for what died)*

---

### Repository claims put on trial

**C-RIG-01** — *"A nonzero `proven_sign` is a proof."* (`zeta/rigor.py`)
origin: repository, standing · attacked by: skeptic (ball arithmetic), then
reproduced by the director · evidence against: `np.float32(21.02203941345215)`
→ `proven_sign = −1`, true `Z = +2.56e-7`, enclosure 3.6e-46 wide excluding the
truth, **both backends** · controls: 46 well-typed abscissae × 3 precisions ×
2 backends showed 0 violations, so the hole is exactly the input path ·
replication: director, independently · knownness: n/a (implementation) ·
formal status: n/a · confidence: certain · **disposition: REJECTED as stated;
repaired, and the repaired contract is pinned by a regression test.**

**C-RIG-02** — *"`sign` is 1/−1 proven, 0 undecided, never guessed."*
evidence against: an unproven Fejér cutoff leaves the unproven-steps list non-empty
while `sign` is read off an enclosure that assumes the very step that failed ·
**disposition: REJECTED as stated; `sign` is now gated on the same flag that
gates `positivity_proven`, pinned by a regression test.**

**C-RIG-03** — *"Two independent implementations must produce overlapping
enclosures."* · evidence: the two backends share `_exact`, the contour and
subdivision policy, the grid policy, and the final interval summation of
`S(T)`/`N(T)`; C-RIG-01 is a live demonstration that a shared-input fault is
invisible to the check · **disposition: INCONCLUSIVE → narrowed. The check is
real for the ζ and log Γ evaluators and does not cover the pipeline; the claim
is now stated at that scope.**

**C-LI-01** — *"The Sturm branch is exact: the polynomial converts to ℚ[X]
without error."* · evidence against: `X² − 2X + (1+10⁻⁴⁵)` returns
`hyperbolic=True, n_real_exact=1, agree=True` at dps 15 and 20 ·
**disposition: REJECTED; repaired (Sturm now runs on the input coefficients)
and pinned by the pre-existing near-miss control, which now discriminates.**

**C-DET-01** — *"`online_list_is_complete` checks the cached list against an
independent count."* · evidence against: the reference is the same technique on
a grid 1.4×–1.8× coarser than the one that produced the list · found
independently by two investigators · **disposition: REJECTED; a genuinely
independent strip-count route added, and the cheap route now reports
`independent: False` in data.**

**C-DET-02** — *"The detector quantifies the violation (1.3e-14)."* · evidence
against: end-to-end through the module's own pipeline the recovery error is
92.8 % · **disposition: REJECTED as a headline; true only when the ordinate is
supplied independently, which is now stated where the claim is made.**

**C-LI-02** — *"`li_positivity_scan` reports whether λ_n is positive."* ·
evidence against: on `method="zeros"` the column is structurally True for every
n · **disposition: REJECTED for that route (a control with no power);
`can_report_negative` now says so in data.**

**C-SHIFT-01** — *"Any coefficient functional is blind to the position of the
critical line by construction."* (`docs/24` §6, `hunts/README.md`,
`localpos.py` docstring **and** `provenance_report()`, `CORRECTIONS.md` §4) ·
attacked by: an explorer, then a skeptic tasked with destroying the explorer,
then a prior-art search · evidence against: mis-cited (`docs/18` §6 says
*ordinate*); premise false (`a_n ↦ n^δ a_n`); universal refuted in-tree by
`criteria.py` face 1 (Titchmarsh 14.25(B)/(C)) · **disposition: REJECTED.**

**C-SHIFT-02** — *`c_p(ζ(·−δ)) = 2x/(1+x)`, `x = p^{δ−½}`; `c_p ≤ d` exactly
when `δ ≤ ½`.* · replication: recomputed by a second investigator from
definitions, not importing the first's code; agreement to 1e-15 · knownness:
**this is the Selberg-class Euler-product axiom's `θ < ½` (Conrey–Ghosh 1992)
and the Jacquet–Shalika bound, stated as sharp by Sarnak** ·
**disposition: KNOWN. Correct, useful in-tree, not new.**

**C-SHIFT-03** — *"θ(f) = abscissa of the partial sums of the coefficients of
`1/f` equals `sup Re(zeros of f)`, for general f."* (produced *by this run*)
· attacked by: skeptic and knownness independently, with different
counterexamples (`1/(1−2·2^{-s})`; `exp(2^{-s})`) · **disposition: REJECTED —
false as an equality. The ζ case (Titchmarsh 14.25) is what survives, and it
needs analytic continuation plus a vertical growth bound on `1/f`.**

**C-LOCPOS-01** — *"`gate` reports PASS/FAIL, with the truncation bound cleared
before a FAIL is spoken."* · evidence against: at `p = 2, δ = 0.49` the reported
"bound" 2.52 understates the actual error 15.0 by 6×; the gate returns FAIL with
named witness primes on `δ ∈ [0.4877, 0.5]` where every place satisfies the
bound, and PASS above `δ = 1` where `c_p = +∞` · **disposition: REJECTED;
repaired to three regimes (summable / boundary / divergent) with the hunt's
recorded verdicts unchanged.**

**C-WEIL-01** — *`W(h) ≈ 8.86e-18` for the near-tight Gaussian, enclosure
~1e-51 wide.* · replication: **blind** — statement only, package forbidden —
reproduced to 43 digits with an independently built Arb enclosure of radius
1.600e-51 · controls: prime tail beyond `n_max = 2·10⁵` bounded by 3.0e-79, so
the value is converged and not a truncation residue; agreement with an
independently computed zero-side sum improves with precision as a real quantity
must · **disposition: RIGOROUSLY COMPUTED, and now independently replicated.**

**C-LEAN-01** — *`lean/` builds with zero `sorry`s.* · replication: elan and
Mathlib installed from nothing on a cold machine; 8715 jobs; every `sorry`
string is prose about the rule · **disposition: FORMALLY VERIFIED (as a build
claim).**

**C-R3-01** — *"The centre needs `nExp` raised, and that trade is the one
genuinely unresolved thing in rung 3."* (`HANDOFF.md`) · evidence against: the
box width is bit-identical under `nExp ∈ {16,20,24,28}`; the floor is the κ
enclosure's 6e-7 width; and the centre could not have passed at **any**
parameters because `normBound` counts the inflation radius twice where the plan
budgeted it once (`2r_c = 7.47e-4 > ε′ = 5e-4`) · **disposition: REJECTED; the
corrected diagnosis and a configuration with ≥1.1× margins are in `docs/25` §4.3.**

**C-R3-02** — *A plan with ≥10 % headroom exists at ~130k terms and unchanged
literal sizes.* · evidence: mirror measurements, margins 1.164 (centre), 1.139
(big box), ≥10× (grid cell) · caveats: 26/104 grid sites, 11/110 big boxes all
on one edge, one re-planned box · **disposition: EMPIRICALLY SUPPORTED, pending
the low-σ edge measurement named in `docs/25` §7.**

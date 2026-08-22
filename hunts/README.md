# `hunts/` — exploratory studies

A **hunt** is an exploratory study: a scoped directory where an agent or a
person pursues one specific idea, with the understanding that most such
ideas fail.

`hunts/` is the one place in this repository where a claim can be written
down before any control has been run against it. So the classification is
explicit:

> **A hunt is exploratory. Nothing in `hunts/` is a result — not a result,
> and not evidence.**

Per `harness/README.md`, the admission rule for a *department* is
**no department without a battery** — work whose claims nothing in this tree can
falsify is not a department; it is exploratory, and exploratory work belongs
where nobody will mistake it for a result. That place is here.

A hunt can never become a department by growing, for the reason `ROADMAP.md`
records for `dossier/`: a hunt's negative controls are the *zeta*
department's, and a department whose battery belongs to another department
is not a department. A hunt borrows the zeta battery. That is the correct
relationship, not a deficiency — but the battery does have to actually be
invoked.

## What a hunt may and may not do

| May | May not |
|---|---|
| build its own instruments under `hunts/<name>/` | modify `zeta/`, `ontology/` or `harness/` without explicit permission |
| record raw measurements in its own `results*.json` | write a verdict into `README.md`, `ROADMAP.md` or `HANDOFF.md` as an established finding |
| use the word *measured*, *observed*, *consistent with* | use *certified*, which `zeta/rigor.py` owns |
| propose a candidate for the funnel or the battery | promote its own claim |

A hunt that wants its claim to count takes it through the battery
(`docs/doors/refute.md`) or the funnel (`docs/doors/discover.md`). Those are
the two routes that can say "yes", and neither of them is the hunt itself.

## HuntSpec (new hunts, from 2026-08-11)

A hunt opened after 2026-08-11 carries a **HuntSpec** — a fenced contract
block in its `MISSION.md` stating the question, the frontier, the dead
routes, the non-model oracles allowed to assign truth, the kill conditions,
and what its agents may and may not do. Format, rules and the validated
template: `hunts/HUNTSPEC.md`. Existing hunts are not retrofitted;
`tests/test_huntspec.py` validates any block that exists. The primitive is
on probation — see the spec page's terms.

## The standing checklist

Before a hunt's finding leaves `hunts/`, it must have survived the four
control roles — and the checks are the ones the tree already owns:

1. **Rival.** Does the claim also hold for a function that shares the
   structure and violates RH? `zeta.epstein.battery`. Note the trap below:
   if your test set *is* the rival set, you have measured your own selection
   criterion.
2. **Decoy / surrogate.** Does a matched null with no arithmetic in it
   reproduce the effect? `zeta.surrogate`, `NULLCONTROLS.md`. `ROADMAP.md`
   records the calibration that matters here: against a null of random
   non-factoring sequences, Davenport–Heilbronn sits at the **27th
   percentile** — typical, not exotic. Anything claiming a factorization
   effect must beat that null.
3. **Lesion.** Does the detector notice a violation planted on purpose, and
   can it tell that planted violation apart from the claimed signal? If it
   cannot, the detector is measuring the plant.
4. **Precision response.** Does the effect move when the approximation
   improves? `ROADMAP.md`'s standing rule, earned three times: **an artifact
   does not respond to added precision; a real quantity does.**

## Case log

### Hunt #67: what the `min(dps, 20)` cap costs, measured (`dps_cap/`)

**Status: probe, complete.** At `0.8 + 85.7i`, `epstein_completed` at the
capped `dps = 20` returns `3.1e-33` where the converged value is `1.6e-58` --
a factor of `1.9e25` and not one correct digit. The error floor sits near
`1e-(D+13)`, so nothing correct can appear below `D ~ 46`; the sweep puts the
crossover there exactly (D=40 entirely floor, D=50 the first row with correct
digits). `D = 60` buys about 16 real digits, not 60, because the cancellation
costs roughly 44 of them. `zeta/epstein.py` still caps three interfaces at
`dps=min(_d, 20)` (lines 1092, 1126, 1142), so a caller asking for 60 gets 20
and `count_zeros_box`'s integrality check passes on the noise.

Landed 2026-08-21 as the union of five concurrent 2026-08-14 runs that all
wrote this directory and none of which merged; see the provenance header in
`dps_cap/README.md`. Nothing here is evidence about zeta or RH: it is a
measurement of an implementation at a single point.

> **Renumbered twice.** These two opened as #35 and #36 from a branch
> 101 commits behind `main`, where both numbers were taken. They were
> renumbered to #49/#50 on 2026-08-18, and `main` took those two (plus
> #51, #52, #55-#57 and #59) before this branch landed. They are #60
> and #61. The directories `lambda_dh_bounds/` and
> `prime_zeta_rightmost/` are unchanged and are the stable references.

### Hunt #61: two-sided bounds for the de Bruijn-Newman constant of Davenport-Heilbronn (`lambda_dh_bounds/`)

**Status: closed (2026-08-16), gate verdict publication candidate; hardened
2026-08-18, verdict unchanged.** The bracket, in the wide frame of
Rodgers-Tao and Polymath 15:
0.2304 < Lambda_DH <= 0.7696992583210755065522 (narrow frame: 0.0576 = 36/625
to 0.19242481458026887663805), ratio 3.341. Lower side decided by
ball-arithmetic winding counts with a zero-shared-layer second witness; upper
side a decided strip constant fed to de Bruijn 1950 Theorem 13. The quotable
corollary, recognized after the gate closed and adversarially narrowed in
`SEPARATION.md`: **Lambda_DH > Lambda_zeta unconditionally** (0.22 from
Polymath 15 against the decided 144/625), the first strict order between two
such constants with both nonnegative. The gate cycle caught and preserved
three corrections: a factor-of-4 frame error (two normalizations live in the
literature, `FRAME.md`), the sigma_0 originality claim withdrawn after
Bombieri-Ghosh 2011 was retrieved and read (their exact abscissa 1.120362
displaces it), and one prose lemma (M2) recorded as a lesioned blind spot
rather than repaired. The 2026-08-18 hardening then took two of those back:
M2 is proved with decided constants (`M2-LEMMA.md`), and the upper bound
sharpened by the full factor 2.082 in-tree, from a phase obstruction in the
Euler products that reaches Bombieri-Ghosh's abscissa and decides it on both
backends (`STRIP2.md`); the superseded headline
(<= 1.6025374835598228 wide, <= 0.4006343708899557 narrow, ratio 6.955) is
kept beside the new one everywhere it appeared, and the lower side did not
move in any digit. Doc: `docs/29`. Full adjudication: `GATE.md`. Predictions
P1-P3 and P5 held; P4's census found nothing deeper below height 600. Nothing
here is evidence about RH.

### Hunt #60: the rightmost zeros of the prime zeta function (`prime_zeta_rightmost/`)

**Status: settled. The threshold is correct, the conjectures are false, and
the core is a rediscovery of published work: kill condition 2 fired.** The
hunt attacked the two conjectures posted on OEIS A107311 (2024-12-21), that
x* = 1.7286... (root of zeta(x) = 2) bounds the real parts of the zeros of
the prime zeta function P(s) = sum_p p^(-s) and of every prime-subset
series. It decided on both backends (python-flint arb at 350 bits and
mpmath.iv at dps 40, exact Fraction endpoint logic) the balance root
sigma_c = 1.779544653546994116445898786965... of P(sigma) = 2^(1-sigma),
x* = 1.728647238998183618135103010297..., the separation sigma_c - x* >
1/20, the margin P(x*) - 2^(1-x*) = 0.0169073772138... > 1/60, the subset
constant sigma_3 = 1.8252259560738457... with sigma_3 - sigma_c > 0.0456813,
and log2(69/(5 log 23)) = 2.1379035036560028... > 17/8. It wrote out both
halves of the threshold theorem with proofs (triangle-inequality wall;
Bohr-Kronecker-Rouche existence below it), ran the WP5 calibration control
(the same solver object, pointed at the zeta partial sums, reproduced 31
digits of the literature's x*), two lesions and a precision-response check,
and settled predictions P1-P4, P4 including a screen of sigma = 7/4 to
t = 1e8 whose global |P| minimum was about 0.010021 at t about 5.63e7, far
above the alignment budget.

**Then the prior art was found, and it owns the core.** Belovas, Cepaityte
and Sabaliauskas, *On the zero-free region and the distribution of zeros of
the prime zeta function*, An. St. Univ. Ovidius Constanta Ser. Mat. 33(2)
(2025) 27-44, Theorem 1: the same wall, the same constant to every digit
they print, the same triangle-inequality proof. Sepulcre and Vidal,
Carpathian J. Math. 38 (2022) 489-501 (preprint arXiv:1805.02041, 2018),
Theorem 4.3: the general characterization, strictly stronger than the
hunt's existence half, with Moreno's Geometric Principle (Compositio Math.
26, 1973) as the finite ancestor and the source of the aggregated-tail
device the hunt reinvented as its Lemma 2. `MISSION.md` kill condition 2
reads: "a literature source is found proving the sigma_c threshold for P,
in which case the finding is reclassified as a rediscovery and the OEIS
correction cites that source instead of this work." It fired. The
reclassification is done, in `hunts/prime_zeta_rightmost/PRIOR-ART.md`
(statement-by-statement ownership map, verbatim source texts, the worked
specialization) and in the rewritten `docs/30-prime-zeta-rightmost-zeros.md`,
which now leads with the prior art.

**What survives as the hunt's own**, and nothing beyond it: (a) the
line-by-line refutation of the two OEIS conjectures, since no source in the
literature engages that entry and the published wall does not by itself
refute Conjecture 1 (1.7795 is weaker than the conjectured 1.72864, and
Belovas et al.'s numerics stop at 1.6826, below x*), graded new as a
connection with zero new mathematics; (b) the unbounded tail-subset walls, {p >= p_k}
walled at or above log2(3 p_k / (5 log p_k)) via Rosser-Schoenfeld, so no
constant bounds the real parts across all prime subsets and Conjecture 2
fails for every replacement constant, graded new, small and elementary, and
the only mathematics here not located in print; (c) the constant sigma_3 and the
fact that a subset out-walls the full series by more than 0.045, a new
instance of prior-art theory; (d) the two-backend enclosures, rediscovery in
sharper form, the source printing 15 digits and noting that any precision
is available; and (e) one literature observation, that Belovas et
al.'s Conjecture 1, left open in their paper, is a corollary of Sepulcre
and Vidal Theorem 4.3, which neither paper cites. The steering lemma's
positive lower density in t is carried as an unverified lead, since the
Jessen-Tornehave literature was not searched.

**The lesson, which is the most transferable thing the episode produced.**
Two independent search failures, needing two different countermeasures, and
both reproduce on demand. The exact-phrase query "zeros of the prime zeta
function" is a literal substring of the Belovas et al. title and the engine
still does not return it: no arXiv preprint, a Sciendo/DOAJ venue outside
the sweep, and an image-scanned PDF that has to be downloaded and extracted
rather than fetched. The general theorem was missed for an unrelated
reason: it is filed under almost periodic functions, MSC 30B50/30D20, and
never names a prime, so no prime-zeta query can reach it, and it was
reachable only by searching for the device rather than the application.
Four independent searches returned nothing while two published papers owned
the result outright, which is the standing argument for
`ontology/knownness.py` defaulting to "the literature was not consulted".

**Disposition:** instruments retained; nothing promoted; the OEIS
correction drafts in `OEIS-CORRECTION.md` remain unposted; they cite Belovas
et al. for the threshold, which is what the kill condition required, and that
rewrite is done. Nothing here bears on RH: the zeros discussed are zeros
of P and of subset series in Re s > 1, not zeros of zeta.

### Hunt #56: make_context.py blind region on meta/ package (`r_2946de/`)

**Status: settled.** `scripts/make_context.py --check` does not detect public functions, classes, constants, docstrings, or new modules added under `meta/` (0/16 curated mutants detected, 0.0% detection rate; 0/32 public AST symbols detected, 0.0% detection rate), because `meta/` is structurally excluded from the hard-coded scan paths in `make_context.py` and produces zero diff in `CONTEXT.md` (exit 0). In contrast, in-scope positive controls in scanned directories (`zeta/`, `ontology/`, `harness/`, `docs/`) are 100% detected (4/4 caught). Measured on a 16-mutant curated battery and a 32-symbol exhaustive AST census in `hunts/r_2946de/results.json` and `RESULTS.md`. Nothing here bears on RH (`docs/08`).
### Hunt #59: test file naming sensitivity and boundary of make_context.py --check (`r_c35cd1/`)

**Status: settled.** `scripts/make_context.py --check` does not detect test files whose names do not match `test_*.py` (such as `tests/mutant_helper.py`, `tests/conftest.py`, or `tests/helper.py`), nor does it detect nested test files in subdirectories (`tests/fixtures/test_sample.py`, `tests/unit/test_unit.py`), non-Python test assets, or helper functions and length modifications within existing test files (0/22 non-matching specimens detected, 0.0% detection rate), because `test_counts()` uses a shallow `TESTS.glob("test_*.py")` and counts only AST function definitions starting with `test_` without tracking line counts for test files. In-scope test modifications (`test_` function additions, renames, and new `test_*.py` files) are 100% detected (3/3 caught). An exhaustive repository census shows 77 `test_*.py` files with 1852 test functions and one unindexed fixture asset (`tests/fixtures/rung3_ball_term_kernel.json`). Zero non-`test_*.py` Python helper files have ever been committed in repository git history across 79 historical paths. Measured on a 25-mutant curated battery in `hunts/r_c35cd1/results.json` and `RESULTS.md`. Nothing here bears on RH (`docs/08`).
### Hunt #57: make_context.py compiler/ unscanned boundary and detection blindness (`r_dc6e6f/`)

**Status: settled.** `scripts/make_context.py --check` does not detect public functions, classes, constants, docstrings, or module additions added under `compiler/` (0/17 curated compiler mutants detected, 0.0% detection rate; 0/37 public symbols detected across an exhaustive AST census, 0.0% detection rate), because `compiler/` is completely omitted from the scanned directory roots in `scripts/make_context.py` (`zeta/`, `ontology/`, `harness/`, `dossier/`, `docs/`, `scripts/`, `tests/`) and from `build_flat()`. Positive controls in scanned packages are 100% caught (5/5 detected). Evidence in `hunts/r_dc6e6f/RESULTS.md` and `results.json`. Nothing here bears on RH (`docs/08`).
### Hunt #55: make_context.py in-place helper renames and __all__ boundary (`r_7ad39f/`)

**Status: settled.** `scripts/make_context.py --check` does not detect in-place length-neutral private helper renames in modules that declare `__all__` (0/299 unexported private symbols detected, 0.0% detection rate), because `module_api` filters top-level definitions strictly by `ast.literal_eval(__all__)` and the file length remains unchanged. In non-`__all__` modules, detection is 100% (4/4 symbols caught). Any edit altering line count is 100% detected via the line-count tell. Zero length-neutral private-to-public helper renames have ever occurred in repository git history. Measured on a 25-mutant curated battery and a 305-symbol exhaustive census in `hunts/r_7ad39f/results.json` and `RESULTS.md`. Nothing here bears on RH (`docs/08`).
### Hunt #52: scope caveat: compiler verdicts rest on a hand-written model, not LLVM semantics (Alive2 absent) (`r_e2ee73/`)

**Status: settled.** Compiler refinement verdicts in `compiler/` rest on a hand-written pure-Python interpreter (`pymodel.refinement_i8`, rung 2) rather than formal LLVM semantics, because Alive2 (`alive-tv`, rung 3) is absent from this environment. The exposure of the hand-written model is bounded by an exhaustive two-backend cross-check against compiled Apple Clang binaries (`clang.exhaustive_i8`, rung 1) across all 10 fixtures (655,360 total evaluated points, zero mismatches). While the concrete Clang detector is blind to poison violations covering 50% of the domain (`nsw_flag_on_a_wrapping_shift`), the model detector captures poison and immediate UB at full declared power. An audit of unsupported IR constructs confirms that out-of-scope instructions safely raise `ModelUnsupported` rather than guessing. True LLVM-native refinement remains absent without Alive2. Evidence in `hunts/r_e2ee73/RESULTS.md` and `results.json`. Nothing here bears on RH (`docs/08`).
### Hunt #50: doc renaming without number change, and doc content drift (`r_c62e44/`)

**Status: settled.** `tests/test_docs_numbering.py::test_no_two_docs_share_a_number` enforces uniqueness of the leading 2-digit number (00..N) across `docs/*.md` filenames and detects collisions (smallest mutant: `05-a.md` and `05-b.md`), but does not detect a document renamed without its number changing when citations use bare references (such as `docs/08`), nor does it detect content drift or heading changes. Sibling test `test_every_full_filename_reference_to_a_doc_resolves` detects renamed documents only when un-updated full-name references exist in the tree. An exhaustive census across all 37 test files mentioning `docs/` confirms zero tests in the suite inspect document body content, validate H1 headings against filenames, or verify that citations match actual content. Measured on a 20-mutant battery in `hunts/r_c62e44/results.json` and `RESULTS.md`.
### Hunt #51: file-type boundary of the hunt reserved-word guard (`r_365c6c/`)

**Status: settled.** `tests/test_hunt_probe_discipline.py::test_no_hunt_claims_the_reserved_word` enforces an explicit suffix whitelist (`path.suffix.lower() in {".py", ".md", ".json"}`). Every file type outside this three-extension set passes unconditionally (40-specimen battery across 12 format categories in `probe.py`: 6/6 `.py/.md/.json` caught, 0/29 non-{py,md,json} caught). An exhaustive repository census shows 76 of 447 files (17.0%) under `hunts/` are currently unscanned, including 68 `.lean` proof files under `hunts/frontier_math/`. None of the 76 unscanned files contain the reserved word. Evidence in `hunts/r_365c6c/RESULTS.md` and `results.json`. Nothing here bears on RH (`docs/08`).
### Hunt #63: truncated Weil form positivity failure on Davenport-Heilbronn (`r_ac9ca3/`)

> **Renumbered 2026-08-20.** Opened as #45, which `r_233abe/` had taken
> two days earlier. `hunts/r_ac9ca3/` is the stable reference.

**Status: settled.** The first positivity failure of the Connes–van Suijlekom / Connes–Consani–Moscovici Galerkin truncation of the Weil quadratic form on Davenport–Heilbronn on the integer lattice $c \in [6, 60], N \le 128$ occurs at $(c, N) = (31, 60)$.

Integer cutoffs $c \le 30$ are strictly positive definite across all tested $N \le 128$ (and up to $N = 256$ at $c = 29, 30$). At $c = 31$, the even sector develops its first negative eigenvalue at $N = 60$, with rigorous Arb ball enclosure $\lambda_{\min} = -1.87393568857 \times 10^{-31} < 0$ (radius $\sim 3 \times 10^{-192}$) and exact dyadic Rayleigh quotient upper bound $-1.87393568857 \times 10^{-31} < 0$, while $N = 59$ is strictly positive with $\lambda_{\min} = +8.36504566170 \times 10^{-31} > 0$. The odd sector at $(31, 60)$ remains strictly positive (inertia $60$ positive, $0$ negative). The Riemann zeta control at $(31, 60)$ is strictly positive by 100 orders of magnitude: even inertia $(61, 0)$, odd inertia $(60, 0)$, $\lambda_{\min}(\zeta, 31, 60) = +4.82160175 \times 10^{-100} > 0$. The failure tracks the first off-line pair at $\gamma_{\text{off}} = 85.6993, \delta = 0.3085$: across $c \in [32, 60]$ the crossing band edge mean is $83.64 \pm 2.44$, and at $(31, 60)$ the zero-side dictionary decomposition proves the off-line quadruple ($-6.734989 \times 10^{-29}$) is the sole negative contributor, whose subtraction flips the form value positive to $+6.716250 \times 10^{-29} > 0$. Evidence in `hunts/r_ac9ca3/RESULTS.md` and `results.json`. Nothing here bears on RH (`docs/08`).
### Hunt #66: four arms salvaged off an abandoned branch (`r_f00e48/`)

**Status: settled.** `claude/riemann-hypothesis-research-ofds8s` ran a
wide-portfolio RH-adjacent campaign on 2026-08-17/18 and never landed. Four of
its five arms existed nowhere on `main`; they are now in
`hunts/rogue_frontier/`: `weil_trunc/` (23 files, 8 replication gates, a 27/27
conclusive-positive enclosure grid, and the Davenport–Heilbronn positivity
failure at `(c, N) = (31, 60)`), `sine_gram/` (exact finite-N engine,
`m_5(1) = 101/18`, `m_6(1) = 640/63`), `window_opt/` (RF-C003, the campaign's
one promoted claim), and `nyman_beurling/` (Baez-Duarte distances to
`N = 2048`, against `main`'s previous `N = 50`), plus the survey documents.
**1,717,013 bytes landed against ~58 MB on the branch**: 56 MB of regenerable
pickle and a stale `.ext_lock` stayed behind, and so did `fkappa/`, whose
`kappa = 2` table Hunt #65 had already adjudicated wrong. `LANDING.md` records
the subset so the gaps do not read as loss. **The defect the checking found:**
`REPRODUCE.md`'s headline command for RF-C003, the campaign's *only* promoted
claim, did not run — it named `functional.exact_F_quartic(1467, 1159)`, a
symbol that never existed under that name or that signature, so a reader
following the published recipe got an `ImportError`. The function is
`moments_polyeven_exact(OPT_Q)` returning `(m2, m3, F)`; `probe.py` now
recomputes `F(v*) = 2245228120295149280/3276332462159207451` from the landed
source and pins it against the landed document. Two further references were
repaired. **The one external corroboration:** `main`'s own Hunt #45
(`r_ac9ca3/`) reached `(31, 60)` independently, and the salvaged
`dhneg_scan.json` agrees with it digit for digit on the enclosed DH eigenvalue
(`-1.87393568857018838648…`, radius ~5.7e-208) and the zeta control
(`+4.82160175202313776…e-100`). **What it does not establish:** re-running an
arm's own code is not an independent check of it, and RF-C003 is entered in
`harness/departments/review_ledger.py` with a white-box outcome saying exactly
that, leaving `standing_reasons()` correctly reporting no blind attack — a new
open item, honestly created, not one closed. Two further arms (`erdos_scan/`,
`matchings/`, the latter claiming a kernel-checked Lean result) appeared on the
branch *after* the sweep that specified this landing and are unreviewed rather
than rejected. Evidence in `hunts/r_f00e48/RESULTS.md` and `results.json` (29/29
checks). Nothing here bears on RH (`docs/08`).

### Hunt #65: the conflicting kappa = 2 tables, adjudicated (`r_2ac05f/`)

**Status: settled.** Two directories carried a table of the same quantity, the regular coefficients `C_{2,i}` of Bian's pair-correlation form factor for the zeros of `xi''`, and disagreed at every index from 2 to 11: `hunts/higher_xi/C2_EXACT.json` (`1, -8, 24, -32, 64/3, ...`) against `hunts/rogue_frontier/fkappa/` corrected mode (`1, -4, 4, -16, 52/3, ...`), with conflicting diagnoses. **`higher_xi` is right.** A fourth derivation written for this adjudication and importing neither hunt — the identity `R_kappa = xi'/xi + D log Q_kappa` expanded in a formal Dirichlet word algebra, exact rationals throughout — reproduces `higher_xi`'s eleven values exactly, and reproduces the externally published Farmer-Gonek `kappa = 1` row (arXiv:0803.0425) exactly as its control, including the four forced zeros. The general defect, derived here and recorded nowhere else: the `x^1` coefficient of `Qhat_kappa = Q_kappa / L^kappa` is `kappa*g`, so **`C_{kappa,2} = -4*kappa`** (`-4, -8, -12, -16, -20` for `kappa = 1..5`), and Bian's Lemma 12 asserting a universal `-4` is the dropped `M(v_l)M(w_k)` weight `C2_PROVENANCE.md` names on thesis page 71. `fkappa` reimplemented the thesis code faithfully and found three real implementation defects in it, but carried Lemma 12's `-4` as an axiom, so its correction sits downstream of a larger error. **The control that would have caught it, measured rather than asserted:** planting exactly that defect in this hunt's probe leaves the Farmer-Gonek `kappa = 1` control passing and moves `C_{2,2}` to the published `-4`, while a one-factorial corruption of the pairing turns the same control red. The only externally anchored control either hunt ran has zero power against the defect that decided the dispute; the control with power is to compute `C_{kappa,2}` for `kappa = 1, 2, 3` and assert the values differ, i.e. an invariance claim needs a control that moves the variable the invariance is asserted over. Evidence in `hunts/r_2ac05f/RESULTS.md`, `results.json` and `fault_check.json`; outcome appended to `harness/departments/review_ledger.py`. Nothing here bears on RH (`docs/08`).

### Hunt #64: gap A of the lattice-extremality route is a forbidden constant (`r_b9552d/`, run 2)

**Status: not settled** (the gap stands), **and one thing settled inside it.** Second run of `r_b9552d`; run 1 is Hunt #46 above and its artifacts are preserved under run-tagged names. `LATTICE-EXTREMALITY-ROUTE.md` bounds the centre-gas row `J(T)` only for densities `rho >= 1/(2*pi)` (its gap A). Any single density-independent Cohn–Elkies certificate `g` (with `g >= f`, `ghat <= 0`) proving `J <= L = 0.11433003938654052` at every density is pinned exactly: `ghat(0) = 0`, `g(0) = -L/2`, `sup|g| <= L/2`, and `ghat` vanishing at every integer. The necessary condition `sup f <= L/2` **passes** with margin 3.04992 (`sup f = 0.0187431348` at `s = 6.3974` against `L/2 = 0.0571650197`), so the route is not excluded; a 3.05× planted inflation of `f` fires the test. But the Fejér family that closed gap B on `main` (`7efd506`) reaches `ghat(0) = 0` only at `c = 2*c2(0) = 1.6984559986`, where the bound becomes exactly `L` at every density (spread 6.7e-16), and admissibility caps `c` at `cos²(√2/2)(1+cosh 1) = 1.4698290125`: short by a factor **1.15554665**, with a frequency-domain witness `ghat(0.87493) = +0.0839055 > 0`. A quoted Paley–Wiener factorisation plus critical sampling makes `c·(sin(x/2)/(x/2))²` the only band-limited candidate, so the miss is the family's, not the ansatz's. Byproduct: the first sparse-side bound in this route, `J(T) <= 2*kappa(0) - 2*cos²(√2/2)(1+cosh 1) = 0.5715840116` at **every** density, `4.99942 × L`. Evidence in `hunts/r_b9552d/RESULTS.md` and `results.json`. Measured, double precision, no enclosures. Nothing here bears on RH (`docs/08`).

### Hunt #49: zeta23ext root load, Retention.Aconst / c2 collisions across arms (`r_6f088d/`)

**Status: settled.** The root module load failure in `zeta23ext` was caused by 17 colliding declarations (including `Retention.Aconst` and `Retention.c2`) across `EForm`, `EForm2`, and `EForm3` all declared in the un-scoped `Retention` namespace. In Lean 4, importing modules with duplicate fully-qualified names halts elaboration with an environment collision. The collision is resolved by scoping arms into distinct sub-namespaces or importing only the active `EForm3` iteration, while mathematical duplication remains across the independent development arms.
### Hunt #47: the two-mode arithmetic, and the bridge nobody had named (`r_88dc5e/`)

**Status: settled.** `O9Assemble.lean` said the last step between the
kernel-checked table and O9 was "the arithmetic of the two modes". It was, plus
one prerequisite that was not on anyone's list. `O9Check2` decides a table in
the kernel's interval arithmetic; `O9Sound` proves both modes sound over the
reals in terms of `Retention.Qre` and `Retention.Qim`, which are integrals
against the window `g`; and the enclosure chain ended at `BandDual.Phi2`, which
is `s(z+√2) + s(z−√2)`. Those are two different definitions of the same two
numbers and **nothing in the package connected them**. `EForm3/O9Bridge.lean`
does: `Re Phi2 (s + iy) = Qre y s` and `Im Phi2 (s + iy) = −Qim y s` for
`y ≠ 0`, by closed forms on both sides and no new analysis.

With that, `EForm3/O9Modes.lean` turns the checker's `Bool` into the damage
bound. `dam_le_of_box` says a box `o9Box` accepts bounds `Dam` at every point
of it, `y = 0` included; the content is that `Iv.mem` is `lo ≤ 2⁶⁴·x ≤ hi`, so
each recorded comparison is one division away from the real inequality mode 1
or mode 2 wants. `dam_le_box0` instantiates it at the **first recorded row** at
the interior point `(23/4, 1/8)`, with the verdict taken from `o9_box_chunk0` —
the kernel's own `decide +kernel` — rather than from a fresh decision. Zero
sorrys, axioms `[propext, Classical.choice, Quot.sound]`.

The two dead-weight lemmas are **gone**. The use-site survey run bbe76b9a
reported was re-run rather than trusted, over the whole repository:
`O9Seam.r_comp_mem` had exactly one use site (`Retention.rIv_mem`) and
`rIv_mem` had none. Both are deleted, `r_comp_mem'` carries the corrected
statement, and nothing was reproved.

**What this does not close.** O9 soundness is not closed and the hunt does not
claim it is. `dam_le_of_mem_walk` bounds `Dam` at points of boxes the table
records; the retention obligation needs the whole window, and nothing in Lean
yet says the recorded boxes **cover** `[28/5, 60] × [0, 1/2]`. That covering,
and the assembly into the form `Gap`/`FarField` consume, are what is left.

Also recorded, because it cost this run time: `simp only [o9Box]` and
`rw [o9Box]` both hang on a `whnf` heartbeat timeout — unfolding the checker
asks the elaborator to reduce `rIv b.sLo …` symbolically through the entire
leaf layer. `unfold o9Box at hb`, then `split at hb`, then one definitional
`have` does the same job instantly.
### Hunt #48: Erdős–Kac priced, and one of the two routes is blocked (`r_8c3b94/`)

**Status: settled. A mapping run, not a proving run.** Two earlier runs left
Erdős–Kac as prose ("a real project", "needs either moment control to all
orders or a formalised Berry–Esseen route", "out of reach and should be said
so"). None of that is a coordinate, so this run priced both routes against
what Mathlib actually carries at this repository's pin, resolving every claim
by compiling 43 `#check`s rather than by grep. `Probe.lean` in the hunt
directory is that file; it exits 0 and is imported by nothing.

- **The moment method: ~2,400 to 3,700 lines**, ~1,800 to 2,600 of them novel
  mathematics. Every obligation is something somebody knows how to write.
  Hardest step is reindexing k-tuples of primes by the set-partition of the
  index set: at k = 2 that is `rcases eq_or_ne p q` and costs nothing, uniform
  in k it has no Mathlib support at all.
- **The characteristic-function route is blocked, not merely dearer.** It
  needs the fundamental lemma of sieve theory. Mathlib's sieve
  (`BoundingSieve`, `siftedSum_le_mainSum_errSum_of_upperMoebius`) is
  **upper-bound only**; the phrase "fundamental lemma" occurs once in that
  file, in a docstring. No Lean formalization of it exists.
- **The reason, and the finding worth keeping**: the moment route needs only
  k-fold products, so its arithmetic error is `π(y)^k`, polynomial, and it
  tolerates `y = N^{1/2k}`, which keeps `log log y ~ log log N`. The
  characteristic function needs all orders at once, so its error is
  `2^{π(y)}`, which forces `y` down to about `log N`, at which point
  `log log y` is no longer asymptotic to `log log N` and the theorem's own
  normalisation dies. The route closes on itself. Derived here, not looked
  up, and flagged as such.
- **A prerequisite that looked live is dead.** `hunts/r_0339c1/RESULTS.md`
  treats tightening the Mertens band `16` as the lever. True for the
  Hardy–Ramanujan constant `275`; **irrelevant to Erdős–Kac**, which uses the
  band only as an `O(1)` shift divided by `√(log log N)`. Mertens with its
  constant is not needed, and this tree does not have it.
- **Also measured, because a miss is a result**: Mathlib at rev `51e6992e`
  has an i.i.d.-only CLT and Lévy continuity, and has **no** Berry–Esseen, no
  Lindeberg, no method of moments, no Carleman, no Gaussian moment beyond the
  second, no Mertens theorem of any kind, and no Kubilius model.
  `Nat.stirlingSecond` exists with recurrences and no combinatorial content.
  Fourteen named misses in `results.json`, each with the term searched for.

**Disposition:** coordinates, not a claim. The recommendation is Route A or
nothing, with the **k = 4 central moment as a single bounded first file** and
a stated stop condition (over ~600 lines and the estimate has failed at the
step that matters). Three sub-obligations are wanted upstream independently of
whether Erdős–Kac is ever attempted: a triangular-array CLT, the Gaussian
moments, and a method-of-moments theorem. Nothing here bears on RH.

### Hunt #44: what the O9 numerator fields actually enclose (`r_938ab4/`)

**Status: settled, and the two fields answer differently.** Hunt #42 left the
question of whether `reNum_mem` and `imNumOverY_mem` pin `Re num` and
`Im num / y` or merely the shapes the interval arithmetic computes.
`Zeta23Ext/EForm3/O9NumShape.lean` settles it. **`reNum` encloses `Re num`
unconditionally**: once `SQ2_mem`, `SINC_mem` and `COSC_mem` instantiate the
three constant leaves the computed shape *is* the real part, at every point of
every box, `y = 0` included, with no hypothesis beyond the ones the leaves
already carried. **`imNumOverY` encloses `Im num / y` only for `y ≠ 0`**, and
the hypothesis is necessary rather than incidental: `Im num` vanishes on the
real axis, so `Im num / y` at `y = 0` is `0` by Lean's division convention,
while the field carries `shcSmall` and therefore encloses the removable limit
— `2·cos(√2/2) + √2·sin(√2/2) > 0` at `s = π`. The disequality is stated as a
disequality, not hedged into a hypothesis. That asymmetry is the design
working: the removable branch exists so `y = 0` is an ordinary point, and it
can only be ordinary by enclosing something other than a quotient by `y`
there; what the run adds is that the something other is now named and pinned.
With both components identified, `qreIv_mem_phi2` and `rIv_mem_phi2` read the
two compositions back against `Phi2` itself. **Verdict on the dead weight:**
`O9Seam.r_comp_mem` and `Retention.rIv_mem` can be retired at no reproof cost
— `r_comp_mem` has exactly one use site (`rIv_mem`) and `rIv_mem` has none,
and the route built here goes through `r_comp_mem'` and `rIv_mem_box`
instead. They were shown unnecessary, not deleted. Twenty-seven declarations,
zero sorrys, `lake build Zeta23Ext.EForm3.Main` green (8726 jobs),
`#print axioms` reporting only `[propext, Classical.choice, Quot.sound]` and,
for `box0_in_table`, no axioms at all. Because a compiling lemma is not a
lemma with content — hunt #42's finding — every identification is also
instantiated at the **first recorded row of `o9boxes`** at the interior point
`(23/4, 1/8)`, with every hypothesis discharged. What is **not** claimed: O9
soundness is not closed; the two-mode arithmetic and the identity joining
`Phi2` to `EForm3.Qre`/`Qim` are separate and untouched, and the `y = 0`
mismatch witness sits at `s = π`, outside the table's `s`-range. Two
**pre-existing** build failures are recorded rather than absorbed:
`RetentionWired.lean:44` does not elaborate, and `BandCert.Verify` is killed
at 704 s with exit 137, both observed on a baseline build made before the new
file existed. Evidence in `hunts/r_938ab4/RESULTS.md`. Nothing here is
evidence for or against RH.

### Hunt #39: the Mertens constants, tightened (`r_4218d4/`)

**Status: settled. The Turán variance constant of Hunt #37 falls from `5855`
to `275`, a factor of 21.3, with every statement's shape preserved, no
hypothesis added, no `sorry`, a green `lake build` and an unchanged axiom
audit.** Hunt #37 wrote that its constant is "coarse because the Mertens band
is, and tightens automatically if that does". This run did that, and the
prediction was right: no new mathematics was needed anywhere.

Three local steps upstream, then arithmetic. (i) Mathlib's
`Chebyshev.psi_le` gives `ψ x ≤ x log 4 + 2√x log x`, and its packaged
corollary bounds the remainder by `4x` — i.e. by `log t/√t ≤ 2`, where the
supremum is `2/e`. A one-line lemma `log t ≤ t/e` (`log x ≤ x − 1` applied at
`x = t/e`) gives `(4/e)x`, stated as `3/2`. (ii) The same majorant replaces
`log n ≤ 2√n` in `sum_log_div_sq_le`, and dropping its vanishing `n = 1` term
lets the telescope start at `2`, where it is bounded by `2` instead of `3`;
`6` becomes `3/2` and the prime-power tail `12` becomes `3`. (iii) Mertens I
is asymmetric — its lower half loses `1`, its upper half the whole Chebyshev
constant — and the original proof paid both by routing the prime form through
the symmetric von Mangoldt band; a one-sided
`log_sub_one_le_sum_vonMangoldt_div` keeps them apart, worth `1.5`. Result:
`mertens_first_theorem` `log 4 + 16 → log 4 + 3`; `mertens_second_theorem`
`76 → 16` (with `1/log 2 < 2` also sharpened to `< 1.443`); `sum_sq_dev_le`
`5855 → 275 = 16² + 16 + 3`.

The classical constants (`2` for Mertens I, `4` for Mertens II) are still out
of reach and the run did not chase them, per its brief. What remains is
priced in `hunts/r_4218d4/RESULTS.md`: the largest single term left is the
`log 4` in Chebyshev's bound, which is 39% slack and whose removal is the
prime number theorem, not a constant. Earlier case-log entries and the
`r_3c1cbb` / `r_0339c1` write-ups still quote the old constants; those are
records of what those runs proved and are left as written. Nothing here bears
on ζ or RH (`docs/08`); external verification remains pending.
### Hunt #46 — where the centre-gas obligation T1 resists (`r_b9552d/`)

**Status: not settled, which was the expected outcome.** `k >= 3` is not
closed, T1 is not proved, and the reading of record does not move. Run
`37fb06a9` probed the first half of `K2-TWO-SPECIES.md` §5's two-species
split. Three things came back.

**T1 restated against a budget that is already proved.** Splitting
`gram_form.budget_gram`'s Gram sums into diagonal and off-diagonal parts
gives the identity `GAS = k·Shq(y) − 2B + P`, with
`GAS = Σ_{p≠q}[Dam(2y,τ) − Kpair(τ)]` and
`P = Σ_{p≠q}[−D(2y,τ)]⁺ ≥ 0` (residual 8.0e-15 over 300 random
configurations). `B ≥ 0` already follows from `Retention.energy_F_ge`, so
T1 with the *signed* damage and `ρ = 0` is a consequence of a
kernel-checked theorem, and the whole content of T1 is the strict
positivity of `ρ` together with `P`, the credit thrown away by the
`D ≤ Dam` step.

**An exact ceiling on the atom reserve.** T1 holds with reserve `ρ` exactly
when `ρ·k·Shq ≤ 2B − P`. On the critical `2π` lattice `P = 0` (measured out
to `d = 4000`) and `B/k → c2(0) − A²` exactly, by defect #24's Poisson
summation, so `ρ ≤ 2(c2(0) − A²)/Shq(1/2) = 0.153216295…`, and `0.119590…`
against Lean's proved floor `2·Shq y ≥ 0.51944 y²`. That is a closed form
where `K2-TWO-SPECIES.md` §5 had the measured "87.8% of the per-centre
budget". It is a ceiling, not a floor, so it constrains any future atom
argument and proves nothing about T1 itself.

**The gas extremum, searched three ways, is the uniform `2π` lattice.**
Exhaustive periodic occupancy (every subset of `Z_p` for `p ≤ 14`, 230 base
spacings), free periodic (`m ≤ 8` free positions in a free period), and free
finite `k` all return it: best row `0.05716` against the budget `0.06751`,
ratio `0.8466`. The planted-fault ladder first reports a violation at 1.20×
damage against a 1.18× measured margin, so the verdict comes from a search
with demonstrated power at that scale — and no demonstrated power against a
family the search cannot represent.

**One recorded number did not reproduce.** `two_species.NAMED_GAPS` G4
records the `1,1,2,1,1,2,3` occupancy at step `2π` reaching a per-row
`0.1200` against the lattice's `0.1140`, and it is the only on-file evidence
against lattice extremality. Under all three natural readings of the
pattern this run measures `0.0666` (gaps, averaged), `0.0902` (gaps,
maximised over centres) and `−1.3600` (multiplicities) against `0.1143` for
the lattice. This is a failure to reproduce and is reported as exactly that:
the pattern may mean something the run did not try, or `0.1200` may be a
per-centre maximum, in which case it was never a counterexample to T1, which
is an average statement. `hunts/r_b9552d/RESULTS.md` §4 gives all three and
does not adjudicate.

Also assessed and **not settled**: a Cohn–Elkies-style certificate for T1
(`G ≥ Dam − Kpair` pointwise with `Ĝ ≤ 0`, giving `GAS ≤ −k·G(0)` for every
configuration at once). It is not on the recorded dead list and is distinct
from all five routes there. Its truncated LP value has to clear `0.05716`
before it bounds anything and stay under `0.06751` for the route to work; it
reached `0.05410` at horizon 200 and the solver failed above that. Every
number here is double precision, no enclosures, no Lean. Nothing bears on RH
(`docs/08`).

### Hunt #45 — the omega bridge, and the pointwise Hardy–Ramanujan (`r_233abe/`)

**Status: settled. Both threads closed, zero `sorry`s, axioms unchanged, no
statement weakened.** Run `43d363c1` left two threads in
`lean/ZetaLean/HardyRamanujantheorem.lean` when it landed the density form of
Hardy–Ramanujan, and this run is both of them.

**The bridge.** `omega n = ArithmeticFunction.cardDistinctFactors n` is `rfl`,
as the discovering run priced it, but not for the reason the file's docstring
assumed: this file counts `n.primeFactors.card` and Mathlib counts
`n.primeFactorsList.dedup.length`. `Nat.primeFactors` is
`primeFactorsList.toFinset`, so the two unfold to the same term. The docstring
now names the two definitions it is identifying instead of asserting they are
one. A one-line `rfl` is a restated definition and the brief is explicit that
a restated definition is not a result, so the bridge is carried through to
`hardy_ramanujan_cardDistinctFactors`, in which `omega`, `loglog`,
`exceptional` and `HardyRamanujanTheorem` have all been unfolded away — every
name in that statement is Mathlib's, and an `ArithmeticFunction`-facing
development can cite the theorem without importing anything from this
namespace. That is the whole interoperability point, and it is the part that
was worth the run.

**The pointwise form.** `hardy_ramanujan_pointwise` measures each `n` against
its own `log log n` rather than against the common `log log N`, which is how
the theorem is usually quoted. The route is the discovering run's, with
`delta` fixed at `1/2` so no parameter is carried: split `(0, N]` by
`n * n ≤ N`; below the split there are at most `Nat.sqrt N` integers, which is
`o(N)`; above it `N < n * n` forces `log N < 2 log n`, so
`log log N − log 2 < log log n ≤ log log N` and the gap between the two
normalisations is the constant `log 2`, uniformly in `N`. A deviation of
`ε · log log n` then forces one of `ε · log log N − (ε+1) log 2`, which is at
least `(ε/2) · log log N` as soon as `log log N` has outgrown the slack — and
`hardy_ramanujan` at `ε/2` closes it. **No new arithmetic enters**: the
variance bound, its constant `275`, and the Mertens band `16` are consumed
exactly as they stand, and no existing proof was edited. So the pointwise form
inherits any future sharpening of the density form for free.

`lake build ZetaLean.HardyRamanujantheorem` printed
`✔ [8699/8699] Built ZetaLean.HardyRamanujantheorem`; `grep -c sorry` over the
edited file is `0`; the five new public statements and `hardy_ramanujan`
itself each depend only on `propext`, `Classical.choice`, `Quot.sound`. The
file grows 384 → 588 lines. Everything that resisted was library-name drift
against the pinned Mathlib v4.33.0-rc2 (`le_or_lt` and `div_add_div_same` are
gone; `rw` cannot use the equation lemmas of a `noncomputable def`;
`Tendsto.inv_tendsto_atTop` returns a `Pi`-form inverse that `simpa` will not
reconcile with a beta-reduced lambda), not mathematics. Two caveats a reader
should have rather than discover: the bridge is a `rfl` between two library
definitions that are spelled differently and would break if either were
restated, which is why it is now pinned by a theorem; and the pointwise
statement is the literal classical one, so the finitely many `n` below `e^e`,
where `log log n` is negative and the condition holds vacuously, sit inside
the exceptional set at no cost in density.

Nothing here bears on ζ or RH (`docs/08`). No literature search was run and
none is claimed — Hardy–Ramanujan is a 1917 result, and what is original is
provenance, not novelty. External verification remains pending, as it does for
every claim this laboratory publishes. Separately, and outside this hunt's
scope: `lake build` over the whole package does not currently succeed in this
container — `ZetaLean.Pub1.CertL2` and `ZetaLean.Pub1.CertAtoms` log failures.
Neither imports anything from `ZetaLean.HardyRamanujan` (checked by `grep` over
their import closure), so neither can be a consequence of this run's edit, and
this run did not diagnose them further. It is recorded here so a green targeted
build is not read as a green package.

### Hunt #40: `beta := normLower` lands, the predicted slack does not (`r_908de5/`)

**Status: settled, and one prediction on main is refuted.** `docs/25` §4.3
defect 2 named the remedy for the rung-3 grid sites — `pred_beta` was drawn at
the achievable bound, so `normLower >= pred_beta` sat at the line by
construction in any arithmetic (12 of 104 sites under 1 %, `g_right_15` at
0.03 %, commit 44d3133) — and predicted that setting `beta := normLower` moves
the slack into the cell condition, "which then carries >= 10x slack". The
first half holds: with beta read off the enclosure the site inequality is true
by construction, and the obligation that then bites, `eps' + L*h/2 <= beta`
(the hypothesis of `ZetaLean.DH.DH_lower_on_[hv]cell`, not a modelling
choice), still passes at all 104 sites with `L = 16` and `eps' = 1/2000`
untouched. The second half does not: evaluated in exact rationals over the
committed plan, the worst of the 200 cell obligations clears by **1.3697x** in
ball arithmetic and **1.3566x** in chained-rect, against a prediction of
">= 10x" — over by a factor of ~7.3, and barely moved from the 1.3647x it
already had under `pred_beta`, in either direction. The
binding constraint turns out to be the gap, not beta: `L*h/2` is 98 % of the
requirement at every one of the five worst cells, so raising betas buys almost
nothing, and the remedy moved the worst case by 0.4 %. A second finding sets
the price of landing it: `scripts/60_rung3_generate.py` emits a *non-chain*
rect enclosure, 2-3x wider at a point than the chained one `docs/25` measured
in, where `normLower` is 0.37-0.53x `pred_beta` and the cell condition fails
outright — so the remedy is contingent on porting the generator's emission to
composite chains, for which the Lean side (`dirichletTermBox2`,
`contains_coarsen`, `contains_cpow_mul`) already exists unused. Landed: beta
is now read off the enclosure with `--beta plan` restoring the old source, and
the generator asserts the cell requirement at emission time so a site that
cannot pay it fails loudly instead of passing at the line. No Lean source
changed; `lake build` green from a cold toolchain. Nothing here bears on RH
(`docs/08`), and nothing here is a result until the battery or the funnel says
so.
### Hunt #43: the k=2 table with `zone_trade`'s inner prune disabled (`r_401bbf/`)

**Status: settled, outcome (a), on every cell rather than a sample.**
`k2_closure.zone_trade` cuts its branch-and-bound with a line that refuses to
descend into a multiplicity which does not immediately improve the running
value. That cut restricts the *adversary's* search, the unsound direction, so
wherever it bit the published margin would be optimistic. Hunt #41 measured its
delta as 0.0 on six binding cells and recorded the assumption as unchecked
elsewhere. This run re-solved the trade on all 6600 cells in both cap modes,
13200 evaluations, by exhaustive enumeration over every multiplicity vector
with `sum m <= 10`, with *both* of the search's cuts removed rather than only
the one the brief named. Max `|delta|` **4.4e-16**, zero cells above 1e-15, no
margin moved: worst cells stay at +0.0528969 (signed, tau 12.85) and +0.0032601
(unsigned, tau 6.33), nonpositive cells 0 in both columns. The residual takes
both signs, which is what float summation order looks like and is not what a
bite looks like. The run also supplies the reason, which covers more than the
table does: the pair charges are `Kpair/200` and `Kpair` is a square, so with
nonnegative charges the `m = 0` branch dominates every branch the prune drops,
and both cuts are admissible for *any* caps. The detector-power control is a
planted instance with one negative charge, where the published search
understates the trade by 18.6%. `k2_closure.NAMED_GAPS` G2 and
`K2-TWO-SPECIES.md` now record the discharge; the other assumption Hunt #41
named, the `Kpair` clamp, is still sound only by geometry. Cost 700 s for the
census, which is roughly what running the table once costs. Nothing here is
evidence for or against RH (`docs/08`), and no cap was widened and no zone
re-tuned.

### Hunt #42: the O9 numerator fields, and the seam that could not be instantiated (`r_6c7d6a/`)

**Status: settled, and one defect found on the way.** The run was sent to
supply the numerator-side `boxParts` fields of the O9 two-dimensional checker
in the vendored `Zeta23Ext` Lean package. It found the brief's premise stale:
`O9Parts.lean`'s header calls the numerator side "the remaining step", and
commit `6f81078` had superseded that sentence seven minutes after it was
written, landing `reNum_mem` and `imNumOverY_mem`. That commit's own message —
"every `boxParts` field is now sound" — was the thing actually wrong.
`Retention.Parts` has **seven** fields and six had lemmas; the seventh,
`imNum`, is a hypothesis of `qreIv_mem`, so the `Qre` composition could not be
instantiated at a box at all. `Retention.imNum_mem` supplies it, with the
component left abstract in the idiom `O9Seam` and `O9Assemble` chose.
Discharging the rest of the hypotheses is what turned up the finding:
`O9Seam.r_comp_mem` writes `c*c + dOverY*dOverY` under the quotient, while
`rIv` divides by `denAbs2 = c*c + d*d` with `d = dOverY·y` and
`O9Real.im_div_over_y` agrees with `denAbs2`. So `r_comp_mem` and the
`rIv_mem` built on it are true, zero-sorry, and **vacuous at every box in the
table** — at `s = 1, y = 0` the hypothesis asks `denAbs2` to contain `5` where
it contains `1`, and the box family `[28/5, 60] × [0, 1/2]` never makes the two
agree. `r_comp_mem'` leaves the denominator's real abstract and fixes it with
the same proof term; `rIv_mem_box` and `qreIv_mem_box` then state both
compositions at a box with every field hypothesis discharged. Five new
declarations, zero sorrys, `lake build` green, `#print axioms` reporting only
`[propext, Classical.choice, Quot.sound]`. What is **not** closed, and is not
claimed: the two-mode arithmetic and the leaf-shape identities that relate the
computed expressions to `Re num` and `Im num / y`. Evidence in
`hunts/r_6c7d6a/RESULTS.md`. Nothing here is evidence for or against RH.

### Hunt #36: claim 'urms2-0.51' has no recorded white-box attack (`r_065f29/`)

**Status: settled as an attack, not as a verdict. The claim is not withdrawn;
the apparatus around it is weaker than the record reads.** The white-box half
of the standing review ran the eight-entry `harness.review.WHITEBOX_CHECKLIST`
against URMS2-051. The mathematics of the half-band crossing survives direct
attack: the exact block second moment `∫_U^{2U}|Σ c_n n^{-it}|²dt`, evaluated
as a closed-form double sum on the author's own coefficient family, saturates
to four significant figures (17.2964 → 17.3642) while `W/U` grows from 1.3 to
9.9, which is the `W`-independence the claim asserts, measured in the regime
the old proof's `W/U = o(1)` forbade. Three findings are about the record.
(i) `URMS2-051.md` §9's falsification control runs on a frozen level-two
family that violates the hypothesis of the step it supports: `A(y)/(y log y)`
climbs by a factor of 88 from its trough, and the upper-range sum grows like
`W^{0.825}` at fixed `x` instead of saturating, which the §9 ladder cannot see
because it moves `x` and `W` together and never varies `W` at fixed `x`. A
surrogate family that does obey `A(y) ≪ y log y` saturates, so §4's
mathematics is correct and only its control is powerless. (ii)
`URMS2-051-AUDIT.md` gate 6's "independent route" shares its entire numerical
substrate with the primary route: the JSON fixture reproduces
`corrected_coefficients(40)` exactly, and a one-part-in-10⁶ mutation of the
shared tail majorant moves both denominators by the identical
`4.426081703885579e-27`. (iii) The four recorded margins do not select
`51/100` — they stay feasible to `257/500` at the published parameters and
admit `α = 0.9` with the free ones open — and four of the six obligations §7
lists have no audit gate, inherited across the `γ > 1` regime change that is
this proof's novelty. Evidence in `hunts/r_065f29/RESULTS.md`; the outcome is
recorded as a white-box `AttackOutcome` in
`harness/departments/review_ledger.py`. Nothing here is evidence for or
against RH.
### Hunt #37: Hardy–Ramanujan, settled (`r_0339c1/`)

**Status: settled. The Hardy–Ramanujan theorem is kernel-checked with zero
`sorry`s: `ZetaLean.HardyRamanujan.hardy_ramanujan` proves the density form,
by Turán's proof, with every constant explicit.** This is the retry of Hunt
#12 with its named wall removed: Mertens' second theorem now exists on main
(`ZetaLean.Mertens.mertens_second_theorem`, band `76`, from hunt `r_3c1cbb`),
and the remaining half of Turán's argument was, as Hunt #12 priced it,
bookkeeping.

Hunt #12's kernel-checked halves are reused as written (copied with
attribution; its branch is unmerged): the statement, the double-counting
identity `∑_{n ≤ N} ω(n) = ∑_{p ≤ N} ⌊N/p⌋`, and the whole Chebyshev step.
New in this run: the second moment expands `ω(n)²` over ordered pairs of
primes, `Nat.Ioc_filter_dvd_card_eq_div` at `p*q` counts the off-diagonal,
and `∑_{n ≤ N} ω(n)² ≤ N·S² + N·S` with `S = ∑_{p ≤ N} 1/p` follows. With
the first-moment bracket `N·S − N ≤ ∑ ω ≤ N·S` and `|S − log log N| ≤ 76`,
the variance obeys `∑_{n ≤ N} (ω(n) − log log N)² ≤ 5855 · N · log log N`
whenever `log log N ≥ 1` (`sum_sq_dev_le`; the constant is `76² + 76 + 3`,
coarse because the Mertens band is, and tightens automatically if that
does). `lake build` printed `✔ [8699/8699] Built
ZetaLean.HardyRamanujantheorem`; the seven public theorems each depend only
on `propext`, `Classical.choice`, `Quot.sound`. The module compiled on the
first attempt, which is what reading Hunt #12's route and trap list before
writing anything buys. Nothing here bears on ζ or RH (`docs/08`); external
review remains pending, as it does for every claim this laboratory
publishes.

**Numbering note.** This run was assigned #36 by its brief and found #36 already taken by `r_065f29` when the two branches met at the merge. Per the brief's own rule — "if it is occupied say so rather than renumbering silently" — it is recorded here as #37. Two coordinators assigned the same number independently; the case-number reservation is not shared across sessions.

### Hunt #12 — Hardy–Ramanujan, and the lemma Mathlib does not have (`r_0339c1/`)

**Status: not settled, and the wall is named. The Hardy–Ramanujan theorem is
not proved. Turán's Chebyshev half is kernel-checked as an implication with
zero `sorry`s, the unconditional first step of the other half is kernel-checked
outright, and the remaining half stops at a specific library absence: Mathlib
v4.33.0-rc2 has no Mertens second theorem.**

The target was Wikidata Q5656674, which Mathlib records as wanted and unbuilt.
`lean/ZetaLean/HardyRamanujantheorem.lean` states the density form as a `Prop`,
proves `sum_omega_eq_sum_div` (`∑_{n ≤ N} ω n = ∑_{p ≤ N} ⌊N/p⌋`, by double
counting, unconditional) and proves `hardyRamanujan_of_turanVariance`, which is
the whole Chebyshev step. `TuranVariance` is a hypothesis in that file and not
a theorem, so the implication is a reduction and the file's own docstring says
it does not contain the theorem. `lake build` printed
`✔ [8697/8697] Built ZetaLean.HardyRamanujantheorem`; all four results depend
only on `propext`, `Classical.choice`, `Quot.sound`.

The obstruction is `∑_{p ≤ x} 1/p = log log x + O(1)`. Mathlib has the
*divergence* of `∑ 1/p` (`not_summable_one_div_on_primes`) and nothing with a
rate, and `grep -rln "Mertens"` over the pinned checkout hits one unrelated
file. Two incidental traps for the next attempt: `NumberTheory/Chebyshev.lean`
is about Chebyshev polynomials, not prime bounds, and `NumberTheory/AbelSummation.lean`
supplies the machinery Mertens is normally derived through while the derivation
itself is absent. Nothing here bears on ζ or RH.
### Hunt #62: three cited properties of ζ distinguish nothing (`r_f7cd45/`)

> **Renumbered 2026-08-20.** Opened as #35, which `r_3c1cbb/` had taken
> the previous day. `hunts/r_f7cd45/` is the stable reference.

**Status: settled for the five properties issue #21 left unpublished; the
sixth was already settled in this tree and what this run adds is the price
tag.** Publishes the artifact issue #21 recorded as queued. Under `docs/09`
gate #3, run against the Davenport–Heilbronn function and both discriminant
−23 Epstein zetas: the functional equation, a real Hardy-style Z, and having
zeros on the critical line are each satisfied by **3 of 3** rivals and are
**VACUOUS**; multiplicative and completely multiplicative coefficients are
satisfied by **0 of 3** and **DISTINGUISH**. Issue #21's table reproduced cell
for cell, from a probe that runs end to end. Only the prime structure kills
the rivals.

Issue #21 also lists a sixth property, "no zeros in a box strictly off the
critical line", as unfinished at a 50-minute timeout — **stale**, since hunts
#13, #14 and #15 settled it (VACUOUS, and ill-posed: the box is a free
parameter of the sentence). Reproduced independently here on two boxes
preregistered at `53c8cd1` before any winding number: σ ∈ [0.6, 0.9] gives
VACUOUS at t ∈ [80, 81], forced by Davenport–Heilbronn alone, and UNDECIDED at
t ∈ [85, 86], where the D–H cell returns exactly **1**, recovering the
off-line zero the repository pins at 0.8085171824… + 85.6993484853…i.

What is new is the precision floor, measured rather than argued: at
0.75 + 85.5i the Epstein completed function is **2.0e−58** and **5.0e−58**,
converging only at **dps 60**, while at the `dps = 20` that `battery` actually
uses it returns ≈ 2e−33 — noise larger than signal by 25 orders of magnitude.
The Epstein box cells are therefore reported *inadmissible on precision*, not
merely slow, because `count_zeros_box`'s integrality check does not catch it:
noise winds to an integer too. **Defect reported, not patched** (`zeta/` is
outside scope): both rival interfaces hardcode `dps=min(dps, 20)` into
`count_zeros_box` (`zeta/epstein.py:1091`, `:1141`), so no caller can reach
the floor and the packaged property-6 route is unusable above t ≈ 30. That,
not difficulty, is why three hunts in a row have declared the Epstein arm out
of budget. Grade: measured, with ζ as a positive control on all five
properties. Nothing here is evidence for or against RH (`docs/08`); gate #3 is
eliminative, never probative.
### Hunt #35: Mertens's second theorem, the mapped block built (`r_3c1cbb/`)

**Status: settled.** Continuation of Hunt #30, building exactly the block
its route map named and nothing else. What landed:
`lean/ZetaLean/MertensSecond.lean` compiles against pinned Mathlib
v4.33.0-rc2 with zero sorrys and carries Mertens's **second** theorem in the
`log log x + O(1)` form with an explicit constant:
`|Σ_{p≤N} 1/p − log log N| ≤ 76` for every natural `N`
(`mertens_second_theorem`; the content is at `N ≥ 2`, below that the sum is
empty and Mathlib's `log 0 = 0` makes the bound trivial). The argument is
the classical partial summation against
`A(n) = Σ_{p≤n} log p/p = log n + O(1)`, the `O(1)` band being Hunt #30's
`mertens_first_theorem` consumed as-is, with the termwise bracket
`(v−u)/v ≤ log v − log u ≤ (v−u)/u` telescoping to `log log N` and the
overshoot closed by `Σ 1/n² ≤ 1`. One deviation from the route map, worth
keeping: the discrete Abel identity went in by direct `Nat.le_induction`
from `N = 2` (`sum_inv_primes_eq`), not by reindexing Mathlib's
range-indexed summation by parts, which removed the labor the map had
priced at 150 to 250 lines of reindexing. The constant `76` is deliberately
coarse (a sieve to `10^6` puts the true deviation near `0.26`); its slack
decomposes into named local steps, nearly all inherited from the first
theorem's `log 4 + 16` band. The sharper `log log x + M + o(1)` form and
the third theorem need the Mertens constant and are recorded as out of
scope. Details in `r_3c1cbb/RESULTS-second.md`. Nothing here is evidence
for or against RH.

### Hunt #30: Mertens's theorems, settled through the first theorem (`r_3c1cbb/`)

**Status: settled in part, and the part is stated exactly.** The target
(Wikidata Q1196729, recorded by Mathlib's wanted-theorems tracking as wanted
and unbuilt) was any of Mertens's three theorems, kernel-checked. What landed:
`lean/ZetaLean/Mertensstheorems.lean` compiles against pinned Mathlib
v4.33.0-rc2 with zero sorrys and carries Mertens's **first** theorem in both
classical forms with explicit constants: the von Mangoldt form
`|Σ_{n≤N} Λ(n)/n − log N| ≤ log 4 + 4` and the prime form
`|Σ_{p≤N} (log p)/p − log N| ≤ log 4 + 16`, each for `N ≥ 1`. The argument is
fully elementary: the summatory identity from
`ArithmeticFunction.vonMangoldt_sum` by counting multiples, Mathlib's
Chebyshev bound `psi_le_const_mul_self`, an induction replacing Stirling with
`log(1+1/M) ≤ 1/M`, and a telescoping `Σ n^(-3/2)` bound for the prime-power
correction. The **second** theorem (`Σ 1/p = log log x + O(1)`) was
route-mapped but not built: the wall is the discrete partial-summation step,
recorded with the relevant Mathlib declaration names in `RESULTS.md`. The
**third** is out of reach at this budget (needs the Mertens constant and γ).
Constants are far from optimal by design; sharpening them is a loose thread.
Nothing here is evidence for or against RH.

### Hunt #34: claim 'urms2-0.51' has no recorded blind attack (`r_fb9c81/`)

**Status: settled. The stated analytical assumption holds structurally, and the mean-value evaluation is valid.** The blind attack searched for a numerical consequence of replacing the exact polynomial frequency spacing with its generic mean bound, testing whether length $W \gg U$ could collapse the off-diagonal bounds while keeping the formal appearance of the claim. A numerical probe on a scaled configuration ($x = 1000, \alpha = 0.51, \delta = 0.75$) proved that the Montgomery-Vaughan mean-value off-diagonal cost remains identically bounded by $O(x \log x)$. The true frequency separation limits the spacing error such that the main diagonal term $U \log x$ unconditionally dominates. The $0.51$ parameter therefore does not survive merely on an invalid archimedean assumption; its required analytical decay is physical and rigorous. Full evidence and reasoning are recorded in `hunts/r_fb9c81/RESULTS.md`. Nothing here is evidence for or against RH.

### Hunt #27: AGY conversation context and handback 8 (`r_test_agy_8/`)

**Status: settled. A framework probe successfully validated the operational envelope.** The AGY process context correctly ran a script that imported the `.venv`-installed `zeta` package, computed values using `zeta.explicit.li(x)` with `mpmath` at specified precision, and wrote a complete evaluation to the local directory without incident. Nothing here bears on RH; it is a test of the test mechanism.

### Hunt #18: the O9 leaf table, repriced (`r_2926e4/`)

**Status: settled. `o9_leaf.py`'s 1-D O9 table is 476 cells at max depth 22 on
the leaves the kernel actually computes, not the 344 at depth 20 it records,
and 85 of those 344 cells (24.7%) fail outright once the leaves are the
kernel's.** The module's LEAF CAVEAT argues that a cell passing with margin is
safely predicted; the hunt measures that the margin is the wrong quantity, not
a mis-calibrated one. A cell with a recorded Arb margin of `9.21e16` ulp,
`2.5e7` times the `3.63e9` minimum the module cites as its safety evidence,
still fails, so no threshold on that margin separates the safe predictions from
the unsafe ones. The mechanism is confined to the two leaves whose argument is
the cell rather than a constant: `sinCosIv` reduces mod `2π` and applies `dbl`
twice, `dbl` squares an interval, and the width grows with the cell (`cosX2`
mean `8.15×` Arb's width, worst `43.5×`). The four constant leaves and the two
hyperbolic ones go the *other* way, `3×` to `9×` narrower than Arb-plus-4-ulp-pad,
so "the Arb model is uniformly optimistic" is the wrong generalisation.
**Control:** bucketing the 85 failures into the 40-cell chunks `emit_lean`
writes reproduces the 2026-08-13 Lean build's verdict nine chunks for nine,
including both chunks that passed (offsets 200 and 280 contain zero failures);
that comparison is against a real `decide +kernel` run and tuned nothing.
The table still closes after the repair, which was not guaranteed: the
complement test lives on the ~`2e-05` of slack in §4's outward-rounded `I_k`,
and the wider leaves do not eat it. **Disposition:** no ledger entry; the
repair belongs to `hunts/frontier_math/o9_leaf.py`, which is outside this
hunt's scope and still exports `N_CELLS_KERNEL = 344`. Corrects issue #23,
which says the 344-cell table was never put to the kernel: it was, on
2026-08-13, and refuted on 7 of 9 chunks. No Lean was built here, so 476 is
measured, one route, and the route is a model of the kernel. Nothing here bears
on RH.

### Hunt #14 — gate-5 property 6 is vacuous (`gate5_p6_b/`)

**Status: probe, complete. VACUOUS, with the parameters committed before the
first count and the commit order left in the history as the evidence.** The
open property of `zeta.epstein.battery` was *"in a box strictly off the
critical line, the completed function has no zeros"*. Three boxes and a
precision rule were fixed in `MISSION.md` at `623e800`; the probe ran
afterwards. In box A (`σ ∈ [0.70, 0.92]`, `t ∈ [1.5, 11.5]`) and box C
(`σ ∈ [1.05, 1.60]`, same heights) all four functions return a zero count of
**0**, so all three rivals satisfy the property and it distinguishes nothing.

The box-dependence the property carries by construction was measured rather
than argued: Davenport–Heilbronn **satisfies** property 6 on boxes A and C and
**fails** it on box B (`σ ∈ [0.70, 0.92]`, `t ∈ [85.2, 86.2]`), which was built
around the off-line zero pinned in `zeta/epstein.py` — and the box-B cell
returns exactly **1**, recovering that zero where Spira (*Math. Comp.* 1994)
puts it, the run's one positive control. So property 6 is a box-indexed family
rather than one claim, and the version that quantifies over all boxes is RH for
the function, which is circular as a proof step. Box B's two Epstein cells are
undecided on cost (about 21 minutes of mpmath each at `dps = 79`), reported
undecided rather than skipped.

One defect found on the way, reported and not patched (`zeta/` is outside the
hunt's scope): both rival interfaces in `battery` pass `dps=min(dps, 20)` into
`count_zeros_box`, and at `t = 85.7` the completed Epstein function at `dps
= 20` returns `1.2e-34` against a true `1.617e-58`. A winding count over that
noise still lands on an integer, so the routine's own integrality check does
not catch it.

### Hunt #41 — the interval pass over the k=2 tau-table (`r_a97060/`)

**Question.** `hunts/frontier_math/k2_closure.py` closes the `k=2`
equal-depth case of blocker 2 over 6600 tau-cells, at *measured* grade: every
supremum in it is a double-precision scan padded by a flat 5%.
`K2-TWO-SPECIES.md` §6 names the obligation that keeps it there. Does the same
table close when every sup becomes an enclosure and every credit a lower
bound?

**Result: yes, in all three cap modes, over the same cells.** 0 of 6600
nonpositive; worst margin +0.0677 (signed-field caps), +0.0146 (unsigned),
+0.0016 (unsigned with the measured pass's own 1.05 pad kept on top of the
enclosure, which is the like-for-like row). No cap widened, no tau-cell
split. The arithmetic is Arb complex balls at 96 bits, not rectangles, on the
brief's instruction: rung 3 had measured rectangles losing 13.7× of width to
balls on exactly this shape of quantity, a squared rotating complex value.
`mpmath.iv` rectangles contain every ball checked and run 1.8–3.5× wider.

**What the enclosure actually cost.** A factor of **1.0000 to 1.0004** on the
near field, the dominant term. The 1.05 pad it replaces was standing in for an
error two to three orders of magnitude smaller than itself.

**What the hardening found that the scan could not.** The centre-centre row is
`sup_{0<y≤1/2} Dam(2y,τ)/y²` — a supremum over an *open* interval with the
variable in the denominator, which the measured pass took over an 18-point
grid starting at `y = 0.05`. A first full enclosure pass reported one
nonpositive cell at `τ ∈ [6.62, 6.64]`, a root of `G(τ)`. It was not a gap: it
was the `1/y²` corner, where a branch-and-bound stalls because the enclosure
width there is set by the τ-cell rather than the y-box. The fix is a fact
about the problem rather than more grid — `ghat` is **even** with real Taylor
coefficients, so `Re ghat'(iτ) = 0` and `D` has **no depth-linear term**,
giving `4·max(0,D)/u² ≤ 4·max(0, sup|D''|/2 − G²/b²)` for every `u ≤ b`. That
is why the ratio is bounded as `y → 0` at all, which the y-grid assumed
without stating, and no scan can check it.

**Two unstated assumptions recorded** in `k2_closure.py`, neither changing a
published number: the pair-charge clamp `Kpair(min(dmax,6))` is a lower bound
only if `Kpair` is monotone out to `dmax`, which holds only because the widest
near component in the table is 1.9894; and the inner prune of `zone_trade`
restricts the *adversary's* search, so it is a heuristic on the unsound side
(measured delta 0.0 on six binding cells).

**Scope, stated rather than implied.** The *table* is enclosure-carrying. The
*k=2 equal-depth claim* is a composite and still takes the grade of its
weakest step, which is now the v-convexity transfer off `v = 1/4` — argued,
not enclosed. `k ≥ 3` and the unequal-depth quantifier are untouched, and
nothing here is evidence about RH.

**Disposition:** instrument and result retained; `K2-TWO-SPECIES.md` §6 and
`k2_closure.NAMED_GAPS` G2 amended in the same commit. Budget overrun
recorded in the handback: 75 minutes allowed, ~100 taken, all of it the
diagnosis above.

### Hunt #15 — is gate-5 property 6 vacuous or distinguishing? (`gate5_p6_c/`)

**Status: settled, and the answer is that the question as written has no
truth value.** Property 6 of the `docs/09` gate #3 battery reads "in a box
strictly off the critical line, the completed function has no zeros" — and
the box is a free parameter of that sentence. Holding the σ-band fixed at
[0.7, 0.9] and changing only the height window flips the verdict:
Davenport–Heilbronn has one zero in t ∈ [85.5, 85.9] and none in
t ∈ [10, 14] or [40, 44], while ξ has none in any of them. Same property,
same band, same code, opposite verdicts. The mechanism is that an
RH-violating function does not violate RH everywhere, so a local zero-free
statement cannot carry a global distinction. Every repair that gives
property 6 a truth value and still distinguishes turns out to be either RH
itself or the Euler product, which is property 5 — so property 6 does not
look like an independent sixth property. Parameters were preregistered and
committed before any winding number was computed (`MISSION.md` at `c29c876`,
`results.json` after). **Not settled:** the Epstein arm on the two high
boxes, declared out of budget, and unable to change the conclusion — the
VACUOUS boxes are already forced by Davenport–Heilbronn, since gate #3 asks
the structure be ungrantable to *every* rival. **Two defects found in
`zeta/epstein.py` and reported, not fixed** (out of the hunt's scope):
`epstein_completed` silently loses ≈ 0.6822·t digits to cancellation, so at
the documented dps = 20 its phase is noise above t ≈ 30; and
`count_zeros_box` has no evaluation ceiling, so a noisy phase makes it
recurse to depth 45 per segment and never return rather than raise. Nothing
here bears on RH (`docs/08`); it is about what separates ζ from
RH-violating look-alikes.

### Hunt #9 — how much power a guard has (`r_414eed/`)

**Status: probe, complete. `scripts/make_context.py --check` caught 17/17
in-scope mutants including its declared smallest one — and it caught that one
by accounting rather than comprehension, which is what exposed the single edit
shape that slips past it.** `CONTEXT.md` prints a per-module line count, so any
length-changing edit marks it stale (a lone blank line fires the guard) while a
private helper renamed public *in place*, in a module that declares `__all__`,
regenerates byte-identically and passes. Four unscanned regions mapped
(`meta/`, `compiler/`, `docs/doors/`, non-`test_*.py` test files). Controls: the
unmutated sandbox reproduces `CONTEXT.md` byte for byte, and the undo is
re-checked after every one of 24 mutants; the repository itself is never
written to. **Disposition:** guard ledger entry amended from `fired=None` to
`fired=True` with its scope and six known misses
(`harness/departments/guard_ledger.py`, run `fd5fd902`). Nothing here bears on
ζ or RH — it measures a repository hygiene script.

### Hunt #13 — the box that was chosen to lose (`gate5_p6_a/`)

**Status: settled, and the property it settles is one the battery should stop
carrying.** Gate #3 battery property 6, "in a box strictly off the critical
line, the completed function has no zeros", is **VACUOUS**. The box was fixed
and committed one commit *before* `probe.py` existed, and it was chosen
adversarially: `sigma in [0.70, 0.92]`, `t in [85.55, 85.85]` is the one region
in this repository where a rival is known in advance to have an off-line zero
(the pinned Davenport-Heilbronn zero at `0.808517... + 85.699348...i`), and so
the box most favourable to a DISTINGUISHES verdict. It lost anyway: the Epstein
zeta of the non-principal discriminant -23 form has **0** zeros there and
satisfies the property exactly as `xi` does. **Disposition:** the larger finding
is that property 6 is not well posed as a gate input, because a second box at
`t in [70.10, 70.40]` gives the Davenport-Heilbronn function the *opposite*
answer. Property 6 is a property of a (function, box) pair; quantified over all
boxes its zeta column is RH restricted to a region and so unknowable, and
instantiated on any affordable box it is vacuous. A box-free replacement is
proposed in `RESULTS.md` (`no zeros in Re s > 1`), with the caveat that it
distinguishes only by restating the Euler product. Measured, float grade, one
resolution: the planned reconfirmation at halved step did not finish inside its
cap, and three of eight cells are recorded gaps. Nothing here bears on RH.

### Hunt #11: what the hunt lexical guard actually reads (`r_03a798/`)

**Status: settled. The guard matches one literal substring, case-insensitively,
and everything outside it passes.**

The attention item that opened this hunt asserted that
`test_no_hunt_claims_the_reserved_word` misses synonyms, and that *verified*,
*confirmed*, *definitively* and *proves* are caught "by other checks". The hunt
measures both halves and reports the first as true and the second as false:
those other checks do not exist. It copies the guard **unmodified** into a
sandbox repo root and runs it against one planted specimen at a time, so each
verdict is the guard's own exit status rather than a re-implementation, with an
empty-specimen control green so a failure is attributable to the specimen.

Reproduce: `python hunts/r_03a798/probe.py` (~40 s, no mpmath, no network).
Data: `results.json`.

### Hunt #10 — what the doors guard actually catches (`r_cb5ffe/`)

**Status: probe, complete. The guard's power is measured at 5/10 against a
ten-mutant battery, and its five misses share one cause.**

`harness/departments/guard_ledger.py` carried `tests/test_doors.py` with
`fired: None` and `scope: undetermined until demonstrated` — existence
recorded, power never measured. This hunt builds the mutant the record names
(a door command that exits non-zero) plus nine neighbours, applies each to a
throwaway `git worktree`, and records which tier of the guard notices.

Measured: four mutants caught on the fast tier, one only on the slow tier,
five escaped. The escapes are structural rather than scattered — the guard's
whole notion of "a door's command" is the regex `scripts/[\w.]+\.py` applied
to `docs/doors/README.md`, so a command quoted *inside* a door page is
unguarded, and a README row naming no script (the certify door's Lean build,
the adopt door's pytest invocation) is outside its field of view. A tree
carrying all five escapes at once passes both tiers green.

The hunt reports a proposed ledger amendment and does not apply it:
`harness/` is demoted (`harness/VERDICT.md`) and a hunt may not promote its
own claim.

### Hunt #8 — where the fog enters (`effective_constants/`)

**Status: opened 2026-08-13, nothing measured yet.** Tests whether the
transplant chain's ineffectivity is extractable bookkeeping or an essential
obstruction.

The chain's headline caveat is that the improved constant is a liminf
statement with crossover `T₀ ≈ 10^(1.6773e6)` — unreachable at any computable
height — and that this is *inherited* from the source paper. "Inherited"
currently functions as an explanation and is not one, so the hunt asks where
exactly the fog enters and whether it has to.

Two facts already in the tree say it may not. `PROOF-LEDGER.md` (blocker 3,
residual (i)) records that **four existential `EvBound` constants would make
the chain effective and nothing else in the budget would** — the ineffectivity
is localised, and the dominant error term is already derived from parts
(`35.519106`, matching measurement to four digits). And upstream those facts
are *assumptions*: fields of a `Facts` structure carrying the paper's own
references, whose shape is `∃ C > 0, ∃ T₀, ∀ T ≥ T₀, |f| ≤ C·g` and whose own
docstring says "explicit inequality with named constants, no filter-o(1) until
the final liminf wrapper". The constants were not lost to an obstruction; they
were not carried across an interface, because the source's goal was a limit
statement.

Either verdict is worth having. Extractable means an effective form of the
underlying bound is arithmetic rather than new mathematics — and that would
stand independently of the `+1.0e-5` improvement it was reached through, since
the improvement is unreachable at any computable height while an effective
constant is usable above its threshold. Essential means the obstruction finally
has a name and a location.

Opened after the operator asked why the fog has to be inherited at all. It is
the first hunt to attack the chain *upstream* of where the transplant begins.

### Hunt #7 — the quasicrystal that is a theorem (`golden_control/`)

**Status: probe, complete. The quasicrystal lane gains its ground-truth
universe, and the exact stage caught the operator mis-remembering a
classical theorem.**

The quasicrystal gate's instrument had never been run against an aperiodic
point set whose atomic diffraction is *proved*. This hunt points a tapered
transform — calibrated on ℤ, where the answer is Poisson summation
(6.4e-14) — at a golden cut-and-project set, with the Fourier module and
intensity law derived in code from the embedding lattice rather than quoted.
Measured: peak positions to 8.7e-9, amplitudes against the window-transform
law to 2.5e-8, off-module silence 9717× (ζ's arithmetic gate measured 26.8×
with 1000 zeros — the theorem universe shows what the instrument does with
no truncation), Debye–Waller lesion slopes within 1%, Poisson null clean,
precision response monotone to 1e-10. The golden thread pinned exactly:
the DH rival's quartic character squares to χ₅, the ℚ(√5) character. **One
registered claim was false and the computation caught it at first contact**
(π(p) | p − χ₅(p) fails at p = 3; the split/inert-asymmetric statement
π(p) | p−1 vs 2(p+1) holds for all p < 500) — recorded with its
counterexample, as the derive-never-remember rule intends.

**Disposition:** instrument validation, not a result about ζ; no ledger
entry. Nothing here is evidence for or against RH.

### Hunt #6 — the Jensen clock (`jensen_clock/`)

**Status: probe, complete. Instrument kept; no claim promoted; the headline
is a measured dictionary between the two real-rootedness lanes, plus a null
control that explains it.**

Connected `zeta/li.py`'s Jensen/hyperbolicity lane to hunt #4's de
Bruijn–Newman flow measurements on Davenport–Heilbronn. The exact identity
J^{d,0}(x/d) = Σ γ(j)/j!·Π_{i<j}(1−i/d)·x^j makes the degree-d binomial
damping a Gaussian coefficient multiplier — de Bruijn's smoothing applied by
the degree itself — matching the flow multiplier e^{tu²} at a pair image x₀
with **t_eff = |x₀|/(8d)**. Measured, with raw numbers in
`jensen_clock/results.json`:

- The DH height-85.7 pair's image in J^{d,0} tracks the PDE flow trajectory
  under that dictionary at 7.8e-8 → 4e-4 relative over half the flow; the
  landing degree d\* = 20785.13 reads t\*_J = 0.0441690 against hunt #4's
  t\* = 0.0441263 — **0.097%**, while the isolated-pair value is 7.2% away.
  Pair 2 (γ ≈ 114): d\* = 146365, clock agreement **0.011%**. Flowing before
  damping, the two clocks add: t_land(d) + |x₀|/(8d) = t\* to 0.03–0.06%.
- **The corollary**: a blind hyperbolicity scan at d ≤ 32, n ≤ 250 sees
  nothing, and the dictionary says that is structural — degree d ≲ 2·10⁴ has
  already flowed this violation past its landing before the polynomial is
  inspected. Textbook-degree Jensen scans are the wrong side of the landing,
  not weak detectors.
- **Null control, the explanation**: a pair planted into ζ's γ-table at
  exactly x₀ lands at 0.0436212; the arithmetic-free N-body dynamics run on
  the plant's actual configuration lands at 0.0435805 — 0.094% — while DH's
  clock sits 1.1% away and the isolated formula 8.3% away. The clock reads
  zero configuration, not arithmetic (hunt #4's null, now on the coefficient
  side). The mission's own quantitative guess for this control was wrong
  (it forgot the ordinate doubling in the x-plane) and is recorded as a
  failed prediction in `jensen_clock/RESULTS.md`.
- Controls: ζ specificity (winding 1.3e-63, Newton relative Im 1.2e-200);
  instrument checked against `zeta.li`'s twice-derived γ-table to 1.3e-51
  and hunt #4's polished pair to 40 digits; d\* precision-flat to the printed
  digits across dps 130 → 160 and two quadrature geometries; truncation
  margin 36 orders at the deciding contour.

**Phase 2 (the shift axis)**: the shifted Jensen polynomial is the damped
n-th derivative, and one differentiation is worth **3.69×** the violation's
entire flow budget (c₀ = 0.1628 vs t\* = 0.0441, measured by re-lifting the
landed pair with backward flow; per-step clock not constant, c₁ = 0.1826).
All six boundary cells of the (d, n) detection map agree with the additive
budget rule |x₀|/(8d) + g(n) < t\* — and the map degenerates: the n = 0 row
flips exactly at phase 1's d\*, and **every n ≥ 1 cell is blind at every
degree**, so by the budget rule all nine known DH pairs are invisible to
every shifted Jensen polynomial with n ≥ 1. The GORZ direction (fixed d,
growing n), where hyperbolicity is a theorem for ζ, is for *detection* the
maximally blind direction. Two registered numeric guesses failed and are
recorded as such (the c₀ bracket; phase 1's planted-pair neighborhood); the
strong three-clock additivity test was not run and is marked untested.
Prior-art hooks recorded: Csordas–Norfolk–Varga's 1988 Λ ≥ −50 came from
non-hyperbolic Jensen polynomials of the flowed function, and its successors
dropped Jensen polynomials as needing impractical degrees — the dictionary
is a quantitative law of that documented inefficiency.

**Phase 3 (falsifier + trichotomy)**: the strong additivity test — re-measure
t_land(n=1) at d = 10⁶, predicted from the d = 10⁸ value and the degree
budget alone — passed at defect 1.46e-5 against a registered ±1e-4 bar, so
degree, shift and flow measurably spend one budget. The third
coefficient-side detector, Li's criterion, has the opposite geometry: a
planted quadruple at ρ = 0.8 + 2.5i turns the Bombieri–Lagarias sum negative
first at n = 95 (registered interval [80, 160]; one trough n = 95–98, period
16, positive again at 99), and the same amplification formula puts DH pair
1's Li onset at n ≈ 3.3·10⁵ (order-of-magnitude, ζ-shaped background hedge).
Trichotomy recorded in `jensen_clock/RESULTS.md`: two erasing clocks (degree,
shift — blind sets cofinal) against one accumulating discriminator (Li —
blind set an initial segment); none of the three blindnesses is a matter of
effort. One auxiliary statistic (the coded envelope-crossing indicator) was
mis-specified and is recorded as unusable.

**Disposition:** portrait and closure, not conjecture — no ledger entry.
Nothing here is evidence for or against RH. Spine candidates in
`jensen_clock/NOTES.md`.

### Higher xi derivatives (`higher_xi/`)

**Status: 2008 discrepancy resolved as a chapter-11 calculation error, two
measured oracles retained, no higher-derivative zeta constant claimed.** Ji
Bian's Figure 10.1 coefficients, substituted exactly into equation (11.5), give
`-202/36855` for `kappa=2` and `-10284002/1216215` for `kappa=3`, not the
reported `0.9544` and `0.9774`. The same substitution at `kappa=1` gives
`348002/405405 = 0.8584057917...`, matching the known control, so this is not
a global normalization mismatch. Page 93 also changes three signs from Figure
10.1; neither row produces the headline. Reconciling it would require omitted
tails canceling `95.46%` and `99.76%` of the shown weighted sums, contradicting
the page's negligible-tail premise. A completed-CUE experiment and an
independent Dirichlet-coefficient recurrence both put the tested
second-derivative form factor well below the displayed eleven-term
polynomial. The finite-cutoff window ladder decreases from `0.9342893` at
`ell=8` to `0.9311081` at `ell=14`; it is a discovery sequence, not a limit or
a theorem. Resolution in `higher_xi/RESOLUTION-2008-DISCREPANCY.md`; full
experiment in `higher_xi/RESULTS-higher-xi.md`.

### Frontier math (`frontier_math/`)

**Status: clean kill of the candidate constant, one measured collapse, one
quantified wall.** Continues `wide_search` THREAD 1 against the 10 August
2026 paper. Measured: the pair-measure LP (positivity + bandwidth-one data +
multiplicity types) reduces exactly to 2 − sup D and descends toward the
paper's 0.6725007 — the measure level adds nothing, answering THREAD 1's
residual question; the ceiling gap is configuration realizability. The
constructive half is withdrawn: the scan used `u u*`, while upstream uses
`u u^T`; the exact witness `1`, `i`, `-i` gives `tr(P₁Q′)=-2`, and the
proposed additive inequality can demand `9 ≥ 13`. The former candidate
**N₀ˢ ≥ 0.672529·N** therefore has no zeta implication. The ordered-gap LP
remains a measured configuration problem, and the bin-width ladder still
records its earlier midpoint-assignment defect. Also recorded: the sieve route to λ > 1
fails at scale T^{λ−1} (only HL itself closes it), and the CGdL transplant
reduces to one named obstruction (inertia counting for non-Gram kernels),
with BGSTB 2023's unconditional F ≥ 0 pinned as known. Closure record in
`frontier_math/CLEAN-KILL-REPORT.md`.

### The frontier map (`frontier_map/`)

**Status: a map, not a result — the `wide_search` findings and the source
paper's own limits assembled into one instrument, one JSON, one figure.**

Builds directly on `wide_search` and the 10 August 2026 pair-correlation
paper. `frontier.py` computes the whole λ-landscape H(λ) for the two kernels
the method accepts unconditionally (ζ and ξ′), pins the ceilings, prior-art
bars and the paper's structural wall as cited data, and renders
`figures/frontier_map.png`. Measured: onsets λ₀ = 0.550194 (ζ) and 0.513320
(ξ′) just above the paper's "nothing at λ ≤ ½" line; both curves monotone and
still climbing at the λ = 1 wall. The numeric ζ curve matches the paper's
closed form (eq. 7.4) to 9.5e-15 pointwise, and a planted mis-constant lesion
moves that comparison by 1.5e-2, so agreement is informative. The map's open
lanes are recorded as intervals: (0.6725007, 0.68185) for ζ within
bandwidth-one data, ξ′-vs-Wu closed negatively at 9.285e-4, κ ≥ 2 blocked on
Bian's missing tail bound, λ > 1 walled behind Hardy–Littlewood-strength
input. Results in `frontier_map/RESULTS-frontier-map.md`; controls in
`frontier_map/probe.py`.

### The wide search (`wide_search/`)

**Status: one measured constant, two negative results and one reproduction, all
about somebody else's method — not a result about zeta.**

An operator asked for one externally checkable mathematical contribution
adjacent to zeta: generate in volume, kill aggressively, search prior art,
reproduce independently, call nothing new without a novelty gate. Mission and
scope in `wide_search/MISSION.md`.

The breadth-first phase was abandoned as the wrong altitude. The target became
the paper of 10 August 2026 that raised the unconditional proportion of zeros
of ζ on the critical line to 0.6725, and specifically the one place it leaves a
variational problem unsolved: its Remark 7.3 on the zeros of ξ′, where it
reports a flat window and an unexplained quartic and records that neither
reaches Wu's unconditional 0.86957.

- **The sharp constant for that method is
  `0.86864150052976706411...`** (simple and on the critical line;
  `0.93432075...` distinct), attained at `lambda = 1`. Full account, with the
  functional and its provenance, in `wide_search/RESULTS-xiprime.md`.
- **It does not reach Wu's 0.86957**, falling short by `9.285e-4`. No admissible
  window closes the gap, so the comparison the paper leaves open is settled
  negatively. The paper's own quartic was already within `1.5e-6` of sharp.
- Checks: the instrument reproduces the paper's Theorem D to 10 digits before
  being pointed at anything unknown; the functional reproduces all four
  published constants of Remark 7.3 to every printed digit; three independent
  derivations of it agree and five independent computations of the optimum
  agree to 14 digits; the coefficient formula is checked exactly by Dirichlet
  convolution; and Bian's 2008 thesis reproduces the same `k = 1` coefficients
  exactly, from sixteen years earlier.
- **Higher derivatives are blocked, and `RESULTS-higher-derivatives.md` records
  why**: `F_k` for `k >= 2` already exists in an unpublished 2008 Rochester
  thesis, it has no closed form, its author states he cannot bound the tail, and
  the tabulated 11-term truncations are measured here to diverge at the
  bandwidth the method needs (`F_4(1) ~ 2476` against `F_1(1) ~ 2.78`, giving
  proportions of 1.198 and −2.64).

A second pass took the remaining thread — whether ζ's own 0.6725 can be moved
toward the 0.68185 ceiling — as far as the public material allows.
`wide_search/RESULTS-pair-ceiling.md`:

- **The scalar-moment formulation collapses, exactly.** Retaining only
  `(tr, ||.||_F^2)` per window makes the joint feasible set the intersection of
  the single-window half-lines, hence `sup_v H(v) = 0.6725007037...`. That route
  cannot move the number, and is closed rather than unfinished.
- **The published ceiling data reproduces.** `wide_search/pair_ceiling.py`
  recomputes, from the enclosures in the public `LawN256.lean` alone and with
  exact rationals, the `2^140` scale, 256 rows, the worst interior error
  `1.83670992316e-40`, `D(1) = 0.8239531607128352`, the stability coefficient
  `2.5431315104166665e-6` and the simple fraction `0.6818286874638315`. All
  agree with the repository. The extremal law itself needs a certificate file
  the authors state is available on request.
- **Remark 1.1's ceiling is stated more uniformly than its finite instance
  supports.** The `N = 256` law gives the `0.68185` sentence for certificates
  with `abs(r'(1)) + integral abs(r'') <= 8.38043022204...`. The formalisation
  carries the error terms and does not make that elision.

**Disposition:** the ξ′ constant and its negative consequence stand, and are
reproducible from this directory. One thread is closed (the scalar-moment LP),
one is blocked (a closed form for `F_k`, `k >= 2`), and one remains genuinely
open: the full-data LP over marked periodic configurations, which does not
reduce to the single-window bounds. No claim promoted, no ledger entry. Nothing
here is evidence for or against RH, and nothing here is a defect report against
the paper's Theorems A-E.

### The director run (`director_run/`)

**Status: not a hunt in the usual sense and not a result — a directorate record.
The instruments it touched are in `zeta/`, and every change it made there is
pinned by a test or stated as a corrected contract.**

An operator handed the laboratory over with no assigned theorem and the standing
instruction that finding a recorded conclusion of this repository to be wrong
counts as a result. Nine investigators with conflicting mandates ran in
parallel; the generator of a claim never judged it. Full record in
`docs/25-the-director-run.md`; programs, claim ledger, graveyard and
intervention ledger in `director_run/`.

- **Six defects in recorded claims**, each reproduced by the director before
  being written down. The most serious: `zeta/rigor.py`'s abscissa conversion
  parsed unrecognised numeric types from their *printed decimal*, so
  `proven_sign` returned a **wrong** nonzero sign on a `numpy.float32` input —
  identically on both backends, because the fault sits upstream of the split.
- **A strategic conclusion corrected.** The claim that a coefficient functional
  is "blind to the position of the critical line by construction" is false as
  written and mis-cited (`docs/18` §6 says *ordinate* statistics). The true
  statement is a threshold — `c_p ≤ d` for `ζ(s−δ)` exactly when `δ ≤ ½` — and
  it is the Selberg-class axiom's `θ < ½`, i.e. known. The `ROADMAP.md` call
  that hunt #5 asked for is answered: **no**, this does not become a standing
  constraint on the coefficient-side programme.
- **Two positives that held under attack.** A blind replicator, given the
  statement only and forbidden the package, reproduced the flagship Weil
  enclosure to 43 digits from scratch; and the Lean arm rebuilt on a cold
  machine, 8715 jobs, zero `sorry`s.
- **The formal arm's blocker was mis-diagnosed and is now measured.** Rung 3's
  centre could not have passed at any Taylor order — its budget counts the tail
  radius once where the norm counts it twice — and the width floor is the κ
  enclosure, not the exponential Taylor order. A configuration with ≥1.1×
  margins exists at 1.63× the term count and the same literal sizes.

**Disposition:** repairs landed with tests; no claim promoted; no ledger entry.
Nothing here is evidence for or against RH.


### Hunt #5 — a norm at every place (`local_positivity/`)

**Status: probe, complete. Instrument kept; no claim promoted; the headline is
a negative result about globalisation, plus an honest boundary on what the gate
actually tests.**

An ontology attempt in the sense of `docs/09` §4, pushed at Requirement C of
§5.1: construct, from prime data alone, a structure in which the Weil form is a
norm square, so its sign becomes formal. Reached one place at a time — and the
localisation is exactly where it dies. Raw numbers in
`local_positivity/results.json`:

- **The prime side factors place by place into a manifest norm.** With
  `Φ_p f = Σ_{m≥0} p^{−m/2} f(· − m log p)` it decomposes as
  `−Σ_p log p (Q_p(f) − ‖f‖²)`, `Q_p = (1−1/p)‖Φ_p f‖²` — a norm at every
  place, from coefficients only, with no zeros entering any definition.
  Reconstruction agrees with `zeta.weil.explicit_formula_sides` to 22 digits.
- **And the local norms do not assemble, which is the result.** `Q_p − ‖f‖²` is
  not of definite sign: 52 of the first 60 places positive, 8 negative. Local
  positivity is therefore compatible with either sign of `W`. Files under
  `docs/09` §5.1's taxonomy item #5, *finite approximants*.
- **Gate #3, with a crisp answer.** The place kernel has the closed form
  `K_p^(d)(θ) = Σ_j (1−|α_j|²/p)/|1−α_j p^{−1/2}e^{iθ}|²`, so `c_p ≤ d` is
  *exactly* the local bound `|α_j| ≤ √p`, with `d` read off each object's own
  gamma factors and never chosen. ζ and `L(χ)` quadratic mod 5 measure
  `c_p = 0.8284` and PASS (matching `2/(√p+1)` to 12 digits);
  Davenport–Heilbronn measures `1.8361` and FAILS at `p = 2, 3`; both disc −23
  Epstein forms FAIL, at `5.995` and `6.462`. "Where exactly does DH fail to
  embed?" — at `p = 2`, excess 0.836.
- **Decoy / surrogate.** Swapped coefficients move the verdict by 15 orders of
  magnitude — the control whose absence made the Imposter Gauntlet vacuous
  (`docs/15`). Against 300 random period-5 sequences 100% fail, median excess
  +5.88, and **DH sits at the 6th percentile**: a mild failure, not an exotic
  near-miss, echoing `ROADMAP.md`'s 27th-percentile calibration from an
  unrelated statistic.
- **Lesion.** Interpolating ζ → DH, blindness sets in at `ε* = 0.184`, so a
  PASS means "no violation above ~18% of the way from ζ to DH at the tested
  places", and nothing stronger. The PASS side is not vacuous either: across 60
  Satake angles the genuine degree-2 family keeps margin ≥ 0.343.
- **The honest boundary, stated so nobody overclaims it.** The gate is *not* a
  test for "has an Euler product". A genuine degree-2 product with
  `α = 2.3, 1/α` — legitimate in the Selberg class, violating Ramanujan — is
  rejected at `p = 5` with `c_p = 65.24`. It tests the local Selberg bound, and
  `localpos.scope()` says so inside the module rather than only in prose.

**Disposition:** instrument kept, avenue closed and recorded so nobody reopens
it; no ledger entry. Nothing here is evidence for or against RH. This is the
third statistic, after `D(f)` (`docs/18` §6) and the Fourier quasicrystal
separation (§4), to read arithmetic and stay blind to the *position* of the
critical line. **The reason recorded here was wrong, and the `ROADMAP.md` call
it asked for has now been made — the answer is no** (2026-08-11, `docs/25`).
`ζ(s−δ)` does *not* have the same coefficients: it has `n^δ a_n`, and `c_p`
reads that twist with threshold exactly `δ = ½` (`c_p = 2x/(1+x)`,
`x = p^{δ−½}`). Blindness is a property of a statistic invariant under that
twist, not of reading arithmetic — and a coefficient-side statistic equivalent
to RH is already in this tree (Mertens, `criteria.py` face 1). So the
repetition across three instruments does **not** rise to a standing constraint
on the coefficient-side programme, and must not be recorded as one. Full record in
`docs/24-the-local-positivity-attempt.md`; the session's own corrections,
including a citation defect it found in `docs/12`, are in
`local_positivity/CORRECTIONS.md`.

### Hunt #4 — repairing the counterexample (`flow_repair/`)

**Status: probe, complete. Instrument kept; no claim promoted; the headline
is a measured constant for the rival — and a null control that explains it.**

Pointed the de Bruijn–Newman flow (`zeta/heatflow.py`'s deformation, rebuilt
generic-Φ in the probe) at the Davenport–Heilbronn function for the first
time. Derived Φ_DH = 4e^{3u/2}Σ n aₙ e^{−πn²e^{2u}/5}, then *measured* the
normalisation rather than trusting the derivation: (c, a) = (1, 1) to 4.2e-42,
route agreement with `completed_dh` to 7.2e-41, and the same evaluator
reproduces `zeta.heatflow.H_t` to 5.4e-42 before being trusted on the rival.
Raw numbers in `flow_repair/results.json`:

- **The nine known off-line quadruples (Spira 1994; Balanzario–Sánchez-Ortiz
  2007, each re-polished in-tree) land on the real axis at measured times
  t\* between 0.00275 and 0.05765.** Each is a lower bound for
  Λ_DH := inf{t : H_t^{DH} real-rooted}; the max comes from the height-240
  pair (β ≈ 0.8695), **not** the famous height-85.7 zero, which places third.
  Λ_DH ≥ 0.0577 measured — inside [0, 0.2], the interval that historically
  bracketed Λ_ζ. In flow time, the counterexample fails RH by less than ζ's
  own uncertainty span: "Λ is small" distinguishes nothing (gate #3 on the
  flow axis).
- **Null control, the headline**: the arithmetic-free N-body zero dynamics
  ż = 2Σ1/(z−z') seeded with the measured t = 0 configuration reproduces
  every PDE repair time to **±0.04%** (target was 1%). The repair clock reads
  zero geometry, not arithmetic — the flow-time distance to real-rootedness
  is a property of where the zeros sit, shared by any function with that
  layout. Position-sensitivity (docs/18) meets the counterexample gate.
- **Method worth keeping**: the pair is tracked through its collision by
  contour moments — Δ(t) = 2q₂ − q₁² is analytic through the landing, so t\*
  is a clean root even though the zeros themselves have a branch point.
  Zero-census accounting closed in all five checked windows (line + 2·pairs
  = strip count; e.g. 49 + 4 = 53 at pair 1).
- **Lesions**: a contour clipping one pair member is refused (N=1 ≠ 2); a
  contour through the zeros returns winding ~1.8e9 and is refused. Post-
  landing, the newborn real pair is invisible to the default mean-gap/20
  sign scan at 3 of 5 grid phases until gap/step ≳ 1.4 — hunt #3's blind
  spot, measured on the other side of a collision.
- **Precision response**: t\*₁ = 0.0441263445516 identical to the last digit
  across dps 44/54/70 and 96/192 contour nodes; spread exactly 0.

**Disposition:** measurement portrait of a rival's flow geometry; no ledger
entry (the surviving observation — repair times are configuration geometry —
is the null control *explaining* the quantity, which is a closure, not a
lead). Nothing here is evidence for or against RH; nine pairs bound a sup
over infinitely many from below and say nothing about Λ_DH itself. Spine
candidate recorded in `flow_repair/NOTES.md`: a Φ-parametric entry point for
`zeta/heatflow.py` (a `zeta/` change, not this hunt's).

### Hunt #3 — the closest call (`lehmer_pair/`)

**Status: probe, complete. Instrument kept; no claim promoted; the headline
is a negative result supplied by the rival.**

Pointed the ball-arithmetic arm at Lehmer's pair γ₆₇₀₉/γ₆₇₁₀ ≈ 7005.06/7005.10
(gap 0.0377, mean spacing 0.895). Measured, with raw numbers in
`lehmer_pair/results.json`:

- The near-miss bump between the pair was decided **positive at 64 bits by
  both backends** — `proven_sign` pattern −,+,− on exact rationals, midpoints
  agreeing on `Z(7005.0819) = 0.003967335016595021` to all 16 digits — and a
  dense scan found exactly 2 sign changes with zero undecided samples.
- **Lesion**: the default grid policy of `rigor.certified_sign_changes`
  (mean_spacing/20 ≈ 0.0448) is *wider than the Lehmer gap*; sweeping the
  window phase, the default grid missed the pair entirely at 1 of 5 phases.
  Honest both times (a sign-change count is a lower bound), but blind.
- **Precision response**: enclosure widths shrink ~2^−prec with the midpoint
  pinned; at 32 bits flint straddles zero while mpmath.iv decides — the
  backends disagree about *decidability* at the boundary, never about value.
- **Rival, the headline**: the predicted "failed Lehmer bump" at
  Davenport–Heilbronn's off-line zero does not exist — Z_dh's closest
  approach on [85.2, 86.2] is **−0.357**, two orders of magnitude farther
  from zero than ζ's bump clears it, while hiding 2 strip zeros. So
  "|Z| gets small" flags nothing: it fires on ζ's healthiest close pair and
  stays silent at an actual RH violation. Magnitude heuristics die here;
  sign counting vs strip counting survives.

**Disposition:** portrait, not conjecture — no ledger entry. Spine candidate
recorded in `lehmer_pair/NOTES.md`: the default-step blind spot deserves a
docstring line on the packaged scanner (a `zeta/` change, not this hunt's).

### Hunt #2 — factorization vs. position (`factorization_vs_position/`)

**Status: probe, not established. The instrument used cannot support the
claim that was recorded.**

The hunt asked whether the factorization defect `D(F)` quantitatively
controls the Weil position residue, and recorded a "verified" correlation on
Epstein forms of discriminants −15, −20, −23, −24. Three defects, each
checked in-tree:

- **The completeness gate was never called.** `zeta/detector.py`'s own
  docstring states the load-bearing caveat: the residue measures "zeros
  unaccounted for by the supplied on-line list", so *a missing on-line zero
  produces a residue indistinguishable from an off-line zero*, and **a scan
  whose completeness has not been checked reports nothing trustworthy**.
  `online_list_is_complete` appears nowhere in `hunts/`. The on-line zeros
  were found by a `step=0.05` sign-change scan, which skips close pairs.
- **The lesion confirms the confound, measured.** Give ζ — factorization
  defect `2.65e-32`, a perfect Euler product — a zero list with **one
  on-line zero removed**, and the residue jumps from `0.0038` to **`1.99`**.
  An O(1) position residue is therefore produced by an incomplete list at
  *zero* factorization defect, which is precisely the signal the hunt read as
  off-line zeros. The recorded residues (4.07–4.33) sit at about twice that
  lesion.
- **The test set is the rival set.** The discriminant −23 principal form
  `(1,1,6)` is a **registered rival in `zeta.epstein.battery`**, admitted
  precisely because it lacks a scalar Euler product while keeping the
  functional equation. Confirming that the battery's rivals lack an Euler
  product and have off-line zeros restates their admission criterion. Under
  gate #3 that distinguishes nothing.

Separately, the recorded data does not show the claimed relationship:
across `results2.json` the defect varies by 2.7× (4.25 → 11.46) while the
residue moves 6% (4.07 → 4.33), and in `results.json` a 67× change in defect
(1.58 → 105.95) moves the residue 1.36× with `argmax_c` pinned at the same
`86.0` for all nine rows — the scan-window signature `docs/17` §2 says to
distrust.

**Disposition:** instrument retained, claim withdrawn, no ledger entry. The
correction to `HANDOFF.md` is in the same commit as this note. What the hunt
did produce is real and worth keeping: a *generalized* residue detector that
accepts an arbitrary archimedean bracket, which is the reusable part.
Pinned by `tests/test_hunt_probe_discipline.py`.

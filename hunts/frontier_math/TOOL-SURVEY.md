<!-- Landed from a survey agent, 2026-08-12. Wording note: this file was
rewritten to respect the hunts/ lexical rules (the reserved word of
zeta/rigor.py and the four banned claim-words are replaced by neutral
equivalents throughout); no factual content was altered. Vendor claims
are the vendors' own and are marked as such in the text. -->

# Tool survey for Zeta Lab, August 2026

Scope: fit against the four open items — (A) the bandlimited nonnegative-kernel
inequality over exponential sums, uniform in configuration; (B) the finite→infinite-lattice
bridge and the measured-cross-term upgrade; (C) adversarial/extremal configuration search
against a fast scorer; (D) finite numerical certificates → Lean-checkable rational/interval
artifacts.

Uncertainty is marked inline. Where I could not confirm something I say so rather than guess.

---

## 1. AlphaEvolve (Google DeepMind)

**What it does.** Evolutionary coding agent: you supply a scoring function and a seed
program; Gemini-driven mutation + selection searches the program space. Its published wins
are algorithm discovery (matrix multiplication, kernel scheduling, packing constants).

**Access, Aug 2026.** Moved from private preview to **general availability in July 2026** on
the Gemini Enterprise Agent Platform. The Google Cloud blog's own instruction is "reach out
to your Google Cloud Representative" — i.e. account-managed. Evaluators run client-side, so
your scorer stays on your infrastructure. **No published price** anywhere I could find, and
**no non-enterprise / self-serve path**. Treat "GA" as "GA to Google Cloud customers with a
rep", not "GA to two people with a credit card".
- https://cloud.google.com/blog/products/ai-machine-learning/alphaevolve-on-google-cloud/
- https://www.infoq.com/news/2026/07/alphaevolve-generally-available/
- https://deepmind.google/blog/alphaevolve-impact/

**Fit verdict.** Format fit for **(C)** is close to exact — "fast numerical scorer + search
over configurations/programs" is literally AlphaEvolve's interface, and packing-constant
problems are its demonstrated genre. Weak-to-no fit for (A) as a *proof* device: it produces
programs and constants, not uniform-in-n arguments. **But the access cost is the whole
story**: you cannot start this week without a Google Cloud account manager. openevolve (§2)
gives you 80% of the same thing today. **Not shortlisted.**

## 2. openevolve

**What it does.** Open-source reimplementation of AlphaEvolve. Apache 2.0,
`pip install openevolve`, ~6.9k stars, active through mid-2026, deterministic seeding for
reproducibility. Ships mathematical examples including circle packing (matches published
n=26 SOTA) and symbolic regression.
- https://github.com/algorithmicsuperintelligence/openevolve
- https://huggingface.co/blog/codelion/openevolve

**Backends.** Any **OpenAI-compatible** endpoint (OpenAI, Gemini, Cohere, plus local Ollama
/ vLLM), and Claude via the **Claude Code CLI** path. There is no first-class native
Anthropic Messages-API driver — you would point it at an OpenAI-compatible shim or use the
CLI integration. Note the caveat: this is what the repo README states; I did not run it.

**Hardware.** Python 3.10+. No GPU needed if you drive it from a hosted API. Cost is LLM
tokens, and evolution runs are token-hungry — budget accordingly.

**Fit verdict.** Best available substitute for AlphaEvolve on **(C)**, and the only one you
can start today with keys you already have. Secondary, more speculative use on **(A)**:
evolve the *parameters and case-split structure* of the damage bound (the thing currently
capping at n ≤ 7) against a scorer that measures the achieved uniform constant. **Shortlist #2.**

## 3. AlphaProof (DeepMind)

**Status.** No public API or downloadable system found as of Aug 2026. What is public is
**results**: DeepMind's AlphaProof Nexus (May 2026) resolved nine open Erdős problems, 44
OEIS conjectures, and an algebraic-geometry question, with Lean and natural-language proofs
posted at `github.com/google-deepmind/alphaproof-nexus-results`.
- https://winbuzzer.com/2026/05/26/google-deepmind-says-alphaproof-nexus-is-still-not-agi-xcxwbn/

**Uncertain:** one widely-shared social post claims DeepMind "open-sourced the system". I
could not confirm that from any primary source; the repository name and the coverage both
point to *proof artifacts*, not the prover. Do not plan around it.

**Fit verdict.** Would be a strong (D) tool if it existed as a service. It does not.
**Not shortlisted — no access.**

## 4. AlphaGeometry / AlphaGeometry2

**Status.** AG2 paper published in JMLR, Jan 2026. The **DDAR symbolic engine is open source
(Apache 2.0)** at `google-deepmind/alphageometry2`, and the original AlphaGeometry repo ships
a weight/vocab download script (`bash download.sh DATA=ag_ckpt_vocab`).
- https://github.com/google-deepmind/alphageometry2
- https://github.com/google-deepmind/alphageometry

**Fit verdict: no fit. Your instinct is correct.** AG/AG2 is a neuro-symbolic system whose
symbolic core (DDAR) is a deduction closure over a fixed vocabulary of *Euclidean geometric
predicates* — collinearity, concyclicity, angle and ratio equalities — with the LLM proposing
auxiliary constructions. It has no representation for measures, Fourier transforms, bandlimited
functions, exponential sums, or inequalities with real constants. There is no adapter from
(A) into its language. **Not shortlisted.**

## 5. Axiom (Carina Hong, founded 2025)

**What it claims.** Formal-mathematics AI producing machine-checkable Lean proofs; goal
stated as an "AI mathematician". AxiomProver reportedly scored 12/12 on the Putnam
(Dec 2025). Raised a **$200M Series A at ~$1.6B (March 2026, Menlo Ventures)**.
- https://b.capital/why-we-invested/toward-mathematical-superintelligence-why-we-invested-in-axiom/
- https://techfundingnews.com/axiom-math-ai-mathematician-64m-seed/

**Product actually available.** Not the prover — **AXLE** (Axiom Lean Engine), a **public
cloud API launched 5 March 2026** at https://axle.axiommath.ai, with an accompanying paper
(arXiv 2606.26442). It provides Lean 4 *utilities*: proof checking, proof-state analysis,
proof repair. Access: **anonymous use allowed** (10 concurrent requests) or API key
(20 concurrent), 15-minute max request timeout, "request more capacity" via form.
**No published pricing.**

**Fit verdict.** Modest, real fit for **(D)** as a second, independent Lean checking/repair
backend — useful for cross-checking Aristotle rather than replacing it, and its proof-repair
endpoint is the interesting piece for artifact maintenance across Mathlib bumps. Not a
generator of the mathematics in (A)/(B). **Not shortlisted — Aristotle already covers this
seat; adopt only if Aristotle's limits start to bite.**

## 6. Math, Inc. / Gauss

**What it does.** Gauss is an autoformalization agent — it completed Tao & Kontorovich's
strong Prime Number Theorem Lean project (~25,000 LOC) in three weeks against 18+ months of
prior partial human progress, using thousands of concurrent subagents at up to 12h each.
- https://www.math.inc/gauss

**Access.** No public pricing or self-serve signup for Gauss itself that I could find.
**But**: Math Inc. released **OpenGauss**, described as "permissively open source", at
`github.com/math-inc/OpenGauss` — a Lean autoformalization harness they claim beats Harmonic's
Aristotle agent on FormalQualBench. (Claim is the vendor's own; unchecked by me.)
- https://www.math.inc/opengauss

**Also relevant:** Math Inc. is associated with **Sphere-Packing-Lean** (see §9), which is the
single most directly reusable Lean asset I found for your problem shape.

**Fit verdict.** **Strong fit for the blueprint-scale formalisation of an extension package
(B and D).** This is exactly the workload Gauss was built for: a blueprint with many
mechanical leaves. The open harness means you can run it against your own model budget
rather than negotiating access. **Shortlist #4** (bundled with Sphere-Packing-Lean).

## 7. Terence Tao's tooling

**`teorth/estimates`** — https://github.com/teorth/estimates — a lightweight Python/sympy
proof assistant, deliberately Lean-shaped in its tactic model, for proving asymptotic
estimates X ≲ Y and X ≪ Y in analysis. v2.0 announced May 2025. Explicitly *less* powerful
than Lean; aimed at "short, tedious" inequality bookkeeping.
(Tao's blog posts describing it returned HTTP 403 to my fetcher; I am relying on the repo
description and search summaries — https://terrytao.wordpress.com/2025/05/09/a-tool-to-verify-estimates-ii-a-flexible-proof-assistant/)

**`teorth/expdb`** — exponent pair database, an actual analytic-number-theory automation
artifact.

**Equational Theories Project / leanblueprint** (Patrick Massot) — the human-readable
blueprint linked to Lean formalisation, and the social/technical machinery for splitting a
formalisation across many contributors (or agents).

**Fit verdict.** Honest answer on **(A)**: **low direct fit**. `estimates` handles scalar
asymptotic inequalities with implied constants; (A) needs *near-sharp explicit constants*
over a function-space positivity condition with a variable number of points. Those are
different problems and `estimates` will not close the n ≤ 7 gap. **Real fit for (B)/(D)**:
leanblueprint is the right project-management substrate for an extension package, and it is
what Gauss/OpenGauss consume. Use the blueprint tooling, not the estimate tool.

## 8. Open-weight / API Lean 4 provers, 2026

| System | Standing | Weights | Hardware |
|---|---|---|---|
| **Pythagoras-Prover-32B** | Claimed **top open-source on PutnamBench: 93/672**, 93.0% miniF2F-test (arXiv 2606.12594, Jun 2026) | 4B on HF substantiated; 32B claimed — *I did not verify the 32B weight card* | ~1×80GB GPU bf16, or quantized on 48GB |
| **Goedel-Prover-V2-32B** | 88.1% miniF2F @Pass@32 (90.4% self-correct), 86 PutnamBench — prior open SOTA | Open, `Goedel-LM/Goedel-Prover-V2` | 1×80GB |
| **Goedel-Prover-V2-8B** | 84.6% miniF2F @Pass@32 — matches DeepSeek-Prover-V2-671B at ~100× smaller | Open | 1×24GB |
| **DeepSeek-Prover-V2-671B** | 47 PutnamBench | Open weights, impractical for a two-person lab | multi-node |
| **Kimina-Prover** | Strong miniF2F/PutnamBench | Open weights (various sizes) | varies |
| **Seed-Prover (ByteDance)** | IMO medal-level | **No open weights found** | n/a |

Sources: https://github.com/Goedel-LM/Goedel-Prover-V2 , https://arxiv.org/html/2606.12594v1 ,
https://arxiv.org/pdf/2507.23726 , https://arxiv.org/pdf/2504.21801

**Complement to Aristotle?** Yes, in one specific way: **cheap, unmetered, high-volume
first-pass `sorry` filling**. These are whole-proof/step provers tuned on competition-shaped
goals — they will clear the mechanical leaves of a blueprint (arithmetic side conditions,
routine bounds, rewriting) without consuming Aristotle calls, leaving Aristotle for the
hard leaves. They will *not* do research-level analysis. Caveat: competition benchmarks
correlate poorly with Mathlib-heavy analysis goals; expect the measured hit-rate on your
actual sorries to be well below headline miniF2F numbers.

## 9. Positivity / SOS / certificate tooling for the shape of (A) — the richest category

This is where I would spend the effort. Four distinct families, and the honest scoping matters.

**(a) Arbitrary-precision SDP solvers.** `SDPA-GMP` (https://github.com/nakatamaho/sdpa-gmp,
open source, CPU) is the workhorse of exactly your lineage: the sphere-packing and
spherical-code LP/SDP bound literature runs numerics at 200+ digits in SDPA-GMP and then
establishes the numerical solution can be replaced by an exact one. See Cohn et al., *Three-point
bounds for sphere packing* (https://arxiv.org/pdf/2206.15373) for the pattern: solve
numerically at high precision, then **prove existence of an exact solution with specified
behaviour**, rather than trusting round-off. This is the same trick you already executed
twice (LP dual, band cover), applied to a bigger cone.

**(b) Numerical SDP → exact rational certificate.** A real literature, with methods:
rounding-projection, perturbation-compensation, SOS over gradient ideals with rational
coefficients (SIAM J. Optim. 10.1137/21m1436245), and **dual certificates yielding exact
weighted-SOS "without any rounding"** over compact sets (SIAM J. Optim. 10.1137/21M1422574).
Crucially, the rounding-projection family **has been extended explicitly to trigonometric
polynomials** — which is what F_on and F_p are, as polynomials in e^{iw}.

**(c) Moment-SOS software.** `TSSOS` (Julia, https://wangjie212.github.io/TSSOS/dev/) exploits
term sparsity to make the Lasserre hierarchy tractable at your sizes; `SumOfSquares.jl`,
`GloptiPoly`, `MomentTools.jl`, `MomentSOS.jl` are the alternatives. Classical
**Fejér–Riesz** gives exact spectral factorisation for a nonnegative univariate trigonometric
polynomial, and positivity of a bandlimited-kernel quadratic form is a Bochner/Toeplitz PSD
condition — so there is a clean, classical certificate route for the *fixed-configuration*
statement.

**Honest limit — read this before getting excited.** SOS/SDP gives you **rigorous certificates
for fixed n and fixed structure**, not a bound uniform over all finite configurations. The
stated obstruction in (A) — needing 1/s² far-field decay plus band/cluster repulsion with
near-sharp constants, uniform in n — is *not* something a moment-SOS hierarchy closes; the
problem is not a fixed polynomial optimisation. What this family buys you is: (i) sharp,
enclosure-carrying constants for each n up to a much larger N than 7, cheaply, which is exactly the
input the finite→infinite bridge (B) consumes; (ii) machine-generated exact rational Gram
matrices, which is exactly the input (D) consumes. Those two are worth a lot. A uniform proof
is not on offer here.

**(d) Rigorous interval global optimisers** — for the far-field damage bounds and for
enclosure-carrying adversarial search:
- **Kodiak** (NASA, C++, https://github.com/nasa/Kodiak): branch-and-bound with interval
  arithmetic *and* Bernstein enclosure; the generic branching algorithm is itself formally
  checked in PVS. v2.0.5, May 2024. Best-in-class for "certify a uniform constant over a
  compact parameter box".
- **IntervalOptimisation.jl** (Moore–Skelboe, Julia), **Ibex** (C++), and your existing
  Arb/`rigor.py` stack.
- Hales-lineage **Taylor interval approximation** for formal nonlinear inequalities
  (https://arxiv.org/pdf/1301.1702) — the method that carried Flyspeck's inequalities.

**(e) SDP/SOS → Lean.** Two concrete assets:
- **NSPI** (arXiv 2605.15445, 2026): LLM conjectures an SOS decomposition, Gauss–Newton +
  rational recovery produces an **exact rational Gram matrix**, and a Lean tactic assembles
  the proof via `linear_combination`. **No public code found.** Polynomial only, ≤10 variables,
  success falls to 11.7% at 10 vars. Low fit as a product — **but the final-mile template
  (exact rational Gram → `linear_combination`) is directly reusable for (D)** and costs you
  nothing to copy.
- **Sphere-Packing-Lean** (https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean ;
  mirrored/associated as `math-inc/Sphere-Packing-Lean`), the Hariharan–Viazovska project,
  reported formally checked in Feb 2026. It contains **`LinearProgrammingBound`,
  `SchwartzMap.PoissonSummation_Lattices`, `IsDecayingMap`, and Fourier-positivity conditions
  in Lean 4** — i.e. an existing, checked Lean API for *bandlimited positivity + Poisson
  summation on lattices*. **This is the closest existing Lean scaffolding to your (B) bridge
  and (D) artifacts that I found anywhere in this survey.** (My fetch of the raw repo 503'd;
  the module inventory comes from the project blueprint and DeepWiki, so treat exact names as
  provisional until you clone it.)

**Adjacent, unavailable:** OpenAI's **Astra** (1 Aug 2026) announced ten results including
**high-dimensional sphere packing, binary and spherical codes** — the exact neighbourhood of
(A) — with Lean certificates published at `github.com/openai/ten-proofs`, compute cost
reported around $2,000. **Astra itself is unreleased.** OpenAI separately opened free model
access for ~100,000 academic researchers ("ChatGPT for Academic Researchers"), which is a real
access path to *frontier chat models*, not to Astra. The published certificates are worth
reading as prior art for (D) regardless.

## 10. "MathCopilot", "AI co-mathematician", "oforge"

- **MathCoPilot** — resolves to a real thing: arXiv 2607.14582, USTC, "An Interactive System
  for Human–AI Symbiotic Paradigm of Mathematical Research". A workbench with a *living proof
  blueprint*, skill orchestration with Lean-integrated iterative checking, and paper
  retrieval + autoformalisation into a Lean knowledge base. Project page mathcopilot.cn.
  **Open-source status and availability: unsubstantiated.** Research prototype; the blueprint-as-
  shared-state idea is worth stealing, the system is not worth waiting for.
- **"AI co-mathematician"** — a *genre label*, not a product. It appears as terminology in
  e.g. LeanMarathon (arXiv 2606.05400). Nothing to integrate.
- **"oforge" / "OForge"** — **does not resolve to any AI or mathematics tool.** The name is
  taken by a Trac-based collaboration tool (2008), a PHP web-application framework
  (`github.com/oforge/oforge-core`), and 2D LiDAR configuration software. If someone told you
  OForge was an AI-for-math product, they were mistaken or thinking of something else. I am
  not going to invent a referent for it.

---

# Ranked shortlist — 5 integrations, by (value to A–D) / (setup cost)

### 1. SDPA-GMP + exact-rational rounding → Lean artifact
**Points at:** (A) at fixed n, and (D). Reformulate the fixed-configuration inequality as an
SDP/LP in the bandlimited cone; solve at 200+ digits; round to an exact rational Gram matrix
by the dual-certificate method; re-verify the rational certificate in `rigor.py`/Arb; emit a
Lean `linear_combination` artifact using the NSPI template.
**Operator needs:** nothing. Open source, CPU only, no keys, no accounts.
**First experiment:** take the n = 7 configuration that currently saturates the uniform damage
bound. Produce a *enclosure-carrying* margin for it via SDPA-GMP + rational rounding, end to end into
Lean. If that lands, push N upward and see where certificate size, not mathematics, becomes
the binding constraint. This is a straight extension of a pipeline you have already run twice
— lowest risk, highest confidence.

### 2. openevolve against the existing fast scorer
**Points at:** (C), with a stretch at (A).
**Operator needs:** an OpenAI-compatible endpoint (their Anthropic key via a shim, or the
Claude Code CLI path), a token budget. No GPU, no cloud account.
**First experiment:** evolve *configuration generators* (programs emitting (x_i, y_i, t_i, n, k))
to minimise the margin under the scorer. Seed the population with the known n ≤ 7 hard cases.
The decisive question it answers cheaply: **is the n ≤ 7 cap an artifact of the uniform-constant
proof technique, or does an actual adversarial configuration approach the bound at larger n?**
Those two answers point at completely different next moves, and the classical global optimiser
already running is a fair baseline to beat.

### 3. Kodiak (or IntervalOptimisation.jl) for enclosure-carrying far-field damage bounds
**Points at:** the specific named obstruction in (A) — 1/s² far-field decay with near-sharp
constants — and rigorous checking of (C)'s findings.
**Operator needs:** nothing (C++ build, or Julia). Interval arithmetic you already trust.
**First experiment:** express the far-field damage function on a compact box in the two or
three parameters that matter and branch-and-bound it to a *enclosure-carrying* uniform constant,
replacing the hand-derived bound. Kodiak's Bernstein enclosures are usually much tighter than
naive interval arithmetic on this shape, which is precisely what "near-sharp" requires. If the
enclosure-carrying constant beats the hand bound, the n ≤ 7 cap moves without new mathematics.

### 4. Sphere-Packing-Lean as scaffolding + OpenGauss as the formalisation labour
**Points at:** (B) and the blueprint-scale extension package in (D).
**Operator needs:** GitHub for the Lean library (free); OpenGauss needs an LLM key and
meaningful parallel compute for its subagent fan-out.
**First experiment:** clone Sphere-Packing-Lean and audit whether
`SchwartzMap.PoissonSummation_Lattices` plus its Fourier-positivity API can *state* the
finite→infinite-lattice bridge in the form you need — the "margins approach the limit from
below at resonance spacings" claim is structurally a Poisson-summation-on-lattices argument.
If the statement types, write the blueprint and hand the leaves to OpenGauss with Aristotle
held in reserve for the hard ones. If it does not type, you have learned that cheaply, in a
day, and you keep the reading.

### 5. Goedel-Prover-V2-32B (or Pythagoras-Prover-32B) as a first-pass `sorry` filler
**Points at:** (D) throughput only.
**Operator needs:** one 80GB GPU — rented by the hour is fine — or a hosted inference endpoint.
This is the only shortlist entry with a hardware ask.
**First experiment:** replay the `sorry`s from the six already-checked Aristotle artifacts as a
held-out set and measure the hit-rate. Adopt only if it clears roughly 30%; below that the GPU
time costs more than the Aristotle calls it saves. Note this is a **budget** optimisation, not
a capability gain — do it fifth, or not at all, if Aristotle is free and not rate-limiting.

## Not on the list, and why

- **AlphaEvolve** — same algorithm as #2, gated behind a Google Cloud account rep with no
  published price. The famous name buys you nothing openevolve does not, and costs weeks.
- **AlphaProof / AlphaProof Nexus** — no access. Only proof artifacts are public. The claim
  that the system was open-sourced is unchecked and probably a misreading.
- **AlphaGeometry2** — wrong domain, categorically. Euclidean-predicate deduction has no
  encoding for Fourier-analytic inequalities. Open weights do not help when the vocabulary
  is disjoint.
- **Astra (OpenAI)** — closest published work to (A)'s neighbourhood, and unreleased. Read
  `openai/ten-proofs` for prior art on certificate style; you cannot run it.
- **Axiom / AXLE** — a genuine public API and a fine tool, but it occupies the seat Aristotle
  already holds for you, for free and working. Adopt only on a rate-limit or repair need.
- **MathCoPilot** — research prototype, availability unsubstantiated. Steal the blueprint-as-shared-
  state design; do not wait for the product.
- **NSPI** — no public code, polynomials only. Copy the `linear_combination` template into
  entry #1 and move on.
- **Tao's `estimates`** — right spirit, wrong target: implied-constant asymptotics, not
  near-sharp explicit constants. Take leanblueprint from that ecosystem instead.
- **"oforge"** — not a real math tool under any spelling I could find.

---

# Addendum, 2026-09-04: three of these were measured against a live board

Written after wiring Aristotle, AXLE and Leanstral into Ostoyae's lean-eval board and watching
real agents use them. The August entries above are unchanged; this records what running them
showed, which is mostly about latency and not about proof strength.

## The operational finding, which outranks the quality question

**A prover an agent cannot wait for is a prover an agent does not use.** An agent's shell tool is
cut off after a couple of minutes. Aristotle takes seven minutes on a good statement and
twenty-five on a hard one. On the third batch, **five of six cells submitted a statement to
Aristotle, then proved the lemma by hand while waiting, and exited before any answer arrived.**
Three of them polled; two never checked back at all. Zero of the five answers were used.

The clearest case: `Turing.TM2ComputableInTime.natAdd`. The cell hand-wrote 545 lines of Lean,
$11.97, and landed it. Aristotle's answer came back twenty-six minutes after submission with a
complete explicit machine — binary arithmetic layer, the machine, a `2n + 3` time bound,
sorry-free, `#print axioms` reporting only `propext`, `Classical.choice`, `Quot.sound`. Nobody was
left to read it. The lemma was proved twice and paid for twice.

Two lessons, both cheap to act on: an out-of-band job must have its id recorded somewhere that
outlives the cell, and a synchronous tool is worth more per dollar than a stronger asynchronous
one for anything a cell does inside its own session.

## 5b. AXLE (Axiom's Lean Engine) — the August entry undersold it

The entry above says "not shortlisted; Aristotle already covers this seat". Wrong for our use, for
a reason that is nothing to do with proving:

- `POST https://axle.axiommath.ai/api/v1/check`, anonymous, no key, `{environment, content}`.
- **Thirteen toolchains, `lean-4.21.0` through `lean-4.33.0`**, which includes both `lean-4.28.0`
  (what Aristotle proves at) and `lean-4.33.0` (what the lean-eval board builds at).
- A true statement with `import Mathlib`: `okay: true` in **12–19 ms**. A false one:
  `okay: false`, `failed_declarations`, and the goal state.

So it answers two questions that were costing real money. *Does this proposed statement even
elaborate* — currently discovered by an Opus verify attempt that builds a workspace to find a
typo, and on this board **6 of the 62 items ever given a prove attempt turned out to be false or
ill-typed**. And *does an Aristotle proof survive the port from 4.28.0* — previously a worktree
and a build; now two calls. Tried on the real case: the `Subgroup.normalizer_bot` proof Aristotle
returned on 2026-09-03 elaborates at 4.33.0 in 18 ms once the statement is rewritten for the
`Set G` signature change.

Caller: `bin/ask-axle` in teal-sea/Ostoyae.

## 10. Leanstral (Mistral, Sept 2026) — new, and the one that fits inside a cell

`mistral.ai/news/leanstral`. Leanstral-120B-A6B, 6B active, Apache 2.0 weights, targeting Lean
4.29.0-rc6, evaluated by its authors on their own FLTEval rather than miniF2F or PutnamBench.

Two things the announcement gets wrong for a caller:

- **The model id is `labs-leanstral-1-5-1`** (and `labs-leanstral-1-5`). The post names
  `labs-leanstral-2603`, which returns "model not found" on the API.
- **Labs models are off by default**: every call is `403 labs_not_enabled` until an org admin
  turns them on at `admin.mistral.ai/plateforme/privacy`.

**Measured, 2026-09-04.** ~0.9–1.2 s per call. On its own it is not reliable: asked for
`Subgroup.normalizer_bot` it returned a plausible tactic block that failed to elaborate, twice.
Paired with AXLE in a propose–check–repair loop it is a different tool — the compiler error and
goal state go straight back into the conversation:

| | wall clock | rounds | outcome |
|---|---|---|---|
| Leanstral alone | ~1 s | 1 | does not elaborate |
| Leanstral + AXLE, by hand | ~4 s | 3 | accepted by the kernel at 4.33.0 |
| `bin/ask-leanstral` (the loop in one call) | **1.178 s** | 1 | accepted by the kernel at 4.33.0 |

Aristotle, on the same statement on 2026-09-03: **seven minutes**, and a better proof —
`Subgroup.normalizer_eq_top_iff.mpr inferInstance`, the library one-liner, against Leanstral's
six-line tactic block. So this is not "Leanstral is stronger". It is that Leanstral is fast enough
to sit inside the loop the agent is already in, and Aristotle is not.

**The shape that follows**: Leanstral + AXLE as the cheap synchronous first pass on every leaf;
Aristotle for what survives it, submitted early with its job id written into the record so a later
attempt collects the answer. One sample, one lemma — the third batch is the first run with any of
this wired, and the numbers above should be re-measured over a spread of real items before anyone
leans on them.

Callers: `bin/ask-leanstral`, `bin/ask-axle`, `bin/ask-aristotle`, all in teal-sea/Ostoyae.

# AGENTS.md — operating context for the repo root

A computational laboratory for the Riemann zeta function and RH. Read
`README.md` for the front door and `docs/00-orientation.md` for scope.

`ROADMAP.md` carries the project's decisions, deliberate non-goals, known gaps
and the next planned build — read it before proposing or planning work.

This file is the single source of operating context for **any** coding agent
working in this repository (Claude Code, Codex, Cursor, Aider, …). `CLAUDE.md`
is a pointer to this file; do not duplicate content between them.

## Setup (first run in a fresh clone)

```bash
python3 -m venv .venv
.venv/bin/pip install -r requirements.txt
.venv/bin/pip install -e .
.venv/bin/python -m pytest -q -m "not slow"   # confirm green before changing anything
```

**Check the ball-arithmetic backend before you trust a green run**:

```bash
.venv/bin/python -c "from zeta import rigor; print(rigor.BACKEND, rigor.available_backends())"
# want: python-flint ['mpmath.iv', 'python-flint']
```

If `python-flint` is missing, `rigor.py` silently falls back to mpmath's `iv`
context. That is by design and the fallback is correct — but it is roughly
**1600× slower** on the certified paths (one `test_rigor.py` case goes from
0.76 s to over twenty minutes, which reads as a hung fast tier, not a slow
one), and the five `skipif(not HAVE_FLINT)` tests silently disappear. Three of
those say *"needs both backends installed"*: they are the Arb-vs-mpmath
cross-check that is the whole reason `rigor.py` may claim the word
*certified*. **A suite that reports "5 skipped" here is not exercising that
cross-check**, so a fresh clone should install `python-flint` (it is pinned in
`requirements.txt`) rather than treat the skips as normal.

## The knowledge index

`CONTEXT.md` is a generated index of the public API, the document list, the
script list and test counts — the *facts*. This file carries the *judgment*.
Regenerate the facts rather than editing them:

```bash
.venv/bin/python scripts/make_context.py          # rewrite CONTEXT.md
.venv/bin/python scripts/make_context.py --check  # non-zero exit if stale
.venv/bin/python scripts/make_context.py --flat   # + CONTEXT_FLAT.md, whole repo in one file
```

Regenerate it whenever you add or rename a public function, a doc or a script.
`llms.txt` is the short curated map for tools that look for one.

## Multiple agents / parallel sessions

Several agents or sessions may work this repository in parallel, on branches
or worktrees. To prevent scope creep and collisions:

- **Repo-wide rules**: this file. **Per-area scope**: an active branch,
  worktree, or exploratory directory (e.g. under `hunts/`) carries a
  `MISSION.md` stating what that work is and is not allowed to touch — read
  it before acting there.
- **Namespacing**: keep exploratory math out of `zeta/` (core) and
  `ontology/` (domain-agnostic); new exploratory work goes in its own
  subdirectory under `hunts/`.
- **Handoffs**: communicate through the `conjectures/` ledger rather than
  editing shared core files simultaneously.
- **Worktrees**: avoid literally simultaneous runs against the same
  checkout; for parallel work use `git worktree add` so each agent gets its
  own tree.
- **Verify first**: confirm the suite is green (see Setup) before building
  on a tree.

### Outside environments (read-only mounts, notebook agents)

Some sessions run this laboratory from an environment that is not this
checkout: a notebook-style agent (Claude Science and anything like it) that
mounts the repository **read-only** and brings its **own Python**. That suits
the exploratory half of this tree — cells, background execution and
interruption fit expensive mpmath work — but it breaks two assumptions the rest
of this file is entitled to make, and both break *silently*.

**Run the preflight as the first cell, before any mathematics:**

```bash
python scripts/science_preflight.py          # or --allow-fallback
```

It reports the interpreter and dependency set, plus three things no outside
session can infer from a snapshot: whether `rigor.BACKEND` is really Arb (a
missing `python-flint` degrades to mpmath's `iv` — correct, ~1600× slower, and
it removes the cross-check that is the only reason `rigor.py` may use the
reserved word), whether a Lean build is possible at all, and **the next free
`docs/` number**. It exits non-zero when the environment cannot support the
claims this tree knows how to make.

The standing rules for such a session:

- **Guess no number and no name.** Take the next free doc number from the
  preflight. Two documents once shared number 21 because a session working from
  a snapshot could not see the tree it was writing into;
  `tests/test_docs_numbering.py` now catches that, but only if you run it.
- **An artifact is not a commit.** Say plainly that files were produced and not
  landed, and never describe a read-only tree as changed. Workspace storage is
  swept after idle gaps; the artifact is the durable copy until someone commits
  it.
- **Write only where a hunt may write**: `hunts/<name>/` with its `MISSION.md`
  written first, one new `docs/NN-*.md`, and `figures/`. Not `zeta/`,
  `ontology/` or `harness/` without explicit permission.
- **The lexical rules are lexical.** The reserved word is banned everywhere
  under `hunts/` *including inside a sentence disclaiming it*, and *verified* /
  *confirmed* / *definitively* / *proves* are banned too. Intent does not exempt
  a file; the test reads the bytes.
- **Before handing anything back**, run at least
  `tests/test_docs_numbering.py`, `tests/test_hunt_probe_discipline.py`,
  `tests/test_doors.py`, and `scripts/make_context.py --check`.

## Where the operating material lives

This repository is the **public research record**: mathematics, tests, proofs,
evidence, and enough method that an outside reader can evaluate or reproduce a
claim. That is why it is public, and it is the standard for what belongs here.

**How the laboratory is operated lives in a separate private repository**
(`fulcrum`): operator strategy, hunt briefs and their generation, the prompt
corpus, session launching, telemetry economics, and any future routing or
allocation logic. Those have no bearing on whether a scientific claim here is
correct, so they are not published.

The boundary, applied with judgment rather than by a rule engine:

> If an outside observer needs it to **evaluate or reproduce a public claim**,
> it belongs here. If it teaches the lab how to **allocate, route, prompt, or
> operate itself**, it belongs in fulcrum unless reproducibility needs it.

Preregistrations and protocols stay here even when unflattering — the harness
gate record (`harness/VERDICT.md`, `harness/gate-evidence/`) is public precisely
because a negative result about our own tooling is credibility, not capability.

Flag genuinely ambiguous cases to the operator. Do not build a framework to
adjudicate them.

## How the work is organised

Two working ideas and one objective. None is settled; all three are here rather
than in a strategy document because you should meet them while working.

**Core ↔ Pursuits.** *Core* is work that improves the lab's reusable ability to
work: infrastructure, tooling, telemetry, agent coordination, reusable method.
*Pursuits* are what the lab is chasing outward: research questions, hunts,
investigations. They are **not** a hierarchy and not an ancestry — they create
each other in both directions. A hunt that needs a tool produces Core; Core work
that trips over a phenomenon produces a Pursuit; a piece of Core can itself
become the subject of a Pursuit (`harness/` did exactly that, and lost). The
distinction describes a thing's **current role**, not its rank or its origin.
Do not rename directories to make the tree look like the metaphor.

**Forage, don't roadmap.** Explore several directions cheaply; when one produces
credible signal, feed it more; when it stops, stop feeding it. Preserve the
threads you are not pulling, so choosing one direction does not require
forgetting the others — that is what `THREADS.md` is for. This is a working
strategy, not a proven optimal policy.

**The economic objective: maximize valuable output per monetary unit of input.**
This is *not* "minimize tokens". Money is the input and valuable output is the
objective; models, tokens, extra agents, verification, formalization,
infrastructure and operator time are all allocation choices. **A more expensive
approach is the right one whenever the extra output justifies the cost** — and a
cheap approach that yields low-value or unreliable output is not efficient, it
is just cheap. We do not yet have a complete metric for "valuable output". Do
not invent one and treat it as settled; it is an open research question, not
a KPI.

**Design discipline, learned the expensive way.** Before adding any abstraction,
answer: *what live thing in this repository will use this immediately?* If the
answer is "future agents might", do not build it. Prefer real need → smallest
implementation → actual use → measurement → only then generalization. Do not
build infrastructure without a live consumer, do not generalize a workflow
before the concrete workflow earns it, and do not build a meta-system to manage
the meta-system. `harness/VERDICT.md` is what the alternative cost.

  Read that verdict as a bet properly made and properly ended, not as a blunder.
  It was a reasonable thing to try, it was built well, it was tested against the
  practice it meant to improve, and it lost. **Being able to kill something you
  funded, on evidence, is the habit worth keeping** — a lab that cannot do that
  has preferences rather than a method. Retiring it is a success of the process
  and a failure of the thing, and the two are not the same judgement.

## Loose threads

Things worth remembering that nobody is pursuing right now. `THREADS.md` is the
whole mechanism: a flat file, one block per thread, five fields. Add one the
moment you notice something and decide not to chase it — the cost of writing it
down is seconds and the cost of losing it is a rediscovery.

`scripts/70_lab_state.py` already derives *live* work from git (every branch
ahead of `origin/main`). It cannot derive a parked thread, because a parked
thread has no branch — that gap is exactly what the file covers, and it is the
only reason it exists rather than being derived.

## Hard rules

- **Python**: ALWAYS `.venv/bin/python (from the repo root)` — never bare
  `python3`. All dependencies live only in that venv (mpmath, numpy, scipy,
  matplotlib, sympy, pytest).
- **matplotlib**: headless. Set the backend *before* importing pyplot:
  `import matplotlib; matplotlib.use("Agg")`. `zeta/plots.py` already does
  this; scripts that plot must too.
- **Precision**: mpmath for anything precision-critical, with `mp.dps` set
  explicitly (house style: `mp.workdps(...)` context managers, guard digits
  internal, no global mpmath state left modified). numpy only for bulk
  statistics.
- **Any mathematical claim added to code or docs must be numerically checked
  by a test, or explicitly hedged at the point of use.** This is the repo's
  central habit: every number in a docstring is pinned by `tests/`; identities
  are exposed as measured *defect* functions (`functional_equation_defect`,
  `theta_modular_defect`, ...), not assumed.
- **Honest-scope rule & Phase II Objective**: Zeta Lab is a computational and formal workbench.
  Phase II's explicit Research Objective is to **produce one externally verified mathematical statement that humanity didn't previously know** (e.g. a new theorem, counterexample, bound, equivalence, or robust conjecture).
  However, it still makes no claims to advance RH itself. Nothing here is evidence for RH (Littlewood's theorem, `docs/08`). Never
  write language implying a computation settles or supports RH; the sanctioned
  framing for the sign-change verification is "proof for the finite range,
  modulo the correctness of the floating-point sign evaluations".
- **The certainty ladder** (amended 2026-08-12; replaces the blunt "an
  apparent settlement is a bug" heuristic, which treated a kernel-checked
  proof and an eyeballed number alike). When a computation appears to
  settle something open, the correct FIRST inference is still a bug -- the
  `hunts/frontier_math` ledger records nine defects in two days caught by
  exactly that reflex -- but the inference is *discharged* by climbing the
  ladder, and a claim may then carry the strongest language its rung has
  earned:
  1. *measured* -- one route, float grade. Say "measured", "observed".
  2. *hardened* -- independent routes agree and/or ball-arithmetic
     enclosures carry every step (`rigor.py` grade). Say "hardened",
     "enclosure-carrying".
  3. *kernel-checked* -- Lean 4 + Mathlib, zero sorrys, standard axioms
     only. These are theorems; call them theorems, without apology.
  4. *externally reviewed* -- a qualified outside reader has walked the
     chain. "Established", "landmark", "settles" become available here
     and not before.
  A composite claim takes the grade of its WEAKEST step: a chain of
  theorems glued by one measured step is a candidate and is called one.
  The reserved words stay reserved ("certified" to `zeta/rigor.py` and
  the Lean arm; the `hunts/` lexical bans unchanged -- tests enforce
  them). This rule licenses confidence at every rung a claim has earned;
  it does not license rounding a rung upward for an audience.
- **Derive conventions, never remember them.** Where the literature disagrees
  on factor placement or a constant, the repo calibrates numerically and
  cross-checks: the Riemann–Weil explicit-formula convention in `zeta/weil.py`
  was validated by computing both sides independently for four test functions
  from three unrelated families; κ in `zeta/epstein.py` is re-derived by a
  linear solve on every call, with the pinned string only a test reference.
  Follow that pattern for any new formula with a contested normalization.
- **The Lean arm counts nothing with a `sorry`.** `lean/` is the second
  certainty regime: theorems kernel-checked by Lean 4 + Mathlib, built with
  `cd lean && PATH="$HOME/.elan/bin:$PATH" lake build`. Nothing there counts
  until it compiles with zero `sorry`s — a `sorry` is an uncertified step,
  tracked in the file, never hidden. Lean proofs and `rigor.py` enclosures are
  the only two things in the repo that may use the word "certified", and they
  are different regimes (kernel-checked symbolic truth vs enclosure-carrying
  numerics); say which one you mean.
- **"Certified" is a reserved word.** Only `zeta/rigor.py` may claim it, and
  only for a quantity every step of whose computation carried an enclosure.
  A dict that reports `certified: True` is asserting a theorem; if any step
  silently falls back to floats, that is a critical defect, not a rounding
  detail. The safe failure mode is mandatory: `proven_sign` returns `0` for
  "not decided", uncertifiable steps are named in `uncertified_steps`, and
  `certified` is False whenever that list is non-empty. Everything else in the
  repo is *accurate*, which is a different and weaker claim — say which one you
  mean. Non-rigorous cross-checks (mpmath `nzeros`, `backlunds`) must stay
  flagged as such in the returned dict.
- **The counterexample battery is a standing test.** Any claimed structural
  property that "explains" RH must be run through `zeta.epstein.battery`
  (ζ and the Davenport–Heilbronn function behind one interface): f satisfies
  the functional equation, has real coefficients and a real Hardy-style Z,
  and violates RH — a claim f also passes distinguishes nothing (docs/09,
  gate #3; docs/08 §4.1).

## Layout

- Package: `zeta/` (flat layout, pip-installed editable — `pip install -e .`).
  - `core.py` ζ/η/Euler–Maclaurin, Jacobi θ, ξ, Ξ, Hardy Z, Mellin, defects.
  - `zeros.py` sign-change hunting, Gram points, N(T), `verify_rh_up_to`.
  - `explicit.py` explicit formula (ψ, π from zeros), prime spectrum.
  - `statistics.py` vectorized Riemann–Siegel, unfolding, GUE comparisons.
  - `moments.py` external LMFDB/Odlyzko zero-table ingestion plus finite
    critical-line moment estimates and a theorem-gated prediction scorecard.
    It preserves high ordinates as decimal base-plus-offset data, requires
    separately sourced `|ζ|` samples, and never computes zeros.
  - `heatflow.py` Φ, H_t, zero tracking, de Bruijn–Newman Λ.
  - `weil.py` Riemann–Weil explicit formula (both sides independently),
    Weil functional W(h), positivity probes, truncation-tail accounting.
  - `epstein.py` the Davenport–Heilbronn counterexample: κ derivation,
    Z_dh, box-vs-line zero counts, the off-line zero, `battery`.
  - `rigor.py` ball arithmetic: `enclose_Z`, `proven_sign`, `certified_zero_count`,
    `verify_rh_certified`. Two backends (Arb via python-flint, mpmath's `iv`);
    every public function takes `backend=` so the two can check each other.
    Nothing is ever silently upgraded to a certificate — see below. The
    two-backend cross-check only *runs* when both are installed; confirm with
    `rigor.available_backends()` (see Setup) before reading a green suite as
    evidence that it did.
  - `li.py` Li's criterion (λ_n, two independent routes) and Jensen
    polynomials / hyperbolicity (numeric *and* exact Sturm in ℚ[X]).
  - `finitefield.py` curves over F_p — the RH that is a theorem: point counts,
    Frobenius eigenvalues, Lefschetz vs brute force in F_{p²}, Sato–Tate.
  - `criteria.py` four equivalence faces: Mertens/Möbius, Baez-Duarte,
    Robin/Lagarias, Speiser.
  - `plots.py` the twenty figures. `zeta/__init__.py` re-exports the curated
    API; plots are loaded lazily (PEP 562 `__getattr__`) — keep it that way,
    `import zeta` must not pull in matplotlib.
- Package: `ontology/` — the conjecture factory (phase 4). `schema.py`,
  `registry.py`, `ledger.py`, `funnel.py`, `metrics.py` and
  `historical_cases.py` are **domain-agnostic** and must stay that way: they
  name no quantity the laboratory computes, and seam tests enforce it (an AST
  import scan, a subprocess that asserts `zeta` never enters `sys.modules`, and
  a lexical scan for subject-matter vocabulary).
  Everything that knows the subject lives in `ontology/domains/`. Read
  `ontology/README.md` before touching any of it. `ontology` is not part of
  the editable install, so a script that imports it must put the repo root on
  `sys.path` (derived from `__file__` — see `scripts/13_discovery_run.py`).
  The numbered scripts alongside the core (`01_f1_geometry.py` …
  `16_adelic_acoustic_absorber.py`) are the **rogue-lab prototypes**: historical
  exploratory operator hunts, kept because `docs/17` dissects four of them as
  case studies and `tests/test_rogue_lab_controls.py` pins their control
  results. They are outside the domain-agnostic seam, and no new work should
  be added there — new exploration goes under `hunts/`.
- Package: `harness/` — **two things, and only one of them is live.** Read
  `harness/VERDICT.md` before doing anything here.
  - **Live, ordinary lab bookkeeping — keep, use, extend as needed.** The
    ledgers and their readers: `graveyard.py` (dead ends recorded so they are
    not re-entered), `guards.py` (guards recorded so they can be attacked),
    `review.py`, `independence.py`, and the three ledgers under
    `departments/` (`graveyard_ledger`, `guard_ledger`, `review_ledger`).
    Their live consumer is `scripts/70_lab_state.py`, the research-state view.
    ~1,050 lines, with a real reader.
  - **Demoted, 2026-08-13 — do not extend.** The generalized
    battery/department/integrity framework: `protocol.py`, `integrity.py`,
    `promotion.py`, `preregistration.py`, `provenance.py`, `shams.py`, and
    the six subject packs under `departments/` that exist to populate it.
    ~8,000 lines with **zero live consumers**. It was tested and did not earn
    core status: four preregistered experiments, three subjects, 74 agent
    runs, the harness arm never once beat the control, the control was 37/37,
    and where correctness was identical the harness cost 1.1–1.7× the tokens
    and 2.4–5.0× the tool calls. Meanwhile live hunts reimplemented the same
    four control roles by hand rather than import them. The evidence is in
    `harness/gate-evidence/`; the negative result stands and is not to be
    quietly relitigated.
  - **What survived the demotion, because it is independently true**: the
    four control roles are still good research practice — a claim that a
    structure-matched rival also satisfies has distinguished nothing, and
    `zeta.epstein.battery` enforces exactly that for ζ without any of this
    framework. `compiler/semantics.py` records a measured fact worth keeping:
    exhaustive concrete testing over all 65,536 i8 inputs cannot see
    poison-class defects, with a planted fault pinning it. Scope discipline —
    stating what a verdict does *not* cover — earned its keep and costs
    nothing.
  - The lesson generalizes and is the reason for the rule two sections down:
    **an abstraction with no live consumer is a liability, however elegant.**

- Package: `dossier/` — an experiment, not a department. It represents
  mathematical research state (intent, definition, rejected alternatives,
  semantic obligations, evidence) so an agent can *resume* work. Two ideas
  under test: intent is data, and "verified" is four independent things —
  `status.py` keeps `numeric` / `certified` / `literature` / `formal` apart,
  offers no aggregate, and `Support.__bool__` raises so `if support:` cannot
  silently collapse them. Same three seam tests as `ontology/schema.py`;
  subject matter only in `dossier/subjects/`. One worked example (Hardy Z),
  one CLI (`scripts/50_dossier.py`). Deliberately registered in no
  department: a dossier has no negative controls of its own, and a
  department whose battery belongs to another department is not a department
  (`docs/19-research-dossiers.md` §6).
- `hunts/` — exploratory studies, not departments and not results. The one
  place a claim may be recorded before any control has been run against it.
  A hunt cannot become a department by growing, for the same reason
  `dossier/` cannot. Read `hunts/README.md` before adding one.
- Package: `meta/` — **the second laboratory**: evidence about the research
  system rather than about ζ. `ledger.py` is the intervention ledger — what a
  human had to do that the machinery could not, with the missing capability
  named, because the quantity under test is *legitimate research output per unit
  of scarce human judgment* and that needs a denominator. It is domain-agnostic
  under the same seam tests as `ontology/schema.py`, and it is built to be hard
  to flatter: no `__bool__`, no autonomy score, a ratio that refuses to divide
  until the caller names its numerator, and an `automated` claim that costs a
  named artifact. `suspicions()` reports the shapes a self-validating log takes.
  `asymmetry-experiment.md` is the pre-registered design for the independent-vs-
  co-designed verification question. `operator-functions.md` decomposes what is
  left of the operator's role once the automatable friction is subtracted, into
  severity calibration, scope discipline, skepticism routing and authority — and
  reframes the target: you do not automate judgment, you measure *calibration*,
  which the `Judgment` record does. Its load-bearing guard is that the system may
  not resolve a disagreement it is party to. Nothing here is a mathematical result
  and nothing here trades against one; a session with no mathematics and a tidy
  ledger produced nothing. Read `meta/README.md` first.
- Project: `lean/` — the certified arm: a Lean 4 + Mathlib package
  (`ZetaLean`) formalizing, rung by rung, facts the laboratory measures.
  `ZetaLean/GroundTruth.lean` is rung 1 (ζ(2), ζ(0), ζ(4), the zero-free
  half-plane); rung 3 (Davenport–Heilbronn) is mathematics-complete and
  waiting on compute — its interval layers are `Rigor`/`IntervalExp`/
  `IntervalCExp`, the analysis is `DHAnalytic`/`DHTailBound`/`DHZeroCriterion`,
  and `DHDemo` is the worked instance. Do not add a `sorry` to any of them
  to "make progress"; the remaining gap is a computation, not a lemma.
  The ladder and the next rung live in `HANDOFF.md`. Toolchain is
  elan-managed and pinned by `lean/lean-toolchain`; `.lake/` build artifacts
  are gitignored.
- Package: `compiler/` — the subject matter of harness department #3 (LLVM IR
  rewrite verification): `catalog.py`, `semantics.py`, fixtures, and
  `FINDINGS.md` — the incident record that "FINDINGS §N" citations in
  `harness/` and `ROADMAP.md` refer to. Like `ontology` and `harness`, not
  part of the editable install.
- `scripts/` numbered standalone demos (01–41, not contiguous),
  `06_tour.py` (~90 s full story), `make_figures.py [--quick|--full]`.
  `13_discovery_run.py` is the funnel's operator console (`--dry-run`,
  `--report`).
- `docs/` 00–26: a reading course; keep cross-references consistent with
  actual filenames (doc 05 is `05-de-bruijn-newman.md`; a bare `docs/08`
  always means `08-why-it-is-hard.md` — the detector-strength findings that
  once shared the number are `22-detector-strength-findings.md`).
  `docs/doors/` holds the entry-point guides: one short page per audience
  (learn, refute, certify, discover, adopt) plus one page per department.
  Adding a purpose to the repo costs a guide page plus a test that the page's
  command still works; a purpose that will not pay that stays a document, not
  a directory. Keep `README.md` an index, not a manual — do not let it grow
  back into a single 400-line front page for four different audiences.
- `interactive_lab/` — standalone browser visualizations; illustrations, not
  results (its README states the contract: single-file pages, values
  hard-coded from what the suite pins).
- `tests/` pytest; `data/` caches; `figures/` PNGs; `references/papers.md`;
  `conjectures/` the discovery ledger — **gitignored**, a private notebook of
  unreviewed leads (only `.gitkeep` is tracked). Nothing in it is evidence for
  anything; publish `ontology.metrics.render_text`, never the log. An empty
  `conjectures/` in a fresh clone is the rule working, not a bug — to share one
  ledger across your own machines run `scripts/ledger_sync.sh init` once, then
  `sync`; it clones a *separate private* repo in place, and this public tree
  still never carries a record.

## The naming trap: three different "theta"s

1. `zeta.core.theta` — Jacobi θ(x) = Σ_{n∈ℤ} e^{−πn²x} (the heat kernel;
   modular identity θ(1/x) = √x·θ(x)).
2. `zeta.core.rs_theta` — Riemann–Siegel phase ϑ(t) in Z(t) = e^{iϑ(t)}ζ(½+it)
   (`zeta.statistics.riemann_siegel_theta` is the fast vectorized variant).
3. `zeta.explicit.theta_cheb` — Chebyshev's prime sum θ(x) = Σ_{p≤x} log p.

Related trap: `xi(s)` is the completed zeta (entire, ξ(s) = ξ(1−s));
`Xi(t) = xi(1/2 + it)` is real for real t. Do not use Ξ for the function of s.
In `heatflow.py`, H₀(z) = (1/8)·Ξ(z/2) — mind the factor 8 and the z/2.

And a fourth collision, this one in the import system: `zeta.explicit.li` is
the *logarithmic integral* and is re-exported as `zeta.li`, but `zeta/li.py`
is Li's *criterion*, so after any `import zeta.li` the package attribute is
the module and `zeta.li(x)` raises `TypeError`. Documented in `zeta/li.py`
and pinned by `tests/test_li.py`. Write `zeta.explicit.li` for the function
and `from zeta.li import …` for the module; never `from zeta import li`.
The Jensen coefficients also come in two normalisations: `zeta/li.py` uses
GORZ's 8·ξ(½+z) = Σ γ(n) z^{2n}/n!, `docs/12` §8.1 derives the heat-kernel
one; they differ by 64·4ⁿ, which changes no hyperbolicity and no Turán ratio.

## Cached data

Expensive results cache to `data/` (`.json` zero tables are committed;
`.npz` scans are gitignored and regenerate on first use). Cache keys encode
parameters in filenames. If you change numerical internals, delete the
affected cache files and re-run, or stale numbers will "pass".

## How to run things

```bash
cd <repo root>
.venv/bin/python -m pytest -q                 # full suite (2189 tests, ~10-20 min)
.venv/bin/python -m pytest -q -m "not slow"   # fast tier (2122 tests, ~3-8 min)
.venv/bin/python scripts/06_tour.py           # end-to-end sanity + demo
.venv/bin/python scripts/make_figures.py --quick   # all figures into figures/
cd lean && PATH="$HOME/.elan/bin:$PATH" lake build  # the certified arm (0 sorrys)
```

Tests run in parallel by default (`-n auto`, set in `pyproject.toml`) — the
fast tier goes from ~320 s to ~115 s. Add `-n0` when you need `--pdb` or clean
per-test output — **not** `-p no:xdist`, which unloads the plugin that owns the
`-n auto` already in `addopts` and dies with "unrecognized arguments: -n". Before optimising anything, run `--durations=20`:
the cost concentrates in `test_li.py`, `test_heatflow.py` and `test_weil.py`
(high-precision zero sums and quadrature).

Tests use mpmath's `zetazero` / `siegelz` / `grampoint` / `nzeros` as an
independent oracle against the hand-rolled machinery — preserve that pattern
when adding features: implement the mathematics, then cross-check.

## Ground truth for quick assertions

- ζ(2) = π²/6 = 1.6449340668482264…, ζ(0) = −1/2, ζ(−1) = −1/12.
- γ₁ = 14.134725141734694, γ₂ = 21.022039638771555, γ₃ = 25.010857580145689.
- N(100) = 29 zeros with 0 < γ < 100. Ξ(0) = 0.4971207781…
- θ(1/x) = √x·θ(x) and ξ(s) = ξ(1−s) hold to working precision (measured
  defects ~1e-30 at dps=30).

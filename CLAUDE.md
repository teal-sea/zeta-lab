# AGENTS.md: operating context for the repo root

A computational laboratory for the Riemann zeta function and RH. `AGENTS.md` is
a symlink to `CLAUDE.md`: every agent shares this text, so do not fork it.

Read first: `README.md` (front door), `docs/00-orientation.md` (scope),
`ROADMAP.md` (current decisions; read before planning work), `ALIGNMENT.md`
(research mandate and evidence discipline; it permits original mathematics
toward RH, so read it before treating an old non-goal or failure as a ban).

## Setup (first run in a fresh clone)

```bash
python3 -m venv .venv
.venv/bin/pip install -r requirements.txt
.venv/bin/pip install -e .
bash scripts/install_hooks.sh                 # pre-push secret guard, see below
.venv/bin/python -m pytest -q -m "not slow"   # confirm green before changing anything
```

**Install the hook in every clone and every worktree**: hooks live in
`.git/hooks` and nothing installs them for you. `scripts/check_secrets.py`
(`--range`, `--all`, `--tree`) matches known key shapes only, so it is a floor,
not a guarantee. Its first version failed open; `tests/test_check_secrets.py`
pins that a bad range now raises: a guard that fails open is worse than none,
because it also supplies confidence. Read credentials at call time, not from a file.

**Check the ball-arithmetic backend before you trust a green run**:

```bash
.venv/bin/python -c "from zeta import rigor; print(rigor.BACKEND, rigor.available_backends())"
# want: python-flint ['mpmath.iv', 'python-flint']
```

Without `python-flint`, `rigor.py` silently falls back to mpmath's `iv`: correct
but about **1600× slower** (a fast-tier case looks hung), and the five
`skipif(not HAVE_FLINT)` tests vanish, including the Arb-vs-mpmath cross-check
that licenses the word *certified*. **"5 skipped" means it did not run**:
install `python-flint` (pinned in `requirements.txt`).

## The knowledge index

`CONTEXT.md` is the generated index of facts (API, docs, scripts, test counts);
this file carries judgment. Regenerate it whenever you add or rename a public
function, a doc or a script; never hand-edit it. `llms.txt` is the short map.

```bash
.venv/bin/python scripts/make_context.py          # rewrite CONTEXT.md
.venv/bin/python scripts/make_context.py --check  # non-zero exit if stale
.venv/bin/python scripts/make_context.py --flat   # + CONTEXT_FLAT.md, whole repo in one file
```

## Parallel sessions

- **Scope**: an active branch, worktree or hunt directory carries a `MISSION.md`
  saying what it may touch. Read it before acting there.
- **Namespacing**: exploratory math goes in its own `hunts/` subdirectory, never
  `zeta/` or `ontology/`. Hand off via the `conjectures/` ledger, not core edits.
- **One agent per checkout** (`git worktree add`); confirm green before building.
- **Look before you report.** Before describing repo or manuscript state, or
  editing outside your hunt directory: `git fetch`, re-read, and call
  `list_sessions` (`status_category`, `needs_action`; `send_message` reaches a
  session). A habit, not a system: build no coordination framework.
- **Shared repositories get branches too**: edit repos this tree publishes into
  on a branch with a pull request, never on `main`.

### Outside environments (read-only mounts, notebook agents)

A notebook agent (Claude Science and the like) mounts the tree read-only with
its own Python. **Run the preflight as the first cell, before any mathematics:**

```bash
python scripts/science_preflight.py          # or --allow-fallback
```

It reports interpreter, dependencies, whether `rigor.BACKEND` is Arb, whether
Lean can build, and **the next free `docs/` number**; it exits non-zero if the
environment cannot support this tree's claims. Then:

- **Guess no number and no name**: take the doc number from the preflight.
- **An artifact is not a commit**: say files were produced, not landed; never
  call a read-only tree changed. Workspace storage is swept when idle.
- **Write only** `hunts/<name>/` (its `MISSION.md` first), one new
  `docs/NN-*.md`, and `figures/`. Not `zeta/`, `ontology/` or `harness/` without
  explicit permission.
- **The lexical rules are lexical**: the reserved word is banned everywhere
  under `hunts/`, including inside a sentence disclaiming it.
- **Before handing back**, run `tests/test_docs_numbering.py`,
  `tests/test_hunt_probe_discipline.py`, `tests/test_doors.py` and
  `scripts/make_context.py --check`.

## Public record vs fulcrum

This repo is the public research record; how the lab is operated lives in the
private repo `fulcrum`. The test:

> If an outside observer needs it to **evaluate or reproduce a public claim**,
> it belongs here. If it teaches the lab how to **allocate, route, prompt, or
> operate itself**, it belongs in fulcrum unless reproducibility needs it.

Negative results about our own tooling stay here (`harness/VERDICT.md`,
`harness/gate-evidence/`). Fulcrum is private, not secret: name it plainly and
credit it with nothing it has not demonstrated. Do not edit fulcrum from here:
report an infrastructure idea as a Core candidate and an out-of-mission loose
end as a thread. Flag ambiguous cases to the operator; build no adjudicator.

## How the work is organised

**Core ↔ Pursuits.** Core improves the lab's reusable ability to work; Pursuits
are what it chases. They create each other and name a thing's current role, not
its rank. Do not rename directories to fit the metaphor.

**Forage, don't roadmap.** Explore cheaply, feed what shows credible signal,
stop when it stops. An **observation** (measured, broken, bounded) is public: a
GitHub issue, or a doc and a test. A **lead** (what next, at what budget) is
allocation: fulcrum's roster. Start no backlog file here.

**Constructive search and scoped challenge.** Compare distinct mechanisms before
favouring one; give candidates bounded construction time and challenge the
actual result. `ALIGNMENT.md` sections 4 and 5 separate refuted, obstructed,
unresolved and paused. Rejection is not the objective.

**The economic objective: maximize valuable output per monetary unit**, not
"minimize tokens". Spend more whenever the extra output justifies it. There is
no settled metric for "valuable output"; do not invent one.

**Design discipline.** No abstraction without a live consumer in this repo that
uses it immediately; "future agents might" is not one. No generalizing a
workflow before it earns it, no meta-system. Kill funded work on evidence.

## Hard rules

- **Python**: always `.venv/bin/python` from the repo root, never bare `python3`.
- **matplotlib is headless**: `matplotlib.use("Agg")` before importing pyplot,
  in any script that plots (`zeta/plots.py` does).
- **Precision**: mpmath for anything precision-critical, `mp.dps` set explicitly
  via `mp.workdps(...)`, guard digits internal, no global mpmath state left
  modified. numpy only for bulk statistics.
- **Every mathematical claim in code or docs is numerically checked by a test,
  or explicitly hedged at the point of use.** Docstring numbers are pinned by
  `tests/`; identities are measured defect functions
  (`functional_equation_defect`, `theta_modular_defect`), not assumptions.
- **Honest scope.** Proof attempts and formalization are permitted
  (`ALIGNMENT.md` section 0). A finite computation, plot or model agreement is
  never a uniform RH result. A stronger theorem keeps its exact hypotheses,
  target, remainder terms and reviewed implication chain; a conjecture stays a
  conjecture. Sign scans state their range and whether sign and completeness
  checks were rigorous; float signs never become a finite-range theorem.
- **Original is not novel, and the lab may claim original.** *Original* is
  provenance (this lab produced it): claim it, name it, give its rung. *Novel*
  is about the world and needs a search: say what was searched (OEIS, arXiv,
  zbMATH; `references/papers.md`) and found. `ontology/knownness.py`'s default
  "not consulted" describes the tool, not the lab. State frontier results as a
  delta against a cited source paper. Unsearched novelty downgrades nothing,
  and refutations count as output within their scope.
- **The certainty ladder.** Check an unexpected result for bugs, missing
  assumptions, unsupported limits and shared failure modes before grading it.
  1. *measured*: one route, float grade. Say "measured", "observed".
  2. *hardened*: independent routes agree and/or ball-arithmetic enclosures
     carry every step (`rigor.py` grade). Say "hardened", "enclosure-carrying".
  3. *kernel-checked*: Lean 4 + Mathlib, zero sorrys, standard axioms only.
     These are theorems; call them theorems.

  The ladder ends there; outside review is a footnote, *pending external
  verification*. Derivations state their assumptions and review status;
  numerical agreement never makes one kernel-checked. **A composite claim takes
  the grade of its weakest step.** Never round a rung up for an audience.
- **"Certified" is a reserved word**, for `zeta/rigor.py` (every step enclosed)
  and the Lean arm; say which. Everything else is *accurate*. A silent float
  fallback under `certified: True` is a critical defect. `proven_sign` returns
  `0` for "not decided", uncertifiable steps go in `uncertified_steps`, and
  `certified` is False if that list is non-empty. Non-rigorous cross-checks
  (`nzeros`, `backlunds`) stay flagged. Banned outright under `hunts/`.
- **The Lean arm counts nothing with a `sorry`**; never add one to progress.
- **No em dashes in prose you write**: use a period, a colon or a pair of
  commas. Never repunctuate quoted material or recorded findings.
- **Derive conventions, never remember them.** Where the literature disagrees on
  a factor or constant, calibrate numerically and cross-check, as `zeta/weil.py`
  does for the explicit formula and `zeta/epstein.py` does for κ on every call.
- **The counterexample battery is a standing test.** A structural explanation of
  RH faces the applicable `zeta.epstein.battery` rivals, compared on complete
  hypotheses including arithmetic and normalization. A rival meeting every
  hypothesis but not the conclusion refutes it; one passing a shared lemma does
  not, so test the distinguishing step. A failed rival computation excludes
  nothing. See `ALIGNMENT.md` section 5 and `docs/08` section 4.

## Layout

`CONTEXT.md` indexes modules. This is the map, with the rule per area.

- `zeta/`: core package. `import zeta` must not pull in matplotlib; every
  `rigor.py` public function takes `backend=` so the backends check each other.
- `ontology/`: conjecture factory; core files are domain-agnostic (seam tests),
  subject matter only in `ontology/domains/`. Not installed: put the repo root
  on `sys.path` from `__file__`. Read `ontology/README.md` first.
- `scripts/01_*` to `16_*`: rogue-lab prototypes (`docs/17`), pinned by
  `tests/test_rogue_lab_controls.py`. No new work there.
- `harness/`: read `harness/VERDICT.md` first. The ledgers (`graveyard.py`,
  `guards.py`, `review.py`, `independence.py`, `departments/*_ledger`) are live,
  read by `scripts/70_lab_state.py`; extend freely. The framework
  (`protocol.py`, `integrity.py`, `promotion.py`, `preregistration.py`,
  `provenance.py`, `shams.py`, subject packs) is demoted, do not extend it:
  four preregistered experiments, two subjects, 74 agent runs, and the harness
  arm never beat the control.
- `dossier/`: resumable research state; `status.py` never aggregates support.
- `hunts/`: exploratory studies. Keep each claim's status explicit; a hunt
  cannot promote its own unreviewed claim. See `hunts/README.md`.
- `meta/`: evidence about the research system, never a math result. Ground
  truth in `meta/evals/` is measured, never read from `SHAM_MODES`. Read
  `meta/README.md` and `docs/28` first.
- `compiler/`: LLVM IR rewrite verification; "FINDINGS §N" means `FINDINGS.md`.
- `docs/`: keep cross-references consistent with actual filenames: a bare
  `docs/08` always means `08-why-it-is-hard.md`. `docs/doors/` has one page per
  audience; a new purpose costs a page plus a test. Keep `README.md` an index,
  not a manual.
- `lean/`: kernel-checked arm; next rung in `HANDOFF.md`, `.lake/` gitignored.
- `interactive_lab/`: illustrations, not results.
- `conjectures/`: **gitignored** private ledger, not evidence. Publish
  `ontology.metrics.render_text`, never the log (`scripts/ledger_sync.sh`).

## Traps: three thetas, xi vs Xi, and `zeta.li`

1. `zeta.core.theta`: Jacobi θ(x) = Σ_{n∈ℤ} e^{−πn²x}, with θ(1/x) = √x·θ(x).
2. `zeta.core.rs_theta`: Riemann–Siegel ϑ(t) in Z(t) = e^{iϑ(t)}ζ(½+it); the
   fast vectorized variant is `zeta.statistics.riemann_siegel_theta`.
3. `zeta.explicit.theta_cheb`: Chebyshev's θ(x) = Σ_{p≤x} log p.

- `xi(s)` is the completed zeta, ξ(s) = ξ(1−s); `Xi(t) = xi(1/2 + it)` is
  real for real t. Never use Ξ for the function of s. In `heatflow.py`,
  H₀(z) = (1/8)·Ξ(z/2).
- `zeta.explicit.li` (logarithmic integral) is re-exported as `zeta.li`, but
  `zeta/li.py` is Li's criterion: after `import zeta.li`, `zeta.li(x)` raises
  `TypeError` (pinned by `tests/test_li.py`). Write `zeta.explicit.li` for the
  function, `from zeta.li import …` for the module; never `from zeta import li`.
- Jensen coefficients: `zeta/li.py` uses GORZ's 8·ξ(½+z) = Σ γ(n) z^{2n}/n!,
  `docs/12` §8.1 the heat-kernel form; they differ by 64·4ⁿ, which changes no
  hyperbolicity and no Turán ratio.

## Cached data

`data/` caches results (`.json` zero tables committed, `.npz` gitignored), keyed
by parameters in filenames. If you change numerical internals, delete the
affected cache files and re-run, or stale numbers will "pass".

## Door analysis: what every ceiling hunt owes

Every hunt that measures a ceiling MUST end its RESULTS.md with a section named
**"The doors"** (a wall without its unfreeze list gives the list away), with:

1. **Active constraints at the optimum**: what binds when the bound stops
   moving, ranked by shadow price, or by saturation-curve slope.
2. **The frozen-constant inventory**: every chosen-not-optimized number, with
   what relaxing it trades against; flag those with genuine trade shape.
3. **The information class**: whether each door stays inside the data the
   current family reads or requires reading more.

A measured optimum is not a proved ceiling: state candidate, parameter range,
information class and proof status. The latest top door gets no automatic
priority over other mechanisms; allocation is the owner's decision.

## Compute discipline

1. **Nothing heavy on the operator's machines** (16 GB M4 laptop, 8 GB M1
   desktop, often driven by phone). A guard kills `lake build`: use CI, don't evade it.
2. **GitHub Actions is the default compute**: free here, 20 parallel jobs, not
   preempted; `full.yml` caches `elan` and `.lake`. Paid only if it can't; say why.
3. **Estimate before you spend**: time one unit, multiply, write it in `RUNS.md`.
4. **Anything over about twenty minutes checkpoints per unit.**
5. **Every detached job has an owner**: a watcher, or `fulcrum adopt` then
   `fulcrum observe` with a terminal outcome.
6. **One `lake build` at a time, never beside heavy numerics**, even in CI.

## How to run things

```bash
cd <repo root>
.venv/bin/python -m pytest -q                 # full suite (2189 tests, ~10-20 min)
.venv/bin/python -m pytest -q -m "not slow"   # fast tier (2122 tests, ~3-8 min)
.venv/bin/python scripts/06_tour.py           # end-to-end sanity + demo
.venv/bin/python scripts/make_figures.py --quick   # all figures into figures/
cd lean && PATH="$HOME/.elan/bin:$PATH" lake build  # the certified arm (0 sorrys)
```

- `-n auto` is set in `pyproject.toml`. Use `-n0` for `--pdb` or clean output,
  **not** `-p no:xdist`, which dies with "unrecognized arguments: -n".
- Run `--durations=20` before optimising; cost sits in `test_li.py`,
  `test_heatflow.py` and `test_weil.py`.
- **Implement, then cross-check** against mpmath (`zetazero`, `siegelz`,
  `grampoint`, `nzeros`) and PARI/GP in `tests/test_pari_oracle.py`, which
  shares no code with mpmath. PARI's `lfunhardy` is normalised differently, so
  Z is rebuilt from its `zeta` and `lngamma`. Neither oracle is a certificate.
- A cross-check that cannot fail is not a cross-check: plant faults to see red.

## Ground truth for quick assertions

- ζ(2) = π²/6 = 1.6449340668482264…, ζ(0) = −1/2, ζ(−1) = −1/12.
- γ₁ = 14.134725141734694, γ₂ = 21.022039638771555, γ₃ = 25.010857580145689.
- N(100) = 29 zeros with 0 < γ < 100. Ξ(0) = 0.4971207781…
- θ(1/x) = √x·θ(x) and ξ(s) = ξ(1−s) hold to working precision (measured
  defects ~1e-30 at dps=30).

---

## Gates, guards and defaults need a named source

Anything an agent builds that blocks, gates, withholds, escalates, mutes, asks for
approval, adds a confirmation step, or refuses by default is a claim that somebody wanted
it. It carries a source naming who asked: a dated message, an issue, a commit, a quoted
line. If the source is the agent's own judgement, it says so in those words, in the code
comment and in any status file, and never as if the owner had asked.

No source, no gate. An agent that believes a safeguard is needed and cannot cite anyone
writes the proposal down for the owner and ships without it. Caution nobody asked for is a
feature nobody asked for.

When reporting state, keep "the code does X" apart from "you asked for X". A status file
written by an earlier agent is not a decision by the owner.

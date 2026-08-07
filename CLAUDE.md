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

## Working with multiple agents

Sequential use by different agents is fine and expected — pick up wherever the
last one left off; this file plus `git log` is the handoff. Two caveats:

- Start by confirming the suite is green (see Setup); never build on top of a
  tree you have not verified.
- Only avoid *literally simultaneous* runs against the same checkout — modules
  and tests are tightly coupled and `data/` caches are shared. If you ever do
  want parallel work, use `git worktree add` so each agent gets its own tree.

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
- **Honest-scope rule**: Zeta Lab is a computational and formal workbench that
  reconstructs, tests, connects, and falsifies ideas around RH, without
  claiming to advance RH. State that; do not hedge around it.
  Nothing here is evidence for RH (Littlewood's theorem, `docs/08`). Never
  write language implying a computation settles or supports RH; the sanctioned
  framing for the sign-change verification is "proof for the finite range,
  modulo the correctness of the floating-point sign evaluations". If a
  computation appears to settle something open, the correct inference is a bug.
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
  the only two things in the repo entitled to the word "certified", and they
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
    Nothing is ever silently upgraded to a certificate — see below.
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
- Package: `harness/` — the referee, factored out of the laboratory, and the
  package that makes the lab extensible by **department**. `protocol.py` is
  domain-agnostic under the same three seam tests as `ontology/schema.py` and
  defines four instrument roles — `Subject` (the genuine article and its
  rivals), `Decoy` (ablation), `Surrogate` (null control), `Lesion` (detector
  power) — bundled into a `Battery`, plus a `Department` = battery + door +
  reference claims. Subject matter lives only in `harness/departments/`;
  `zeta_department.py` is department #1 and the worked example.
  **The admission rule is `no department without a battery`**: `validate_battery`
  refuses one with no rival, with neither decoy nor surrogate, or with no
  lesion, because such a battery could never fail. A department must also
  declare reference claims with known verdicts — at least one its battery kills
  and one it passes — so a referee that only ever says "no" is caught.
  `tests/test_department_conformance.py` is parametrized over
  `harness.departments.KNOWN_DEPARTMENTS`, so listing a department there is
  what turns its audit on. Read `harness/README.md` before adding one. Like
  `ontology`, it is not part of the editable install.
- Package: `dossier/` — **a probe, not a department.** An experiment in
  representing mathematical research state (intent, definition, rejected
  alternatives, semantic obligations, evidence) so an agent can *resume* work.
  Two ideas under test: intent is data, and "verified" is four independent
  things — `status.py` keeps `numeric` / `certified` / `literature` / `formal`
  apart, offers no aggregate, and `Support.__bool__` **raises** so `if support:`
  cannot silently collapse them. Same three seam tests as `ontology/schema.py`;
  subject matter only in `dossier/subjects/`. One worked example (Hardy Z), one
  CLI (`scripts/50_dossier.py`). It is registered in no department and has no
  door **on purpose**: a dossier has no rivals of its own, and *a department
  whose battery is another department's battery is not a department*
  (`docs/19-research-dossiers.md` §6).
- `hunts/` — **probes, not departments.** Scoped exploratory attacks, with
  permission to be wrong in public and the one place a claim may be written
  down before anything has tried to kill it. Nothing in `hunts/` is a result;
  a hunt cannot become a department by growing, for the same reason `dossier/`
  cannot. Read `hunts/README.md` before adding one.
- Project: `lean/` — the certified arm: a Lean 4 + Mathlib package
  (`ZetaLean`) formalizing, rung by rung, facts the laboratory measures.
  `ZetaLean/GroundTruth.lean` is rung 1 (ζ(2), ζ(0), ζ(4), the zero-free
  half-plane). The ladder and the next rung live in `HANDOFF.md`. Toolchain is
  elan-managed and pinned by `lean/lean-toolchain`; `.lake/` build artifacts
  are gitignored.
- `scripts/` 01–05 and 07–13 standalone demos, `06_tour.py` (~90 s full
  story), `make_figures.py [--quick|--full]`. `13_discovery_run.py` is the
  funnel's operator console (`--dry-run`, `--report`).
- `docs/` 00–18: a reading course; keep cross-references consistent with
  actual filenames (doc 05 is `05-de-bruijn-newman.md`).
  `docs/doors/` is the switchboard: one short page per way in (learn, refute,
  certify, discover) plus one page per department. The repo has one spine and
  several doors — a purpose costs a door plus a test that the door still works,
  and a purpose that will not pay that stays a document, not a directory.
  `README.md` is the switchboard, not the manual; do not let it grow back into
  a single 400-line front door for four different audiences.
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
.venv/bin/python -m pytest -q                 # full suite (1704 tests, ~9 min)
.venv/bin/python -m pytest -q -m "not slow"   # fast tier (1648 tests, ~3 min)
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

# AGENTS.md — operating context for the repo root

A computational laboratory for the Riemann zeta function and RH. Read
`README.md` for the front door and `docs/00-orientation.md` for scope.

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
- **Honest-scope rule**: this repo is an instrument, not a proof attempt.
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
  - `heatflow.py` Φ, H_t, zero tracking, de Bruijn–Newman Λ.
  - `weil.py` Riemann–Weil explicit formula (both sides independently),
    Weil functional W(h), positivity probes, truncation-tail accounting.
  - `epstein.py` the Davenport–Heilbronn counterexample: κ derivation,
    Z_dh, box-vs-line zero counts, the off-line zero, `battery`.
  - `plots.py` the fourteen figures. `zeta/__init__.py` re-exports the curated
    API; plots are loaded lazily (PEP 562 `__getattr__`) — keep it that way,
    `import zeta` must not pull in matplotlib.
- `scripts/` 01–05 and 07–08 standalone demos, `06_tour.py` (~90 s full
  story), `make_figures.py [--quick|--full]`.
- `docs/` 00–11: a reading course; keep cross-references consistent with
  actual filenames (doc 05 is `05-de-bruijn-newman.md`).
- `tests/` pytest; `data/` caches; `figures/` PNGs; `references/papers.md`.

## The naming trap: three different "theta"s

1. `zeta.core.theta` — Jacobi θ(x) = Σ_{n∈ℤ} e^{−πn²x} (the heat kernel;
   modular identity θ(1/x) = √x·θ(x)).
2. `zeta.core.rs_theta` — Riemann–Siegel phase ϑ(t) in Z(t) = e^{iϑ(t)}ζ(½+it)
   (`zeta.statistics.riemann_siegel_theta` is the fast vectorized variant).
3. `zeta.explicit.theta_cheb` — Chebyshev's prime sum θ(x) = Σ_{p≤x} log p.

Related trap: `xi(s)` is the completed zeta (entire, ξ(s) = ξ(1−s));
`Xi(t) = xi(1/2 + it)` is real for real t. Do not use Ξ for the function of s.
In `heatflow.py`, H₀(z) = (1/8)·Ξ(z/2) — mind the factor 8 and the z/2.

## Cached data

Expensive results cache to `data/` (`.json` zero tables are committed;
`.npz` scans are gitignored and regenerate on first use). Cache keys encode
parameters in filenames. If you change numerical internals, delete the
affected cache files and re-run, or stale numbers will "pass".

## How to run things

```bash
cd <repo root>
.venv/bin/python -m pytest -q                 # full suite (~486 tests)
.venv/bin/python -m pytest -q -m "not slow"   # fast tier
.venv/bin/python scripts/06_tour.py           # end-to-end sanity + demo
.venv/bin/python scripts/make_figures.py --quick   # all figures into figures/
```

Tests use mpmath's `zetazero` / `siegelz` / `grampoint` / `nzeros` as an
independent oracle against the hand-rolled machinery — preserve that pattern
when adding features: implement the mathematics, then cross-check.

## Ground truth for quick assertions

- ζ(2) = π²/6 = 1.6449340668482264…, ζ(0) = −1/2, ζ(−1) = −1/12.
- γ₁ = 14.134725141734694, γ₂ = 21.022039638771555, γ₃ = 25.010857580145689.
- N(100) = 29 zeros with 0 < γ < 100. Ξ(0) = 0.4971207781…
- θ(1/x) = √x·θ(x) and ξ(s) = ξ(1−s) hold to working precision (measured
  defects ~1e-30 at dps=30).

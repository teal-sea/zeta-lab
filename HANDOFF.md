# Session handoff — Li-criterion detector strength, F1 fingerprints

**Snapshot:** 2026-08-05
**Branch:** `main`
**Detailed sources of truth:** `ROADMAP.md`, `docs/07-equivalences-and-criteria.md` §4,
`docs/11-f1-and-the-missing-geometry.md`, `docs/09-new-ontologies.md` §5

**Status in one line:** three scripts left untracked and broken by an interrupted
external-agent session were rebuilt; one produced a genuine measured result about
how weak Li's criterion is as an RH detector. Still **no next build chosen** —
the moments programme remains closed (previous handoff, superseded below).

## Provenance — read this before trusting the starting point

The three files this session started from (`scripts/14_repulsion_floor.py`,
`scripts/15_f1_fingerprints.py`, `scripts/15_novel_dh_li.py`) were **not** written
by a previous session of this repo's workflow. They were produced by a Gemini
session in an external IDE, which hit a model quota mid-write; the files were
untracked, unnumbered against the existing `14_`/`15_` slots, and contained
errors. They have been rewritten and renumbered to `16_`/`17_`/`18_`. Nothing
from the original three survives unverified.

Two defects in the originals are worth recording because they are the kind that
pass silently:

1. `15_f1_fingerprints.py` asserted, in a bare `print` with no computation
   behind it, that the archimedean factor `s (2 pi)^{-s/2} Gamma(s/2)` is
   "EXACTLY" the factor Riemann attached to zeta. It is not; see below.
2. `15_novel_dh_li.py` hand-rolled a Cauchy-integral Li extraction with
   `mpmath.quad` on a periodic integrand, principal-branch `log`, and no
   validation against anything. `zeta/li.py` already contains a correct, tested
   version of exactly this machinery.

## Where the work landed

### `scripts/18_dh_li_coefficients.py` — the substantive result

Li's criterion says `lambda_n >= 0` for all `n` iff RH. The Davenport–Heilbronn
function `F` satisfies `F(s) = F(1-s)`, has real coefficients and a real
Hardy-style `Z`, and has a zero off the critical line — so some `lambda_n` for
`F` must eventually go negative. (That leans on the Bombieri–Lagarias multiset
form of the criterion, not Li's original: `F` has no Euler product and is outside
the Selberg class, and the multiset statement needs neither.) **It does not go
negative anywhere in reach.**

- The extractor reuses `zeta.li._unwrapped_log` and `_roots_of_unity` rather than
  re-deriving them, and is **validated on `xi` against `zeta.li.li_coefficients`
  before being pointed at `F`**: worst absolute difference over `n <= 24` is
  exactly `0.0` (bit-identical). The script asserts this and aborts otherwise.
- On `F`: `lambda_n > 0` for every `n <= 24`, and uniformly *larger* than zeta's
  (`n = 24`: `30.1998` for `F` against `12.3513` for zeta).
- Why, quantitatively: the mirror `1 - rho` of the off-line zero has `Re < 1/2`
  and `|1 - 1/(1-rho)| = 1.00004200616427`, i.e. `log` of that is `4.20053e-5`.
  The exponentially growing term needs `n ~ 2.4e4` merely to double, against a
  background growing like `(n/2) log n`.

So `lambda_n >= 0` observed for zeta over any comparable range distinguishes
nothing — a function that provably violates RH passes the identical test. This
is `docs/09` §5 gate 3 applied to a *criterion* rather than to a structural
claim, and it sharpens `docs/07` §11 into a quantitative statement about one of
the four equivalence faces. Recorded in `docs/07` §4.

### `scripts/17_f1_fingerprints.py` — Tits fingerprints, computed, plus one measurement

The `q -> 1` limits are correct and now assert-backed: `|P^{n-1}| -> n`, the flag
variety `-> |S_n|`, `Gr(2,4) -> 6`. `docs/11` §3 already states these; the script
computes them.

The addition is the archimedean-factor measurement, at `s = 0.3 + 7.1i`, dps 25:

| factor | `\|A(s) - A(1-s)\|` |
| --- | ---: |
| `s (2 pi)^{-s/2} Gamma(s/2) zeta(s)` (the informal version) | `0.057095031` |
| `pi^{-s/2} Gamma(s/2) zeta(s)` | `1.6408307e-28` |
| `zeta.core.xi` | `0.0` |

The informal factor has no functional equation at all: it conflates
`Gamma_R(s) = pi^{-s/2} Gamma(s/2)` with `Gamma_C(s) = 2 (2 pi)^{-s} Gamma(s)`
and drops the `s(s-1)/2`. The script then runs the Gate 3 check: DH functional
equation defect `0.0`, `|completed_dh(rho)| = 7.9e-58` at `Re(rho) - 1/2 =
+0.308517`, so "the Gamma factors are secretly geometry, therefore the zeros are
on the line" applies verbatim to a function where the conclusion is false.

### `scripts/16_repulsion_floor.py` — a real test replacing a vacuous one

The original asked whether the minimum normalised gap exceeds `1e-4` and called a
positive answer "the conjecture HOLDS". That test is vacuous: a Poisson sample of
the same size also has a positive minimum. Replaced with the small-`s` tail,
which is where repulsion actually lives (GUE density vanishes like `s^2`, Poisson
does not vanish at all).

Over 138,068 spacings from 138,069 zeros with `0 < gamma < 1e5`:

| `s` | observed | GUE | Poisson |
| ---: | ---: | ---: | ---: |
| `0.02` | `0.000e+00` | `8.770e-06` | `1.980e-02` |
| `0.05` | `1.086e-04` | `1.368e-04` | `4.877e-02` |
| `0.10` | `7.315e-04` | `1.088e-03` | `9.516e-02` |
| `0.50` | `9.705e-02` | `1.131e-01` | `3.935e-01` |

Poisson is off by `449x` at `s = 0.05`; GUE by `1.26x`. Sharper test: fitting the
cubic coefficient of the GUE CDF near zero gives `c = 1.09654`, so the smallest of
138,068 draws should be about `0.01876`; observed is `0.02186`, ratio `1.165`. The
closest pair is `gamma_95248 = 71732.901208`, `gamma_95249 = 71732.915909`.

Spacing variance is `0.161375` against the GUE bulk `~0.178`; the script notes the
approach is slow in `T` and points at the CUE-control measurement rather than
treating the gap as a discrepancy.

## Reproduction commands

From the repository root with the project venv:

```bash
.venv/bin/python scripts/16_repulsion_floor.py        # ~1 s, uses the cached zero table
.venv/bin/python scripts/17_f1_fingerprints.py        # ~10 s, sympy limits + mpmath checks
.venv/bin/python scripts/18_dh_li_coefficients.py     # ~3 s, self-validating
```

All three are self-checking: 17 asserts the `q -> 1` limits and both
functional-equation defects, 18 asserts agreement with `zeta.li` before computing
anything about Davenport–Heilbronn.

## Test-run status — the previous handoff's caveat did not reproduce

The previous handoff recorded a pre-existing teardown/worker hang in the parallel
pytest runner near completion, and explicitly declined to claim a clean
repository-wide exit. **Both tiers ran to a clean exit in this session:**

```text
.venv/bin/python -m pytest -q -m "not slow"   ->  1417 passed in 165.18s (2:45)
.venv/bin/python -m pytest -q                 ->  1464 passed in 477.26s (7:57)
```

Default `-n auto` parallel settings, no hang, no interruption, exit code 0 both
times. So the repository-wide suite *was* run to a clean exit here, and the
claim in the previous handoff's caveat no longer holds for this tree.

That is a **non-reproduction, not a fix** — nothing in this session touched the
runner, the packages, `pyproject.toml`, or any test file; the only changes were
three new scripts and three documentation files. Treat the hang as intermittent
and still unexplained, and do not assume it is gone.

Note the drift in counts worth reconciling at some point: `AGENTS.md` documents
the fast tier as 1,328 tests and the full suite as 1,365, against the 1,417 and
1,464 measured here. The previous handoff saw 1,370 before interrupting. Nothing
in this session added a test, so the drift predates it.

## What not to infer

- None of this is evidence for or against RH (Littlewood; `docs/08`).
- The DH result is about the **detector**, not about `F`. Li's criterion is
  correct; it is just numerically useless at reachable `n`. Nothing here casts
  doubt on the equivalence itself.
- `n ~ 2.4e4` is a doubling scale for one term, **not** a proven bound on where
  the first negative `lambda_n` for `F` appears. The true onset depends on the
  full sum over zeros and is not computed here. Do not quote it as a threshold.
- GUE agreement in script 16 describes the distribution of zeros already known to
  be on the line in that range. It is not a verification of anything.
- The `q -> 1` limits are combinatorial identities. They are not a step toward
  RH, and `docs/11` §5 is the sober scorecard on that.

## What is open now

Still **no next build chosen**; `ROADMAP.md`'s only "Next build" heading was
moments, and moments closed in the previous session. The three narrow moments
items listed in the previous handoff (exact `N(T)` exposure, seed replication of
the CUE and DH rows, the `10^7`–`10^8` drift) remain open and unaddressed here.

New candidates raised by this session, neither started:

1. **Weil positivity against Davenport–Heilbronn.** The natural sequel to script
   18: find an explicit test function `h` with `W(h) < 0` for `F`. Unlike Li's
   `lambda_n`, `h` can be chosen to sit on the off-line zero, so the negativity
   should be reachable rather than sitting at `n ~ 1e4`. `zeta/weil.py` already
   has both sides and positivity probes. This would give the repository a
   criterion that *does* detect the known violation — currently it has none.
2. **A detector-strength audit across the other faces.** Script 18 measured one
   of `docs/07`'s equivalences against the counterexample. Mertens/Möbius,
   Baez-Duarte and Robin/Lagarias have not been measured this way. The honest
   expectation is that they are all weak; the value is in the numbers.

Neither is recorded in `ROADMAP.md`. Choosing a next build is still an open
decision, not something already made.

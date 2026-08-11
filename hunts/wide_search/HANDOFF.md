# HANDOFF — `wide_search`

Written for an agent starting cold. Read `MISSION.md` for scope,
`RESULTS-xiprime.md` for the finished piece, `RESULTS-higher-derivatives.md`
for the blocked one. This file is the operating state.

## Where things are

- **Branch `hunt/wide-search-xiprime`**, one commit (`38a2d1e`), **not pushed**.
  `main` is clean and carries the merge of PR #9 (`902294c`).
- Everything this hunt owns is under `hunts/wide_search/`:
  - `xiprime.py` — the instrument. Takes a pair-correlation form factor, returns
    `1/c`, `H`, `Hd`, and the optimal window. Its zeta control reproduces the
    source paper's Theorem D to 10 digits.
  - `probe.py` — the four standing controls (precision response, rival battery,
    null band). `precision_response` is calibrated in both directions: zeta(2)
    settles to 41 digits, a random value to 0.
  - `RESULTS-xiprime.md`, `RESULTS-higher-derivatives.md`, `MISSION.md`.

## The source paper — get it first, it is not in the repo

*More than two thirds of the zeros of the Riemann zeta function lie on the
critical line*, author "Claude", dated 10 August 2026. Public PDF:

    https://www-cdn.anthropic.com/564f962e60643842f5fcb4a17c9dbc8f608f1c37.pdf

    curl -sL <that url> -o /tmp/cz.pdf && pdftotext -layout /tmp/cz.pdf /tmp/cz.txt

2260 lines. The sections that matter: §1.4 (the idea), §3 (linear algebra),
§4 (zero side), §5 (prime side), §7.1 (the window optimisation for zeta),
**Remark 7.3 (zeros of xi', near line 1521)**, §7.5 (limits of the method),
and **Remark 1.1 (near line 180)**, which states the 0.68185 ceiling.

Note the OCR renders `2/L^3` in eq. (7.1) as `L23`. The reading that makes
`c_lambda(1) = F(lambda) = lambda/(1+lambda^2/3)` come out right is `2/L^3`;
this was checked independently and is not negotiable.

## What is established

The paper's machinery turns a pair-correlation form factor into an
unconditional proportion. With `v >= 0` even on `[-1/2,1/2]`:

    H = 2 - 1/c,   Hd = (1+H)/2,
    1/c_lambda(v) = [ int v^2 + lambda * iint F(lambda(s-s')) v(s)v(s') ]
                    / ( lambda (int v)^2 )

- `F(x) = |x|` (Montgomery) is zeta. Optimum `cos(sqrt(2) s)`, `H = 0.6725007`.
- `F_1(x) = |x| - 4x^2 + sum_{k>=1} ((k-1)!/(2k)!)(2|x|)^{2k+1}` (Farmer-Gonek,
  arXiv:0803.0425 Thm 1.1) is `xi'`.

**The finished result.** The paper's Remark 7.3 never solves the variational
problem for `xi'`. Solved here:

    H*  = 0.86864150052976706411...   (simple and on the critical line)
    Hd* = 0.93432075026488353205...   (distinct)

at `lambda = 1`, maximiser strictly positive (`v*(+-1/2)/v*(0) = 0.671042`).
Consequences: the paper's quartic was within `1.5e-6` of sharp, and **no
admissible window reaches Wu's unconditional 0.86957** (short by `9.285e-4`),
which settles the comparison the paper leaves open.

Reproduce in one line from the repo root:

    .venv/bin/python -c "import sys; sys.path.insert(0,'hunts/wide_search'); \
      from xiprime import optimise; print(optimise(kernel='xiprime')['H'])"

## THREAD 1 (open, harder, worth the most) — can zeta's 0.6725 move?

The paper's Remark 1.1 states that no certificate reading bandwidth-one data
"configuration by configuration" can exceed **0.68185**, while its Theorem D
attains **0.6725**. So the best such certificate lies in `[0.6725, 0.68185]`,
and closing any of that moves a headline number.

Framing, worked out but barely begun:

- For a single window `v` the prime side **pins** both `tr G = N` (configuration
  independent) and `||G||_F^2 = (1/c(v)) N`. So every window yields the same
  shape of constraint, `s_1 >= (2 - 1/c(v))N`, and the max over windows is
  exactly 0.6725. That is why one window cannot do better.
- The live question: the configuration must satisfy the constraints of **every**
  admissible window simultaneously, and different windows are different
  compressions of the *same* Weil form. Does the joint constraint set beat the
  best single member? Formulate "minimise `s_1/N` over configurations consistent
  with the known `(tr, ||.||_F^2)` for all windows" and solve it — it looks like
  an SDP/LP.
- A clean proof that the joint problem **collapses** to the single-window one is
  an equally good answer, and is what I would bet on.
- Strong check available: reproduce 0.68185 itself. If you cannot reconstruct
  the extremal configuration attaining it, you have not understood the ceiling.
- §7.5(b) says Prop 4.4 is sharp given only `tr`, `||.||_F^2`, the block
  structure and `tr P_1 <= s_1`; §7.5(d)-(e) close off higher moments
  unconditionally (Rudnick-Sarnak range `k*lambda < 2` allows only `k=3`, and
  odd moments do not help). So the extra juice, if any, is **not** more moments.

An agent was launched on this and stopped almost immediately; nothing from it
was kept.

## THREAD 2 (open, blocked) — closed form for `F_k`, `k >= 2`

Prior art that nearly went unnoticed: **Ji Bian, *The Pair Correlation of Zeros
of xi^(kappa)(s)*, PhD thesis, Univ. of Rochester, 2008, advisor Gonek.** Never
published, not on arXiv, ~one citation. Rochester institutional repository,
item 5500. It gives `F_kappa` under RH for `0 < |alpha| < 1`.

What is still open, and why it is blocked:

- Bian has **no closed form** (a ~14-fold combinatorial sum over set partitions,
  his eq. 7.8, evaluated by Mathematica in his Appendix A).
- He states he **cannot bound the tail** for `kappa >= 2`; his 0.9544 and 0.9774
  assume "the coefficients after 11 terms are negligible".
- Measured here: that assumption fails where it matters. The 11-term truncations
  give `F_kappa(1)` = 2.78, 31.9, 427.3, 2476.3 for `kappa` = 1..4, and
  proportions of 0.596, **1.198** (impossible) and **-2.64**. Usable only to
  `alpha ~ 0.4`; the optimum sits at `lambda = 1`.

So a closed form or a real tail bound is required, and either would repair a gap
Bian flagged himself. The exact rational check grid (his Fig. 10.1, `kappa`
1..4, `i` 1..11) is tabulated in `RESULTS-higher-derivatives.md`, together with
his proved stabilisation lemma `C_{j,i} = C_{i-2,i}` for `j >= i-2`. The
`kappa=1` row is reproduced exactly by the closed form above — that is what
fixes the normalisation.

**Do not fit coefficients to that grid and call it a derivation.** Eleven
targets per row makes fitting easy and worthless; three fitted two-parameter
kernels already hit the published `k=1` data points to machine precision and are
all wrong.

Two derivation agents were stopped mid-flight. One had matched `kappa=1`
exactly, found its general-`k` formula failing `kappa >= 2`, and said it had
located the cause without landing a fix. Neither produced a formula; nothing was
kept.

Expected value warning before spending on this: Conrey's unconditional bar is
0.79874 (k=1), 0.93469 (k=2), 0.9673 (k=3). At the efficiency seen at k=1 the
method lands ~1.6 points over Conrey at k=2 and under a point at k=3. Real, but
much less striking than k=1.

## Environment gotchas that cost time

- Python is **always** `.venv/bin/python` from the repo root. Never `python3`.
- Ball-arithmetic backend must be Arb: `.venv/bin/python -c "from zeta import
  rigor; print(rigor.BACKEND, rigor.available_backends())"` should say
  `python-flint ['mpmath.iv', 'python-flint']`.
- **No Lean toolchain on this machine** and the disk was at 90% (21 GB free).
  Installing elan + Mathlib would consume most of it. Deferred deliberately; do
  it only if something formalizable actually exists.
- `gh` is authenticated as `tlince`, which **cannot merge** in this repo. Use
  `gh auth switch --user teal-sea`, then switch back.
- The lexical ban under `hunts/` is machine-enforced by
  `tests/test_hunt_probe_discipline.py` on the reserved word that
  `zeta/rigor.py` owns — which this file therefore cannot spell. It is a
  case-insensitive *substring* match, so it also catches the word with a
  negating prefix, and it applies inside a sentence disclaiming it. Writing this
  bullet the obvious way failed the suite; see `CLAUDE.md` for the term itself.
  *verified / confirmed / definitively / proves* are banned by documentation but
  not by a test. Say *measured*, *observed*, *consistent with*.
- Before handing back, run: `tests/test_hunt_probe_discipline.py`,
  `tests/test_docs_numbering.py`, `tests/test_doors.py`, and
  `scripts/make_context.py --check`.

## Standing honesty constraints

- Nothing in this hunt is evidence for or against RH, in either direction.
- The finished result is an **optimisation**, not a new theorem: the functional
  is the paper's, the form factor is Farmer-Gonek's. Novelty of the sharp
  constant was gated at about 0.85 confidence by reading primary sources.
- It rests on a paper published 10 August 2026 that has not been peer reviewed.
- Two citation problems are recorded and should not be propagated: the
  "Conrey 1989 = 79.874%" figure was not located in that paper (its stated
  results concern zeta); and the `alpha_j` family appears to be Farmer's 1995
  combination of Conrey 1989 + 1983-II rather than a display in either.
- A generator of a claim never judges it. Every number above that matters was
  reproduced by an independent route before being written down.

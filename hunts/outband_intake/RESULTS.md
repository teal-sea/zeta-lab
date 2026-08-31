# outband_intake — the information is worth about 0.0068, and no known certificate can spend it

**Verdict: the kill condition did NOT fire, and the hunt found a gap rather than a wall.**
The unconditional out-of-band positivity of Baluyot, Goldston, Suriajaya and
Turnage-Butterbaugh (arXiv:2306.04799, Theorem 1) is worth about `+0.0068` at the
measure level, landing the configuration class near `0.6793`. Separately, and this is
the point of the hunt, the certificate machinery that would turn that into a theorem
provably cannot reach it. What separates them is one structural obstruction, stated
below with a counterexample.

Grade: **measured**, and only that. Two LP ladders on matched grids with a calibrated
extrapolation. Nothing is kernel-checked, no theorem is claimed, and nothing here is
evidence for or against RH (`docs/08`).

## 1. The measurement

Four matched rungs, once with out-of-band nonnegativity enforced on `(1, 3]` and once
with bandwidth-one data alone. The discretisation restricts the adversary, so both
ladders descend toward their limits from above.

| X | J | out-of-band | in-band control | difference |
|---|---|---|---|---|
| 40 | 200 | 0.6918387 | 0.6793882 | 0.0124505 |
| 80 | 320 | 0.6862544 | 0.6775676 | 0.0086868 |
| 120 | 480 | 0.6847195 | 0.6768963 | 0.0078232 |
| 160 | 640 | 0.6838668 | 0.6764627 | 0.0074041 |

The in-band ladder was extended alone, being roughly 240 times cheaper: `0.6759394`
at `X = 240` and `0.6756339` at `X = 320`.

**The difference is the signal, and the method is calibrated before it is believed.**
Extrapolating `d(X) = v_out - v_in` by `a + b·X^(-p)` gives `a = +0.0068`. The same
fit applied to the in-band excess, whose true limit is known to be zero because the
in-band LP measures the Montgomery-Taylor dual, returns `+0.0022`. That is the method
error. The gain exceeds it by about threefold, so zero is excluded, though not
overwhelmingly. The implied class value is `0.6793`, which sits essentially on top of
Chirre, Goncalves and de Laat's `0.6792`.

**A ratio test was tried first and is withdrawn.** Comparing excesses over the record
gives `2.808, 2.714, 2.780, 2.869`, and an earlier draft of this file read that
flatness as proof of a common limit. It is not. Over this range the two ladders decay
at nearly the same rate, so the ratio is flat under both hypotheses and carries no
information; the slight rise across the range is in fact what a positive limit
predicts. The difference test with a calibrated error is the right instrument.
Recorded because the withdrawn argument was stated confidently and was wrong.

Solver robustness: the out-of-band solve at `X = 80` agrees to seven digits across
`highs`, `highs-ds` and `highs-ipm`. The in-band ladder independently reproduces the
published values in `frontier_math/RESULTS-frontier-math.md` §1.

## 2. Why no certificate can spend it

The inertia argument that would consume out-of-band information needs the evaluation
form to be positive semidefinite. That forces the window's spectral density
`v = phi^2` to be nonnegative, and the pair weight in alpha-space is its
self-convolution `Khat = v * v`, nonnegative everywhere by identity. **The framework
never has a free `ghat`. It has a free `v >= 0`.** The source paper's own functional
carries `int |Khat|`, and `v >= 0` is exactly what discharges that modulus
(`hunts/frontier_math/paper_pin.py`).

The requirement cannot be weakened to something a signed kernel satisfies. Replacing
the Frobenius inner product by a weighted `tr(X^H S Y S)` with indefinite `S` keeps
the rank half of the lemma, which needs no definiteness, and breaks the inertia half,
which needs `S^(1/2)`. Minimal counterexample: one off-line pair with
`Q = t·[[0,1],[1,0]]`, `S = diag(1,-1)`, `c = 2` gives slack `+2.0` at `t = 1` and
`-0.5` at `t = 1.5`. Against 4000 random positive-semidefinite pairs the inequality
was never violated, worst slack `+0.001321`, so the instrument would have seen a
violation had one existed.

The first-order perturbation law says where the gain lives. Adding out-of-band mass
`-eps` where `F >= Lbar` moves the bound by `dJ/deps = (J - Lbar)/g(0)`, which is
adverse for every `Lbar` below about `1.3275`. BGSTB gives `Lbar = 0`, so the direct
channel pays nothing. **The entire gain is indirect**: negative out-of-band mass
relaxes the constraint and licenses an in-band profile that is not an autocorrelation.
That is precisely the profile the inertia framework cannot represent.

## 3. So the result is a gap, not a wall

The information supports about `0.679`. Every known certificate construction is
confined to `0.6725007`. The difference is not a missing computation and not a
frozen constant. It is that the only proof technology available insists on kernels
that are squares, and the value lives at a kernel that is not one.

**That gap is the research problem this hunt hands forward**, and it is the one
shape the operator asked for: not a ceiling, not a bridge over somebody's theorem,
but a construction nobody has. It is also why the CGdL value is conditional. They
reach `0.6792` with an isolation input that costs RH; the LP reaches the same place
with unconditional inputs, which says the RH is doing work in their *proof* that it
may not be doing in the *truth*.

## 4. One open question that bounds this entire file

**Whether the LP's constraint set is unconditionally valid for zeta's zeros has not
been checked here, and it is load-bearing.** The out-of-band constraint is BGSTB and
is unconditional. The `tau >= -1` bound is `rho >= 0`, the nonnegativity of a pair
density, true of any point process and costing no hypothesis. An intermediate report
claimed that bound smuggles in the diagonal-isolation drop and cited
`frontier_math/CLEAN-KILL-REPORT.md`; that document concerns a different object, the
`-2` off-line block interaction in the rank-trace inequality, and does not support
the claim. **The in-band pair-correlation data is the one not audited**, and until
someone traces it to an unconditional source rather than to Montgomery's
RH-conditional theorem, `0.6793` is a class value and not an unconditional one. That
audit is the cheapest next step and it decides whether §3's gap is worth funding.

## 5. Cost

Under two hours of laptop compute, no CI, no formalization. A negative would have
been reached before anything expensive was funded; so was a positive.

## The doors

**Active constraints at the optimum.** One binds: the certificate kernel must be an
autocorrelation. Everything in §2 is that constraint seen from a different angle, and
§1 measures what it costs, about `6.8e-3`.

**Frozen-constant inventory.**

| Frozen | Chosen as | What relaxing it would trade |
|---|---|---|
| kernel class: autocorrelations `Khat = v*v` | forced by the inertia lemma | **The door.** Any construction certifying a bound from a signed kernel converts §1's measured `0.679` into a theorem. Trades proof technology for `6.8e-3`, seven times the public race's total progress. |
| out-of-band reach `A_out` | 3.0 | Untested; lane B never ran. The first-order law predicts the direct channel is worthless, so this prices the indirect channel only. Cheap. |
| truncation `X` | 160 out-of-band, 320 in-band | Sharpens the extrapolation and shrinks the `2.2e-3` method error, which is currently a third of the signal. The out-of-band arm costs about `X^2.8`; `X = 240` exceeded an hour on a laptop and was killed. Belongs in CI. |
| in-band data provenance | inherited from `frontier_math` | Not a constant but an unaudited assumption, see §4. Decides whether the number is unconditional. |

**Information class.** The reach and truncation doors stay inside the data the family
already reads and buy only confidence. The kernel-class door and the provenance audit
are the two that matter, and neither requires reading more information: the
information is already in hand and unspent. That is what makes this different from
the sieve wall of `frontier_math` §2, where the missing input is Hardy-Littlewood
grade and genuinely absent.

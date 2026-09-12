# Higher derivatives: what blocks the extension, measured

**Status: a measured obstruction and a located piece of buried prior art. Not a
result about zeta. Nothing here is evidence for or against RH.**

## The obvious extension, and why it is not obvious

The paper's Remark 7.3 treats `xi'` only. Since its machinery turns a
pair-correlation form factor into an unconditional proportion, the natural next
move is `xi^(k)` for `k >= 2`, where Conrey's unconditional constants are
higher and would have to be beaten.

Two things had to be established first: whether the form factor `F_k` is known,
and whether it is usable.

## The prior art, which is easy to miss

`F_k` for general `k` **exists**: Ji Bian, *The Pair Correlation of Zeros of
xi^(kappa)(s)*, PhD thesis, University of Rochester, 2008, supervised by
Gonek, the companion to Farmer-Gonek-Lee. His Theorem 1 gives `F_kappa(alpha)`
under RH for `0 < |alpha| < 1`.

It was never published, is not on arXiv, is not in the arXiv full-text index,
and carries essentially one citation in the literature. It is a genuine
buried-prior-art hazard: a novelty claim for "the form factor of `xi^(k)`" made
without it would have been wrong.

Two things it does **not** do, which is where the room is:

1. **No closed form.** Bian's coefficients come from an unevaluated ~14-fold
   combinatorial sum over set partitions and integral vectors (his eq. 7.8),
   evaluated by a Mathematica program reproduced in his Appendix A. There is no
   analogue of the `k = 1` closed form
   `2|x| int_0^1 (exp(4 x^2 t(1-t)) - 1) dt/t`.
2. **No tail bound for `kappa >= 2`.** In his words: *"For higher cases of
   kappa, we can not prove that the tail of the function F_kappa(alpha) is
   small."* His constants 0.9544 (`k=2`) and 0.9774 (`k=3`) rest on *"assuming
   the coefficients after 11 terms are negligible"*, and he notes that for
   `kappa = 3` *"the coefficients are not settling down yet"*.

His Figure 10.1 tabulates exact rationals `C_{kappa,i}` in
`F_kappa(alpha) = spike + sum_i C_{kappa,i} |alpha|^i`:

| kappa | `C_{kappa,1..11}` |
|---|---|
| 1 | 1, -4, 4, 0, 4/3, 0, 16/45, 0, 8/105, 0, 64/4725 |
| 2 | 1, -4, 4, -16, 28, 16, 544/45, -512/45, -104/63, -416/945, 6688/1575 |
| 3 | 1, -4, 4, -16, 332/5, -448/3, 81296/315, 75512/315, 17104/2835, -219808/2025, 1350848/10395 |
| 4 | 1, -4, 4, -16, 332/5, -224, 189584/315, -382024/315, 1414256/945, 28355392/14175, -4107904/17325 |

The `kappa = 1` row is reproduced **exactly**, all eleven coefficients, exact
rational equality, by the closed form used in `RESULTS-xiprime.md`. That is an
independent check on the whole `xi'` computation from a source written sixteen
years earlier, and it fixes the normalisation, so the rest of the table can be
read with confidence.

## The measured obstruction

Bian's caveat is not a formality. Feeding the 11-term truncations into the
optimiser at `lambda = 1`:

| kappa | `F_kappa(1)` from 11 terms | `H*` from the truncation | plausible? |
|---|---|---|---|
| 1 | 2.78 | 0.8686569 | yes, `1.5e-5` above the exact 0.8686415 |
| 2 | 31.9 | 0.5962859 | no |
| 3 | 427.3 | **1.1978387** | impossible: it is a proportion |
| 4 | 2476.3 | **-2.6389193** | impossible |

For `kappa = 4` the terms are still *growing* at `i = 10` (2000.4). The
truncation is usable only for `alpha` up to roughly 0.4, and the optimum sits at
`lambda = 1`, which is exactly where it fails. `kappa = 1` is the only row where
truncating at eleven terms is harmless, and that is because its tail is known in
closed form.

**So no constant for `kappa >= 2` is obtainable from the tabulated coefficients
at the bandwidth the method needs.** Bian's own numbers for `k = 2, 3` are
therefore RH plus an assumption that this measurement does not support at
`alpha` near 1; whether they survive a real tail bound is open.

## What would have to be true for the extension to work

A closed form for `F_k`, `k >= 2`, or a genuine bound on the tail. Either would
also repair the gap Bian flagged himself. Two independent derivations were
commissioned against the check grid above; their outcome is recorded separately
if they reach one.

Worth knowing before anyone spends more on this: the headroom shrinks fast.
Conrey's unconditional constants for simple-and-on-the-line are 0.79874
(`k=1`), 0.93469 (`k=2`), 0.9673 (`k=3`); the `k=1` optimum reached here,
0.86864, recovers about 84% of the best RH-conditional constant. At the same
efficiency `k=2` would land near 0.951, about 1.6 points over Conrey, and `k=3`
near 0.976, under a point. Real, unconditional, and an order of magnitude less
striking than `k=1`. (That extrapolation is an inference from read constants,
not anything published.)

## Provenance note

Conrey's unconditional constants are quoted from Conrey, *Zeros of Derivatives
of Riemann's Xi-Function on the Critical Line I and II* (J. Number Theory 16
(1983) 49-74 and 17 (1983) 71-75), and from Farmer's 1995 restatement of
Conrey's Crelle 399 (1989) results. The Crelle paper itself is paywalled and was
not read; the `alpha_j` family for `j >= 1` appears to be Farmer's combination
of the 1989 and 1983-II results rather than a display in the 1989 paper, and is
cited here as such. See `RESULTS-xiprime.md` for the related caveat about the
79.874% attribution.

---

## TO BE CONTINUED

Two threads were live when this session ended and are **not** claimed. Both are
picked up from here, not restarted.

1. **A closed form for `F_k`, `k >= 2`** (or a genuine tail bound). Two
   independent derivations were mid-flight. One had reproduced Bian's `k = 1`
   row exactly on all eleven coefficients, found its general-`k` formula failing
   the `kappa >= 2` rows, and reported it had located the cause but had not yet
   landed a fix. The other was mid-way through a structural simplification. No
   general-`k` formula survived, so nothing from either is recorded as a result.
   The check grid they must satisfy is the `kappa = 2,3,4` table above, plus
   Bian's stabilisation lemma. Do not fit to that grid: eleven targets per row
   makes fitting easy and worthless.

2. **Whether zeta's own 0.6725 can be moved toward 0.68185.** The paper's
   Remark 1.1 states an explicit ceiling of 0.68185 for any certificate reading
   bandwidth-one data configuration by configuration, while Theorem D attains
   0.6725, so the truth for the best such certificate lies in
   `[0.6725, 0.68185]`. The well-posed question is whether the constraints from
   the *whole family* of admissible windows, which all describe the same zero
   configuration, beat the best single window; the paper's per-window
   certificate is what gives the lower end. This is the highest-value thread of
   the three and it was barely begun. A clean proof that the joint problem
   collapses to the single-window one would also be a real answer.

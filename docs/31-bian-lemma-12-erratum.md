# Erratum to Bian, Lemma 12: `C_{kappa,2}` is `-4 kappa`, not `-4`

Hunt #65 (`hunts/r_2ac05f/`) adjudicated two contradicting `kappa = 2` tables
in this repository and, in doing so, located the error that produced the
disagreement. It is not in either table's code. It is in the analytic lemma
both of them inherited.

Bian's Lemma 12 asserts that the second regular coefficient of the pair-
correlation form factor for the zeros of `xi^(kappa)` is `C_{kappa,2} = -4`,
universally in `kappa`. The correct value is

    C_{kappa,2} = -4 kappa.

The two agree at `kappa = 1`, which is the whole reason this survived: every
control anyone ran was a `kappa = 1` control, and `-4 kappa` and `-4` are the
same number there.

This page states the correction, its three-line proof, the mechanism that
produced it, and what it changes. Every number here is produced by
`hunts/r_2ac05f/probe.py` and pinned in `hunts/r_2ac05f/results.json`.

Nothing here is evidence for or against RH (`docs/08`). The object is a form
factor for the zeros of a derivative of `xi`, not a statement about the zeros
of `zeta`.

## 1. The correction

Write `P = xi'/xi`, so that `xi^(kappa) = Q_kappa(P) xi` with `Q_0 = 1` and
`Q_{kappa+1} = D Q_kappa + P Q_kappa`. With `P = L + g`, `L = (1/2)
log(T/2pi)` held constant, `g = zeta'/zeta`, and `x = 1/L`, set
`Qhat_kappa = Q_kappa / L^kappa`. Dividing the recursion by `L^{kappa+1}`
removes `L` entirely:

    Qhat_0 = 1,    Qhat_{kappa+1} = x D Qhat_kappa + (1 + g x) Qhat_kappa.

**The three lines.** The `x^1` coefficient of `Qhat_kappa` is `kappa * g`, for
every `kappa` — it accumulates once per application of the recursion, and the
recursion is applied `kappa` times. Hence the first arithmetic coefficient of
`R_kappa = xi^(kappa+1)/xi^(kappa)` is `q_1 = kappa * (Lambda log)`. And since
`C_{kappa,i} = 2^{i-1} sum_{p+q=i-1} <q_p, q_q>`,

    C_{kappa,2} = 2(<q_0,q_1> + <q_1,q_0>) = -4 kappa.

The probe prints the coefficient directly, and it is `-kappa` on the single
word `(0,)` at every `kappa`:

| kappa | 1 | 2 | 3 | 4 | 5 | 6 |
|---|---|---|---|---|---|---|
| `x^1` coefficient of `Qhat_kappa` | -1 | -2 | -3 | -4 | -5 | -6 |
| `C_{kappa,2}` derived | -4 | -8 | -12 | -16 | -20 | -24 |
| Lemma 12 as published | -4 | -4 | -4 | -4 | -4 | -4 |

`hunts/r_2ac05f/results.json` pins `kappa = 1..3` under
`multiplicity_witness`. The `kappa = 4..6` columns were re-derived for this
page by calling `hunts/r_2ac05f/probe.py` directly
(`form_factor(kappa, 2)` and `qhat(kappa, 2)`), and are recorded here as
reproduced rather than as quoted from the hunt.

## 2. The mechanism: a dropped multiplicity

`hunts/higher_xi/C2_PROVENANCE.md` names the step, on thesis p. 71: the
weights `M(v_l) M(w_k)` are present before the application of Theorem 3 and
absent from the next displayed line and from eq (8.1). That multiplicity is
exactly the factor of `kappa`. The diagnosis was recorded in this repository
before this hunt ran; what was missing was an independent derivation that
confirmed it rather than asserting it.

The consequence is not confined to one cell. The same missing multiplicity
sits inside `Qhat_kappa`, therefore inside every `q_j`, therefore inside every
`C_{kappa,i}`. Correcting `C_{kappa,2}` alone would not repair the table.

## 3. What it changes

The corrected `kappa = 2` row is `hunts/higher_xi/C2_EXACT.json`, and this
hunt's independent derivation reproduces it exactly at all eleven indices:

| i | 1 | 2 | 3 | 4 | 5 | 6 |
|---|---|---|---|---|---|---|
| corrected | 1 | **-8** | **24** | **-32** | **64/3** | **-64/3** |
| Bian Fig. 10.1 | 1 | -4 | 4 | -16 | 28 | 16 |

| i | 7 | 8 | 9 | 10 | 11 |
|---|---|---|---|---|---|
| corrected | **1216/45** | **-256/15** | **1088/63** | **-11776/945** | **42496/4725** |
| Bian Fig. 10.1 | 544/45 | -512/45 | -104/63 | -416/945 | 6688/1575 |

Only `i = 1` survives unchanged.

## 4. Why it was invisible, measured rather than asserted

The published `kappa = 1` row is the natural control, and it cannot see this
defect. `hunts/r_2ac05f/fault_check.py` demonstrates that instead of claiming
it, by planting the defect in the probe's own machinery:

| plant | Farmer-Gonek `kappa = 1` control | effect at `kappa = 2` |
|---|---|---|
| force `Qhat_kappa`'s `x^1` coefficient to `g` instead of `kappa * g` | **still passes** | `C_{2,2}` becomes `-4`, the published value |
| corrupt the pairing denominator by one factorial step | **fails** | n/a |

The first row is the finding: a control that passes while the defect under
audit is planted has no power over that defect. The second row is the
calibration that stops the first from being explained away as a dead control.

This is the general lesson, and it is recorded as a Core candidate rather than
built here: **when a claim asserts a quantity is invariant in a parameter, the
control must vary that parameter.** Every control here was at `kappa = 1`, and
the claim under test was a claim about all `kappa`.

## 5. Standing, and what this is not

The derivation is exact rational arithmetic throughout: no floating point, no
precision parameter, no enclosures, because nothing here is a numeric
estimate. It is **not** kernel-checked; the Lean arm carries none of it.

Its external anchor is Farmer-Gonek (arXiv:0803.0425), whose `kappa = 1` row
this repository owns no part of. The probe reproduces all eleven of its
values exactly, including the four forced zeros, through the same code path
that produces the `kappa = 2` row.

**The one borrowed ingredient** is the basis pairing, taken from
`hunts/higher_xi/`. It is `kappa`-independent by construction and calibrated
by the `kappa = 1` control, and the second row of the table in section 4 shows
that control does go red when the pairing is corrupted — so the borrowing is
anchored rather than circular. A fully independent rederivation of the pairing
from the mean-value theorem was not attempted, and is the first thing to do if
this correction is ever submitted anywhere.

The three implementation defects that `hunts/rogue_frontier/fkappa/` found in
the thesis code are not disputed by this page and are not withdrawn by it.
They concern eq (10.1)'s assembly, eq (7.8)'s phantom slots and eq (6.18)'s
normalization; they appear to be real findings about the code. They are simply
not the whole error. An audit that reimplements a computation faithfully,
finds genuine defects in it, and inherits the author's *analytic* lemma as an
axiom cannot detect an error in that lemma — which is what happened, and
`fkappa/RESULTS.md` §1 says so in writing: `C_{kappa,2} = -4` was "carried as
constants here, as Bian carried them."

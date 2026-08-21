# R-2AC05F: the kappa = 2 table on `main` is right, and the other one inherited the defect it was auditing

**Verdict: settled.** An independent recomputation, written for this
adjudication and importing neither disputant, reproduces
`hunts/higher_xi/C2_EXACT.json` exactly at all eleven indices, and reproduces
the externally published Farmer-Gonek `kappa = 1` row exactly at all eleven
indices as its control. `hunts/rogue_frontier/fkappa/`'s corrected
`kappa = 2` row is wrong from `i = 2`.

Grade: **hardened**. Two independent derivations of the same eleven rationals
in exact arithmetic (higher_xi's three routes, and this probe's fourth), with
an external anchor the literature fixes. Not kernel-checked; no enclosures are
involved because nothing here is a numeric estimate.

Nothing here is evidence for or against RH (`docs/08`).

## 1. The table

`C_{2,i}`, the regular coefficients of Bian's pair-correlation form factor for
the zeros of `xi''`. All values exact rationals.

| i | this probe | `higher_xi` C2_EXACT | `fkappa` corrected | Bian Figure 10.1 |
|---|---|---|---|---|
| 1 | 1 | 1 | 1 | 1 |
| 2 | **-8** | -8 | -4 | -4 |
| 3 | **24** | 24 | 4 | 4 |
| 4 | **-32** | -32 | -16 | -16 |
| 5 | **64/3** | 64/3 | 52/3 | 28 |
| 6 | **-64/3** | -64/3 | 16/3 | 16 |
| 7 | **1216/45** | 1216/45 | 208/45 | 544/45 |
| 8 | **-256/15** | -256/15 | -64/15 | -512/45 |
| 9 | **1088/63** | 1088/63 | -40/63 | -104/63 |
| 10 | **-11776/945** | -11776/945 | -32/945 | -416/945 |
| 11 | **42496/4725** | 42496/4725 | 3424/4725 | 6688/1575 |

Control row, `kappa = 1`, against Farmer-Gonek (arXiv:0803.0425)
`F_1 = |a| - 4a^2 + sum_k ((k-1)!/(2k)!)(2|a|)^{2k+1}`:

| i | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 |
|---|---|---|---|---|---|---|---|---|---|---|---|
| derived | 1 | -4 | 4 | 0 | 4/3 | 0 | 16/45 | 0 | 8/105 | 0 | 64/4725 |
| published | 1 | -4 | 4 | 0 | 4/3 | 0 | 16/45 | 0 | 8/105 | 0 | 64/4725 |

Exact agreement, including the four forced zeros. Both disputants also agree
on this row, so it is common ground and not itself in dispute.

## 2. How the probe derives it, and what it borrows

Write `P = xi'/xi`. Then `xi^(kappa) = Q_kappa(P) xi` with `Q_0 = 1` and
`Q_{kappa+1} = D Q_kappa + P Q_kappa`, so

    R_kappa := xi^(kappa+1)/xi^(kappa) = P + D log Q_kappa.

With `P = L + g`, `L = (1/2) log(T/2pi)` held constant, `g = zeta'/zeta`, and
`x = 1/L`, put `Qhat_kappa = Q_kappa / L^kappa`. Dividing the recursion by
`L^{kappa+1}` removes `L` entirely:

    Qhat_0 = 1,    Qhat_{kappa+1} = x D Qhat_kappa + (1 + g x) Qhat_kappa,

and `R_kappa = L + g + D Qhat_kappa / Qhat_kappa =: L + sum_j q_j x^j`. The
`q_j` are finite combinations of Dirichlet convolutions of
`A_b(s) = sum_n Lambda(n) log^b(n) n^{-s}`, represented as multiset words, with
`g = -A_0`, product = concatenation, and
`D (b_1..b_r) = - sum_j (b_1..b_j+1..b_r)`.

The form factor is then `C_{kappa,i} = 2^{i-1} sum_{p+q=i-1} <q_p, q_q>`.

**The one borrowed ingredient** is the basis pairing, taken from
`hunts/higher_xi/C2_EXACT.json`:

    <(b_1..b_r),(d_1..d_r)> = sum_{sigma in S_r} prod_j (b_j + d_sigma(j) + 1)!
                              / (2r + sum b + sum d - 1)!,   0 on unequal lengths.

This is legitimate to borrow because it is **kappa-independent by
construction**: it knows only about products of `Lambda`'s and nothing about
which derivative of `xi` produced them. It is therefore fully pinned by the
`kappa = 1` row, which the literature fixes independently, and §4 below shows
by fault injection that the `kappa = 1` control does have power against it.
Everything else in `probe.py` was written for this adjudication.

Sanity checks along the way, all confirmed by the code:
`Qhat_1 = 1 + g x` and `Qhat_2 = 1 + 2 g x + (g' + g^2) x^2`, which is exactly
the object `hunts/higher_xi/C2_PROVENANCE.md` writes down by hand.

## 3. Why the other table is wrong, in one line

The `x^1` coefficient of `Qhat_kappa` is `kappa * g`, for every kappa. The
probe prints it:

    kappa=1: -1 * (0,)     kappa=2: -2 * (0,)     kappa=3: -3 * (0,)

so the first arithmetic coefficient of `R_kappa` is `q_1 = kappa * (Lambda log)`
and therefore

    C_{kappa,2} = 2(<q_0,q_1> + <q_1,q_0>) = -4 kappa.

Derived by the probe for kappa = 1..5: **-4, -8, -12, -16, -20**.

Bian's Lemma 12 asserts `C_{kappa,2} = -4` universally. That assertion is the
dropped multiplicity, and it is exactly the defect
`hunts/higher_xi/C2_PROVENANCE.md` names on thesis p. 71: the weights
`M(v_l) M(w_k)` present before the application of Theorem 3 and absent from the
next displayed line and from eq (8.1). `higher_xi`'s causal diagnosis is
confirmed.

**And this is the specific mechanism by which `fkappa` went wrong.**
`fkappa/RESULTS.md` §1 states it plainly: "`C_{kappa,1} = 1` and
`C_{kappa,2} = -4` are universal (his Lemma 12); they come from analytic main
terms outside this machinery and are **carried as constants here, as Bian
carried them**." An audit that reimplements a computation faithfully, finds
three real implementation defects in it, and then inherits the author's
*analytic* lemma as an axiom, cannot detect an error in that lemma. The three
defects `fkappa` found look genuine on their own terms and are not disputed
here (they concern eq (10.1)'s assembly, (7.8)'s phantom slots and (6.18)'s
normalization). They are simply not the whole error, and correcting them while
keeping `-4` propagates the larger one into every corrected value from `i = 3`
on, because `C_{kappa,2}` is not an isolated cell: the same missing
multiplicity sits inside `Qhat_kappa` and therefore inside every `q_j`.

So the two diagnoses are not symmetric competitors. `fkappa`'s is a correct
finding about the thesis *code*; `higher_xi`'s is a correct finding about the
thesis *mathematics*, and it dominates.

## 4. The control that would have caught it

`fkappa/RESULTS.md` §5(a) already writes the indictment of its own control
set, without drawing the conclusion:

> the kappa = 1 row ... is simultaneously the strongest validation of the
> engine and the reason none of the three defects was ever visible from the
> literature side.

`fault_check.py` measures that blindness instead of asserting it. Two plants
in the probe's own machinery:

| plant | Farmer-Gonek `kappa=1` control | effect at `kappa=2` |
|---|---|---|
| force `Qhat_kappa`'s `x^1` coefficient to `g` instead of `kappa*g` (i.e. plant the defect under audit) | **still passes** | `C_{2,2}` becomes **-4**, the published value |
| corrupt the pairing denominator by one factorial step | **fails** | n/a |

The first row is the finding. The only externally anchored control either hunt
ran has **zero power** against the defect that decides the dispute, and the
plant reproduces the published wrong value exactly. The second row shows the
control is not vacuous: it does catch a corruption of the ingredient it
calibrates.

**The control that would have caught it, stated so it can be reused:**

> When a claim asserts that a quantity is *invariant* in a parameter, the
> control must vary that parameter. Compute `C_{kappa,2}` independently for
> `kappa = 1, 2, 3` and assert the values are not equal.

It is three lines of the derivation above, it needs no thesis and no
reimplementation, and it turns Lemma 12 from an inherited axiom into a
checkable statement. `fkappa` ran `kappa = 1..9` grids throughout and never
ran this check, because the quantity it varied `kappa` over was always
downstream of the constant it had already fixed.

This is the same failure shape the roster already carries from run `726a6b3f`
on `finite_height_spacing_experiment`: a control that "sweeps `ell` only,
holding effective gamma at 1, so it cannot vary W at fixed x ... the control
is blind to its own subject". The thread match on this brief was correct, and
the shared name for it is: **an invariance claim needs a control that moves
the variable the invariance is asserted over.**

## 5. What this does and does not change

* `hunts/higher_xi/C2_EXACT.json` and `C2_EXTENDED.json`, and everything on
  `main` that consumes them, stand. This adjudication is a third exact route
  agreeing with them.
* `hunts/rogue_frontier/fkappa/`'s **kappa = 1 row survives** in all modes: it
  is the Farmer-Gonek closed form and it is right.
* `fkappa`'s reproduction of Figure 10.1 cell for cell survives as a
  statement about the thesis code, and is independently useful: it is how we
  know both hunts are reading the same published row (`fkappa`'s
  `skip`/`rows_figure` kappa=2 row equals `higher_xi`'s recorded
  `bian_figure_10_1` column exactly, all eleven cells).
* `fkappa`'s three implementation defects (A, B, C) are **not adjudicated
  here**. They may all be real; this hunt did not test them and takes no
  position. What it establishes is that correcting them is not sufficient,
  because the row is already wrong at `i = 2`, upstream of all three.
* `fkappa`'s corrected values from `i = 5` on, its `i <= 20` extension, its
  closed generating identity `C((a),(b)) = (-1)^{a+b} ab/(a+b-1)`, and its
  observed radius-1/2 coherence with Bian's picket-fence Lemma 13 are all
  computed on top of the wrong constant. The coherence observation is the one
  worth a second look: it is a real structural signal, and if it survives
  redoing the extension on the correct `C_{kappa,2} = -4 kappa`, it is
  evidence for the corrected diagonal rather than for `fkappa`'s.

## 6. Reproduce

```bash
.venv/bin/python hunts/r_2ac05f/probe.py        # ~1 s, writes results.json
.venv/bin/python hunts/r_2ac05f/fault_check.py  # ~1 s, writes fault_check.json
```

Exact rational arithmetic throughout; no floating point, no mpmath, no
precision parameter to get wrong.

## Loose threads

1. **`fkappa`'s extension to `i = 20` should be re-run on `C_{kappa,2} = -4 kappa`.**
   Why it might matter: `fkappa` observed that its corrected diagonal has ratios
   converging to `-2`, i.e. radius of convergence exactly `1/2`, matching the
   phase transition of Bian's own picket-fence heuristic (his Lemma 13) at
   `|alpha| = 1/2`, and that the published diagonal admits no such reading. That
   is a genuine internal-coherence signal, and it was computed with the wrong
   `C_{kappa,2}`. If it *strengthens* on the corrected constant, it is real
   evidence for the corrected table's structure; if it evaporates, the
   coherence was an artifact and the observation should be withdrawn. Either
   answer is worth having. First step: take `fkappa`'s `bian_engine.py`
   `--extend 20 --reading corrected`, replace its hard-carried `C_{kappa,2}`
   with `-4*kappa`, and recompute the stable diagonal ratios `r_i`.

2. **`fkappa`'s three implementation defects are unadjudicated.** Why it might
   matter: defects A, B and C are claims about Bian's *code* independent of the
   Lemma 12 error, each pinned by a finite witness (`consikapa(6,2,3,2) = 1/30`;
   `|C((j),(1))| = 1` against the skip convention's `6/5, 7/6, 9/7`;
   `Lambda_2(6) log 6 = 2 log2 log3 log6` against the printed RHS `4 log2 log3 log6`).
   They are cheap to check and nobody has. First step: check the third witness
   by hand against thesis (6.18) — it is a single `n = 6` evaluation.

3. **The `fkappa` directory exists on no branch that has landed.** Why it might
   matter: it was found at commit `360c545` on the `hunts(rogue_frontier)`
   checkpoint lineage, and it carries a `.ext_lock` file and a campaign ledger.
   The lab's public record does not contain it, so a reader of `main` cannot see
   either side of this dispute. First step: decide whether `rogue_frontier/`
   lands with a correction notice pointing at this hunt, or stays unlanded; that
   is an operator call, not a mathematical one.

4. **`C_{kappa,2} = -4 kappa` is a small original result about Bian's
   Theorem 1 and is currently recorded nowhere but here.** Why it might matter:
   it is a one-line correction to a published lemma with a three-line proof, and
   the two hunts between them spent considerable compute never stating it. First
   step: if `higher_xi`'s Bian findings are ever written up, state the general
   `kappa` form rather than only the `kappa = 2` instance.

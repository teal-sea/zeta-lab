# Gauss-positivity lane: the Fourier structure of Xi and the moment problem

Started 2026-10-03. Route chosen under the 2026-09-12 owner mandate
(`ALIGNMENT.md` section 0), which permits original mathematics toward RH and
useful intermediate results. This hunt attempts a contribution and may fail;
it does not presume success, and it cannot promote its own claims.

## The question

`Ξ(t) = ξ(1/2 + it)` is the cosine transform of a function `Φ` that is
documented positive on the real axis (`zeta/heatflow.Phi`, verified in
`zeta/heatflow.py` and pinned by `tests/test_heatflow.py`). Pólya's classical
theorem family says a positivity condition on the Fourier-side function can
force the transform's zeros to be real, and RH is exactly the statement that
`Ξ` has only real zeros.

> **Question.** Does the positivity of `Φ` buy anything, and what is the exact
> criterion that converts Fourier-side positivity into real zeros?

The naive form of the folklore criterion is false and this hunt says so with a
computed witness: `φ(t) = e^{-t^4}` is positive and even with a convex
exponent, and `F(z) = ∫ φ(t) e^{izt} dt` has complex zeros (argument-principle
count, this hunt's `journal.md`). So convexity of the exponent is not
sufficient, and any real criterion is strictly sharper. Finding the sharp
criterion and testing whether `Φ` meets it is the work.

## The concrete plan

1. **The exact moment table.** `b_n = ∫_0^∞ Φ(u) u^{2n} du`. Nobody in this
   tree has this table; `zeta/li.py` has `γ(n)` (a different normalisation of
   the same data), and the exact conversion between them is derived and
   checked here rather than quoted.
2. **The Newton / higher-Turán battery.** For a function with only real zeros,
   the normalised coefficient sequence satisfies the Newton inequalities at
   every order. Each order is a necessary condition for RH and each is
   separately checkable. The first violation at any order refutes RH; an
   all-pass table for the orders computed is *not* evidence for RH
   (`docs/08` section 3, Littlewood).
3. **The Gate-3 rival check.** Anything proposed is run against
   `W_a = ζ(s+a)ζ(s-a)` and Davenport-Heilbronn, per `zeta.epstein.battery`
   and the `hunts/epp_herglotz` finding that the standing rivals are all
   linear combinations of genuine Euler products.

## Compute discipline

Heavy work runs on Modal, never on the operator's machines, per `AGENTS.md`
"Compute discipline". One unit is measured and multiplied before any sweep.
Budget and per-run notes in `RUNS.md`.

## Dead routes carried in

- **`hunts/epp_herglotz`**: "Euler-product positivity plus the functional
  equation implies RH" is refuted by `W_a`. Any candidate here must survive
  that rival.
- **`hunts/local_positivity`**: place-local norm identities do not globalise;
  `Q_p - ||f||^2` has mixed sign (52/60 positive).
- **`docs/35`**: the out-of-band positivity information is worth about
  `+0.0068` in the configuration class but the certificate machinery cannot
  reach it, for a stated structural reason.
- **`hunts/family_wall`**: the n-point pressure family has a configuration
  ceiling it cannot reach.

```huntspec
id: gauss_positivity
question: Does Fourier-side positivity of Phi, via the sharp Pólya-type criterion, force the zeros of Xi to be real?
frontier: The folklore convexity criterion is false by an explicit computed witness; the sharp criterion and the moment table b_n = int Phi u^{2n} are not established in this tree.
proposed_attack: Build the exact moment table on Modal, test the full Newton/higher-Turan inequality family at each order, and check every candidate criterion against the W_a and Davenport-Heilbronn rivals.
dead_routes:
  - Convexity of the Fourier-side exponent is not sufficient; e^{-t^4} has a convex exponent and its transform has complex zeros, computed by argument principle in this hunt.
  - Euler-product positivity plus the functional equation, refuted by W_a = zeta(s+a)zeta(s-a) in hunts/epp_herglotz.
  - Place-local norm identities do not assemble into a global one, measured in hunts/local_positivity.
required_oracles:
  - mpmath quadrature at two independent precisions and two independent panel families
  - the committed zeta/li.py gamma(n) table, computed by two independent routes already pinned in tests/test_li.py
  - exact integer arithmetic for the Newton identities on rationalised coefficients
  - zeta.epstein.battery for the rival gate
kill_conditions:
  - the moment table disagrees between the two independent quadrature routes beyond the stated error budget
  - a Newton inequality fails, which would refute RH and requires independent confirmation before being reported as such
  - the derived exact relation between b_n and gamma(n) fails to hold numerically
  - a candidate criterion is satisfied by W_a or Davenport-Heilbronn
agents_may:
  - compute
  - derive
  - code
  - attack
  - formalize
agents_may_not:
  - declare novelty
  - declare theorem status
  - promote their own claim
  - run heavy work on the operator's machines
```
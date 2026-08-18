# Hunt R-FB9C81 / urms2-0.51

claim 'urms2-0.51' has no recorded blind attack: the review is not standing until one runs

```huntspec
id: r_fb9c81
question: Does a blind attack find a structural or analytic failure in the URMS2 0.51 bandwidth claim, without access to the author's reasoning?
frontier: the claim asserts the URMS2 bandwidth extends past the half band to 0.51, resting on the stated assumption that the true logarithmic frequency separation is preserved rather than collapsed into a cutoff estimate; no blind attack had been recorded against it, so the review was not standing
proposed_attack: ask what modification of the world would preserve the appearance of the result while making its interpretation false — specifically whether perturbing the polynomial frequency spacing or the coefficient bounds can keep the mean-value integral looking sound while falsifying it — then probe the Montgomery-Vaughan off-diagonal bound numerically
dead_routes:
  - reading the author's derivation before attacking; that makes the review white-box and a separate exercise, and this one is blind by construction
  - arguing from the shape of the assumption alone; the blockpos-0.672529 kill shows an assumption can read as sound and still fail on an exact witness, so the attack must compute
  - treating a bounded off-diagonal error as sufficient on its own; it must be compared against the main diagonal term, since domination is the property in question
required_oracles:
  - the Montgomery-Vaughan mean-value theorem as stated in the primary literature
  - exact evaluation of the polynomial spacing cost sum n |c_n|^2 by direct computation, not by quoting the asymptotic
  - the main diagonal term U log x, recomputed in the same probe rather than carried in from the claim
kill_conditions:
  - the off-diagonal error diverges, or is not strictly dominated by the main diagonal term, at any admissible alpha and delta
  - the spacing cost exceeds its O(x log x) bound once the upper polynomial length W is allowed to exceed the integration block U
  - the probe cannot reproduce the claim's own regime, in which case the attack has not reached the claim and reports that instead of a verdict
agents_may:
  - search
  - derive
  - code
  - attack
agents_may_not:
  - declare novelty
  - declare theorem status
  - promote their own claim
  - read the author's derivation before the probe has run
```

# CORE_CANDIDATE: a P-local rival for `zeta.epstein.battery`

Hunt #149, step 6 of `MISSION.md`. **A proposal, not an edit.** Nothing in `zeta/` is
changed by this hunt; the operator decides whether the battery takes this rival. The
prototype lives in `rivals.py` (`plocal_interface`, `claim_unitary_euler_factor_at_2`,
`battery_with_plocal`) and runs `zeta.epstein.battery` unchanged. Every claim below is
pinned by `test_rivals.py`.

## The gap it closes

Every rival in the battery departs from an Euler product at the first prime or two:
Davenport-Heilbronn has b(2) = kappa, the discriminant -23 Epstein forms have b(2) = 0 or
a(1) = 0, and the shifted product has b(2) = 2^{1/4} + 2^{-1/4}. So a claim whose content
is "the function has a genuine Euler factor at the small primes" fails for every rival and
passes for zeta, and the battery reports that it **distinguishes**. That is a false
positive: F_17 = eps^{-1/2} L(s, chi) + eps^{1/2} L(s, chi-bar) (chi of order 4 mod 17)
has the exact Euler factor of L(s, chi) at p = 2 (and at every quadratic-residue prime),
a self-dual functional equation, real coefficients, and zeros off the critical line
starting at height 25.69 (`ZEROS.md`).

Pinned demonstration, with the claim "b(2^j) = b(2)^j for j <= 6 and |b(2)| = 1":

| | zeta | DH | Epstein (2,1,3) | Epstein (1,1,6) | W_{1/4} | F_17 | verdict |
|---|---|---|---|---|---|---|---|
| battery as it stands | pass | fail | fail | fail | fail | | **distinguishes** |
| with the P-local rival | pass | fail | fail | fail | fail | pass | shared with plocal_17 |

## The proposed entry

`plocal_interface(q, dps)` with `zeta_interface`'s field contract (all seven fields, pinned):

- `coefficient(n)`: b(n) = Re chi(n) + k Im chi(n), periodic mod q, k from the linear solve
  of the functional-equation defect (the same pattern as `kappa`, re-derived on every call,
  cross-checked by the Gauss sum and by PARI's root number);
- `completed(s)`: (q/pi)^{s/2} Gamma(s/2) F(s), via q - 1 Hurwitz values;
- `fe_defect(s)`, `Z(t)`, `zeros_on_line(t0, t1)`: as for Davenport-Heilbronn;
- `count_zeros_box(s0, s1)`: `zeta.epstein.count_zeros_box` with `fn = completed`, which
  already sees the zero at height 25.69 in the box [0.6, 0.75] x [25.5, 26].

Recommended default q = 17: 16 Hurwitz values per evaluation, P = 2, first off-line zero
lower than Davenport-Heilbronn's (25.69 against 85.70), so box-local claims can be tested
at low height. q = 73 (P = 4) is the deeper member and costs 72 Hurwitz values.

## Scope caveat, to ship with it (as `SHIFTED_PRODUCT_SHIFT` ships with its own)

- F_q has conductor q, not 1. By Hamburger's theorem nothing with zeta's own conductor and
  Gamma factor can play this role (`OBSTRUCTION.md` section 3). A claim it shares is shown
  to be blind to the non-residue primes, not to be irrelevant to RH.
- It agrees with L(s, chi) only where the information class of `OBSTRUCTION.md` looks:
  local data at residue primes and windows with c <= n(q). It fails multiplicativity
  (at the coprime pair (3, 7) for q = 17) and Euler-product positivity (Lambda_F(2) =
  -log 2), so it adds nothing for claims the existing rivals already refute.
- It is self-dual while L(s, chi) is not; a claim that reads the root number or the dual
  separates the two at once.

## What landing it would take

A `plocal_interface` in `zeta/epstein.py` mirroring `dh_interface` (about 60 lines on the
prototype), its registration in `battery` behind a keyword the way `shift` is, the
linear-solve and FE-defect tests of `test_rivals.py` moved to `tests/test_epstein.py`, and
the operator's decision. The census of `ZEROS.md` is not needed for the entry; one pinned
off-line zero (the one at 25.69) is.

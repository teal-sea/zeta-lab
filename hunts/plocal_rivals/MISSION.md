# MISSION: `plocal_rivals`, rivals that agree with an Euler product at every prime up to P

**Opened 2026-10-21. Hunt #149.** One lane of the campaign the owner directed on
2026-10-21 (route 6, the P-local rivals half). Nothing in this directory is a result
until the case log in `hunts/README.md` says how it ended.

Grades used here: *measured* (one float route), *hardened* (independent routes agree,
or ball enclosures carry every step), *kernel-checked* (not used here: there is no Lean
in this hunt). The reserved enclosure word belongs to `zeta/rigor.py` and the Lean arm
and appears nowhere in this directory, including in the names of `rigor.py`'s routines.

## The question

> Can the battery be given rivals that agree with a genuine Euler product at every
> prime up to P, share its conductor and Gamma factor, carry a self-dual functional
> equation, and still have zeros off the critical line? And what exactly does such a
> rival prove about criteria that read only small-prime and short-window data?

## Why

Every rival in `zeta.epstein.battery` disagrees with an Euler product at the very first
primes: Davenport-Heilbronn already at p = 2 (its normalised coefficient there is
kappa, not a unitary local root), the discriminant -23 Epstein forms at n = 2 or 6,
and the shifted product W_a in its normalisation. So a criterion that reads only the
local factors at the first few primes, or only a short window of the explicit formula,
is never tested by the battery at all. `hunts/weil_propagation/theory/RESULTS.md`
section 7.2 records the same gap for its candidate C4: no rival satisfying its
hypotheses exists in the tree.

## The construction

Take a prime q = 1 (mod 4), a primitive character chi mod q of order 4, and its root
number eps = e^{i theta}. Put

    F_chi(s) = eps^{-1/2} L(s, chi) + eps^{1/2} L(s, chi-bar).

Its coefficients 2 Re(eps^{-1/2} chi(n)) are real and it inherits a completed
self-dual functional equation from the one relating L(s, chi) and L(s, chi-bar). The
Davenport-Heilbronn function is the case q = 5. If every prime p <= P is a square
mod q, then chi(p) = +-1 for those p, the coefficients are 2 cos(theta/2) chi(n) on
P-smooth n, and the Dirichlet coefficients of -F'/F are Lambda(n) chi(n) there.

Cases: q = 17 with P = 2, and q = 73 with P = 4 (2 and 3 are squares mod 73, 5 is not).
q = 5 is the calibration case: it must reproduce `zeta.epstein`'s kappa.

## Steps

1. Derive the combination by a linear solve from the functional equation, as
   `zeta/epstein.py` derives kappa. Check cos(theta/2) != 0 and measure the
   functional-equation defect at dps 40.
2. Check the P-smooth identities exactly for n <= 10^4.
3. Assemble the band-N window forms of F_chi and of L(s, chi) at c <= P + 1 with
   `hunts/rogue_frontier/weil_trunc/galerkin.py`; show they agree, and that they
   differ once c passes the first non-square prime.
4. Locate the zeros with Re s > 1/2 up to height 1000 by two code-disjoint routes
   (the decision rule of `hunts/lambda_dh_bounds/winding.py` on Arb balls, and an
   independent mpmath argument principle), at most 4 worker processes; bound
   sup Re rho by the Euler-phase abscissa method of `hunts/lambda_dh_bounds/`.
5. `OBSTRUCTION.md`: the restricted-class statement and its scope.
6. `CORE_CANDIDATE.md`: a proposed battery entry, with no edit to `zeta/`.

## Scope

- **In scope.** New files under `hunts/plocal_rivals/`, this hunt's case-log entry in
  `hunts/README.md`, and an entry in `docs/37-methods.md` if a method survives.
- **Out of scope.** Any edit to `zeta/`, `ontology/` or `harness/`; any claim about RH
  or about zeta's zeros; any claim beyond the stated heights; Lean.
- **Compute.** The swarm box, shared. Under `CLAUDE.md` compute rule 6 as ruled for the
  box: `MemAvailable` above 20 GiB, at most 4 worker processes for the census, no heavy
  start while the 1-minute load average is above 64. `RUNS.md` carries the estimate
  before any run longer than about 20 minutes, and the census checkpoints per window.

```huntspec
id: plocal_rivals
question: Do the self-dual combinations F_chi = eps^(-1/2) L(s, chi) + eps^(1/2) L(s, chi-bar) of order-4 characters mod q = 17 and q = 73 agree with L(s, chi) in every local factor at primes up to P and in every window form with c <= P + 1 while having zeros off the critical line below height 1000, and what does that prove about criteria reading only that data?
frontier: every battery rival in zeta.epstein disagrees with an Euler product at p = 2 or at n <= 6; hunts/weil_propagation/theory section 7.2 records that no rival satisfying the C4 hypotheses exists in the tree; Davenport-Heilbronn (q = 5, P = 1) has its first off-line zero at height 85.699 and a phase abscissa 1.12036249819 (hunts/lambda_dh_bounds STRIP2.md)
proposed_attack: derive the self-dual combination by a linear solve, check the P-smooth coefficient identities in exact arithmetic, compare the galerkin.py window forms of F_chi and L(s, chi), and census the off-line zeros below height 1000 on two code-disjoint routes
dead_routes:
  - reading an off-line zero from a residue or a window-form sign alone, without a completeness check of the line zeros (hunts/README.md, the Hunt 2 confound)
required_oracles:
  - exact integer and rational arithmetic for the character table, the Jacobi sum and the P-smooth identities
  - Arb ball enclosures from python-flint for the decided winding counts and the phase abscissa
  - mpmath at stated precision as the second, code-disjoint zero route
  - PARI/GP lfun as a third evaluation route for one off-line zero and for the functional equation
kill_conditions:
  - the linear solve gives a k that is not real, or its functional-equation defect does not fall with precision
  - the Gauss-sum root number disagrees with the linear solve
  - some P-smooth n <= 10^4 violates the coefficient identity in exact arithmetic
  - the window forms of F_chi and L(s, chi) differ beyond rounding at some c <= P + 1, or fail to differ past the first non-square prime
  - the two zero routes disagree on any count or location below height 1000
  - no zero with Re s > 1/2 is found below height 1000 for either q, in which case the rival is reported as untested at that height
agents_may:
  - read
  - derive
  - code
  - compute within the box rules
  - attack the construction
agents_may_not:
  - declare novelty
  - declare theorem status for anything not kernel-checked
  - edit zeta, ontology or harness
  - promote their own claim
  - push, publish or contact outside parties
```

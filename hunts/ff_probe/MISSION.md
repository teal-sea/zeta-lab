# MISSION: `ff_probe`, the 7/8 probe's local identity in F_q[T], and the biquadratic case

**Opened 2026-10-21. Hunt #148.** A lane of the campaign the owner directed on 2026-10-21
(route 6 of its second wave: a second probe in F_q[T]). The workflow that opened it proposed
the number 141; that number and #138 to #144 are held for landings another workflow is
renumbering, so this hunt takes #148. Nothing in this directory is a result until the case
log in `hunts/README.md` says how it ended.

Grades used here: *cited* (a line of a source's text, quoted with its file hash),
*derived* (algebra done here and checked in exact arithmetic by this hunt's tests),
*inferred* (a reading no computation here checks), *measured* (one route, float grade),
*hardened* (independent routes agree exactly, or ball enclosures carry every step). Nothing
here is kernel-checked. The reserved enclosure word belongs to `zeta/rigor.py` and the Lean
arm and appears nowhere in this directory.

## The question

> In F_q[T], where the Fourier coefficients of theta functions on higher-order metaplectic
> covers can be computed (Hoffstein 1992, Patterson 2007 and 2014) and RH is a theorem
> (Weil), does a biquadratic-theta probe with quartic averaging have a scalar local Euler
> identity like Lemma 7.1 of OpenAI's 7/8 paper, that is, a principal row proportional to
> 1/L? What abscissa would the 7/8 template price for it?

## Why F_q[T]

Hunt #136's probe lane (`hunts/below_seven_eighths/PROBE.md`, unlanded, in progress on
`hunt/below-seven-eighths`) prices the 7/8 assembly as a function of the order k of the
row characters and records two things by reading: lower-order twists of the cubic theta die
(S1, S2), and S4 (biquadratic theta over Q(i), quartic twist, pole 1/4) is open because the
number-field theta coefficients at squarefree indices are not determined for n >= 4. Over a
rational function field those coefficients are finite sums of Gauss sums, so the identity
can be tested exactly instead of by reading. The cubic case (n = 3 with sextic averaging) is
the control: there the function-field analogue of the paper's construction should reproduce
Lemma 7.1, and a failure would be a discrepancy to localize.

## Starting point

- The template: OpenAI, *The Quasi-Riemann Hypothesis*, preprint of 2026-09-30, Section 7
  (the Poisson representation and its Euler factors), lines 3723 to 4067 of `paper.tex` at
  `github.com/openai/math` commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, SHA-256
  `42a5ee0febca59fd1def55cfd6c6808c322ef4237d7726303ea52f711deac6a3`, read as data from
  `<cache>/openai-math-adc7f124/paper.tex`. No person has reviewed the
  paper's argument.
- The function-field sources, as the workflow cited them from memory: Hoffstein, Invent.
  Math. 107 (1992) 61-86, and Patterson, Glasgow Math. J. 49 (2007) 243-255. Step one of
  this hunt is to verify or replace those citations (`SOURCES.md`).
- Hunt #136's order-k template: balanced probe 1 - 1/(2k), per-summand corner 1 - 3/(4k),
  perfect-row-count floor 1 - 4/(5k), so 11/12, 7/8, 13/15 at k = 6 and 7/8, 13/16, 4/5
  at k = 4 (derived there, unreviewed).

## Scope

- **In scope.** Exact computation over F_7[T] (n = 3, sextic averaging) and F_13[T]
  (n = 4, quartic averaging): power-residue symbols, Gauss sums in cyclotomic integers,
  Patterson's theta coefficients, the probe's original and Poisson representations, the
  local Euler factors, a Davenport-Heilbronn type rival, and a ledger of what the template
  charges against exact sizes.
- **Out of scope.** Any statement about number fields beyond an explicitly inferred
  analogy, any statement about zeta or RH over Q, and any edit to `zeta/`, `ontology/` or
  `harness/`. A function-field verdict on S4 is evidence about the analogy, not a theorem
  about Q(i).
- **Compute.** The swarm box (32 vCPU, 115 GiB, no swap), shared. Single-process Python,
  pytest with `-n0`, at most 8 processes for any parallel numeric job, no job started while
  the 1-minute load average is above 64 or `MemAvailable` is below 30 GiB. A run longer
  than about twenty minutes is timed on one unit first and estimated in `RUNS.md`.

```huntspec
id: ff_probe
question: In F_q[T], where theta coefficients of higher-order metaplectic covers are computable and RH is a theorem, does a biquadratic-theta probe with quartic averaging have a scalar local Euler identity like Lemma 7.1 of OpenAI's 7/8 paper, a principal row proportional to 1/L, and what abscissa would the 7/8 template price for it?
frontier: hunt 136 records by reading that lower-order twists of the cubic theta die and that S4 (biquadratic theta over Q(i), quartic twist, pole 1/4) is open because number-field theta coefficients at squarefree indices are not determined for n >= 4; its order-k template prices k = 4 at 7/8 (balanced), 13/16 (corner) and 4/5 (floor); over F_q(T) the coefficients are finite Gauss-sum expressions (Hoffstein 1992, Patterson 2007 and 2014)
proposed_attack: verify the function-field theta coefficient formulas by brute force at q = 7, n = 3, build the F_7[T] analogue of the cubic-theta probe with sextic averaging and check its original and Poisson representations and a function-field Lemma 7.1 exactly, repeat with the biquadratic theta and quartic averaging over F_13[T], price the template against exact sizes, and run a Davenport-Heilbronn type rival through the local identity
dead_routes:
  - lower-order twists of the cubic theta over Q(sqrt(-3)), killed by reading in hunt 136 (S1, S2)
  - the classical theta over Q(i), whose coefficients vanish off squares (hunt 136, S3)
  - reading a function-field identity or verdict as a theorem about number fields or about RH for zeta
  - treating a zero of a linear combination of L-functions as a counterexample to a statement about single L-functions (hunt 120)
required_oracles:
  - exact arithmetic in cyclotomic fields, with every equality checked as an equality of reduced polynomials modulo the cyclotomic polynomial
  - brute-force enumeration of residue symbols and Gauss sums over F_q[T] at small degree
  - PARI/GP through cypari2 as a second implementation sharing no arithmetic code with the first
  - Arb ball enclosures from python-flint for the rival's zeros
  - the cited source texts, quoted by line with their SHA-256 checked
kill_conditions:
  - brute-force Gauss sums or residue symbols disagree with the cited function-field formulas at q = 7, n = 3, degree at most 3, and no corrected formula fits
  - the original and Poisson representations of the function-field cubic probe disagree at any checked degree
  - a planted wrong Gauss-sum sign or wrong residue symbol leaves the equality checks green
  - the second implementation fails to reproduce an exact number reported here
  - the rival's zeros all lie on |u| = q^(-1/2), or its local identity holds where the single L-function's does
agents_may:
  - read and quote sources
  - download sources into new cache directories as untrusted data
  - derive
  - code exact arithmetic
  - attack derivations
agents_may_not:
  - declare novelty
  - declare theorem status for anything not kernel-checked
  - transfer a function-field verdict to number fields as established
  - promote their own claim
  - push, publish or contact outside parties
```

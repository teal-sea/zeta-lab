# The sharp window constant for zeros of xi'

**Status: measured, and independently reproduced three ways. Not a new analytic
theorem, an optimisation, run to its exact answer, of a functional somebody
else derived. Nothing here is evidence for or against RH.**

The full-space variational step, including coercivity, inverse existence,
optimizer positivity, and the endpoint `lambda = 1`, is supplied in
[`RESULTS-xiprime-global-optimality.md`](RESULTS-xiprime-global-optimality.md).

## The question, and who left it open

The August 2026 paper *More than two thirds of the zeros of the Riemann zeta
function lie on the critical line* restricts Weil's Hermitian form to a finite
Gabor family and reads an unconditional lower bound for the proportion of zeros
that are simple and on the critical line off the first two moments of the
resulting matrix.

For zeta itself the paper **solves** the window-optimisation problem (its
Theorem D): the Euler-Lagrange equation is `v'' + 2 lambda^2 v = 0`, the
maximiser is Montgomery-Taylor's `cos(sqrt(2) s)`, and the constant is
`0.6725008...`. It states that no window does better.

Its **Remark 7.3** applies the same machinery to `xi'`, the derivative of the
completed zeta function, and reports two numbers:

| window | simple & on-line | distinct |
|---|---|---|
| flat, `v = 1` | 0.85838 | 0.92919 |
| quartic `v(s) = 1 - (7/100)(2s)^2 - (51/200)(2s)^4` | 0.86864 | 0.93432 |

The quartic is an unexplained ansatz; **the variational problem is not solved
there**. And the paper records the comparison it cannot settle: Wu [Wu15, §3]
has **0.86957** unconditionally for zeros of `xi'` merely on the critical line
(without simplicity), "which neither our 0.85838 nor our 0.86864 exceeds".

So: does some admissible window close that 9e-4 gap?

## The answer

**No, and by a definite margin.** The supremum over all admissible windows is

    H*  = 0.8686415005297670641100164...        (simple and on the critical line)
    Hd* = 0.9343207502648835320550082...        (distinct)
    c*  = 0.8838931253605797508122324...
    1/c*= 1.131358499470232935889984...

attained at `lambda = 1` by `v* = (I + T_{F_1})^{-1} 1`, which is strictly
positive (`v*(+-1/2)/v*(0) = 0.671042`), so the constraint `v >= 0` is inactive.

Two consequences:

1. **The paper's quartic was already essentially sharp.** It sits
   `1.5005e-6` below the true optimum. Nothing of substance was left on
   the table, which is worth recording precisely because it looked like an
   ad hoc choice.
2. **The method cannot reach Wu's constant.** `H* - 0.86957 = -9.2850e-4`.
   No admissible window closes the gap, so within this method the new content
   for `xi'` remains the *simplicity*, exactly as the paper says. The open
   comparison is settled, negatively.

The remaining distance to Chirre-Goncalves-de Laat's RH-conditional 0.8825 is
attributable to their optimising over a larger cone: they use `F_1 >= 0`
*outside* `[-1,1]`, information the Gabor construction at bandwidth `<= 1` does
not have.

## Where this sits against the literature

| quantity | constant | conditional? | source |
|---|---|---|---|
| `xi'` simple and on the line | 0.7869 | unconditional | Conrey 1983-II, Cor. 1 |
| `xi'` simple and on the line | **0.8686415005** | unconditional | this note (sharp for the method) |
| `xi'` on the line, no simplicity | 0.86957 | unconditional | Wu 2015, §3 (arXiv:1206.3737) |
| `xi'` simple | 0.8584 | RH | Farmer-Gonek-Lee, Cor. 1.3 |
| `xi'` simple | 0.8825 | RH | Chirre-Goncalves-de Laat, Cor. 7 |

Conrey 1983-II also gives the higher derivatives: `beta_2 > 0.9314`,
`beta_3 > 0.9666`, `beta_4 > 0.9799`, `beta_5 > 0.9863`, and `beta_0 > 0.3485`
for zeta itself.

**A citation caveat, recorded because it changes the comparison.** The paper
and Farmer-Gonek-Lee both attribute "79.874%" to Conrey, *Zeros of derivatives
of Riemann's xi-function on the critical line*, J. reine angew. Math. **399**
(1989). On inspection that paper's stated results are about zeta
(`kappa >= 0.4077`, `kappa* >= 0.401`), and the 79.874% figure was not located
in it; pages 13-21 (Kloosterman-sum lemmas) were not read, so this is not
conclusive. The published unconditional constant that *was* located is
Conrey 1983-II's `beta_1 > 0.7869`, and 79.874% is the natural `theta = 4/7`
mollifier upgrade of it. The table above uses the located value. Either way the
comparison is unaffected: 0.8686415 exceeds both.

**Wu's 0.86957, read at the primary source rather than through Remark 7.3.**
The row above was originally taken from the paper's own citation. It has since
been checked against Wu's text (X. Wu, *Distinct zeros of the Riemann
zeta-function*, Q. J. Math. **66** (2015) 759-771; arXiv:1206.3737), because a
constant that travels between papers is exactly where a quantity gets swapped
for a neighbouring one. What that paper says:

- §3 is titled *"zeros of ξ′(s) on the critical line (1/2-line)"*.
- `N_{xi',c}(T)` is defined in §1 as "the number of zeros of `xi'(1/2 + it)`
  with `0 < t < T`", on the line, with **no** simplicity condition and **no**
  distinctness condition.
- §3 ends at `N_{xi',c}(T) >= 0.86957 N(T)`, from `theta = 4/7 - eps`,
  `R = 1.104`, `delta = 0.869` and a named `(P, Q)` pair.
- Its closing sentence is the one this note relies on for the novelty
  argument, verbatim: "one may find that this way is useless when consider
  simple zeros of `xi^(n)(s)`, `n >= 1` on the critical line."

So the classification in the table, `xi'`, on the line, no simplicity, is the
paper's own, and the comparison in §"The answer" is between two constants
counting the same zeros of the same function.

Two things worth recording alongside it, because they are the ways this
constant is misread. First, the **66.036%** in that paper's title and abstract
is a statement about *distinct zeros of zeta*, not about `xi'`; 0.86957 is an
input to it (§4: `N_d(T) >= (1/2 + 0.434785 - 0.27442) N(T) > 0.66036 N(T)`).
A reader meeting 0.86957 by way of the title will take it for a distinctness
proportion, and the two sit on opposite sides of that derivation. Second, if it
*were* the distinctness constant the comparator would be `Hd* = 0.9343207`, not
`H* = 0.8686415`, and the negative result of §"The answer" would invert, so
this is not a bookkeeping detail, and it is why the row is now sourced.

Wu's §3 also reports the prior unconditional `xi'` on-line constants as
Levinson 71%, Conrey 81.37%, and 82.402% with the `theta = 4/7` mollifier.
Those count zeros merely on the line, so they do not settle the caveat above,
which is about a *simple*-and-on-line attribution; they are recorded here as
the nearest located data for whoever takes that caveat further.

## Novelty

The *unconditional* window optimisation for `xi'` appears to be unpublished, on
a literature search that read the primary sources rather than their abstracts.
Farmer-Gonek-Lee use what is effectively the flat window (their Cor. 1.3,
85.84%, matches the flat-window value 0.858384 to four decimals). Wu's route is
Levinson-Conrey mollification and he states explicitly that it cannot handle
simple zeros of `xi^(n)`. Chirre-Goncalves-de Laat *do* optimise, by
semidefinite programming over a Cohn-Elkies class, but RH-conditionally and
over a strictly larger cone. No analogue of the Carneiro-Chandee-Littmann-
Milinovich one-delta extremal solution exists for the `F_1` kernel. No academic
response to the paper of 10 August 2026 was found.

Confidence that the unconditional optimum is unpublished: about 0.85. What
would overturn it: a paper phrasing the object as `xi^(n)`, `Xi'` or `Z'`; the
published JLMS version of Farmer-Gonek-Lee containing an optimisation absent
from the 2008 preprint; or a 2026 preprint not yet indexed.

Incidentally, the price of removing RH is about the same on both sides: for
zeta, unconditional `1/c* = 1.327499` against CGdL's RH-conditional `1.3208`;
for `xi'`, `1.131358` against their `1.1175`.

## The functional

Writing `v >= 0` even on `[-1/2,1/2]`, the proportion is `H = 2 - 1/c`,
`Hd = (1+H)/2`, with

    1/c_lambda(v) = [ int v^2 + lambda * iint F_1(lambda (s-s')) v(s) v(s') ]
                    / ( lambda (int v)^2 )

    F_1(x) = |x| - 4 x^2 + sum_{k>=1} ((k-1)!/(2k)!) (2|x|)^{2k+1}
           = |x| - 4 x^2 + 2|x| int_0^1 (exp(4 x^2 t(1-t)) - 1) dt/t

`F_1` is Farmer-Gonek's pair-correlation form factor for the zeros of `xi'`,
minus its Dirac spike (the spike is what produces the `int v^2` term). Setting
`F_1(x) = |x|` recovers Montgomery's kernel and the paper's (7.3) for zeta
exactly. Sources: D. W. Farmer and S. M. Gonek, *Pair correlation of the zeros
of the derivative of the Riemann xi-function*, arXiv:0803.0425, Theorem 1.1
(with Y. Lee, JLMS 90 (2014) 241-269); restated above Lemma 11 of
Chirre-Goncalves-de Laat, arXiv:1810.08843, Adv. Math. 361 (2020).

## How it was checked

The standing checklist of `hunts/README.md`, answered.

**Control (the instrument reproduces a known answer).** With `F(x) = |x|` the
same code returns the paper's Theorem D: `c* = 0.7532960679` against the
paper's `0.7532960`, `1/c* = 1.3274992963` against `1.3274992`,
`H = 0.6725007037` against `0.6725008`, `Hd = 0.8362504` against `0.83625`, and
the maximiser matches `cos(sqrt(2) s)` to `4.3e-7`. The flat window reproduces
`F(lambda) = lambda/(1+lambda^2/3)` at three separate `lambda`. A battery
calibrated only in one direction would be worthless here, so the instrument is
pinned against a *known* answer before being pointed at an unknown one.

**Two-point check against Remark 7.3.** The functional must reproduce the
paper's own two rows, and does, to every digit the paper prints:

| window | computed H | paper | computed Hd | paper |
|---|---|---|---|---|
| flat | 0.858384055 | 0.85838 | 0.929192027 | 0.92919 |
| quartic | 0.868640515 | 0.86864 | 0.934320258 | 0.93432 |

**Five independent computations of the optimum agree.** Exact-rational basis
with closed-form `F_1` moments at 50 digits: `0.8686415005297670641`;
double-precision spectral Galerkin: `0.868641500530`; an even-Legendre Galerkin
run stable to 13 digits across basis sizes 6-26: `0.86864150052977`; an
independent Nystrom run: `0.8686416` (converging `0.8686489, 0.8686434,
0.8686420, 0.8686416`); and a further Nystrom/Galerkin pair: `0.868641534`.
The first three agree to **14 digits**. The last is the least converged and is
recorded as an outlier at the 8th digit, not averaged in.

**The kernel locates the paper's own quartic.** This is the sharpest check,
because it uses information no fit can see. Three *fitted* two-parameter
kernels also reproduce both of the paper's data points to machine precision, so
hitting them establishes nothing on its own. But the paper's quartic coefficients
`(-7/100, -51/200) = (-0.070, -0.255)` look like a rounded numerical optimum
inside the family `1 + b(2s)^2 + c(2s)^4`. Maximising over that family with the
*derived* kernel puts the argmax at `(-0.071596, -0.256074)`, a distance of
`0.0019`; the nearest fitted rival is `0.100` away, fifty times worse. The
derived kernel reconstructs a choice the paper never explains.

**The coefficients are checked exactly, not asymptotically.** For squarefree
`n = p_1...p_k` the derivation gives
`c(p_1...p_k) = -(k-1)! 2^k l (prod u_i)(sum u_i)`, `u_i = log p_i / l`; direct
Dirichlet convolution of `B'/(1-B)` up to `n = 2e5` for `k = 1,2,3,4` checks
1260 squarefree `n` with zero mismatches. An end-to-end run against real primes
at `N = 4e6` reproduces the predicted mean-square density, the ratio rising
`0.851 -> 0.943` toward 1 as `y -> l` (an `O(1/l)` secondary term converging the
right way); the zeta density `y^2/2` is wrong there by factors, not percents.

**Three independent derivations of the functional agree.** One from the
literature (Farmer-Gonek's Theorem 1.1, read directly); one from scratch by
direct computation of the Dirichlet coefficients of `-xi''/xi'`, summing the
geometric series exactly through the identity
`(Lambda.log) * Lambda^{*k}(n) = log n * Lambda^{*(k+1)}(n)/(k+1)` and carrying
zero free parameters; and one numerical implementation written against the
paper alone. The second route's kernel `W_lambda(u) = 1 - 4 lambda u +
Psi(2 lambda u)` satisfies `F_1(x) = x K(2x)` identically, i.e. the two closed
forms are the same function. A naive truncation of that series gives
`(1-2u)^2` and the wrong answer `0.9333`; the dropped tail sums to exactly the
discrepancy, `0.074949`.

**Precision response.** The optimum is stable to `8e-15` across four
independent refinements of the basis size and quadrature order, and the
high-precision run (exact rational polynomial basis, closed-form `F_1` moments,
mpmath at 50 digits) agrees with the double-precision spectral run to `1e-14`.
An artifact does not respond to added precision this way; the constant is real
to the digits quoted.

**`lambda = 1` is optimal.** After scaling to the interval
`[-lambda/2,lambda/2]`, extension by zero shows that the optimized quotient is
nondecreasing on `(0,1]`; see `RESULTS-xiprime-global-optimality.md`. The
previously measured values at `lambda = 0.5, 0.6, 0.7, 0.8, 0.9, 0.95, 0.99,
1.0` agree with that theorem. `lambda <= 1` is forced: beyond it the prime side
needs information on prime pairs.

## Scope, stated plainly

- This is an **optimisation result, not a new analytic theorem**. The functional
  is the paper's, the form factor is Farmer-Gonek's, and the analytic inputs
  (the unconditional prime side, and §§4-6 of the paper) are taken as given.
  What is new here, if anything, is the exact value of the supremum and the
  negative consequence that follows from it.
- The maximiser has no closed form of the `cos(sqrt(2) s)` kind: `F_1''` is not
  a Dirac mass plus a polynomial, so the Euler-Lagrange equation is a genuine
  integral equation rather than a constant-coefficient ODE.
- Nothing here bears on the Riemann hypothesis in either direction.

## Falsifiable predictions

Recorded so that anyone can refute this without re-deriving it. All at
`lambda = 1` unless stated; `H = 2 - 1/c`, `Hd = (1+H)/2`. Two independent
implementations agree on every row to `1e-10`.

| window `v(s)` on `[-1/2,1/2]` | `1/c` | `H` |
|---|---|---|
| `cos(pi s)` | 1.301169031 | 0.698830969 |
| `1 - (2s)^2` | 1.270318253 | 0.729681747 |
| `cos(sqrt(2) s)` (zeta's maximiser) | 1.132111135 | 0.867888865 |
| `1 - 0.25 (2s)^2` | 1.131978799 | 0.868021201 |
| `(1 - (2s)^2)^2` | 1.486059083 | 0.513940917 |
| the maximiser `v*` | **1.131358499** | **0.868641501** |

The maximiser itself, in the even-monomial basis:

    v*(s) = 1 - 0.078363 (2s)^2 - 0.236013 (2s)^4 - 0.013820 (2s)^6
              - 0.000763 (2s)^8 - ...,      min v* / max v* = 0.6710

The `lambda`-dependence is the sharpest test, because it cannot be reproduced
by anything fitted to the two published `lambda = 1` values. The kernel is
`K_lambda(r) = r W(lambda r)`, not `lambda`-free:

| `lambda` | flat `1/c` | quartic `1/c` | optimal `1/c*` | `H*` |
|---|---|---|---|---|
| 0.75 | 1.3935805 | 1.4034120 | 1.3934478 | 0.6065522 |
| 0.90 | 1.2055231 | 1.2057479 | 1.2029684 | 0.7970316 |
| 1.00 | 1.1416159 | 1.1313595 | 1.1313585 | 0.8686415 |

`dH*/dlambda ~ 0.492` at `lambda = 1`, so crossing Wu's 0.86957 would need
`lambda ~ 1.00177`; `lambda <= 1` is forced, because beyond it the prime side
needs information on prime pairs.

## Reproducing

    cd $REPO
    .venv/bin/python -c "import sys; sys.path.insert(0,'hunts/wide_search'); \
      from xiprime import optimise; o=optimise(kernel='xiprime'); print(o['H'])"

The instrument is `hunts/wide_search/xiprime.py`; the zeta control is the first
thing it runs.

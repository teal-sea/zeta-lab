# Independent check of `MAJOR_ARC_EXPLICIT.md` (commit a795a3f)

2026-09-12, attempt `a-0080`. Scripts written fresh for this review, not
reusing `major_arc_explicit_probe.py`: `major_arc_explicit_independent_check.py`
(item 1) and `major_arc_explicit_section5_check.py` (item 5), both under this
directory, results quoted below.

Summary of verdicts: (1) confirmed, (2) defective, (3) confirmed, (4) confirmed
with one inherited defect from (2), (5) confirmed with one inaccurate closing
sentence. The defect found in (2) does not appear to break the boxed result
(S''), because the threshold `c_0` is taken to be a small absolute constant
well inside the corrected condition; it does break the derivation of the
compatibility hypothesis (H) as written, and the document's own stated
numeric bound `2/9` should read `1/6`.

## (1) Section 2: the explicit formula on an arc, the three integral bounds,
the zero-sum estimate, the choice of T

**Verdict: confirmed.**

*The remainder in (1).* With `T = R^3`, `(1+N|theta|) <= 1+R/r <= 1+R` and
`N/T = N/R^3`, so the bracket `(1+N|theta|)[(N/T)l^2+N^(1/4)l]` is at most
`(1+R)(N/R^3)l^2 + (1+R)N^(1/4)l`, which is `<< N l^2 R^{-2}` for the first
piece (worst case r=1) and negligible for the second, matching the document.
The `O(l^2)` for prime powers of primes dividing `r`: with `r <= R = e^{sigma
sqrt l} < Z`, the number of prime powers `p^k <= N` with `p | r` is at most
`omega(r) * l/log2 <= (sqrt(sigma) sqrt l) * l/log2`, order `l^{3/2}`, each
weighted by 1 in the exponential sum; `O(l^2)` is a valid, non-tight, upper
bound for this, not an error.

*The three bounds on I_rho.* With `phi(t) = gamma log t + 2 pi theta t`,
`phi'(t) = gamma/t + 2 pi theta`, `phi''(t) = -gamma/t^2`: the trivial bound
needs nothing; the first-derivative test needs `phi'` of one sign and bounded
away from 0 on the dyadic block, which the stated condition `|gamma| >= 4 pi
N|theta|` supplies (`2 pi|theta| <= |gamma|/(4N) <= |gamma|/(4t)` for `t<=N`,
so `|phi'(t)| >= (3/4)|gamma|/t`, consistent with the document's weaker but
sufficient `|gamma|/(2t)`); the second-derivative test needs `phi''` bounded
away from 0, which holds unconditionally (`|phi''(t)|=|gamma|/t^2>=|gamma|/
(4U^2)` on `[U,2U]`) and is legitimate on the complementary range `1<=|gamma|
<4 pi N|theta|` where the phase can have a stationary point. Both conditions
and both derivative-test applications are stated correctly.

**Numerical check, written fresh (not `major_arc_explicit_probe.py`).**
`major_arc_explicit_independent_check.py` computes `I_rho(theta)` by
composite 16-point Gauss-Legendre with panel edges spaced uniformly in the
*phase* `phi(t)` (found by Newton's method, since `phi` is monotone for
`gamma,theta>=0`), not uniformly in `t`; a first attempt with panels uniform
in `t` badly aliased the fast oscillation near `t=1` and gave ratios up to
6.5, caught by cross-checking against the closed form `I_rho(0)=(N^rho-1)/
rho` (exact reldiff `~1e-13` after the fix, reported in the script's own
sanity-check block). On the document's own sample (60 zeros of zeta with
`gamma<=163.0` from `mpmath.zetazero`, `N in {1e4,1e6}`, `N theta in {0,1,
10,100}`, 472 integrals after discarding `gamma<1`):

- far range (`|gamma|>=4 pi N|theta|`): largest `|I_rho|/(N^beta/|gamma|)` is
  `1.009918` (at `N=1e4`, `N theta=0`, `gamma=101.318`).
- stationary range (`1<=|gamma|<4 pi N|theta|`): largest `|I_rho|/(N^beta/
  sqrt|gamma|)` is `0.064235` (at `N=1e4`, `N theta=10`, `gamma=65.113`).

These match the document's own section 7 numbers (`1.010` and `0.064`)
closely enough to be the same computation done independently, which confirms
both the sign/normalisation of the bounds and the specific constants quoted.

*The zero-sum estimate (2) and the choice of T.* `N(U,chi) << U log(rU) +
log r` is the standard zero-counting bound for `L(s,chi)` (Davenport,
Multiplicative Number Theory, the analogue of the zeta zero-count with the
`log r` term for small `U`); correctly quoted. Recomputing the two exponents:
`r(H_0+2) <= r*4piR/r + 2r = 4 pi R + 2r <= (4 pi+2) R`, so `log(r(H_0+2)) <=
log R + O(1) = sigma sqrt l + O(1)`, giving the far-zero contribution `N^{beta
_chi(H_0)} <= N exp(-c l/log(r(H_0+2))) = N exp(-(c/sigma) sqrt l (1+o(1)))`,
matching the boxed `c/sigma`. With `T=R^3`, `3rT <= 3 R * R^3 = 3R^4`, so
`log(3rT) <= 4 log R + O(1) = 4 sigma sqrt l + O(1)`, giving `N exp(-c l/
log(3rT)) = N exp(-(c/(4 sigma)) sqrt l (1+o(1)))`, matching the boxed
`c/(4 sigma)`. Both recomputations agree with the document exactly.

## (2) Section 3, lemma (5): the Gauss-sum expansion, the model side H_chi,
the twisted main term, and the passage to (4)

**Verdict: defective.** The step from `H_chi(theta) = ... + O(r E_md(1+R/
r))` to the final bound `"+8R E_md"` in (4) drops a factor of `sqrt r` (up to
`sqrt R` at the extreme).

*Where the error is.* `F(alpha)` and `H(alpha)` are both represented, up to
the exact prime-power term for `F`, as `(1/phi(r)) sum_chi chi(a)
tau(chi-bar) [F_chi(theta) or H_chi(theta)]`; this is an exact identity for
both sides (section 1's remark that both sums vanish for `(b,r)>1` on the `H`
side makes it exact there too, not just an approximation). Subtracting and
bounding termwise with `|tau(chi-bar)| <= sqrt r` (GS) gives, correctly,
`|W(alpha)| <= sqrt r * max_chi |F_chi(theta) - H_chi(theta)| + O(l^2)`. This
inequality applies `sqrt r` to *every* part of `F_chi - H_chi`, including
whatever error is already inside `H_chi`. The document's own derivation of
that error is `H_chi(theta) = delta_chi K_N(theta) - ... + O(r E_md(1+R/r))`,
where the factor `r` comes from summing the (up to `r`, in fact `phi(r)`)
residue classes `b mod r` that make up the character sum `H_chi(theta) =
sum_b chi(b) H_b(theta)`, each class contributing `O(E_md(1+R/r))` after
partial summation against `e(n theta)`. So the error carried inside `F_chi -
H_chi` from the model side is `O(r E_md(1+R/r))`, and multiplying by the
`sqrt r` from the Gauss-sum step (as the inequality above requires) gives

```
sqrt(r) * r * E_md * (1+R/r) = r^{3/2} E_md + r^{1/2} R E_md,
```

which at the extreme `r = R` (both terms increasing in `r` on `[1,R]`) is
`O(R^{3/2} E_md)`, not `O(R E_md)`. The ratio of the correct bound to the
document's stated one is `sqrt(r)`, unbounded as `R -> infinity`, so this is
not a matter of a loose but valid inequality: `R E_md` is too small to be a
valid upper bound for `sqrt(r) * O(r E_md(1+R/r))` at `r` near `R`. By
contrast the `F_chi` side's own error `N Upsilon(r)` *is* correctly carried
with its `sqrt r` in (5) (the term `sqrt r * N * Upsilon(r)`), which shows
the `sqrt r` was applied to one contribution and not the other, rather than
omitted as a matter of principle.

**The corrected statement.** Equation (4) should read `|W(alpha)| <= sqrt r
max_chi |F_chi - delta_chi K_N + ...| + O(R^{3/2} E_md) + O(l^2)`, and (5)'s
boxed bound should carry `R^{3/2} N e^{-sqrt(l)/3}` in place of `R N e^{-sqrt
(l)/3}`.

**Propagation.** Squaring, this term becomes `R^3 N^2 e^{-2 sqrt(l)/3}` in
place of `R^2 N^2 e^{-2 sqrt(l)/3}` in section 4's squared bound, and after
the same `* N l` factor from `int_M(|F|+|H|)^2`, the corresponding exponent
in (6) is `2/3 - 3 sigma` in place of `2/3 - 2 sigma`. At the claimed balance
`sigma = c_0`, requiring this exponent to be at least `c_0` gives `c_0 <=
1/6`, not the document's stated `c_0 <= 2/9` (item 4 below redoes this
arithmetic). Since `1/6 < 2/9`, condition (H) as printed is not sufficient
for the argument as printed; the corrected condition needs the extra clause
`c_0 <= 1/6` (or the whole minimum lowered to it, since `1/6 < 2/9`). This
does not by itself refute the boxed result (S''), since `c_0` is described
as "TT's sufficiently small `c_0`" and is presumably far below `1/6` in any
case; it is a genuine arithmetic error in the paper's own verification of
its hypothesis, not merely a stylistic slip, and the checked value `2/9`
printed in both section 4 and the boxed (H) is wrong as a consequence of the
missing `sqrt r`.

*The rest of (5).* The exceptional-zero matching term `1_{q~|r} sqrt r N
e^{-c_0 sqrt l}` is correctly built from the `F_chi` side alone (the model
carries the same `beta_e` term with the same coefficient, by construction of
`a(n)`, so it cancels inside `W` exactly when `q_e | r` and `chi = chi_{e,r}`,
per section 3's first bullet; this is unaffected by the item above). The
identification of the twisted main term with `I_{beta_e}` (the parenthetical
remark) is correct: for `chi = chi_{e,r}` and `(n,r)=1`, `chi_e(n)=chi_e(b)`
on the class, and the untwisted-with-weight-`n^{beta_e-1}` sum's main term is
exactly `int_1^N t^{beta_e-1} e(t theta) dt = I_{beta_e}(theta)` by (Md) and
partial summation, as claimed.

## (3) Section 3, matching the exceptional zeros with Page at (Q,T)=(R,R^3)

**Verdict: confirmed.** Checked the specific case named in the assignment
and found it does not arise: a character mod `r` "induced by a real
primitive character of conductor not dividing `r`" is a contradiction in
terms (an induced character's inducing primitive character's conductor
divides `r` by definition of induction), so this exact phrase names an empty
case, not a missed one.

Looking for the substance behind the hint instead: does the three-way split
(chi induced by tilde-chi=chi_e; induced by tilde-chi != chi_e; not induced
by tilde-chi at all) miss a character whose TT-exceptional conductor `q_e`
exceeds the arc cutoff `R`? Checked directly: if `q_e > R`, then `q_e` does
not divide any arc modulus `r <= R`, so `1_{q_e|r}=0` on every major arc, on
*both* sides of `W`. On the model side, the exceptional twist in `a(n)` still
exists (it is defined at scale `Z`, not `R`), but section 1's own version of
(Md), `sum_{n<=y,n=b(r)} nu(n) chi_e(n) n^{beta_e-1} = 1_{q_e|r} chi_e(b)
(y^{beta_e}-1)/(beta_e phi(r)) + O(E_md)`, already states the main term is
*zero* (not just uncounted) when `q_e` does not divide `r`, with the whole
sum absorbed into `O(E_md)`; this is exactly the content of `ENDPOINT_SHARP.
md` section 4's "twisted part, `q nmid r`" case (the character-orthogonality
cancellation, equation (4.1)-(4.2) there), reused verbatim rather than
re-derived. So the `q_e>R` case is already covered by (Md) as quoted, and
does not need separate treatment in section 3.

The parenthetical remark ("a real zero of a real character that is not the
Page-exceptional one is not exceptional for (ZF) either") is the correct
invocation of Landau-Page uniqueness across the whole family of real
primitive characters of conductor `<=R`, not just a per-character statement:
(ZF) alone only asserts *at most one* real zero *per character*; the
cross-character uniqueness needed to rule out a second, unrelated
exceptional character is exactly what (Pg') supplies, and that is why it is
invoked here rather than left to (ZF). The reduction of an imprimitive real
`chi mod r`'s real zero to its primitive inducing character's real zero is
also correct: for `chi` induced by `chi* mod q*` (`q*|r`), `L(s,chi) =
L(s,chi*) * prod_{p|r,p nmid q*}(1-chi*(p)p^{-s})`, and the extra Euler
factors do not vanish for `Re(s)>0` (each has modulus `|1-chi*(p)p^{-s}|>0`
there), so the real zeros of `L(s,chi)` in `(0,1)` are exactly those of
`L(s,chi*)`; likewise `chi` mod `r` is real if and only if `chi*` is real,
since reduction `(Z/r)^* -> (Z/q*)^*` is surjective when `q*|r`, so `chi`
real on `(n,r)=1` forces `chi*` real on all of `(Z/q*)^*`.

Also checked: `T` in Page's box `(Q,T)=(R,R^3)` is irrelevant to this whole
argument, since every zero under discussion in this section is real
(`Im=0<=T` automatically); only `Q=R` (the conductor bound) does any work,
which is consistent with `T` playing no role in the three bullets beyond
fixing the zero-counting range for the *non*-exceptional zeros in section 2.

No case is missed by the three bullets.

## (4) Section 4, the budget (6), the six exponents, the balance, and the
comparison with `ARC_SPLIT_BUDGET.md`

**Verdict: confirmed, except for the exponent inherited from item (2).**

*Recomputing the six exponents from (6) as printed*, with `R=e^{sigma sqrt
l}`: writing each bracketed term as `e^{-(rate) sqrt l}`,

```
R e^{-2 c_0 sqrt l}              -> rate 2 c_0 - sigma
R^2 e^{-(2c/sigma) sqrt l}       -> rate 2c/sigma - 2 sigma
R e^{-(c/(2 sigma)) sqrt l}      -> rate c/(2 sigma) - sigma
R^{-3}                           -> rate 3 sigma
R^2 e^{-2 sqrt(l)/3}             -> rate 2/3 - 2 sigma
R^{-1}                           -> rate sigma
```

matching the document's list exactly. Balancing the first and last (`2 c_0 -
sigma = sigma`) gives `sigma = c_0`, at which both equal `c_0`, confirmed.
Requiring the other four rates to be `>= c_0` at `sigma=c_0` reproduces the
document's stated conditions exactly: `2c/c_0 - 2c_0 >= c_0 <=> c_0^2 <=
2c/3`; `c/(2c_0) - c_0 >= c_0 <=> c_0^2 <= c/4`; `3c_0 >= c_0` automatic; and
`2/3 - 2c_0 >= c_0 <=> c_0 <= 2/9`, all recomputed independently and
agreeing with the printed numbers. The document also correctly notes that
`c_0^2 <= c/4` implies `c_0^2 <= 2c/3` (since `c/4 < 2c/3`), so only `sqrt(c)
/2` needs to appear in (H), not a separate bound for the second exponent.

**But** the fifth condition, `c_0 <= 2/9`, is the one item (2) shows is
computed from an exponent that is wrong by a factor of `R^{1/2}`: with the
corrected `R^3 e^{-2 sqrt(l)/3}` (rate `2/3 - 3 sigma`), the condition at
`sigma=c_0` is `2/3 - 3 c_0 >= c_0 <=> c_0 <= 1/6`. Section 4's own sentence
"`c_0<=2/9`" and (H)'s boxed `min(2/9, ...)` should both read `1/6` in place
of `2/9`; this is the same defect as item (2), located here at its point of
use rather than its point of origin.

*The comparison with `ARC_SPLIT_BUDGET.md`* (`2 gamma/3` with `gamma < c_0/
2`, giving at most `c_0/3`): arithmetically correct as a comparison of the
two documents' own stated constants (`c_0` vs `2 c_0/3`, an improvement by
more than 3 whenever the two `c_0`s are the same constant, which they are by
construction here).

*The repair of (1'), confirmed by direct recomputation.* `ENDPOINT_SHARP.md`
section 4's "Small y" step discards `y <= N exp(-gamma sqrt l)` and then
falls back to the much weaker bound `log y >= l/2` for everything that
follows, in particular for bounding the exceptional term `y^{tilde beta_y-1}
<= exp(-c_0 log y/sqrt l) <= exp(-c_0 sqrt(l)/2)`. But the discarded range
gives directly `log y > log N - gamma sqrt l = l - gamma sqrt l`, and using
that instead: `y^{tilde beta_y - 1} <= exp(-c_0 (l - gamma sqrt l)/sqrt l) =
exp(c_0 gamma) * exp(-c_0 sqrt l)`, a fixed constant `exp(c_0 gamma)` times
`exp(-c_0 sqrt l)`, i.e. rate `c_0` rather than `c_0/2`. This loses nothing
elsewhere: the other steps in `ENDPOINT_SHARP.md` section 4 that use `log y
>= l/2` (to get `e^{sqrt(log y)} >= R`, etc.) only need a *lower* bound on
`log y`, and `l - gamma sqrt l` is a larger (better) lower bound than `l/2`
for fixed `gamma` as `l -> infinity`, so the sharper bound can replace `l/2`
everywhere in that argument without breaking anything else. This confirms
both halves of the claim: `ENDPOINT_SHARP.md`'s "Small y" paragraph does
lose a factor of 2 exactly this way, and the repaired `(1')` (valid for any
`gamma < min(c_0, delta/sqrt2, 1/2)`) does feed into `ARC_SPLIT_BUDGET.md`'s
own optimum (`sigma=2 gamma/3`) to give `2 c_0/3` in place of `2 gamma_old/
3` with `gamma_old<c_0/2`, i.e. exactly a further factor `3/2` on top of the
already-stated factor 3, as the document says.

## (5) Section 5, the conditional lower bound and its corollary

**Verdict: confirmed**, with one imprecise closing sentence flagged below.

*Why `T` needs `l^4` and not `l^2`.* Tracing the choice through: the
remainder in (1) on the sub-arc is `<< N l^2/T`; with `T = q~^2 e^{kappa
sqrt l} l^p`, this is `N e^{-kappa sqrt l} l^{2-p}/q~^2`. Compared with
`N^{tilde beta} = N e^{-kappa sqrt l}` itself (before any `1/sqrt(q~)`
rescaling), the ratio is `l^{2-p}/q~^2`. At `p=2` this ratio is `1/q~^2`, a
fixed nonzero constant for fixed `q~` (e.g. `q~=3` gives `1/9`), not `o(1)`
as `l -> infinity`; at `p=4` the ratio is `l^{-2}/q~^2 -> 0` for any fixed
`q~`. This is exactly the document's own justification once traced through
(its "the ratio would be `phi(q~)/q~^2`, not small for `q~=3`" is the same
point up to the precise constant in front), and `l^4` is genuinely needed,
not a safety margin: `l^2` would leave the smallest admissible conductors
(`q~=3` being the smallest odd prime conductor) uncontrolled.

*Page condition.* Recomputed `log(q~ T) = 3 log q~ + 4 log l + kappa sqrt l
<= (kappa+3 eps) sqrt l (1+o(1))` using `q~ <= e^{eps sqrt l}`. Requiring
`tilde beta = 1-kappa/sqrt l > 1-b/log(q~T)` reduces to `kappa * log(q~T) <
b sqrt l`, and substituting the bound on `log(q~T)` gives exactly `kappa
(kappa+3 eps) < b` for large `l`, matching the hypothesis.

*(ZF) condition and the far-range error.* Recomputed `log(3 q~ T) <= (kappa+
3 eps) sqrt l (1+o(1))`, giving the far-range term `N l^2 exp(-(c/(kappa+3
eps)) sqrt l)`. For this, multiplied by the outer `sqrt(q~)`, to be `o(N^
{tilde beta}/sqrt(q~))`, the needed condition is `c/(kappa+3 eps) > kappa +
eps`. The stated hypothesis is `kappa < min(sqrt c, sqrt b) - 3 eps`, i.e.
`kappa + 3 eps < sqrt c`, i.e. `(kappa+3 eps)^2 < c` (the task names this
condition with `2 eps`; the document's own text uses `3 eps`, which is a
valid, slightly less tight, choice, not an error: `(kappa+3eps)^2<c` gives
`c/(kappa+3eps) > kappa+3eps > kappa+eps`, i.e. more room than is needed).
So the far-range error is controlled with margin to spare; no defect, and
the stated `3 eps` could very likely be relaxed to `2 eps` but does not need
to be.

*Size and phase of K_N and I_beta, checked numerically*
(`major_arc_explicit_section5_check.py`, `K_N` by direct summation, `I_beta`
by Simpson's rule at 4000 panels, no oscillation issue here since `gamma=0`
for a real zero) at `N in {1e3, 2e4, 5e5}`, `beta in {0.9, 0.99, 0.999}`,
`theta in {0, +-1/(16N), 1/(8N)}` (the full range `|theta|<=1/(8N)`):
`|K_N(theta)|/N` ranged `0.974` to `1.000` (claimed `>=1/2`); `|I_beta
(theta)|/N^beta` ranged `0.975` to `1.111` (claimed `>=1/4`); the phase gap
`|arg(K_N) - pi(N+1)theta|` was exactly `0` to floating precision (`K_N`
has the closed form `e^{i pi(N+1)theta} sin(pi N theta)/sin(pi theta)`, and
the ratio is real and positive throughout this range, so the phase is exact,
better than the claimed "within pi/8"), and `|arg(I_beta) - pi(N+1)theta|`
ranged `0` to `0.021` radians (claimed `<= pi/8 = 0.393`). Both bounds hold
with very large margin on this sample; `cos(pi/4)` as the resulting constant
in `Re(K_N-bar * I_beta) >= cos(pi/4)|K_N||I_beta|` follows from the two
phase gaps summing to at most `pi/4` by the triangle inequality, correctly.

*`mu(q)=+-1` for odd squarefree `q`*: immediate from the definition of the
Mobius function, not worth a script.

*The assembled lower bound vs `SIEGEL_UNIFORMITY.md` (23).* The proven lower
bound is `c_3 N^{2 beta+1} q/phi(q)^3`; (23)'s matching term is `N^{2 beta+1}
q^2/phi(q)^4`. Their ratio is `phi(q)/q <= 1`, so the lower bound proven here
is never larger than (23)'s upper bound for the same quantity, consistent
with the stated reading: `SIEGEL_UNIFORMITY.md` shows this term *would* be
size `N^{2beta+1}q^2/phi(q)^4` if `tilde chi` were subtracted as exceptional;
here it is not subtracted, and (7) shows the resulting error is at least of
the matching order (up to the bounded factor `phi(q)/q`).

*The corollary's arithmetic, recomputed step by step.* Setting `kappa =
(1-tilde beta) sqrt l = (c_0+kappa'/2)/2` and solving for `l` gives `sqrt l
= (c_0+kappa'/2)/(2(1-tilde beta))`, matching the stated choice exactly;
`kappa` is the midpoint of `c_0` and `kappa'/2`, hence strictly inside
`(c_0,kappa'/2)` since `kappa'>2c_0`, confirmed. The stated equivalence
`q~<=e^{eps sqrt l} <=> 1-tilde beta <= eps(c_0+kappa'/2)/(2 log q~)` is pure
algebra from the same substitution, confirmed. The contradiction threshold:
comparing (7)'s lower bound `c_1 N^3 e^{-2 kappa sqrt l}/q~^2` against the
assumed upper bound `N^3 e^{-kappa' sqrt l}` gives a contradiction exactly
when `q~^2 < e^{(kappa'-2 kappa) sqrt l}`; substituting `kappa=(c_0+kappa'/
2)/2` gives `kappa'-2 kappa = kappa'/2 - c_0`, a fixed positive constant
(since `kappa'>2c_0`), and for `eps` small enough that `2 eps < kappa'/2 -
c_0`, the assumed `q~<=e^{eps sqrt l}` already forces `q~^2 <= e^{2 eps sqrt
l} < e^{(kappa'/2-c_0) sqrt l}`, supplying the contradiction as claimed.

**What the corollary does and does not establish.** It establishes: *if*
`E_corr^(Z)(N) << N^3 exp(-kappa' sqrt l)` unconditionally for some fixed
`kappa'>2c_0`, *then* no even primitive real character of odd conductor `q~`
has a real zero with `1-tilde beta <= c'/log q~`, for `q~` beyond an
effective bound depending on `kappa',c_0,eps`. It does not establish this
for odd primitive real characters (the proposition's proof uses `tau(tilde
chi)=sqrt(q~)` for even `tilde chi`; the remark right after (7) explicitly
says the odd case needs either an extra `l^{-1}` loss or a different, `|W|^
4`-based, route, "neither is needed for the corollary", i.e. genuinely not
done here); it does not establish anything for characters of even conductor
(the argument uses `q~` odd squarefree throughout, for the exact identity
`mu(q~)=+-1` and to avoid the separate mod-4/mod-8 cases `SIEGEL_UNIFORMITY.
md` section 4 treats differently); and, being conditional on the assumed
unconditional bound at `kappa'`, it establishes nothing unconditionally by
itself, only the stated conditional implication.

**The closing sentence is not accurate as written.** "That is an effective
zero-free interval `(1-c'/log q~,1)` for real zeros of real characters, i.e.
the non-existence of Siegel zeros in the classical form" drops the even/
odd-conductor qualification that the same paragraph (and the Proposition's
own hypothesis) states explicitly two sentences earlier. The classical
Siegel-zero statement is unqualified over all real primitive characters,
both parities and every conductor with no special exclusion for the
conductor's own parity; what is actually shown here, conditionally, is
restricted to even primitive real characters of odd conductor. The document
is internally consistent about this restriction everywhere except in this
one closing sentence, which should read "for even primitive real characters
of odd conductor" rather than "for real characters" generically, and should
not be summarised as the classical statement without that qualifier.

## What would settle the one open point

Item (2)'s defect is a bookkeeping error (a missing `sqrt r`), not a gap
requiring new input; it is settled by the recomputation given above, and the
fix is mechanical: replace `8 R E_md` by `8 R^{3/2} E_md` in (4)/(5), replace
`R^2 e^{-2 sqrt(l)/3}` by `R^3 e^{-2 sqrt(l)/3}` in the squared bound of
section 4, and replace `c_0 <= 2/9` by `c_0 <= 1/6` in section 4's text and
in the boxed hypothesis (H). Nothing here was left unresolved.

# Review of ARC_SPLIT_BUDGET.md

Independent check, 2026-09-12 (attempt `a-0078`). Scope: the five items
listed in the assignment, covering sections 1, 2 (arcs), 3 (major arcs), 4
(minor arcs, including 4.1 in full), and 5 (budget) of `ARC_SPLIT_BUDGET.md`
at commit dbe1c98.

Read: `ARC_SPLIT_BUDGET.md` in full; `UPPER_BOUND.md` sections 2-6;
`LOCALIZED_MIXED_ENERGY.md` sections 1 and 6; `SIEGEL_UNIFORMITY.md` in
full; `ENDPOINT_SHARP.md` sections 1, 4, 5, 6; `ENDPOINT_BOUND.md` sections
1-7.

Item 1 was checked with a script written from scratch for this review,
`review_a0078_identity_check.py`, results in
`results_review_a0078_identity_check.json`; it does not import or reread
`arc_split_probe.py`. Items 2-5 are hand recomputations against the cited
source equations, reproduced below with the intermediate numbers.

## Item 1: the identities of section 1 (equations (2) and (3))

**Verdict: confirmed.**

Both identities are algebraic consequences of the definitions and hold
exactly, not just asymptotically.

**Equation (2).** Writing the coefficient of $|F|^2$ at shift $h\ge1$ as
$\psi_2(N,h)$ and of $V_y$ as $(N-h)\mathfrak S_y(h)$ (both standard, from
the Ramanujan expansion of $|K_N(\alpha-a/q)|^2$ and orthogonality), and
unwinding $X=\mathcal C(2\mathrm{Re}(\overline HW))$,
$Y=\mathcal C(|W|^2)$, $R_{\rm mod}=\mathcal C(|H|^2-V_y)-\widehat C_N$ from
`LOCALIZED_MIXED_ENERGY.md` section 6, gives
$[X+Y]_h=\psi_2(N,h)-\psi_2^a(N,h)$,
$[R_{\rm mod}]_h=\psi_2^a(N,h)-(N-h)\mathfrak S_y(h)-C_N(h)$, and their sum
$[G_{\rm corr}]_h=\psi_2(N,h)-(N-h)\mathfrak S_y(h)-C_N(h)$, matching the
document exactly. The toy-model script confirms this in coefficient space
at $N=600$: the maximum absolute difference between $[G_{\rm corr}]_h$ and
$[X+Y]_h+[R_{\rm mod}]_h$, computed two independent ways (direct windowed
sums $\psi_2,\psi_2^a,\mathfrak S_y$ versus the definitional sum), is
$4.4\times10^{-16}$.

**Equation (3).** $\mathcal C(|F|^2)-\mathcal C(|H|^2)=|F|^2-|H|^2-\kappa$
since the constant Fourier coefficients are $d_N$ and $\sum a(n)^2$
respectively, and $G_{\rm corr}=\mathcal C(|F|^2)-\mathcal C(V_y)-\widehat
C_N$ splits as $[\mathcal C(|F|^2)-\mathcal C(|H|^2)]+R_{\rm mod}$, giving
$G_{\rm corr}=(|F|^2-|H|^2)+R_{\rm mod}-\kappa$ exactly as stated. Checked
pointwise on an independent toy model, $\nu(n)=b\,1_{(n,30)=1}$ built from
scratch (not the document's own toy model or script) at $N=600$, $Z=10$,
on a grid of $4096$ points, with $F,H$ evaluated directly and $V_y$ via the
closed form of $K_N$: the maximum of
$|G_y-(|F|^2-|H|^2)-R_{\rm mod}+\kappa|$ is $9.1\times10^{-13}$ against
$\max|G_y|=2.24\times10^4$, relative defect $4.1\times10^{-17}$, with no
exceptional character ($C_N=0$), matching the document's own check (1) in
character but on an independently built model.

## Item 2: major arcs, section 3

**Verdict: confirmed**, including the account of where $R^7$ became $R^2$.

Recomputing each step: (5) follows from `ENDPOINT_SHARP.md` (1$'$) applied
to each residue class mod $r$ ($r\le R$ classes) plus Abel summation
against $e(n\theta)$ (cost $1+2\pi N|\theta|$), then $N|\theta|\le R/r$ on
$I_{r,a}$ gives $r(1+2\pi R/r)=r+2\pi R\le(1+2\pi)R<8R$ since $r\le R$;
this reproduces $|W(\alpha)|\le8C_1RNe^{-\gamma\sqrt\ell}$ exactly. For
(6): $||F|^2-|H|^2|\le|W|(|F|+|H|)$ is the standard factorization
$F-H=W$, so $(|F|^2-|H|^2)^2\le|W|^2(|F|+|H|)^2$, and bounding
$\sup_{\mathfrak M}|W|^2$ times $\int_{\mathbb T}(|F|+|H|)^2\le
2(d_N+\sum a(n)^2)\ll N\ell$ (Parseval, $d_N=\sum\Lambda(n)^2$,
$\sum a(n)^2\ll Nb^2\ll N\ell$) gives
$64C_1^2R^2N^2e^{-2\gamma\sqrt\ell}\cdot O(N\ell)=N^3\ell R^2
e^{-2\gamma\sqrt\ell}$, matching.

The comparison with `ENDPOINT_BOUND.md` (9), $N^3\ell^2R^7e^{-2\gamma t}$:
tracing that derivation, $\sup_{\mathfrak M}|W|\ll NR^2e^{-\gamma t}$ there
(radius $2R/N$ gives $N|\theta|\le2R$, so $r(1+N|\theta|)\le R(1+4R)\ll
R^2$, one power of $R$ worse than here), $|\mathfrak M|\ll R^3/N$ there
(radius $2R/N$ instead of $R/(rN)$, one more power of $R$ in the measure,
absent entirely from the new derivation which uses no measure factor at
all), and the pointwise $(|F|+|H|)^2\ll N^2\ell^2$ there in place of the
integrated $\int(|F|+|H|)^2\ll N\ell$ (one power each of $N$ and $\ell$).
Multiplying out: old $=(R^3/N)\cdot(N^2R^4e^{-2\gamma t})\cdot(N^2\ell^2)
=N^3R^7\ell^2e^{-2\gamma t}$; new $=(N^2R^2e^{-2\gamma\sqrt\ell})\cdot(N\ell)
=N^3R^2\ell e^{-2\gamma\sqrt\ell}$. Ratio old/new $=R^5\ell$, splitting as
claimed into $R^3\ell$ from dropping the arc-measure factor via Parseval
and $R^2$ from the arc radius. The document's accounting of the $R^7\to
R^2$ change is correct in every factor.

(7) and (8): the split $[R_{\rm mod}]_h=[\psi_2^a-(N-h)\mathfrak
S-C_N]+(N-h)(\mathfrak S(h)-\mathfrak S_y(h))$ is exact algebra from (2);
squaring and summing with $(a+b)^2\le2a^2+2b^2$ gives $\|R_{\rm
mod}\|_2^2\ll N\cdot N^2e^{-2c_m\sqrt\ell}+D_{\rm tail}(N,y)\ll
N^3e^{-2c_m\sqrt\ell}+N^2$ (using $D_{\rm tail}(N,y)\ll N^2$ from
`UPPER_BOUND.md` section 2 at $y=\lfloor\sqrt N\rfloor$). The constant
term $\kappa^2|\mathfrak M|\ll(N\ell)^2\cdot R^2/N=NR^2\ell^2$ follows
directly from $|\kappa|\ll N\ell$ (section 1) and $|\mathfrak
M|\le2R^2/N$. Assembling the three parts with $(a+b+c)^2\le3(a^2+b^2+c^2)$
reproduces (8) exactly.

## Item 3: minor arcs, section 4

**Verdict: confirmed.**

The identity $G_{\rm corr}|_{\mathfrak m}=|F|^2-H_R-a_0(N,R)-T_{y,R}
-\widehat C_N$ is `UPPER_BOUND.md` (10), $G_y=B_Q-H_Q-a_0(N,Q)-T_{y,Q}$,
restricted to $Q=R$ and to $\mathfrak m$, where the arc model $A_R$
vanishes by construction (it is supported on indicator functions of the
arcs comprising $\mathfrak M_R$), so $B_R=|F|^2-A_R=|F|^2$ there, and
$G_{\rm corr}=G_y-\widehat C_N$. A point worth recording: `UPPER_BOUND.md`
(7) defines its arcs with radius $\delta_q=Q/(qN)$, which at $Q=R$ is
exactly the radius $R/(rN)$ that `ARC_SPLIT_BUDGET.md` section 2 adopts
(rather than `ENDPOINT_BOUND.md`'s $2R/N$). The two arc systems therefore
coincide exactly when $Q=R$, which is what makes citing `UPPER_BOUND.md`'s
estimates directly, without re-deriving them for a different arc geometry,
valid.

On the four cited bounds holding for arbitrary $R$ with $2R^2<N$, not only
for the specific $Q$ used in `UPPER_BOUND.md`'s own sections:

- (20), $I_Q\ll(N^3/Q+N^{13/5})L^6$: derived in `UPPER_BOUND.md` section 5
  from Dirichlet approximation with $\lceil N/Q\rceil$, which uses only the
  general arc setup (7) (needing $2Q^2<N$ for disjointness), not the
  specific choice $Q=\lfloor L^B\rfloor$ used earlier in that section.
  Valid for any $R$ with $2R^2<N$.
- (13), $\|H_Q\|_2^2\ll(N^3/Q^2)\log(2Q)w(Q)^2$: `UPPER_BOUND.md` states
  this "uniformly for the parameters in (7)", i.e. for any $Q$ meeting
  $2Q^2<N$. Valid.
- $a_0(N,Q)=N\log(N/Q)+O(N)$: a CHHL asymptotic identity for the
  Ramanujan-sum truncation at any level $Q\le N$, not tied to a specific
  $Q$. Valid.
- (9), $\|T_{y,Q}\|_2\ll N^{3/2}/Q$: this uses $D_{\rm tail}(N,Q)\ll
  N^3/Q^2$, which `UPPER_BOUND.md` section 2 proves only for $1\le z\le
  \sqrt N$. The constraint $2R^2<N$ in `ARC_SPLIT_BUDGET.md` section 2
  gives $R<\sqrt{N/2}<\sqrt N$, so this is exactly the range where the
  bound is available; the constraint is not incidental, it is what this
  step needs.

The assembly (9) is Cauchy-Schwarz on the five-term pointwise identity
($(a_1+\cdots+a_5)^2\le5\sum a_i^2$), and (11) follows by substituting the
four bounds above plus (10) (checked in item 4) and dropping subdominant
terms ($N^3/R^2$ terms are $\le N^3/R$ for $R\ge1$, absorbed into the
$\ell^{O(1)}R^{-1}$ notation). Recomputed and correct.

## Item 4: the correction polynomial on the minor arcs, section 4.1

**Verdict: confirmed**, with one auxiliary estimate (identified below)
accepted on order-of-magnitude grounds rather than fully re-derived, and
noted because it is not the binding term either way.

**The $C_N(h)$ formula.** Substituting $u_q(h)=\mu(q)\chi(-h)/q$,
$v_q(h)=\mu(q)\chi(h)/q$ (odd $q$, `SIEGEL_UNIFORMITY.md` (17)) into
$C_{q,\beta,Z}(h)=\mathcal L_h[-u_q(h)J_1(h)-v_q(h)J_2(h)+(c_q(h)/q)
J_{12}(h)]$ (its (19)) reproduces the displayed formula exactly, with the
$1_{q\ \rm odd}$ correctly gating the linear part (at $4\mid q$,
$u_q=v_q=0$, only the quadratic term survives, matching (19) directly).

**The quadratic piece.** Recomputed the full three-range split from
scratch.

*Range $R<m\le\sqrt N$.* Writing $A(h)=\sum_{R<qd\le\sqrt N}(q/\phi(qd)^2)
c_{qd}(h)$, expanding $c_{qd}(h)=\sum_a^*e(ah/qd)$ turns $\sum_h|A(h)|^2$
into a dual-large-sieve sum over $\sim1/N$-spaced points (fractions with
denominator $\le\sqrt N$ are at least $1/N$ apart), giving $\sum_h|A(h)|^2
\le2N\sum_{R<qd\le\sqrt N}\phi(qd)q^2/\phi(qd)^4$ (the $2N$ is $N+\delta^{-1}$
at $\delta=1/N$, matching the additive large sieve (LS) of
`UPPER_BOUND.md` used in dual form). With $\sup J_{12}(h)^2\le4N^2$, the
total is $8N^3(q^2/\phi(q)^3)\sum_{d>R/q}\mu(d)^2/\phi(d)^3$, exactly the
displayed chain. Using $\sum_{d>D}\mu(d)^2/\phi(d)^3\ll D^{-2}\ell^{O(1)}$
($D\ge1$) or $O(1)$ ($D<1$) and $q/\phi(q)\ll\ell$: at $q\le R$ this gives
$N^3\ell^{O(1)}q/R^2$ (using $q^4/\phi(q)^3=q(q/\phi(q))^3\ll q\ell^3$); at
$q>R$ it gives $N^3\ell^{O(1)}/q$ (using $q^2/\phi(q)^3=(1/q)(q/\phi(q))^3
\ll\ell^3/q$). Both recombine exactly into $N^3\ell^{O(1)}\min(1/q,
q/R^2)$, and both branches of the minimum are indeed $\le1/R$ as stated
($q\le R\Rightarrow q/R^2\le1/R$; $q>R\Rightarrow1/q<1/R$); the direction
is not reversed.

*Range $m>\sqrt N$.* The final order $N^{2+o(1)}$ was checked
dimensionally: with the stated per-$h$ coefficient bound
$\ll Nq\tau(h)\ell^{O(1)}/\sqrt N$, $\sum_h\tau(h)^2\ll N\ell^3$
(standard), and $q<Z=e^{\sqrt\ell}$, the mean square is
$\ll(N^2q^2/N)\cdot N\ell^3\cdot\ell^{O(1)}=N^2q^2\ell^{O(1)}\ll
N^2e^{2\sqrt\ell}\ell^{O(1)}=N^{2+o(1)}$, matching. The auxiliary bound
$\sum_{m>X,g\mid m}\phi(m)^{-2}\ll g\phi(g)^{-2}X^{-1}\ell^{O(1)}$ feeding
the per-$h$ coefficient estimate was not independently re-derived here; it
is a plausible sieve-type tail bound and, since $N^{2+o(1)}\ll N^3/R$ for
any $R=N^{o(1)}$ regardless of its precise constant, an error here of a
power of $\ell$ would not change the final budget, which never binds on
this range.

*Range $m\le R$ (present only when $q\le R$).* Recomputed: centers $a/m$
for $m\le R$ lie in $\mathfrak M$ by construction of the arcs in section
2, so on $\mathfrak m$, $\|\alpha-a/m\|>R/(mN)$, giving
$\sum_a^*\|\alpha-a/m\|^{-1}\le mN/R+O(m\log m)\ll mN/R$ for large $N$.
Chaining this through the Abel bound $|\Phi_{J_{12}}(x)|\le J_{12}(1)/\|x\|
\le2N/\|x\|$ and summing over $d\le R/q$ reproduces both displayed bounds,
$\sup_{\mathfrak m}|\cdot|\ll N^2\ell^{O(1)}/R$ and
$\int_{\mathfrak m}|\cdot|\ll N\ell^{O(1)}$, and hence $\ll N^3\ell^{O(1)}
/R$ via $\int f^2\le(\sup f)(\int f)$.

**The linear pieces.** The Gauss-sum expansion $\chi(h)\tau(\bar\chi)
=\sum_a\bar\chi(a)e(ah/q)$ combined with $S_*(h)=\sum_{d\mid P,(d,q)=1}
c_d(h)/\phi(d)^2$ correctly produces a sum over fractions with denominator
dividing $qd$ and coefficient modulus $\le q^{-1/2}\phi(d)^{-2}$; combined
with the front weight $(q/\phi(q))^2q^{-1}=q/\phi(q)^2$, the net per-fraction
weight is $q^{1/2}/(\phi(q)^2\phi(d)^2)$, exactly a factor $q^{-1/2}$
smaller than the quadratic piece's weight $q/(\phi(q)^2\phi(d)^2)$, and
this is the weight the document uses later for the $qd\le R$ range. The
three sub-ranges were not each re-derived to the same constant-tracking
level as the quadratic piece, but the claimed final orders,
$N^3\ell^{O(1)}/R^2$ for $R<qd\le\sqrt N$ (an extra $q^{-1}$ from the
squared weight relative to the quadratic piece's $1/R$, consistent), $N^{2
+o(1)}$ for $qd>\sqrt N$ (same argument as the quadratic case), and
$N^3\ell^{O(1)}/R$ for $qd\le R$ (same single power of $R$ as the
quadratic case, since that range's $R$-dependence comes from one
reciprocal-distance factor, not the large-sieve tail), are structurally
consistent with the mechanism verified in full for the quadratic piece,
and none of them exceeds $N^3\ell^{O(1)}/R$, so (10) follows.

**The consistency check against `SIEGEL_UNIFORMITY.md` (23).** Recomputed
independently: at $q>R$, only the first two ranges apply (the third
requires $q\le R$), giving $N^3\ell^{O(1)}/q$ from the quadratic piece
(dominant over the linear piece's $N^3\ell^{O(1)}/q^2$ there) plus the
subdominant $N^{2+o(1)}$. Taking the crude bound $J_1,J_2,J_{12}\ll N$
(the $\beta\to1$ worst case implicit in the document's generic bounds) in
`SIEGEL_UNIFORMITY.md` (23), $N^{4\beta-1}q^2/\phi(q)^3\to
N^3q^2/\phi(q)^3=N^3(1/q)(q/\phi(q))^3\ll N^3\ell^3/q$, exactly matching.
The cross-check holds.

No lost factor of $q/\phi(q)$, $\phi(qd)$, or $\sqrt q$ was found in the
quadratic-piece derivation (fully re-derived), no reversed direction in
$\min(1/q,q/R^2)\le1/R$, and the $q>R$ case is explicitly and correctly
handled (range 3 is explicitly gated on $q\le R$, and the consistency
check confirms the $q>R$ regime separately).

## Item 5: the budget, section 5

**Verdict: confirmed.** Recomputed both optima independently.

**General balance.** For a budget of the shape $N^3R^ke^{-2\gamma\sqrt\ell}
+N^3R^{-j}$, balancing $2\gamma-k\sigma=j\sigma$ at $R=e^{\sigma\sqrt\ell}$
gives $\sigma^*=2\gamma/(j+k)$ and exponent $j\sigma^*=2\gamma
j/(j+k)$.

**This budget**, $k=2$, $j=1$: $\sigma^*=2\gamma/3$, exponent $2\gamma/3$.
Matches the document. Checked directly: at $\sigma=2\gamma/3$,
$R^2e^{-2\gamma\sqrt\ell}=\exp((4\gamma/3-2\gamma)\sqrt\ell)
=\exp(-(2\gamma/3)\sqrt\ell)$ and $R^{-1}=\exp(-(2\gamma/3)\sqrt\ell)$,
equal as required.

**Previous budget** (`ENDPOINT_SHARP.md` (18$'$)), $k=7$, $j=1/6$, but
with an extra factor $\tfrac12$ in that document's own definition
$c'=\tfrac12\min(2\gamma-7\sigma,\sigma/6,c,2c_m)$: balancing
$2\gamma-7\sigma=\sigma/6$ gives $12\gamma=43\sigma$, i.e.
$\sigma^*=12\gamma/43$, value at optimum $\sigma^*/6=2\gamma/43$, and with
the document's own $\tfrac12$ factor, exponent $=\gamma/43$. Matches the
document's claim exactly. At the document's actually stated
$\sigma=\min(\gamma/20,1/20)=\gamma/20$ (since $\gamma<1/2$ throughout,
established in `ENDPOINT_SHARP.md` section 4's own range for $\gamma$):
$2\gamma-7\sigma=33\gamma/20$, $\sigma/6=\gamma/120$, so
$c'=\tfrac12\min(33\gamma/20,\gamma/120,\ldots)=\tfrac12\cdot\gamma/120
=\gamma/240$, exactly reproducing the stated $\gamma/240$ and confirming
that $\gamma/43$ is a genuinely better exponent available from the same
budget structure that was not the one used.

**Constraints.** $\sigma=2\gamma/3<1/3$ since $\gamma<1/2$, and $1/3<
1/\sqrt2$, so $\sigma\le1/\sqrt2$ holds with room. $2R^2<N$ holds for
sufficiently large $N$ for any fixed $\sigma$. $2c_m>2\gamma/3$: with
$c_m=1/4-o(1)$ (fundamental lemma at level $N^{1/4}$, giving sieve
parameter $s=\sqrt\ell/4$ and hence $c_m\approx1/4$) and $\gamma<1/2$,
$2c_m\to1/2-o(1)>1/3>2\gamma/3$. All confirmed.

**Section 7's cross-term claim.** $2c_m=1/2-o(1)$ exceeds both
$\sigma/6=\gamma/120$ (this budget's binding rival in the old chain) and
$2\gamma/3$ (this budget's own binding term) since $\gamma<1/2$ makes both
$\gamma/120$ and $2\gamma/3<1/3$ strictly below $1/2-o(1)$. So in both
budgets the cross term with $R_{\rm mod}$, bounded by $2\|R_{\rm
mod}\|^2\ll N^3e^{-2c_m\sqrt\ell}$, is dominated by a strictly smaller
exponent elsewhere and cannot move either budget's binding constant.
Confirmed.

**Section 6's list.** Scanned `ARC_SPLIT_BUDGET.md` for the named
objects: $D_0$, $A(N)$, the properties (P1)-(P4), and the term
$N^{2+A(N)}e^{\sqrt\ell/2}$ do not appear anywhere in the document, nor do
`ENDPOINT_BOUND.md`'s Type I estimate (10), character estimate (12),
Cases A/B (13)-(14), or cubic moment (16). What is cited instead is
`UPPER_BOUND.md` (7), (9), (13), (15), (20), which is a different source
document's estimates entirely, matching the claim that the divisor
approximant is genuinely unused rather than silently smuggled back in.
Input (1$'$) and input (2) of `ENDPOINT_SHARP.md`, cited directly in
sections 3(a) and 3(b), are the two of the original four inputs that
remain, plus the singular-series truncation (also via input (2)/$c_m$);
the fundamental lemma inside the proof of (1$'$) is inherited implicitly
through citing (1$'$) as a black box. Consistent with the document's own
accounting.

## Summary

No defect found in any of the five items. Item 1 was verified numerically
to floating-point precision on an independently written toy model. Items
2, 3, and 5 were fully recomputed by hand against the cited source
equations and match exactly, including the specific accounting of how
$R^7$ became $R^2$ on the major arcs and the numerical optimum of both
budgets. Item 4, the document's own most novel and highest-risk estimate,
was recomputed in full for the quadratic piece and the three-range split
technique (dual large sieve, gcd/tail bound, minor-arc reciprocal-distance
bound), all of which check out exactly including the self-consistency
test against `SIEGEL_UNIFORMITY.md` (23); the linear-piece constants and
one auxiliary sieve-tail lemma in the $m>\sqrt N$ range were checked only
at the order-of-magnitude level rather than re-derived symbol by symbol,
but neither is the binding term in the final bound, so an error there
confined to logarithmic factors would not change (S$'$).

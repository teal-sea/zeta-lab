# Route G: a direct arc-transfer attempt for \(Z_{(q)}\), and a literature
# connection that sharpens the wall

**Scope and relation to prior documents.** This document's task is the one
`RANK3_QUARTIC_TOOLS.md` closes with as unfinished (its §4, "What would
settle this precisely"): (i) search further for a named, unconditional,
\(q\)-averaged fourth-moment tool bounding \(Y(b_1,b_2,b_3,b_4)\) or
\(Z_{(q)}\) directly, and (ii) attempt, from scratch, an arc-transfer
argument for \(Z_{(q)}\) specifically, rather than only citing why
\(U_{(q)}\)'s does not apply (`RANK3_ROUTE_D.md` §7). It assumes
`RANK3_ROUTE_D.md`, `RANK3_MEAN_VALUE_TOOLS.md`, `RANK3_SCOPE.md`, and
`RANK3_QUARTIC_TOOLS.md` as already established and does not restate their
content beyond what is needed to extend it. Notation is theirs:
\(F_N,K_N,\Lambda,\mu,\phi\) as in UPPER_BOUND.md §1;
\(P_{q,a},R_{q,a},U_{(q)},Z_{(q)}\) as in UPPER_BOUND.md §6 and
RANK3_SCOPE.md §1; \(Q=\lfloor\sqrt N/3\rfloor\), \(R_0=Q/L\), \(L=\log N\);
\(Y\) as defined in RANK3_ROUTE_D.md §7 and restated in the assignment.

This document contributes three things beyond what is already on record:
a direct, mechanism-by-mechanism attempt to build an arc-transfer argument
for \(Z_{(q)}\) (§1); a specific literature connection —
Montgomery–Vaughan's mean-square theorem for Goldbach's problem — that
turns "no tool found" into "no tool can exist at the full-circle level,
provably" (§2); and a correction, with more data, to a numerical overclaim
in `RANK3_QUARTIC_TOOLS.md` §2 (§3). Like that document, this one cannot run
a live literature search in this environment (only `grep`/`rg`/`ls`/`cat`/
`head`/`tail`/`wc`/`find` over this worktree and the lab's Python
interpreter are available; there is no network access and no bibliographic
database), so §2's citation is stated as recollection, not as something
independently verified against a live source here — the same limitation
`RANK3_QUARTIC_TOOLS.md` §3 already flags for its Heath-Brown citation.

## 1. A direct attempt at an arc-transfer argument for \(Z_{(q)}\)

RANK3_ROUTE_D.md §7 states, correctly, that \(Z_{(q)}\)'s integrand
\(|R_{q,a}|^4\) carries no factor comparable to \(U_{(q)}\)'s
\(|P_{q,a}|^2\) that decays away from the arc, so the transfer step used for
\(U_{(q)}\) (§4 there) has no direct analogue. That is a statement about
*one* mechanism (bounding the arc integral by the full-circle integral via
a decaying weight). It does not by itself rule out every mechanism. This
section tries three others, each concretely, and shows each collapses into
a tool already priced and found insufficient.

**(a) Triangle-inequality transfer via \(P_{q,a}\)'s own decay.** The one
piece of \(R_{q,a}=F_N-P_{q,a}\) that *does* decay off the arc is
\(P_{q,a}\) itself: \(|P_{q,a}(\beta)|=(|\mu(q)|/\phi(q))|K_N(\beta)|\ll
(|\mu(q)|/\phi(q))\min(N,1/\|\beta\|)\), the standard Dirichlet-kernel
bound. Expanding \(|R_{q,a}|^4=|F_N-P_{q,a}|^4\) via
\(|x-y|^4\le8(|x|^4+|y|^4)\) (the same inequality UPPER_BOUND.md uses at
(28), and RANK3_ROUTE_D.md §7 uses for the \(R^{(2)}\) piece) gives, on any
arc,
\[
 \int_{\rm arc}|R_{q,a}|^4\le8\int_{\rm arc}|F_N|^4+8\int_{\rm arc}|P_{q,a}|^4.
\]
The second term is exactly computable and small: \(|P_{q,a}|^4=
(|\mu(q)|/\phi(q))^4|K_N|^4\), and
\(\int_{\mathbb T}|K_N|^4\,d\beta\) is the classical, purely combinatorial
fourth moment of the Dirichlet kernel — the number of solutions to
\(n_1+n_2=n_3+n_4\), \(1\le n_i\le N\), which is \(\Theta(N^3)\) with an
explicit elementary constant and no arithmetic input at all (this is the
\(q=1\), unweighted, \(\Lambda\)-free case of the same convolution counting
problem). Summed over \(a\) and \(q\le R_0\), this term costs
\(O\!\big(N^3\sum_{q\le R_0}\phi(q)(\mu(q)/\phi(q))^4\big)=O(N^3\sum_q
\phi(q)^{-3})=O(N^3)\) at worst (the sum over \(q\) converges), so it is
never the obstruction. **The whole difficulty is pushed onto the first
term**, \(\int_{\rm arc}|F_N|^4\): a *raw*, unweighted, unrestricted local
fourth moment of the prime exponential sum itself on a shrinking arc around
\(a/q\), with no residue-class bias subtracted at all. This matches, and
sharpens, the structural observation already on record in
`RANK3_QUARTIC_TOOLS.md` §2 (that \(Z_{(q)}\) does not vanish, and shows no
saving, on non-squarefree \(q\), where \(R_{q,a}=F_N\) exactly): here the
same object, \(\int_{\rm arc}|F_N|^4\), reappears as the irreducible core of
\(Z_{(q)}\) even at squarefree \(q\), once the transfer is attempted. So
**any** arc-transfer argument for \(Z_{(q)}\), not just the specific one
`RANK3_ROUTE_D.md` §7 rules out, must in the end bound
\(\int_{I_{q,a}}|F_N|^4\) directly — there is no way to route around this
term by manipulating \(P_{q,a}\) alone, since \(P_{q,a}\)'s own fourth
moment is cheap and the cross terms in a finer expansion (below) do not
remove \(|F_N|^4\) either.

**(b) Hölder/interpolation transfer.** A second natural mechanism: bound
the arc integral of \(|R_{q,a}|^4\) by \(\big(\sup_{\rm arc}|R_{q,a}|\big)^2
\cdot\int_{\rm arc}|R_{q,a}|^2\), i.e. an \(L^\infty\)-times-\(L^2\)
interpolation rather than a full-circle comparison. This substitutes the
problem for two already-named quantities: a pointwise bound on \(R_{q,a}\)
on the arc, and the arc-restricted second moment (an \(U_{(q)}\)-type
object, already summed in RANK3_SCOPE.md §1). The pointwise bound is
exactly Vaughan's (V), and RANK3_SCOPE.md §2 ("(V) is weakest exactly
here") already prices it: for \(q\lesssim N^{2/5}\) — a sub-range fully
inside \(2\le q\le R_0\), since \(R_0\sim N^{1/2}/(3L)\gg N^{2/5}\) — (V)
gives \(|F_N|\ll NL^{5/2}\), the trivial order, no saving. Carrying that
through: \(\sup_{\rm arc}|R_{q,a}|^2\ll N^2L^5\) at worst, and
\(\int_{\rm arc}|R_{q,a}|^2\le\int_{\mathbb T}|R_{q,a}|^2\ll NL\) by
Parseval (coefficients are \(O(\Lambda(n))\), and
\(\sum_{n\le N}\Lambda(n)^2\ll NL\)); the product is \(O(N^3L^6)\) — the
same order as the trivial bound on \(Z_{(q)}\) itself, with no saving, and
for exactly the same reason (V) fails to save \(U_{(q)}\) or the direct
on-arc \(Z_{(q)}\) bound at small \(q\) (RANK3_SCOPE.md §2, third bullet).
This mechanism is not new: it is the on-arc-via-(V) route RANK3_SCOPE.md §2
already prices and finds wanting, arrived at from a different starting
point (an attempted transfer, rather than a direct arc bound), confirming
it is not a route around that obstruction.

**(c) A finer binomial expansion, isolating cross terms.** Expanding
\(|R_{q,a}|^4=|F_N-P_{q,a}|^4\) exactly (not via the crude \(8(x^4+y^4)\)
bound of (a)) produces cross terms of the shape
\(|F_N|^3|P_{q,a}|\), \(|F_N|^2|P_{q,a}|^2\), \(|F_N||P_{q,a}|^3\), each
controllable by Cauchy–Schwarz in terms of moments of \(F_N\) up to order 3
and moments of \(P_{q,a}\) (which, being a scaled \(K_N\), has every moment
computable in closed form as above). This does **not** remove the
\(|F_N|^4\) term found in (a) — that term has coefficient 1 in the exact
expansion and no cross term cancels it, since cross terms only ever pair
\(F_N\) with the small, decaying \(P_{q,a}\), never eliminate a pure
\(F_N\) power. So a finer expansion changes the bookkeeping around the
edges (potentially sharpening the constant, or converting some
\(|F_N|^3|P_{q,a}|\)-type terms into \(U_{(q)}\)-adjacent quantities via
Cauchy–Schwarz) but does not change the conclusion of (a): the exact
\(|F_N|^4\) term is unavoidable and irreducible, appears with full weight,
and is not itself reducible to \(\Delta(t;q,b)\)-type quantities (that is
`RANK3_ROUTE_D.md` §7's first point, restated here for the isolated term
rather than for the full \(R_{q,a}^4\)).

**Conclusion of this section.** Three natural transfer mechanisms — direct
decay comparison, sup-times-\(L^2\) interpolation, and a finer cross-term
expansion — all reduce to the same two facts already on record:
\(\int_{\rm arc}|F_N|^4\) is the irreducible core (not removable by any
splitting against \(P_{q,a}\), since \(P_{q,a}\)'s own moments are cheap),
and every tool available to attack that core directly — (V) via
interpolation, or a full-circle-to-arc comparison — is priced at trivial
order in exactly this \(q\)-range by `RANK3_SCOPE.md` §2. No fourth
mechanism suggests itself from the algebra of \(|x-y|^4\) beyond these
three (binomial expansion has exactly these term-shapes, and Hölder/
interpolation admits no other split of \(4=p+q\) with \(p,q\ge0\) integers
that avoids reproducing either (a) or (b)). This is offered as a genuine,
if negative, answer to "can a fresh arc-transfer argument be constructed at
all": not merely that `RANK3_ROUTE_D.md`'s specific mechanism fails, but
that the natural alternatives fail for the same underlying reason, and
identify the same missing ingredient — a non-trivial bound on
\(\int_{\rm arc}|F_N|^4\) itself, at \(q\lesssim N^{2/5}\), which no tool
named in UPPER_BOUND.md or found in §2 below supplies.

## 2. Literature: Montgomery–Vaughan's mean-square theorem, and why it
##    sharpens rather than fills the wall

`RANK3_QUARTIC_TOOLS.md` §3 already covers two candidate directions and
finds neither adapts: a structure-free "quartic large sieve" cannot exist
(the \(L^4\) inequality is sensitive to additive energy, unlike the
structure-free \(L^2\) large sieve), and the multiplicative-side quartic
moment of Dirichlet \(L\)-functions (Heath-Brown 1981 and antecedents) is a
fixed-height statement, the wrong variable for \(Z_{(q)}\)'s
height-integrated need. This section adds a third, more classical
direction, specific to \(\Lambda\)-weighted quadruple convolutions rather
than to \(L\)-function moments or large sieves: the second-moment (in \(n\))
theory of Goldbach representations.

**The connection.** Write \(r(n)=\sum_{n_1+n_2=n}\Lambda(n_1)\Lambda(n_2)\)
for \(2\le n\le2N\) (summing over \(1\le n_1,n_2\le N\)); these are exactly
the Fourier coefficients of \(F_N(\alpha)^2\). By Parseval,
\[
 \sum_{n=2}^{2N}r(n)^2=\int_{\mathbb T}|F_N(\alpha)|^4\,d\alpha,
\]
i.e. the full-circle, \(q=1\), *no residue restriction at all* case of
exactly the raw quantity Section 1(a) isolates as \(Z_{(q)}\)'s irreducible
core (restricted there to a single arc rather than the whole circle).
The classical circle-method literature on Goldbach's problem's error term
— Montgomery and Vaughan, "The exceptional set in Goldbach's problem," Acta
Arith. 27 (1975), 353–370, building on the Hardy–Littlewood/Vinogradov-era
major-minor arc apparatus for this exact convolution — establishes, as
recollected here (not verified against a live source in this environment,
per this document's preamble):

- \(\sum_{n\le N}r(n)^2\sim CN^3\) for an explicit constant \(C\) coming
  from the singular series average (major arcs, via the prime number
  theorem in arithmetic progressions, give a convergent main term of
  exactly this order; minor arcs contribute a provably smaller error via
  Vaughan/Vinogradov-type bounds on \(F_N\)) — a genuine two-sided
  asymptotic, not merely an upper bound;
- separately, \(\sum_{n\le N}\big(r(n)-\mathfrak S(n)n\big)^2\ll
  N^3(\log N)^{-A}\) for every fixed \(A>0\) (\(\mathfrak S(n)\) the
  pointwise-in-\(n\) singular series), an unconditional log-power saving
  relative to that *different*, pointwise-in-\(n\) bias subtraction.

**What this settles.** The first fact is a proved *lower* bound, not just
an upper one, on \(\int_{\mathbb T}|F_N|^4\,d\alpha\) — the unrestricted
quantity is \(\Theta(N^3)\), unconditionally. This means no tool of any
kind (quartic large sieve, \(L\)-function moment, additive-combinatorial
energy bound, or anything else) can ever produce a bound on
\(\int_{\mathbb T}|F_N|^4\) better than \(O(N^3)\), on pain of contradicting
a proved theorem. This is a strictly stronger statement than
`RANK3_QUARTIC_TOOLS.md` §4's "no candidate tool is found" — it says no
candidate tool *could* exist for the full-circle version of the quantity
Section 1 shows is \(Z_{(q)}\)'s irreducible core. Combined with Section 1's
reduction, the entire hope for a useful bound on \(\sum_{2\le q\le R_0}
Z_{(q)}\) has to come from the *arc-restriction* — the fact that
\(I_{q,a}\) has width \(\sim1/(qN)\ll1\), a small fraction of the full
circle — buying a saving that the full-circle quantity provably does not
have on its own; it cannot come from the quartic moment itself somehow
being smaller in size than \(\Theta(N^3)\), because it is not. Numerically,
this matches `RANK3_QUARTIC_TOOLS.md` §2's finding exactly (and Section 3
below): \(Z^*_{(q)}/(\phi(q)N^3)\) is bounded above and below by positive
constants for every \(q\ge2\) checked, exactly the signature of a
\(\Theta(N^3)\) quantity, not a quantity with room for a hidden
\(N\)-power saving waiting to be found by a cleverer tool.

**What this does not settle.** The second (mean-square exceptional set)
fact is a genuine, unconditional saving — but relative to a *different*
bias subtraction (pointwise in \(n\), via \(\mathfrak S(n)\)) than the one
\(R_{q,a}=F_N-P_{q,a}\) uses (indexed by \((q,a)\) via the arc
decomposition), and it is a statement about the *whole circle*, not an
individual arc restricted to width \(\sim1/(qN)\) around one rational. It
does not, as it stands, supply the arc-restricted bound Section 1 shows is
needed, and this document does not find a way to convert it into one; it is
recorded here because it is the closest named, unconditional, fourth-moment
(in the sense of a quadruple \(\Lambda\)-convolution) result this document
locates, and because it upgrades the wall from a search gap to a proved
obstruction at the full-circle level. Whether the *log*-power saving in the
mean-square-exceptional-set result has any analogue at the arc-restricted,
\((q,a)\)-indexed level is a question this document does not answer and
does not attempt to guess at; it is a possible next step, not a result
here.

**Vinogradov-type mean value theorems do not apply either, for a different
reason than (BV)/(BDH).** A natural fourth candidate, given the shape of
\(Y\) (a quadruple additive convolution \(n_1+n_2=n_3+n_4\)), is Vinogradov's
mean value theorem and its modern strengthenings (Wooley's efficient
congruencing; Bourgain–Demeter–Guth decoupling). These bound the number of
solutions to *systems* of equations \(\sum u_i^j=\sum v_i^j\) for
\(j=1,\dots,k\) with a power-saving over the trivial count, for degree
\(k\ge2\) monomial curves. The equation defining \(Y\), \(n_1+n_2=n_3+n_4\),
is the *degree-1* (single, linear) case — the additive energy of the
interval \([1,N]\) itself — which is elementary and exact
(\(\sum_k r_K(k)^2=\Theta(N^3)\), the same computation behind
\(\int_{\mathbb T}|K_N|^4\) in Section 1(a)), not a case where Vinogradov's
machinery or decoupling supplies anything beyond what direct combinatorics
already gives. What is missing is not a sharper count of solutions to
\(n_1+n_2=n_3+n_4\) — that count is known exactly — but a saving in the
\(\Lambda\)-weighted version, i.e. arithmetic information about *which*
quadruples the primes occupy relative to the uniform measure, which is
additive-energy-of-a-specific-set information (`RANK3_QUARTIC_TOOLS.md`
§3's point, restated: this is not a structure-free geometric statement, and
Vinogradov/decoupling machinery is exactly such a structure-free geometric
tool, aimed at a different, higher-degree problem).

## 3. Numerical data: the deviation from \(\Theta(N^3)\) tracks
##    \(|\mu(q)|/\phi(q)\), not squarefreeness

`RANK3_QUARTIC_TOOLS.md` §2 measures \(Z^*_{(q)}/(\phi(q)N^3)\) at
\(N=20000\) and reports it as "the same constant... for every \(q\ge3\)
checked." Re-running `rank3_fourth_moment_probe.py` (unchanged; results
reproduced exactly in `results_rank3_fourth_moment_probe.json`) and cross-
checking with a new script, `rank3_fourth_moment_mod3_probe.py` (results in
`results_rank3_fourth_moment_mod3_probe.json`), shows this is not quite
right as stated: at \(N=20000\), \(q=3\) gives \(1.484566\) and \(q=6\)
gives \(1.484700\) — about \(3\%\) below the \(\approx1.5259\) band that
\(q=5,7,10,15,30\) and every non-squarefree \(q\) checked land in, not
matching it "to at least four digits."

The new script checks two things: whether this \(q\in\{3,6\}\) gap is a
finite-\(N\) artifact tied to \(N=20000=2^5\cdot5^4\) (coprime to 3), and
what actually governs it.

- **\(N\)-sweep at fixed \(q\in\{3,5,6,10\}\), \(N=4000\) to \(128000\):**
  the gap between \(q\in\{3,6\}\) and \(q\in\{5,10\}\) is present at every
  \(N\) tested and does not shrink (e.g. at \(N=128000\):
  \(q=3\to1.490907\), \(q=6\to1.490930\), vs. \(q=5\to1.529912\),
  \(q=10\to1.529914\) — a gap of \(\approx0.039\), the same width as at
  \(N=4000\)). This rules out a finite-\(N\) artifact: the gap is a
  persistent \(O(1)\) feature, not decaying noise.
- **Second independent \(N=21000\) (divisible by 3), full original
  \(q\)-list:** \(q=9,12,15,18,30\) — all divisible by 3, but with
  \(|\mu(q)|/\phi(q)\le1/6\) — land back in the \(\approx1.52\) band
  (\(1.520073\), \(1.520073\), \(1.519912\), \(1.520073\), \(1.519912\)
  respectively), matching \(q=4,8,16,20,25\) (not divisible by 3) closely.
  Only \(q=3,6\) themselves, with the largest \(|\mu(q)|/\phi(q)=1/2\)
  after \(q=2\)'s \(1\), stay low (\(1.478910\), \(1.479037\)).

So the deviation of \(Z^*_{(q)}/(\phi(q)N^3)\) from the common
\(\approx1.5259\) band is governed by \(|\mu(q)|/\phi(q)\) — the relative
weight of the bias-subtraction term \(P_{q,a}\) itself — not by
squarefreeness or by \(3\mid q\) as such: \(q=2\) (weight \(1\)) deviates
most (\(\approx0.864\)); \(q=3,6\) (weight \(1/2\)) deviate next most
(\(\approx1.48\)); \(q=5,7,10\) (weight \(1/4,1/6,1/4\)) and every
\(q\ge9\) checked (weight \(\le1/6\)) sit within a percent or so of
\(1.5259\). This is consistent with, and refines, the reading in Section 2
above: \(Z^*_{(q)}\) is \(\Theta(\phi(q)N^3)\) with an \(O(1)\) constant
depending mildly on \(|\mu(q)|/\phi(q)\) (largest at \(q=2\), shrinking
toward a common limit as \(|\mu(q)|/\phi(q)\to0\)), never an \(N\)-power or
even a clear \(q\)-power saving. `RANK3_QUARTIC_TOOLS.md` §2 has been
corrected in place to state this precisely rather than "the same constant
to four digits," with a pointer to this document for the full data; its
core conclusion (no order-of-magnitude saving, for any \(q\ge2\) checked)
is unaffected by the correction.

## 4. Where this leaves rank 3's fourth moment

- **Section 1** is a completed, negative result: three natural arc-transfer
  mechanisms for \(Z_{(q)}\) (full-circle comparison, Hölder/interpolation,
  finer binomial expansion) are tried directly rather than only ruled out
  by citing why \(U_{(q)}\)'s mechanism fails, and all three are shown to
  reduce to the same irreducible core, \(\int_{I_{q,a}}|F_N|^4\), bounded
  at trivial order by every tool named in UPPER_BOUND.md or
  `RANK3_SCOPE.md` in this \(q\)-range.
- **Section 2** is a completed, negative literature finding, sharpened
  beyond `RANK3_QUARTIC_TOOLS.md` §4's "wall": the full-circle version of
  \(Z_{(q)}\)'s irreducible core is not merely lacking a known bound — by
  Montgomery–Vaughan's classical mean-square theorem for Goldbach's
  problem (recollected, not independently verified in this environment),
  it is *provably* \(\Theta(N^3)\), so no tool of any kind could supply a
  power-saving for it. Any eventual bound on \(\sum_{2\le q\le R_0}
  Z_{(q)}\) has to come entirely from the arc-restriction, and Section 1
  shows the tools on hand ((V), (LS)) do not supply that saving at
  \(q\lesssim N^{2/5}\subset[2,R_0]\).
- **Section 3** corrects a numerical overclaim in `RANK3_QUARTIC_TOOLS.md`
  §2 with more data, without changing its conclusion: the residual
  \(q\)-dependence in \(Z^*_{(q)}/(\phi(q)N^3)\) tracks
  \(|\mu(q)|/\phi(q)\), an \(O(1)\) effect, not an \(N\)-power saving.

**The wall, stated precisely:** what would still be needed is a genuinely
new, unconditional bound on \(\int_{I_{q,a}}|F_N|^4\,d\alpha\) — the raw,
unrestricted local fourth moment of the prime exponential sum on a single
arc of width \(\sim1/(qN)\) — that beats the trivial order at
\(q\lesssim N^{2/5}\), summed over \(q\le R_0\). This document does not
find such a bound, and Section 2 gives an unconditional reason (not merely
an unsuccessful search) why the natural places to look for one — the
\(L^4\) large sieve, \(L\)-function fourth moments, Vinogradov-type mean
value theorems, and the classical Goldbach-representation second-moment
literature — either cannot supply a structure-free version of it or answer
a differently-shaped question. This is consistent with, and extends,
`RANK3_SCOPE.md` §3's conclusion that no route it names is costed to
completion, and `RANK3_QUARTIC_TOOLS.md` §4's finding that \(Z_{(q)}\) has
no known candidate tool: this document looked at the arc-transfer question
directly (rather than only citing why one specific mechanism fails) and at
one further literature direction (the classical Goldbach second-moment
theory, rather than only large sieves and \(L\)-function moments), and
still finds no route past this range, for reasons this document can name
precisely rather than only report as absent.

This document assumes and establishes nothing about zeros of
\(L\)-functions or the Riemann Hypothesis, does not weaken the definitions
of \(Z_{(q)}\), \(R_0\), or the reduced-residue/coprimality conditions, and
is: a direct three-mechanism arc-transfer attempt (§1), a literature
connection with an explicit, appropriately-hedged citation (§2), and a
numerical correction backed by a new script and its output (§3,
`rank3_fourth_moment_mod3_probe.py`,
`results_rank3_fourth_moment_mod3_probe.json`).

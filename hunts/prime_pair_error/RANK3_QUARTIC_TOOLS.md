# Route F: is there any q-averaged unconditional tool for the fourth moment?

**A note on sources.** This attempt's assignment describes a file
`RANK3_TOOLS.md` (Section 3: a second-moment identity for \(U_{(q)}\), which
does not apply to \(Z_{(q)}\), verified in `rank3_identity_check.py`) and asks
whether any unconditional, \(q\)-averaged tool could bound
\(\sum_{2\le q\le R_0}Z_{(q)}\). Neither `RANK3_TOOLS.md` nor
`rank3_identity_check.py` exists anywhere in this worktree (checked by
`grep -rl RANK3_TOOLS .` and `find . -iname '*rank3_tools*'`, both empty, and
`find . -iname '*identity_check*'`, also empty). What this worktree does
contain, and what matches the assignment's description almost verbatim, is
`RANK3_ROUTE_D.md`: its Section 3 derives the exact second-moment identity
(D7) for \(U_{(q)}\) (Parseval, summed over residues, a Ramanujan-sum-weighted
diagonal-plus-cross-term decomposition), and its Section 7, "As far as
possible for \(Z_{(q)}\)," shows this does not extend to \(Z_{(q)}\): the
full-circle analogue of \(Z_{(q)}\) Parseval-reduces to a quadruple additive
convolution \(Y(b_1,b_2,b_3,b_4)=\sum_{n_1+n_2=n_3+n_4}d_{b_1}(n_1)\cdots\),
\(d_b(n)=\Lambda(n)\mathbf1_{n\equiv b(q)}-1/\phi(q)\) — an additive-energy-type
object, not a sum of squares of \(\Delta(t;q,b)\), because there is no
\(K_N\)-convolution turning \(d_b\) into its own partial sums the way there is
for \(U_{(q)}\)'s \(T(q,b)\) (RANK3_ROUTE_D.md §7, first point). This document
proceeds on the working assumption that `RANK3_ROUTE_D.md` is the source
being described (its content is otherwise an exact match) and that
`rank3_identity_check.py` is either a name for verification done by hand
in that document's exact-algebra derivation, or a script that exists in a
sibling attempt's worktree and has not landed here. If a differently-named
`RANK3_TOOLS.md` exists elsewhere with content beyond what `RANK3_ROUTE_D.md`
already supplies, it was not available to produce this document, and whoever
next holds both should reconcile them. This document is filed under a new
name, `RANK3_QUARTIC_TOOLS.md`, rather than recreating `RANK3_TOOLS.md`,
because several attempts are working this same item in parallel and cannot
see each other's output; picking the name the assignment quotes risked a
collision this attempt cannot detect or avoid.

Notation throughout is UPPER_BOUND.md's, RANK3_SCOPE.md's, and
RANK3_ROUTE_D.md's: \(F_N,K_N,\Lambda,\psi,\mu,\phi\) as in UPPER_BOUND.md
§1; \(P_{q,a},R_{q,a},U_{(q)},Z_{(q)}\) as in UPPER_BOUND.md §6 and
RANK3_SCOPE.md §1; \(Q=\lfloor\sqrt N/3\rfloor\), \(R_0=Q/L\), \(L=\log N\).
This document assumes RANK3_SCOPE.md, RANK3_ROUTE_D.md, and
RANK3_MEAN_VALUE_TOOLS.md as already established and does not re-derive
their content.

## 1. What is already on record

RANK3_MEAN_VALUE_TOOLS.md §6 already searched one specific candidate class —
the multiplicative large sieve and its consequences (Bombieri-Vinogradov,
Barban-Davenport-Halberstam) — for a \(Z_{(q)}\) tool, and found none: (BDH)
is a second-moment tool, \(Z_{(q)}\) is a fourth moment, and RANK3_ROUTE_D.md
§7 shows the fourth moment does not even reduce to \(\Delta(t;q,b)\)-type
quantities structurally, independent of what estimate is available for
\(\Delta\). RANK3_ROUTE_D.md §7 separately shows \(Z_{(q)}\)'s integrand
carries no \(|P_{q,a}|^2\) decay factor, so no arc-transfer argument of the
kind that works for \(U_{(q)}\) (§4 there) is available either — a *second*,
independent obstruction on top of the missing moment estimate itself. This
document's task, as assigned, is to look further than (BV)/(BDH) specifically
— at any other unconditional, \(q\)-averaged tool — and to report what is
found, including a negative finding if that is what results.

## 2. A structural fact not previously recorded: \(Z_{(q)}\) does not vanish on non-squarefree \(q\)

RANK3_ROUTE_D.md §4 records, as a byproduct of (D11), that \(U_{(q)}\)
vanishes identically for every non-squarefree \(q\), because \(\mu(q)=0\)
forces the leading coefficient of (D11) to zero. The same fact does **not**
hold for \(Z_{(q)}\), for a more basic reason than any estimate: by
UPPER_BOUND.md §6's own definition, \(P_{q,a}(\beta)=(\mu(q)/\phi(q))K_N(\beta)\)
is identically the zero function whenever \(\mu(q)=0\), for **every** \(a\).
Consequently \(R_{q,a}=F_N-P_{q,a}=F_N\) exactly, on every arc, for every
non-squarefree \(q\), and
\[
 Z_{(q)}=\sum_{a\bmod q}^*\int_{I_{q,a}}|F_N|^4\,d\alpha
 \qquad(\mu(q)=0),
\]
with no bias-subtraction of any kind. This is exact algebra from
UPPER_BOUND.md's own definitions (D0), not a new estimate, and is checked
numerically below rather than only asserted. Two consequences:

- **The non-squarefree part of rank 3's \(q\)-range is not a smaller or
  easier sub-problem than the squarefree part; if anything it is the same
  difficulty as the already-unresolved minor-arc moment \(I_Q\)**, restricted
  to a union of arcs near low-order rationals rather than to the minor arc
  set as a whole. Any tool that hoped to exploit \(U_{(q)}\)'s
  squarefree-only support (a simplification RANK3_ROUTE_D.md notes but does
  not use, since Route A's uniformity gap already blocks \(U_{(q)}\)
  everywhere) has no analogous shortcut available for \(Z_{(q)}\): a positive
  proportion of \(q\le R_0\) — density \(1-6/\pi^2\approx0.392\) — contributes
  to \(\sum_{q\le R_0}Z_{(q)}\) with *no* structural bias-subtraction at all.
- This sharpens, rather than changes, the conclusion of RANK3_MEAN_VALUE_TOOLS.md
  §6: any candidate \(q\)-averaged tool for \(Z_{(q)}\) has to work for the
  raw local fourth moment of \(F_N\) itself near a positive-density family of
  small denominators, not merely for a "residual" quantity that is small away
  from where the model already explains it.

**Numerical check.** `rank3_fourth_moment_probe.py` (results in
`results_rank3_fourth_moment_probe.json`) computes the full-circle analogue
\(Z^*_{(q)}=\sum_a^*\int_{\mathbb T}|R_{q,a}|^4\,d\beta\) exactly (DFT
quadrature at \(M\ge4N\) points, exact for this band-limited quartic
quantity — self-checked against Parseval's identity for the matching second
moment and against doubling \(M\), both exact to float64 precision) directly
from the true von Mangoldt function, for \(N=20000\) and \(q=2,\dots,30\).
\(Z^*_{(q)}/(\phi(q)N^3)\) — the natural per-residue trivial-order
normalization — lands within a narrow, bounded band around \(\approx1.5259\)
for every non-squarefree \(q\ge3\) checked (e.g. \(q=4,8,9,12,16,18,20,25\)
land at \(1.525934\) to six digits) and every squarefree \(q\ge3\) with
\(|\mu(q)|/\phi(q)\) small (e.g. \(q=15,30\), weight \(1/8\), land at
\(1.525756\)). This is **not**, however, a single constant to four digits
across every \(q\ge3\): \(q=2\)
(\(\phi(2)=1\), weight \(|\mu(q)|/\phi(q)=1\)) shows the largest deviation
(\(Z^*_{(2)}/(\phi(2)N^3)\approx0.864\)), and \(q=3,6\) (weight \(1/2\), the
next-largest after \(q=2\)) show a real, non-noise deviation of their own,
landing at \(\approx1.4846\) — about \(3\%\) below the \(1.5259\) band, not
matching it to four digits. `rank3_fourth_moment_mod3_probe.py`
(results in `results_rank3_fourth_moment_mod3_probe.json`), written to
check whether this \(q=3,6\) gap was a finite-\(N\) artifact of
\(N=20000=2^5\cdot5^4\) (coprime to 3), finds it is not: the same
\(\approx0.039\)-wide gap between \(q\in\{3,6\}\) and \(q\in\{5,10\}\)
persists, without shrinking, across \(N=4000\) through \(N=128000\), and at
a second, independent \(N=21000\) (divisible by 3) the full \(q\)-list shows
the deviation tracking \(|\mu(q)|/\phi(q)\) directly — \(q=9,12,15,18,30\)
(all divisible by 3, but each either non-squarefree, weight \(0\), or with
weight \(|\mu(q)|/\phi(q)=1/8\)) sit back in the \(1.52\) band, while only
\(q=3,6\) themselves (weight \(1/2\)) stay low.
So the deviation from \(1.5259\) is governed by \(|\mu(q)|/\phi(q)\) — the
relative size of the bias-subtraction \(P_{q,a}\) — not by squarefreeness or
by \(3\mid q\) as such; see `RANK3_QUARTIC_LITERATURE.md` §3 for the full
data and this reading. §2's structural point stands with this correction:
the bias-subtraction changes the fourth moment by an \(O(1)\) multiplicative
factor that shrinks toward \(1\) as \(|\mu(q)|/\phi(q)\to0\), never by an
order-of-magnitude or \(N\)-power saving, for every \(q\ge2\) checked.

## 3. Candidate: a "quartic large sieve"

The natural next candidate, given that (BV)/(BDH) rest on the *multiplicative*
large sieve rather than the *additive* one (RANK3_MEAN_VALUE_TOOLS.md §1),
is to ask whether an analogous *quartic* large-sieve inequality exists —
on either side, additive or multiplicative — playing the role for
\(Z_{(q)}\) that (LS) plays for \(U_{(q)}\)'s dyadic-block bound (24)-(27),
or that (BDH) plays for \(U_{(q)}\)'s low-\(q\) range. None is found; the
reason is structural, not merely a citation gap.

**The additive large sieve (LS) is an \(L^2\) phenomenon with no \(L^4\)
analogue for general sequences.** (LS)'s proof (Montgomery-Vaughan,
*Multiplicative Number Theory I*, Theorem 6.7 and its additive dual;
Iwaniec-Kowalski, *Analytic Number Theory*, Theorem 7.7 and surrounding
material) is a Bessel's-inequality argument in Hilbert space: it holds for
*every* sequence \(b_n\) and *every* set of \(\delta\)-spaced points, with no
arithmetic input about \(b_n\) at all. A literal quartic analogue —
\(\sum_j|\sum_nb_ne(nx_j)|^4\ll(\text{something explicit in }N,\delta)\cdot
(\sum_n|b_n|^2)^2\), uniform over *all* sequences \(b_n\) and all
\(\delta\)-spaced \(x_j\) — is **false** in general: take \(b_n\) supported
on a generalized arithmetic progression or any set with large additive
energy (e.g. \(b_n=1_{n\in\{1,\dots,K\}}\), \(K\sim\sqrt N\)); then
\(\sum_n|b_n|^2\sim K\) while a single exponential sum \(\sum_nb_ne(nx)\)
already reaches size \(K\) at \(x=0\), giving \(|{\cdot}|^4\sim K^4\) against
\((\sum|b_n|^2)^2\sim K^2\) — no inequality of the shape (LS)'s quartic
analogue would demand can hold with a constant independent of the sequence's
own additive structure. This is the actual mechanism behind why the second
moment (Bessel/Plancherel) is universal and structure-free while the fourth
moment is not: \(L^2\) bounds are geometric (orthogonality), \(L^4\) bounds
are arithmetic (they measure additive energy, i.e. how often \(n_1+n_2=
n_3+n_4\) inside the support of \(b_n\)), and additive energy is exactly the
kind of quantity that depends on the fine structure of the set, not just its
size. For \(b_n=\Lambda(n)\), the only unconditional handle on this energy
used anywhere in UPPER_BOUND.md is Vaughan's pointwise bound (V) on
\(|F_N|\) itself, which RANK3_SCOPE.md §2 already shows gives no saving at
small \(q\); this document does not find a second, independent unconditional
handle on the same energy.

**The multiplicative side (a quartic moment of Dirichlet \(L\)-functions,
averaged over \(q\) and \(\chi\)) exists, but at the wrong strength and in
the wrong variable for this problem.** Fourth-power moments of Dirichlet
\(L\)-functions **on the critical line at a fixed point**, averaged over
\(q\le Q\) and \(\chi\bmod q\) — results in the spirit of Heath-Brown's
unconditional fourth moment of \(\zeta\) (Heath-Brown, "The fourth power
mean of Dirichlet's \(L\)-functions," *Analysis* 1 (1981), 25–32, and its
antecedents) — are a real, unconditional, power-saving tool of exactly the
kind (BDH) is for the second moment, and are genuinely different from (V):
they come from the functional equation and approximate functional equation
machinery, not from an elementary large-sieve duality, so they are not
subject to the argument two paragraphs above. But what \(Z_{(q)}\) needs,
after passing \(R_{q,a}\) through the explicit formula, is not a fourth
moment of \(L(1/2,\chi)\) at one point — it is a fourth moment **integrated
over a range of height \(t\)** corresponding to the arc \(|\beta|\le\delta_q\)
(width \(\sim1/(qN)\), translating to a range of \(t\) growing with \(N\)),
jointly averaged over \(q\) and \(\chi\). This is a genuinely harder,
"doubly-averaged" (family \(\times\) height) fourth-moment problem; it is not
the classical Heath-Brown-type statement, and this document does not find,
or have the means in this environment to search for, a named unconditional
result of that joint strength. Even granting one, two further steps this
document cannot supply would remain: (i) translating an \(L\)-function-side
bound back through the explicit formula reintroduces the zeros of
\(L(s,\chi)\) explicitly, the same kind of ineffective or GRH-adjacent input
this hunt's other documents (SW_EFFECTIVE.md, THEOREM_B_SEQUENCE.md) already
find recurring as a wall for comparable questions; (ii) even a fully
successful bound on the full-circle quartic moment would still need
RANK3_ROUTE_D.md §7's missing arc-transfer argument, since nothing on the
multiplicative side supplies one either.

## 4. Where this leaves rank 3's fourth moment

No candidate unconditional, \(q\)-averaged tool is found for
\(\sum_{2\le q\le R_0}Z_{(q)}\), beyond confirming and sharpening
RANK3_MEAN_VALUE_TOOLS.md §6's "no candidate" finding for the (BV)/(BDH)
route specifically:

- The additive large sieve (LS)'s exactness is an \(L^2\)-only phenomenon
  (Section 3); no structure-free quartic analogue can exist, so any quartic
  tool must come from the primes' own arithmetic (i.e. from (V) or a
  strengthening of it) — RANK3_SCOPE.md's Route C, not a new averaged
  mechanism.
- A genuine quartic moment tool exists on the multiplicative side (q-and-\(\chi\)
  averaged \(L\)-function fourth moments at a point), but it answers the
  wrong question — a fixed-height fourth moment, not the height-integrated
  one \(Z_{(q)}\) needs — and this document cannot determine, without a
  literature search this environment does not support, whether an
  integrated-in-height version is known unconditionally. This is the
  **wall**: not "no such theorem exists," which this document cannot prove,
  but "no such theorem is identified here, and identifying one requires a
  literature capability outside this attempt's tools."
- \(Z_{(q)}\)'s failure to vanish on non-squarefree \(q\) (Section 2, checked
  numerically) means even a hypothetical tool restricted to squarefree \(q\)
  — mirroring \(U_{(q)}\)'s free simplification — would leave a
  positive-density sub-range of rank 3 completely uncovered, at the same
  difficulty as the unresolved minor-arc moment \(I_Q\).
- The numerical measurement (Section 2) of \(Z^*_{(q)}\), the full-circle
  analogue, shows no visible saving at all — squarefree or not — for every
  \(q\ge3\) up to \(N=20000\), and no visible \(N\)-power or \(\log N\)-power
  saving at the single worst case \(q=2\) across \(N=2000\) to \(64000\). This
  is consistent with, and adds direct measurement to, the conclusion that no
  unconditional cancellation is being left unexploited by the tools already
  named and found insufficient (RANK3_SCOPE.md §2, RANK3_MEAN_VALUE_TOOLS.md
  §6): the trivial order is not merely the best *proved* bound, it appears to
  be the true order at this computational scale, for every \(q\ge3\) checked.

What would settle this precisely: (i) a named, unconditional, height-integrated
and \(q\)-averaged fourth-moment (or additive-energy) bound for
\(\sum_{n_1+n_2=n_3+n_4\le N}\Lambda\)-weighted quadruples restricted to
residue classes mod \(q\), summed over \(q\le R_0\) — Section 3 explains
precisely why this cannot be a structure-free large-sieve statement and must
instead come from prime-specific input; (ii) independently, a non-crude
arc-transfer argument for the fourth moment, which RANK3_ROUTE_D.md §7
already shows has no counterpart to the one used for \(U_{(q)}\); (iii)
separately, whatever (i) supplies must also cover the non-squarefree
sub-range, where no bias-subtraction exists at all (Section 2). None of the
three is supplied here. This is consistent with, and extends, RANK3_SCOPE.md
§3's conclusion that no route it names is costed to completion, and
RANK3_MEAN_VALUE_TOOLS.md's finding that \(Z_{(q)}\) has no known candidate
tool at all — this document looked further afield (a genuinely different
large-sieve mechanism, and the higher-moment \(L\)-function literature) and
still found none, for a structural reason (Section 3) rather than only an
unsuccessful search.

This document is: an exact structural observation from UPPER_BOUND.md's own
definitions (Section 2, first half), a direct numerical measurement backing
it (Section 2, second half; `rank3_fourth_moment_probe.py`,
`results_rank3_fourth_moment_probe.json`), and a structural argument
(Section 3) about why the second moment's universal large-sieve mechanism
has no quartic analogue, together with an explicit, honestly-labeled gap in
what this document could check about the \(L\)-function-side alternative. It
assumes and establishes nothing about zeros of \(L\)-functions or the
Riemann Hypothesis, and does not weaken the definitions of \(Z_{(q)}\) or
\(R_0\).

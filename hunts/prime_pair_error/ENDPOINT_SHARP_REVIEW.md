# Review of ENDPOINT_SHARP.md

Independent check, 2026-09-11. Read in order: `ENDPOINT_SHARP.md`,
`ENDPOINT_BOUND.md` (section 2 and equations (5), (10), (13), (14), (17),
(18)), `ENDPOINT_HALF.md` (including its correction notice), and
`SIEGEL_UNIFORMITY.md` sections 3-5. Two scripts were written from scratch
for this review and are not derived from `endpoint_sharp_mertens_probe.py`
or `endpoint_sharp_probe.py`:

- `review_a0075_mertens_check.py` (item 1)
- `review_a0075_character_check.py` (item 2)

Both were run with `/opt/zeta-venv/bin/python`; raw output is reproduced
inline below rather than saved to a separate JSON file.

## Item 1: the Mertens correction, section 2.1

**Verdict: defective**, in the finite illustration only. The asymptotic
claim, equation (A), is confirmed.

The algebra of equation (A) was rechecked by hand. Writing \(l=\log N\),
\(m+1=\lceil(2c/\kappa)\,l^\kappa/\log l\rceil\), and using Mertens'
theorem \(H_Z=\kappa\log l+M+o(1)\) at \(Z=\exp(l^\kappa)\):

\[
\log\frac{m+1}{eH_Z}=\kappa\log l-2\log\log l+O(1)=\kappa\log l\,(1+o(1)),
\]

so the exponent in (5') is \((m+1)\cdot\kappa\log l(1+o(1))=2c\,l^\kappa(1+o(1))\ge c\,l^\kappa\)
for large \(N\), and

\[
A(N)=\frac{m\log Z}{l}=\frac{m\,l^\kappa}{l}
=\frac{(2c/\kappa)\,l^\kappa/\log l\cdot l^\kappa}{l}
=\frac{2c}{\kappa}\cdot\frac{l^{2\kappa-1}}{\log l}(1+o(1)),
\]

which is exactly the document's (A). At \(\kappa=1/2\) this is
\(4c/\log l\to0\). This part is correct: the endpoint is attained, and
the argument that no fixed \(m\) works past \(\kappa=1/2\) (`ENDPOINT_HALF.md`
section 2.3) is correctly identified as an artifact of the elementary
bound \(H_Z\le1+\log Z\), not a real obstruction. My own script reproduces
`ENDPOINT_SHARP.md`'s own section 7 item (1) table almost exactly, using
an independent exact-prime sieve up to \(Z=e^{13}\) rather than reusing
the project's probe:

```
logZ= 5  exact=1.8798  mertens=1.8709  elementary(1+logZ)=6
logZ= 7  exact=2.2124  mertens=2.2074  elementary(1+logZ)=8
logZ= 9  exact=2.4598  mertens=2.4587  elementary(1+logZ)=10
logZ=11  exact=2.6599  mertens=2.6594  elementary(1+logZ)=12
logZ=13  exact=2.8266  mertens=2.8264  elementary(1+logZ)=14
```

(document: 1.880, 2.212, 2.460, 2.660, 2.827 against Mertens; matches to
the stated precision.)

**The defect.** Section 7 item (2)'s table, and the two crossover
sentences that quote it in section 2.1 ("\(A(N)<1\) from about
\(\log N=400\)" and "\(A(N)<1/2\) only from about \(\log N=4.7\times10^4\)"),
report a "retuned \(m\)" that is too small by exactly 2 at every row with
\(\log N\in\{100,400,10^4,10^6\}\), and so does not actually meet the
stated target decay \(\exp(-\sqrt l)\) at those rows. I verified this at
\(\log N=100\) with an exact prime sieve up to \(Z=e^{10}\approx22026\)
(2466 primes, 40-digit arithmetic, no Mertens approximation involved):

```
H_Z = 2.564650626927288538780604720642885262695
m=12: exponent = 8.10   (needs >= sqrt(100) = 10)   -- FAILS
m=13: exponent = 9.76   (odd, not admissible anyway) -- FAILS
m=14: exponent = 11.49  (needs >= 10)                -- first m that works
```

So the document's own \(m=12\) for this row gives decay only
\(\exp(-8.10)\), not the claimed \(\exp(-\sqrt{100})=\exp(-10)\); the
least even \(m\) that actually reaches the target is \(14\), not \(12\).
The same pattern (document's \(m\) two below the true least even \(m\))
holds at \(\log N=400\) (document 20, true 22), \(10^4\) (document 62,
true 64), and \(10^6\) (document 346, true 348; here I used Mertens'
formula for \(H_Z\) since exact enumeration to \(Z=e^{1000}\) is not
possible, matching what the document itself must have done at that
scale). At \(\log N=10^{10}\) and \(10^{20}\) the document's numbers
(16078 and \(6.2\times10^8\)) do match the true least even \(m\) exactly
in my independent search, so the error is confined to the four smaller
rows; the finite-precision search that generated section 7's table
appears to have an off-by-one-step bug that only shows up before the
asymptotic regime.

Correcting the table changes the reported \(A\) values (all understated
by the same margin: \(1.4\) not \(1.2\) at \(\log N=100\); \(1.1\) not
\(1.0\) at \(400\); \(0.64\) not \(0.62\) at \(10^4\); \(0.348\) not
\(0.346\) at \(10^6\)) and moves both quoted crossovers later. Using the
correct least-even-\(m\) search:

```
l=400     m=22   A=1.1000
l=676     m=26   A=1.0000   <- true crossover for A<1
l=47000   m=110  A=0.5074
l=53824   m=116  A=0.5000   <- true crossover for A<1/2
l=60000   m=120  A=0.4899
```

So: **the claimed crossovers are not right.** \(A(N)<1\) first holds
around \(\log N\approx676\), not \(400\) (the document's own \(400\) row
in fact has \(A=1.1>1\) once computed with an \(m\) that really meets the
target); \(A(N)<1/2\) first holds around \(\log N\approx5.4\times10^4\),
not \(4.7\times10^4\) (at \(4.7\times10^4\) the correct value is
\(A\approx0.507>1/2\), just short). Both errors run in the same
direction: the document is about 1.15-1.7x too optimistic about how soon
the decay sets in.

This does not touch the two things that actually matter for the proof:
equation (A) itself is algebraically correct (checked above), \(A(N)\to0\)
as \(l\to\infty\) at \(\kappa=1/2\) is correct, and \(\kappa>1/2\)
genuinely fails by the same equation (the numerator exponent
\(2\kappa-1>0\) then, so \(A(N)\to\infty\)). The defect is confined to the
specific integers in section 7's second table and the two sentences in
section 2.1 that repeat them; the corrected statement is: \(A(N)<1\) from
\(\log N\gtrsim676\), and \(A(N)<1/2\) from \(\log N\gtrsim5.4\times10^4\).

## Item 2: the modulus factor, section 4, case \(q\nmid r\)

**Verdict: confirmed.**

*Cancellation claim.* I rebuilt real primitive characters from scratch
(not using a library Dirichlet-character routine): the Jacobi symbol for
odd squarefree conductors, and explicit \(\chi_4\), \(\chi_8^{\pm}\) for
the two 2-power conductors, combined multiplicatively by CRT for
conductors \(q=m\), \(4m\), \(8m\). For every such \(\chi\) of conductor
\(q\le200\) (119 characters), every proper divisor \(g\mid q\), and every
residue \(a\bmod g\) with \((a,g)=1\), I summed \(\chi(c)\) over the coset
\(\{c\bmod q:(c,q)=1,\ c\equiv a\ (g)\}\): 3540 cosets tested, zero
exceptions. This is 37x more cases than the document's own 96-coset check
in section 7 item (3), and it agrees with the claim exactly: the sum
always vanishes, because \(\chi\) primitive of conductor \(q\) cannot be
trivial on \(K=\ker((\mathbb Z/q)^*\to(\mathbb Z/g)^*)\) when \(g<q\)
(triviality there would make \(\chi\) induced from a character mod
\(g\), contradicting primitivity of conductor \(q\)).

I also checked, separately, that the "\((a,g)>1\)" branch the document
disposes of in one line is in fact unreachable rather than merely rare:
since \(g=\gcd(q,r)\mid r\), \((a,r)=1\) forces \((a,g)=1\) always (a
common factor of \(a\) and \(g\) would be a common factor of \(a\) and
\(r\)). Brute force over \(q,r<60\) and \(a\) up to \(65\) found 0
violations, as expected. This is a harmless redundancy in the text, not
an error.

*Error bound (4.1)-(4.2).* I redid the algebra by hand. From \(X=u/M\),
\(W=V(Z)M/\phi(M)\), \(M=rq/g\):

\[
\frac{\phi(q)}{\phi(g)}XW\le\frac{q}{g}\cdot\frac{ug}{rq}\cdot V(Z)\frac M{\phi(M)}
=\frac ur\,V(Z)\frac M{\phi(M)}\ll\frac ur\,V(Z)\log l,
\]

using \(M\le rq<Z^2\) so \(M/\phi(M)\ll\log\log M\ll\log l\); this matches
the document's bound exactly. Continuing with \(u/r\le N\),
\(bV(Z)=1\), \(b\ll\sqrt l\), \(q<Z=e^{\sqrt l}\), and the total-variation
bound on \(u\mapsto u^{\beta-1}\):

\[
b\Big|\int_1^yu^{\beta-1}dT(u)\Big|\ll N(\log l)e^{9-s}+bqD_0\ll N(\log l)e^{9-s}+l^{1/2}e^{\sqrt l}D_0,
\]

again matching (4.2) exactly. Absorption at both level choices checks
out asymptotically: with \(D_0=N^{o(1)}\), the second term is
\(N^{o(1)}e^{(1+o(1))\sqrt l}\), and since \(N=e^l\) with \(l\gg\sqrt l\)
this is \(\ll N\exp(-\gamma\sqrt l)\) for any fixed \(\gamma\) once \(N\)
is large; with the \(\beta\)-sieve's \(D_0=N^{1/2}\), the second term is
\(N^{1/2+o(1)}e^{\sqrt l}=e^{l/2+O(\sqrt l)}\), again \(\ll e^{l-\gamma\sqrt l}\)
for large \(l\) since \(l/2<l(1-o(1))\). Both hold with a full power of
\(N\) to spare, as claimed.

I looked for other places in section 4 where a factor of \(q\), \(\phi(q)\),
or a residue-class count could have been dropped: the untwisted part
(\(b\prod_{p<Z,p\nmid r}(1-1/p)=r/\phi(r)\)), the \(q\mid r\) twisted part
(single residue class, no extra factor needed), and the assembly into
(1') at the end of section 4 all carry their multiplicities correctly.
No further dropped factor found.

## Item 3: are \(E_{\rm corr}^{(Z)}\) at the two values of \(Z\) kept separate

**Verdict: confirmed.**

Every one of the twelve places `ENDPOINT_SHARP.md` mentions
`ENDPOINT_BOUND.md` (lines 5, 6, 28, 39, 47, 68, 91, 95, 111, 136, 170,
202, 216, 351, 381, 391 by grep) either (a) reuses the generic
architecture with the parameter substituted (sections 2-3, which is
legitimate: it is the same lemma applied at a different \(t\) and
\(D_0\), not a claim that the two final bounds are the same object), or
(b) explicitly disclaims comparability (the boxed-result discussion at
the top, and section 6's "For the original \(E\)" paragraph, which states
outright that the two versions are "not comparable term by term" because
the exceptional class differs). I found no place where a bound proved at
one \(Z\) is used to conclude something about the corrected quantity at
the other \(Z\), and no place where the two are silently identified.

The description of the two exceptional-class ranges is also right: going
from \(Z_1=\exp(l^{1/10})\) to \(Z_2=\exp(\sqrt l)\), the conductor range
\(q<Z\) widens (\(Z_2>Z_1\)) while the exceptional threshold
\(\beta>1-c_0/\log Z\) tightens (\(c_0/\log Z_2<c_0/\log Z_1\), so fewer
zeros qualify as exceptional at the larger \(Z\)). Because \(r(h)\) is
fixed (built from the true \(\Lambda\)) but \(C_N\) depends on \(Z\)
through both \(\nu\) (support of the sieve, present even with no
exceptional zero at all) and the exceptional term when one exists,
\(E_{\rm corr}^{(Z_1)}\) and \(E_{\rm corr}^{(Z_2)}\) are different
quantities in general, including in the no-exception case; there is no
generic inequality forcing one to dominate the other, and the document
does not assert one. This is a correct scoping statement, not a proved
non-domination theorem, and the document does not claim more than that.

Section 6's statement for the original \(E\) is correctly scoped: it
gives the bound at this \(Z\), names the exceptional term's dependence on
\(q,\beta\) explicitly (not deleted), and states plainly that it is "not
comparable term by term" with `ENDPOINT_BOUND.md` section 7's version.

## Item 4: input (1') from Davenport, Page, and the fundamental lemma

**Verdict: unresolved for the primary-source check; the internal
derivation logic is confirmed.**

I do not have web access in this environment and did not check
Davenport's *Multiplicative Number Theory* Chapter 20 or Page's 1935
theorem against a primary source; I can only say what I checked
internally. What would settle this fully is fetching the actual chapter
and theorem statement and comparing constants; I did not do that and am
saying so plainly rather than guessing.

What I did check, against my own recollection of the standard statements
(the general shape of the prime-number-theorem-in-progressions with an
explicit exceptional-zero term, and Page's uniqueness theorem for a real
exceptional zero among characters of bounded conductor), is that the
document's citations (D) and (Pg) are the right shape for those classical
results, and that the four-case derivation built on top of them is
internally consistent:

- \((a,r)>1\): \(a(n)=0\) on \(B\) is correct (every \(n\in B\) shares a
  factor \(p\mid(a,r)\) with \(p<Z\), which is inside the sieve modulus
  \(P\)); the \(\Lambda\)-side bound \(\omega(r)\log y\) is valid, though
  loose (\(\omega(r)\ll\sqrt l\), not \(\ll l\), for \(r\le R<Z\); the
  document's \(\ll l^2\) bound still holds, just not tightly, and nothing
  downstream needs it tight).
- \((a,r)=1\), untwisted: the sieve computation
  \(b\prod_{p<Z,p\nmid r}(1-1/p)=r/\phi(r)\) is correct because every
  prime factor of \(r\) is \(<Z\) (since \(r\le R<Z\)).
- \((a,r)=1\), \(q\mid r\): the claim that Davenport's \(\chi_1\) (induced
  by a primitive \(\chi_1^*\) of conductor \(q_1\mid r\)) must coincide
  with the document's model character \(\chi\) follows from (Cmp)+(Pg):
  fixing \(c_0\le c_4\) makes any TT-shaped exceptional zero at this
  \(Z\) automatically the unique Page-exceptional zero, so if Davenport's
  middle term is present at all, its character is the same \(\chi\).
  Given that, \(\chi_1(a)=\chi(a)\) for \((a,r)=1\) is immediate from the
  definition of an induced character.
- \((a,r)=1\), \(q\nmid r\): checked in item 2 above.

On (Cmp) itself: \(c_0\) here is not a constant inherited from Tao and
Teräväinen's own proof of Proposition 2.2 (that proposition is explicitly
not used at this endpoint; see the document's own "Remark 2.8 is not
used"). It only appears in this document's own definition of "exceptional"
(the shape of TT Definition 2.1 is reused, not its proof), so constraining
it to \(c_0\le c_4\) is a free choice available to whoever writes this
argument, not a violation of an external constraint. I did not trace
every other use of \(c_0\) across the rest of the project (that would
require reading `EXCEPTIONAL_ENERGY.md` and `LOCALIZED_MIXED_ENERGY.md`
in full, which the assigned reading list for this review does not
include); `ENDPOINT_HALF.md` section 2.2 already traces the one place
those two files use a \(Z\)-dependent range and finds it a bookkeeping
substitution, not a break, which this document's section 5 relies on
without re-deriving it.

## Item 5: the budget assembly, equation (18')

**Verdict: confirmed.**

Term by term against `ENDPOINT_BOUND.md` equation (18), with \(t\to\sqrt l\)
and \(D_0\to N^{A(N)}\):

- \(N^3R^7e^{-2\gamma t}\to N^3e^{-(2\gamma-7\sigma)\sqrt l}\): matches,
  using \(R=e^{\sigma\sqrt l}\).
- \(N^3R^{-1/6}\to N^3e^{-\sigma\sqrt l/6}\): matches.
- \(N^{14/5}\): unchanged, matches.
- \(N^2D_0\sqrt Z\to N^{2+A(N)}e^{\sqrt l/2}\): matches, using
  \(D_0=N^{A(N)}\), \(\sqrt Z=e^{\sqrt l/2}\).
- the two direct exponential terms carry over unchanged.

I rechecked the absorption conditions by hand. Requiring
\(N^{2+A(N)}e^{\sqrt l/2}\le N^3e^{-c'\sqrt l}\) reduces to
\((2+A(N))l+\sqrt l/2\le3l-c'\sqrt l\), i.e.
\(A(N)\le1-(c'+1/2)/\sqrt l\), exactly the condition the document states;
since \(A(N)=4c/\log l\to0\) this holds for large \(N\) (both sides
converge, left to \(0\), right to \(1\)), and it would hold with more
room using the \(\beta\)-sieve's fixed \(A(N)=1/2\) as noted. Requiring
\(2\gamma-7\sigma>0\) with \(\sigma\le\gamma/20\) gives
\(2\gamma-7\sigma\ge2\gamma-7\gamma/20=33\gamma/20>0\), so the first term
does decay; \(\sigma/6>0\) trivially for the second. \(N^{14/5}=N^3e^{-l/5}\)
is far below any \(N^3e^{-c'\sqrt l}\) rate since \(l/5\gg\sqrt l\)
eventually, so calling it "a fixed power below \(N^3\)" understates how
comfortably it is absorbed but is not wrong.

The four-input account of what fixes the exponent at \(1/2\) (divisor
approximation via (A); the classical progression error
\(\exp(-c\sqrt{\log y})\), which does not improve with \(\kappa\); the
fundamental lemma parameter \(s=\log D_0/\log Z\), which stops growing
fast enough past \(\kappa=1/2\); and the singular-series truncation,
which is the only one of the four that improves with \(\kappa\)) is a
correct restatement of what the preceding sections establish; it does not
introduce a new equation to check beyond (18').

## Summary

| Item | Verdict |
| --- | --- |
| 1. Mertens correction (section 2.1, eq. (A)) | Defective (finite table/crossover numbers only; the asymptotic equation (A) is confirmed) |
| 2. Modulus factor (section 4, eq. (4.1)-(4.2)) | Confirmed |
| 3. Two values of \(Z\) kept distinct | Confirmed |
| 4. Input (1') from classical sources | Unresolved (no primary-source check performed); internal logic confirmed |
| 5. Budget assembly (eq. (18')) | Confirmed |

The one confirmed defect is narrow: section 7 item (2)'s table and the
two sentences in section 2.1 quoting it understate the least even \(m\)
needed to reach the stated target decay by 2 at \(\log N\in\{100,400,10^4,10^6\}\),
which pushes the two named crossovers (\(A<1\), \(A<1/2\)) later than
claimed (about \(\log N\approx676\) and \(\approx5.4\times10^4\), against
the document's \(400\) and \(4.7\times10^4\)). Equation (A) itself, the
claim that the endpoint \(\kappa=1/2\) is attained, and the claim that
\(\kappa>1/2\) is not reachable by this device are all algebraically
correct and unaffected by this table error.

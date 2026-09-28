# 08. Why It Is Hard: An Honest Failure Catalogue

## The short version

The mathematical tools in this repository have proved many useful statements.
Their current estimates do not by themselves establish RH. That is not a
proof that every use of those techniques has a ceiling below RH.

**Scope correction, 2026-09-12.** This catalogue is not a list of forbidden
research methods. Its former method-wide closure claims and blanket dismissal
of computation as evidence were too broad. The owner-directed mandate in
[ALIGNMENT.md](../ALIGNMENT.md) permits original mathematics toward RH and
useful intermediate results while retaining proof and review requirements.

The [previous catalogue is preserved unchanged](../history/research-guidance-2026-09-12/failure-catalogue.md)
for its historical examples and source notes. This revision corrects the scope
of the conclusions, not the underlying experiments. It is not a fresh audit of
every source or a current-record survey.

Use four distinct descriptions: a candidate is refuted; a theorem obstructs a
specified restricted class; an attempt remains unresolved; or work is paused
by allocation. Only a proof with matching hypotheses establishes a class-wide
obstruction. Neither a failed search nor an unproved estimate supplies one.

---

## 1. The scoreboard: what transform methods actually deliver

### 1.1 Zero-free regions

The classical de la Vallee Poussin and Vinogradov-Korobov regions illustrate
a precise distinction: a bound excluding zeros only in a region that shrinks
toward `Re(s) = 1` does not imply exclusion in the whole fixed half-plane
`Re(s) > 1/2`.

Improving only a constant in that displayed shrinking region does not turn
it into a fixed strip. This is a limitation of that inference, not a theorem
that Mellin transforms, contour integration, exponential-sum methods or the
explicit formula can never supply additional information.

A new estimate that would imply a fixed zero-free strip can be a research
target. It does not require assuming the strip first. State the estimate,
prove its implication and identify what additional arithmetic the attempt uses.
For classical statements and historical constants, consult the source notes
in the archived catalogue and verify the precise version before using one.

### 1.2 Zero-density estimates

A density estimate bounds how many zeros can lie in a region. Such an upper
bound may permit a finite exceptional set and therefore need not establish
that no off-critical zero exists. It neither proves that an exceptional zero
exists nor rules out combining density information with another mechanism.

Do not describe a density theorem as an RH proof. Equally, do not dismiss
new density or large-value estimates as incapable of contributing to a larger
argument merely because their statement alone is weaker than RH. A proposed
combination owes the full implication, with every error term retained.

### 1.3 A positive proportion on the line: and why that is not "all"

A positive-proportion theorem is a genuine counting result. Even a proportion
arbitrarily close to one need not by itself exclude all off-line zeros. It
is not a percentage of RH solved, but that does not erase the theorem's
value or establish a universal limit on counting methods.

Mollifier lengths, Fourier support, moment orders and available correlation
estimates can constrain a particular argument. A claimed optimum or ceiling
must name those restrictions and its proof. A finite optimizer's best output
is not automatically a bound on the whole admissible class. New arithmetic,
new invariants or a different construction may fall outside a proved
restricted-class obstruction; their success still has to be demonstrated.

---

## 2. The parity problem

Parity obstructions concern specified sieve axioms and the information those
axioms can distinguish. A theorem showing that this information does not
suffice is substantive and must be respected. It is not a prohibition on all
elementary or sieve-related research.

For an attempted application, identify the exact axiom set, the indistinguishable
examples and the requested conclusion. If an argument adds a bilinear estimate
or another input outside that axiom set, evaluate that input rather than
assuming the original obstruction automatically covers it. Conversely, merely
renaming or rearranging the same information does not evade a proved barrier.

The classical elementary PNT and the asymptotic-sieve examples discussed in
the archived catalogue illustrate why the scope matters. They are not blanket
licenses to claim that a new RH estimate has been obtained.

---

<a id="3-why-numerical-verification-cannot-help"></a>
## 3. What numerical verification can and cannot establish

### 3.1 What has been checked

Rigorous finite-range zero counts are theorems about their stated range.
Floating-point scans without complete sign and zero-count control have a
weaker status. Neither automatically establishes an assertion over all heights.
Use `zeta/zeros.py`, `zeta/rigor.py` and their actual completeness and
precision contracts; report an undecided check as undecided.

A computer-assisted proof may combine a verified finite certificate with a
proved reduction or a uniform tail estimate. The complete chain matters.
There is no rule that a result involving computation cannot be mathematical
progress. There is a rule against substituting a large sample for that chain.

### 3.2 The relevant quantity crawls

A short observed range may not reveal eventual asymptotic behavior, especially
when the quantity grows slowly or the constants are large. Precision studies,
held-out ranges and independent implementations can detect some errors and
support a candidate, but are not substitutes for a uniform argument.

Conversely, experiments can expose false conjectures, locate extremizers,
identify missing terms and suggest constructive lemmas. Their value should be
judged by the statement actually tested, not denied in advance.

### 3.3 Littlewood, Skewes, and the limits of numerical intuition

Littlewood's sign-change theorem is a warning that a long observed sign
pattern can fail later. It is not a theorem that all numerical evidence is
useless or that a computation-supported proof must contain a bug. Preserve
both the finite observations and the theorem that limits their extrapolation.

### 3.4 Mertens: a numerical pattern that did not give a uniform proof

The disproved Mertens conjecture is another warning against inferring a
uniform inequality from finite agreement. Distinguish that conjecture from
the weaker family of bounds equivalent to RH. Refuting a stronger statement
does not refute RH, and it does not prohibit another use of Mobius sums.

The source examples in the archived catalogue remain available. An unexpected
new result calls for checking assumptions, arithmetic, precision, truncation
and independent evidence, not automatic promotion or automatic rejection.

---

## 4. The counterexamples that should govern your intuition

### 4.1 Functional equation alone: Davenport-Heilbronn

Davenport-Heilbronn provides a useful rival: it shares important analytic
symmetries with zeta but has off-critical zeros and lacks zeta's scalar Euler
product. An implication whose complete hypotheses hold for that rival while
its conclusion fails is refuted.

The words "functional equation" are not a complete hypothesis list. Check
normalization, analytic class, coefficient conditions, growth and every
arithmetic input before claiming the rival refutes a proposed proof.
A lemma shared with the rival may be a valid and useful intermediate step.
The full argument must supply the distinguishing information somewhere; not
every intermediate lemma has to do so by itself.

### 4.2 Euler product alone: Beurling systems

Generalized-prime examples can show that an Euler product together with
specified weak regularity assumptions does not force the desired zero control.
That is a result about the stated class. It does not establish that the
ordinary primes satisfy only those hypotheses or that every argument using
an Euler product is trapped in that class.

When invoking such an obstruction, cite the actual construction, match its
assumptions and say what it excludes. A proposed use of additional arithmetic
must itself be justified, not dismissed by a broader slogan.

### 4.3 The two-sided test

For any rival or surrogate, compare the full implication:

    rival satisfies all hypotheses and violates conclusion -> implication refuted
    rival lacks a hypothesis used by the proof              -> not that counterexample
    rival passes only a shared intermediate lemma           -> no full-proof verdict
    rival test fails to run                                 -> no exclusion established

A diagnostic model with a hypothetical off-critical zero is not an
unconditional counterexample about the actual von Mangoldt sequence.
A successful discrimination test is not an RH proof either. It identifies
which step to justify. No one vocabulary, ontology or combination of labels
is imposed as the only possible proof architecture.

---

## 5. The graveyard, stated respectfully

Preserve failed attempts, exact counterexamples, retractions and the errors
that caused them. They prevent repetition and can suggest the next
construction. Before using an old disposition to veto a new attempt, check
that it addresses the same claim, parameter range, assumptions and information.

A missing step in a proof is not automatically a counterexample to its target.
Failure of one estimate is not optimality of the best available estimate.
A conditional lower bound is not an unconditional error floor, and a budget
closeout is not a theorem that no further route exists.

Names, reputation and the age of a problem do not settle a mathematical
claim. Challenge a claimed obstruction with the same care as a claimed
breakthrough. Correct an overbroad conclusion without erasing the experiment
or claiming that a reopened route is thereby promising.

---

<a id="6-if-you-want-to-work-on-this-what-is-actually-tractable"></a>
## 6. Constructive directions, not a whitelist

The existing workbench supports explicit-formula and arithmetic estimates,
zero counting and correlation statistics, real-rootedness and heat flow,
controlled approximations, positivity and trace-formula constructions,
function-field comparisons and rigorous finite certificates. This list is
neither exhaustive nor a ranking of their prospects.

For a bounded trial, state the actual object to construct and the theorem
or useful intermediate statement it could support. Identify the proposed
new information, retain the complete error budget and compare with relevant
prior attempts. A reformulation without its missing estimate is not a proof,
but its equivalence to RH does not prohibit trying to establish that estimate.

Choose and develop routes within the owner's mandate. Preserve unused leads;
do not turn the most recent failure into the entire laboratory's frontier.
An intermediate lemma can justify further work if its application is stated
honestly. Do not require an RH proof merely to recognize a useful lemma.

## Where to go next

Use `04-explicit-formula.md` for the prime-zero identity,
`03-functional-equation.md` for its analytic structure,
`05-de-bruijn-newman.md` for heat flow,
`07-equivalences-and-criteria.md` for alternative formulations, and the
relevant hunt for current constructions and exact evidence.

The goal is checkable mathematical progress. The catalogue helps prevent
invalid inferences; it does not replace constructive research with rejection.

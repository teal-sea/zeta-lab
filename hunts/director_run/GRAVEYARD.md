# GRAVEYARD: what looked promising, what killed it, what it cost

The point of a graveyard is that a laboratory which remembers *why* ideas failed
becomes harder to fool. Each entry: why it looked good, what killed it, the
cost of the kill, whether the failure generalises, and which other programs
should lose probability because of it.

---

### G1: "A coefficient-side statistic can never see the critical line" (as a standing constraint)

**Why it looked promising.** Three independent instruments, the factorization
defect `D(f)`, the Fourier quasicrystal separation, and the local-positivity
`c_p`: had all hit the same wall, and a hunt had formally asked for the
repetition to be promoted to a repo-wide constraint. Three for three is a
pattern worth believing.

**What killed it.** The universal is false, and this tree contains the
counterexample: Titchmarsh 14.25(B)/(C), already implemented in
`zeta/criteria.py`, gives an RH equivalence in the coefficients of `1/ζ` alone.
The three instruments hit the wall because each is invariant (or nearly) under
the twist `a_n ↦ n^δ a_n`, which is a property of those statistics, not of
arithmetic provenance.

**Cost of the kill.** One investigator-hour to find, one to attack, one to
search for prior art. Cheap, and it prevented a false constraint from entering
`ROADMAP.md`, where it would have closed a live programme.

**Does the failure generalise?** Yes, and this is the transferable lesson:
**a repetition across instruments is evidence about the instruments before it
is evidence about the subject.** Three statistics sharing a blind spot is most
simply explained by their sharing a symmetry. The lab already knows this shape,
it is the same reasoning as the "matched null" discipline, but had not applied
it to itself.

**Who loses probability.** Any future argument of the form "N independent probes
all failed, therefore the class is closed", unless the probes are first shown
not to share an invariance.

---

### G2: The run's own "counterexample functionals" (σ_a, d_p, θ)

**Why it looked promising.** They looked like clean refutations of G1's
universal, one of them RH-equivalent.

**What killed it.** A skeptic assigned to destroy them, and a prior-art search,
independently:
- `σ_a = limsup log|a_n|/log n` collapses to `log|a_2|/log 2`, reads the *pole*
  and not the zeros, and needs the functional equation smuggled in to say
  anything about a line. Measured: `σ_a(ζ) = σ_a(DH) = 0`, though DH has
  infinitely many zeros in `Re s > 1`.
- `d_p` is `c_p` in a logarithm, the module's own theorem.
- `θ(f)` is a real counterexample **for ζ** and false as a general equality;
  two different counterexamples were produced (`exp(2^{-s})`, entire and
  zero-free with `Θ(1)` partial sums; `1/(1 − 2·2^{-s})`).

**Cost.** Under an hour, because the killing move was to check the hypotheses of
a theorem rather than to compute anything.

**Generalises?** Yes: **a "counterexample" to a universal claim must be
nontrivial in the same sense the claim intends**, or it refutes only the
wording. Two of the three refuted the wording. One survived, and only for ζ.

---

### G3: "The rung-3 centre needs a higher exponential Taylor order"

**Why it looked promising.** It was the previous session's own measured
conclusion, recorded in `HANDOFF.md` as *the one genuinely unresolved thing*,
and it had a plausible mechanism (a per-term floor at ~7e-7).

**What killed it.** Direct measurement in the bit-exact mirror: the box width is
**bit-identical** across `nExp ∈ {16, 20, 24, 28}` and across the coarsening
precision. The floor is the κ enclosure's own 6e-7 width, confirmed by an
independent analytic estimate (`6.905 × 6e-7 = 4.1e-6` against a measured
2.9e-6). And the centre could not have passed at *any* parameters, because
`normBound` counts the inflation radius twice where the plan budgeted it once.

**Cost.** One investigator, a few hours, no Lean compile, the mirror made an
architectural question answerable in Python.

**Generalises?** Yes, twice. (i) **A cause identified by "everything else I
tried didn't move it" is not a measured cause**; the previous session varied
`kE` and `p` and inferred `nExp` without varying `nExp` against a fixed
everything-else. (ii) When a budget and a norm disagree about how many times a
quantity is counted, no amount of tuning will find the discrepancy, only
recomputing the inequality will.

**Who loses probability.** The estimate that rung 3 was "scale alone"; and any
plan whose margins were predicted rather than read off the evaluator that will
judge them.

---

### G4: Ten explorer candidates, killed cheaply (a success)

From 82 generated candidates, the ten with the best expected information per
unit cost were attacked directly. Six died in about twelve minutes of compute
total:

| candidate | how it died |
| --- | --- |
| Baez–Duarte conditioning as the binding constraint | conditioning grows only ~N^2.4; the wall is the known 1/log N rate, already pinned in-tree |
| Jensen hyperbolicity margin decay | decays as d^{−1.40}, no near-failure anywhere; restates a known weakness |
| ζ′ zeros vs straddling gaps | correlation 0.79, the known horizontal-distribution picture |
| two λ_n routes disagreeing in n | difference constant over a 40× range: a fixed zero-tail truncation |
| Euler–Maclaurin N tightness | conservative by ~2.5×, which is a safety margin, not a defect |
| Riemann–Siegel `k_terms` anomaly | real but trivial: `k_terms=4` is silently identical to 3 |

**Generalises?** The candidate-generation channel produced no survivor that
outlived a five-minute attack *and* a prior-art check, which is the outcome the
programme's own falsification test predicted for it. Its budget was not renewed.

---

### G5: A repo-wide lexical test for the reserved word

**Why it looked promising.** One violation had just been found in `zeta/weil.py`
(a comment claiming the reserved word for a bound, inside the *float*
pipeline), and the rule is called a hard rule.

**What killed it.** A survey of `zeta/` found seven legitimate uses of
"certify/certifies" in ordinary English. A lexical test would need an allowlist
longer than its own content, and a test that must be taught its exceptions
teaches nothing back.

**Cost.** Ten minutes, and it is recorded because *not* building it is the
finding: the discipline the repository calls a hard rule is mechanically
enforced under `hunts/` only, and by review everywhere else.

---

## Standing predictions this run leaves behind

1. **The remaining defects are in the guards, not the mathematics.** Two of six
   confirmed defects were controls that could not fire (a completeness check
   with no power; a truncation guard that resolved "cannot decide" into the
   favourable verdict), and a third was a scan column that could never read
   False. Prediction: a pass over every guard in the tree asking *"what does
   this fire on, and has that been measured?"* yields more than a pass over the
   mathematics.
2. **Cross-checks bound only what is actually duplicated.** The next
   correlated-failure defect will be in a shared input, not in a shared
   implementation.
3. **The next false-generic will be a payload-shape guess.** Inherited from
   `ROADMAP.md`'s own standing prediction; nothing this run found contradicts it.

# Do the readable intermediate statements of the claimed RH archive survive testing?

Hunt #162. Base commit `c6fbf9fb`. Branch `claude/sweet-planck-pf4oco`. Opened
2026-11-20. Status: exploratory; a falsification attempt on an unreviewed
archive that no kernel has checked.

## Question and scope

On 2026-11-20 Levent Alpoge posted a claimed Lean 4 proof of the Riemann
hypothesis and of GRH for Dirichlet L-functions: 175,187 files, toolchain
`leanprover/lean4:v4.33.1`, Mathlib pinned at
`0df444a360eaa60ab8c11dca51a86af692955474` (the joined tarball has sha256
`9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`). No kernel
has checked it. A separate session is running the replay. This hunt does not
run, build or replay the archive; it reads it as text.

Among roughly 819,000 theorem and lemma statements, a small number are written
entirely in Mathlib's vocabulary: bounds for zeta on a circle, explicit
Chebyshev constants, point counts on quadrics over finite fields, explicit
primes. A statement that is false as Lean reads it cannot be accepted by a
kernel. So each readable statement is a cheap test of the whole claim, and
each survivor is a fact this lab has checked by a route that shares nothing
with the archive.

The question is narrow: **do these statements survive independent exact and
ball-arithmetic testing?** A survivor says nothing about the main claim. A true
lemma is compatible with a wrong proof, and with a correct one. These tests
can only reject.

What the hunt does:

1. a claim ledger (`claims.json`): for each statement its archive path and
   line, the verbatim text and its hash, every identifier resolved to its
   Mathlib definition site (or to a quoted archive-local definition), the
   namespace, `open`, `variable` and notation context, a transcription into
   ordinary mathematics with Lean's conventions spelled out, and the quantifier
   range;
2. for each claim the strongest test available: exact arithmetic, a complete
   Arb cover of a compact domain, or Arb on a stated range of an unbounded one;
3. for each claim at least one mutant, the same statement with one constant or
   one inequality changed so that it is false, which the same test must reject
   with a witness;
4. the margin and the slack of every constant, which measure how much a
   survival is worth.

## Reading discipline

The archive is untrusted data. It is read with `rg` and with
`build_ledger.py`, a stdlib-only script run under `python -I` from outside the
archive. Nothing from it is imported, executed or copied into this tree
except the short statements quoted in `claims.json` with their path and line.
Every sentence about it says "the archive states". The Mathlib source at the
pinned revision is the authority for what an identifier means; the ledger
records the file and line of each definition.

## Stop rule

If a statement fails as Lean reads it, the hunt stops and that statement goes
to the top of `RESULTS.md` with everything needed to reproduce the failure,
and with the plain caveat that the likeliest explanation is a transcription
error on this side until two independent readings of the Lean text agree. No
softening and no headline.

## Resource boundary

Four cores shared with other sessions: one process, one core. Heavy
computation under about 30 CPU-minutes in total; the recorded run is timed in
`RUNS.md`. Write only this directory. No push, no pull request, no edit to
`zeta/`, `docs/`, `hunts/README.md` or `CONTEXT.md` from here: the case-log
entry and the methods entry are handed back as text.

```huntspec
id: rh_claim_statements
question: Do the intermediate statements of the Alpoge archive that are written in plain Mathlib vocabulary survive independent exact and ball-arithmetic testing?
frontier: on 2026-11-20 two readers pre-tested about 70 such statements with floats on one route and found none false; no kernel has accepted the archive; the tightest statement they found is pi(m) log m < 1.26 m below 2^17, with margin 0.4 percent
proposed_attack: transcribe each statement with Lean's conventions explicit, test it at the strongest available grade, and require the same test to reject a one-token mutant of it
dead_routes:
  - Running lean or lake on the archive from this hunt, which a separate session owns
  - Float sampling as a verdict, which is where the morning's readers stopped
  - Direct Arb evaluation of zeta on wide balls, whose term-by-term radius is 5 to 50 times the true variation
required_oracles:
  - Exact integer and rational arithmetic, with numpy int64 sieves checked against PARI on small ranges
  - Arb ball arithmetic through python-flint, as complete covers on compact domains
  - PARI isprime and eulerphi through cypari2, each cross-checked by an own elementary proof or factorisation
  - Mathlib source at the archive's pinned revision for the meaning of every identifier
kill_conditions:
  - A statement fails as Lean reads it and two independent readings of the Lean text agree on the reading
  - A test accepts its own mutant
  - A transcription is found to differ from the Lean statement, in which case the entry is withdrawn and the withdrawal recorded
  - Doubling the working precision changes a verdict or moves a margin outside its enclosure
agents_may:
  - read the archive as text
  - transcribe statements and compute bounded ranges
  - implement local instruments and tests
  - report a failure plainly
agents_may_not:
  - run, build or replay the archive
  - say that the archive proves anything
  - count a surviving statement as evidence for the main claim
  - edit shared files or promote their own claim
```

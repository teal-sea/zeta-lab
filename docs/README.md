# The documents

Thirty-seven numbered documents. The first five are a single argument and are
meant to be read in order; everything after 14 is a record of a particular
piece of work and can be read on its own.

`docs/doors/` is a different thing: one short page per audience (learn, refute,
certify, discover, contribute, adopt) plus one per department. Start there if
you want a task rather than a subject.

A bare `docs/NN` reference anywhere in this tree always means the document with
that number, and `tests/test_docs_numbering.py` fails if two documents claim
one number, if a heading disagrees with its own filename, or if a citation
points at a document that does not exist.

## The course

`00 → 01 → 02 → 03 → 04` is one argument: theta is the heat kernel, Poisson
summation gives its modular identity, the Mellin transform turns that into the
functional equation whose mirror axis is `Re(s) = 1/2`, and the explicit formula
rebuilds the primes from the zeros.

| Doc | One line |
| --- | --- |
| [00](00-orientation.md) | The statement, the stakes, the status, and the honest scope of this whole repo. |
| [01](01-sums-integrals-and-continuation.md) | Euler–Maclaurin continues ζ by hand; how ζ(−1) = −1/12 is forced, not chosen. |
| [02](02-theta-heat-and-modularity.md) | Theta as the heat kernel; Poisson summation; θ(1/x) = √x·θ(x) in one line. |
| [03](03-functional-equation.md) | The Mellin bridge: modularity in, ξ(s) = ξ(1−s) out, derived line by line. |
| [04](04-explicit-formula.md) | Zeros ↔ primes as an *identity*: ψ(x) as a sum of waves, one per zero. |
| [05](05-de-bruijn-newman.md) | Heat flow on Ξ; zero collisions; Λ ∈ [0, 0.2] and RH ⟺ Λ = 0. |
| [06](06-hilbert-polya-and-gue.md) | The spectral dream and the Montgomery–Odlyzko law, measured on your laptop. |
| [07](07-equivalences-and-criteria.md) | A catalogue of statements exactly equivalent to RH, and why equivalence is not progress. |
| [08](08-why-it-is-hard.md) | The failure catalogue: what each known technique provably cannot do. |
| [09](09-new-ontologies.md) | What "RH needs new mathematics" actually means, with the Weil precedent. |
| [10](10-trace-formulas-and-connes.md) | The Weil explicit formula as a trace formula; Selberg's working analogue; Connes' program. |
| [11](11-f1-and-the-missing-geometry.md) | The field with one element, Deninger's dynamics, and the hunt for geometry under ℤ. |
| [12](12-how-hard-problems-die.md) | Eight problems that fell, the mechanism that killed each, and an honest scoring of RH against the board. |
| [13](13-moments.md) | External zero/value tables, finite-moment estimation, error separation, and the theorem-gated scorecard. |
| [14](14-how-new-mathematics-gets-invented.md) | Eleven recurring ways new mathematics has appeared, scored against the missing Frobenius over ℤ. |

## The record

What was built, what was measured, and what did not survive.

| Doc | One line |
| --- | --- |
| [15](15-the-f1-discovery-engine.md) | The F1 discovery engine: prime orbits, a cohomology scaffold, and what it could not reach. |
| [16](16-poisson-cokernel-plan.md) | Poisson-summation cokernel: the implementation blueprint. |
| [17](17-the-falsification-harness.md) | The falsification harness: how five claims died in one day. |
| [18](18-five-longshots.md) | Five longshots, each run to the wall that stopped it. |
| [19](19-research-dossiers.md) | Research dossiers: an experiment in AI-native mathematical state. |
| [20](20-verification-integrity.md) | Verification integrity: the referee, refereed. |
| [21](21-forward-deployed-verification.md) | Forward-deployed verification: can a report refuse a crossing? |
| [22](22-detector-strength-findings.md) | Detection strength of RH equivalences, stress-tested against the Davenport-Heilbronn imposter. |
| [23](23-rival-distance-and-detector-independence.md) | Rival distance and detector independence: closing two declared blind spots. |
| [24](24-the-local-positivity-attempt.md) | The local positivity attempt, run to its wall. |
| [25](25-the-director-run.md) | The director run: the laboratory pointed at itself, and six of its own claims died. |
| [26](26-the-adopted-builds.md) | The adopted builds: the decision of 2026-08-11, made runnable. |
| [27](27-state-of-the-transplant.md) | State of the transplant: what is kernel-checked, what is refuted, what is open. |
| [28](28-asymmetry-e0-disposition.md) | E0: the independent checker reproduced the audit's blind spots exactly. Read its correction notice. |
| [29](29-de-bruijn-newman-davenport-heilbronn.md) | The de Bruijn-Newman constant of the Davenport-Heilbronn function. |
| [30](30-prime-zeta-rightmost-zeros.md) | The rightmost zeros of the prime zeta function. |
| [31](31-bian-lemma-12-erratum.md) | Erratum to Bian, Lemma 12: `C_{kappa,2}` is `-4 kappa`, not `-4`. |
| [32](32-the-palomar-arm.md) | The Palomar arm: what an outside mechanical check adds, and what it does not. |
| [33](33-chroma-hue.md) | Pitch classes against the colour wheel. |
| [34](34-zeros-in-tuning-units.md) | The Riemann zeros in tuning units. |
| [35](35-the-unspent-fact.md) | The unspent fact: what out-of-band positivity is worth, and why nobody can claim it. |
| [36](36-what-you-can-run.md) | Twelve worked demonstrations, the figure gallery, the repository map, and the standing limitations. |

## Adding one

Take the next free number from `scripts/science_preflight.py` rather than
guessing it: two documents once shared number 21 because a session working from
a snapshot could not see the tree it was writing into. Give the file an H1 of
the form `# NN. Title` matching its own filename, and add a row here.

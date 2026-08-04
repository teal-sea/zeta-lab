# ROADMAP.md — what was built, why, and what is next

`README.md` says what the lab *is*. `AGENTS.md` says how to work in it. This file
records the **decisions**: why the work went the way it did, what is deliberately
not being attempted, what is known to be missing, and what the next build is.

It exists because the reasoning behind a project is the first thing lost between
sessions, and the cost of losing it is repeating settled arguments.

---

## What is built

| phase | what landed | why |
| --- | --- | --- |
| 1 | `core`, `zeros`, `explicit`, `statistics`, `heatflow` + docs 00–08 | the classical machinery, each identity measured rather than assumed |
| 2 | `weil`, `epstein` + docs 09–11 | the two ontology gates that can be made computational (positivity; the counterexample constraint) |
| 3 | `rigor`, `li`, `finitefield`, `criteria` + doc 12 | certified arithmetic; the real-rootedness lane; the universe where RH is a theorem; the remaining equivalence faces |
| 4 | `discovery/` + `scripts/13` | the conjecture funnel, schema-first, with conversion metrics |

The organising chain is in `README.md`: theta is the heat kernel → Poisson
summation → the functional equation → the mirror at `Re s = 1/2` → the explicit
formula → the same heat flow on `Ξ` gives the de Bruijn–Newman constant, where
RH ⟺ Λ = 0 and Λ ≥ 0 is a theorem.

---

## The strategic bet, and its honest status

Of the attacks catalogued in `docs/08-why-it-is-hard.md`, every one has a
standing no-go result against it. The **ontology route** — new objects, new
actions, new rulebooks (`docs/09`) — is the only strategy with a win on the board
(the Weil conjectures, 1974) and no impossibility theorem against it. That is why
phases 2–4 point that way.

Three independent lines converge on the same corner, which is the reason for the
emphasis on heat flow and real-rootedness (`docs/05`, `zeta/li.py`):

1. Λ ≥ 0 says the zeros sit at an exactly *marginal* configuration — the
   signature of an equilibrium of some dynamics.
2. GUE statistics say they behave like the spectrum of a chaotic system.
3. Poincaré fell to a smoothing flow with singularity control; Kadison–Singer
   fell to real-rootedness control via its equivalence web (`docs/12`).

**Honest caveat, recorded deliberately.** Calling this "the field's consensus"
overstates it. The content is standard; the confidence is not. Many number
theorists would say plainly that nobody knows what RH needs. The bet is a bet.

---

## What is deliberately *not* being attempted

- **Proving RH, or any part of it.** See `docs/00` §scope and `docs/08`. Nothing
  computed here is evidence. If a computation appears to settle something, the
  correct inference is a bug.
- **Representing ontology *proposals* inside the discovery funnel.** The schema
  has no representation of a mechanism (`discovery/README.md` §7, blind spot 5),
  and a proposed new ontology is nothing but a mechanism. Forcing it in would
  make the schema pretend. Ontology work stays in `docs/` and is judged against
  the four gates in `docs/09` directly.
- **Chasing computational reach for its own sake.** mpmath, Arb, PARI/GP,
  SageMath and LMFDB already exist and are better at raw computation than
  anything written here. This repo uses them as engines and independent oracles.
  What it adds is the assembled workbench and the written course.

---

## Completed audits

**Phase 4's cross-cutting audit is complete.** It forced plug-in exceptions and
an operating-system kill, resumed the open checkpoint, exercised duplicates,
grepped code/docs/console output for novelty leakage, recomputed the scorecard
from raw run records, mutation-tested the Mertens adjudicator by forcing a false
`survives`, and mechanically checked the domain-agnostic seam. Two accounting
defects were fixed: crash-interrupted candidates now remain in per-generator
denominators, and `refuted` no longer counts as `unsettled`.

## Known gaps

Listed because an undocumented gap becomes an assumption.

1. **The documents were audited by agents, not by domain experts or against the
   literature.** The audits caught real errors, which is evidence they work, but
   correlated blind spots are exactly what that method cannot catch. No one with
   domain expertise has read a line of it. This is the largest unhedged risk in
   the repository.
2. **The discovery schema cannot express implication edges** between candidates —
   "this claim implies that one", "these are the same theorem in different
   clothes". `discovery/README.md` §7 blind spot 4. It matters because the
   equivalence web is one of the three kill mechanisms `docs/12` flags as
   RH-relevant, and `docs/07` is literally an implication graph the schema cannot
   hold. Fix is small: an optional `related_to` field, unhashed, unenforced.
3. **Expected funnel yield is approximately zero, by design.** Nearly everything
   will return already-known or refuted. The first real run: 26 candidates → 20
   known, 1 trivial, 5 inconclusive, 0 survivors. That is the machine working.
   A conjecture factory that produced discoveries on its first run would be
   broken. The value is the discipline and the record, not the hits.

---

## Next build: moments

Ladder rung 1 from `docs/12`'s closing section, and the most realistic target
identified so far.

**First increment shipped.** `zeta/moments.py` ingests LMFDB plain-text exports
and all six tables on Odlyzko's public index, including the offset headers at
the `10^12`, `10^21`, and `10^22` landmarks. It verifies caller-supplied
checksums, records the actual input digest, and validates declared counts,
contiguous indices, positivity and strict ordering. Absolute ordinates
stay as exact decimal base-plus-offset data: converting the `10^22` window to
float64 would collapse neighbouring zeros to the same number. It computes no
zeros. The next increment is the moment estimator and theorem/prediction
scorecard over these externally supplied windows. The format, precision and
provenance contract is documented in `docs/13-moments.md`.

**Why.** The 2nd (1918) and 4th (1926) moments of `ζ` on the critical line are
proven; the **6th and 8th are open**, with exact constants predicted by random
matrix theory (Keating–Snaith). Moments are self-convolutions — `ζ(s)² = Σ d(n)n^{-s}`,
and the `2k`-th moment corresponds to the `k`-fold divisor function — so this is
the analytic face of the same convolution algebra that produces the Euler
product. It is also the retail version of the Lindelöf Hypothesis, the domino
most likely to fall before RH.

**Critical design constraint.** Do **not** compute the zeros for this. The lab
holds ~10⁴ zeros reaching height ≈3.5×10³; the moment behaviour worth measuring
lives many orders of magnitude higher, and Odlyzko's published tables reach the
10²⁰–10²² landmarks. Build an ingestion path for external zero tables
(LMFDB, Odlyzko) and run the verified machinery against real data at real
heights. Computing our own would be both slower and worse.

**Then:** the schema `related_to` edges (gap 2 above).

# Guide: see the machinery run

**For you if** you want real intuition and real numerics about ζ — to watch the
theorems occur rather than read that they hold.

**First command:**

```bash
.venv/bin/python scripts/06_tour.py        # the whole story, ~90 seconds
```

## The one that makes the subject real

The primes are reconstructed from the zeros alone. Nothing else in the subject
lands the same way:

```bash
.venv/bin/python scripts/03_primes_from_zeros.py
```

## The reading course

`docs/00`–`docs/18` are a course, in order. Short version of the path:

| Read | For |
|---|---|
| `00-orientation.md` | scope, and the house rule about what a computation can settle |
| `01`–`03` | continuation, θ and modularity, the functional equation |
| `04-explicit-formula.md` | the zeros ↔ primes duality, measured |
| `06-hilbert-polya-and-gue.md` | why everyone reaches for an operator |
| `08-why-it-is-hard.md` | **read this before believing any numerical evidence** |
| `12-how-hard-problems-die.md` | the failure catalogue |

## The house habit

Every identity here is exposed as a measured **defect**, not asserted. `ξ(s) =
ξ(1−s)` is not a comment; it is `functional_equation_defect(s)`, and a test
pins how small it is. Every number in a docstring is checked by `tests/`.

That habit is the reason the numbers can be trusted, and it is the thing worth
stealing if you are building something similar.

## What you will not find

Evidence for RH. `docs/08` explains why: Littlewood's theorem guarantees a
pattern can hold for every case anyone will ever compute and still be false.
The house rule is that if a computation here appears to settle something open,
the correct inference is a bug.

Next door: [refute.md](refute.md), for when you have a claim of your own.

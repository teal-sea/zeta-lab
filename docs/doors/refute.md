# Guide: test a claim against the controls

**For you if** you have a structural claim about the zeros, a spectral
operator, a positivity argument, a pattern in the statistics, and you want to
know whether it is about ζ at all before you spend a month on it.

**First command:**

```bash
.venv/bin/python scripts/23_gate_3_battery.py
```

## What this door does that a notebook does not

A plausible "explanation" of RH now costs minutes to generate: discretize an
operator, fit a spectrum, tell an evocative story. A referee's rebuttal
traditionally costs days. This door makes the rebuttal cost minutes too.

It does **not** tell you whether your claim is true. It answers a weaker and
decidable question: *is your demonstration about ζ, or about any function that
happens to look like ζ?* Most claims die here, and they die for reasons that
do not depend on anybody's taste.

`docs/17-the-falsification-harness.md` is the methods retrospective: five
independent claims of zero structure arrived in a single day, and the standing
instruments dispatched all five.

## The four instruments

| Instrument | The question it asks | If your claim fails |
|---|---|---|
| **Rivals** | does it also hold for a function that satisfies the same functional equation and violates RH? | it explains nothing, see `zeta.epstein.battery`, gate #3 of `docs/09` |
| **Decoys** | does the result survive when the primes are swapped for non-primes, or merely reordered? | it was never reading the arithmetic, `zeta.spectral_gate` |
| **Surrogates** | does a null model with no arithmetic in it reproduce the pattern? | the pattern is a property of the model class, `zeta.surrogate`, `NULLCONTROLS.md` |
| **Lesions** | does your detector notice a violation planted on purpose? | your detector is blind, and its silence measures that, not the world, `zeta.detectors` |

The rival test is the sharpest, because it needs no threshold and no
statistics. It is a modus tollens: if the Davenport–Heilbronn function has the
property too, and it has zeros off the line, then the property cannot be why
the zeros are on the line.

**If your claim is about the Euler product, read this before you celebrate a
pass.** Davenport–Heilbronn and the Epstein zetas are built by combining Euler
products, so neither can test a claim whose content is the Euler product
itself. The rival set carries one that can: `W_a(s) = ζ(s+a)ζ(s−a)` has a
scalar Euler product, multiplicative coefficients, the functional equation,
and zeros on `Re s = 1/2 ± a` by Hardy's theorem alone. Its scope is stated in
`docs/09` §5.1: it sits outside the Selberg class, so a claim it shares is
blind to a shift rather than irrelevant, and the repair it forces is that you
name which normalisation your mechanism uses and where.

## Running it on your own claim

Write your claim as a predicate over the interface dict and hand it to the
battery:

```python
from harness import get_department, run_battery
from harness.departments import load

load("zeta")
battery = get_department("zeta").battery

def my_claim(iface) -> bool:
    return abs(iface["Z"](14.5)) < 1.0      # whatever your structure is

verdict = run_battery(battery, my_claim)
print(verdict.summary())
print(verdict.shared_with)   # the rivals that also have it
```

`verdict.distinguishes` is the only field to act on. It is true exactly when
the claim fires for ζ and for none of the rivals.

## What a pass does and does not mean

A claim that distinguishes ζ from every rival is **a candidate for where a real
proof must live**. It is not evidence for RH, and nothing computed in this
repository ever will be, see `docs/08-why-it-is-hard.md` for Littlewood's
theorem and why a pattern holding for every computed case can still be false.

Related: [discover.md](discover.md), for generating leads rather than refuting
them.

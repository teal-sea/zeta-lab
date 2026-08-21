# Mathlib's wishlist, and what this repository already proves

Mathlib keeps `docs/1000.yaml`: the Wikipedia list of famous theorems, each
entry tagged with the Lean declaration that proves it. An entry with **no
`decl:` field** is Mathlib stating, in its own tree, that the theorem is wanted
and unformalized. As of 2026-08-19 there are **970** such entries.

This directory records the overlap: entries Mathlib says it lacks, for which
the Lean arm of this repository already holds a complete, `sorry`-free proof.

It is a **record, not a plan**. The porting work is tracked in the
`contrib-lab` repository (`../contrib-lab/TARGETS.md`), which is where the
outward-facing judgment lives. Nothing here should be read as a claim that
something has been contributed to Mathlib; see *Status* on each row.

## The overlap

| Mathlib entry | our declaration | file | status |
| --- | --- | --- | --- |
| `Q5656674` Hardy–Ramanujan theorem | `ZetaLean.HardyRamanujan.hardy_ramanujan` | `lean/ZetaLean/HardyRamanujantheorem.lean` (588 lines) | proved here; **not ported, not submitted** |
| `Q1196729` Mertens's theorems | `ZetaLean.Mertens.mertens_second_theorem` | `lean/ZetaLean/MertensSecond.lean` (354), `Mertensstheorems.lean` (530) | proved here; **not ported, not submitted** |
| `Q205966` Critical line theorem | — (infrastructure only) | `lean/ZetaLean/HardyZ.lean` | Hardy's `Z` **submitted** as [mathlib4#42963](https://github.com/leanprover-community/mathlib4/pull/42963); the theorem itself is not proved |
| `Q1632301` Sturm's theorem | groundwork only | `lean/ZetaLean/Sturm*.lean` | four support lemmas; the theorem is **not** proved |

`Q5656674` also depends on `ZetaLean.HardyRamanujan.turan_variance`, Turán's
variance bound, which is the hard input and is proved here too.

## What "proved here" was checked to mean

Per file, on 2026-08-19, on this repository's pinned toolchain:

- zero occurrences of `sorry` in the source;
- the module's `.olean` is built, so it compiles;
- `#print axioms` on the headline declaration reports exactly
  `[propext, Classical.choice, Quot.sound]` — the three axioms Mathlib itself
  is built on. No `native_decide`, no added axioms.

This is the same two-legged gate as `lean/proof_adapter.py`: a static refusal
scan plus a kernel check, both run locally.

## What it does not mean

**Proved here is not ported.** Mathlib has its own idiom, naming, file layout
and generality expectations. A proof that compiles in `ZetaLean` may need
substantial rework — and may duplicate something Mathlib already has under a
different name. Two live examples:

- `lean/ZetaLean/ChebyshevBounds.lean` overlaps
  `Mathlib/NumberTheory/Chebyshev.lean`, which already exists upstream.
- Of four Sturm support lemmas here, `Polynomial.continuousOn_eval_real` is
  already Mathlib's `Polynomial.continuousOn`, and
  `simple_roots_of_coprime_deriv` is already
  `Polynomial.Separable.eval₂_derivative_ne_zero` — `Separable` is *defined* as
  coprimality with the derivative. Only `sign_change_of_odd_multiplicity`
  appears genuinely absent.

Assume any short mathematical name collides until proven otherwise, and confirm
with `../contrib-lab/tools/check_target.py` before writing a word for a public
audience.

## How this list was produced

    ../contrib-lab/tools/inventory_source.py --source lean --wishlist

It fetches `docs/1000.yaml` from Mathlib master, keeps the entries with no
`decl:`, and reports which of this repository's `.lean` files contain every
keyword of the entry's title. That is a keyword heuristic and it is noisy: the
2026-08-19 run returned 61 candidate rows, of which **57 were coincidences**
("Odd number theorem" matching a file containing the words *odd* and *number*).
Every row in the table above was confirmed by hand afterwards. Re-run the sweep
rather than editing this file by hand, then re-confirm.

**One warning worth repeating.** The first version of that tool filtered out
declarations whose names contained `mertens`, `hardy` or `chebyshev`, treating
them as this project's private vocabulary. They are mathematicians' names. The
filter silently discarded both findings in the table above, and the tool then
reported that this repository had almost nothing Mathlib wanted. Never put a
mathematician's name in an exclusion list.

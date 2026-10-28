# RESULTS: Requirement A, scanned

> Bounded outcome of `hunts/ontology_provenance/`, 2026-10-24, corrected
> 2026-10-27. Acceptance: `test_provenance.py`, including planted violations
> that must go red, a `clean` case whose only crime is the word "zero" in an
> identifier, and a pin that frame 07 is not reported tainted.
>
> **Nothing here is a proof, a certificate, or evidence for RH.** It is a
> static name and import-graph analysis with stated blind spots. A clean
> verdict means nothing zero-derived is reachable by name, not that the
> construction is prime-derived.

## 1. What was built

`provenance.py` answers one question about a proposed frame: is anything it
reaches zero-derived? It parses the file, classifies the names it uses against
a rule set of zero-derived quantities (ordinates, xi-phases, zero finders,
zero counters, zero tables, ordinate statistics), and then walks the
repository's own import graph.

`from module import name` follows that name, not the rest of the module. A
reference to a name counts, not only a call, and a from-import that a file
only re-exports is followed to its source. A name defined in the file is
exempt from the file's own consumer check: a file that manufactures a
xi-phase is a `provider`, and a frame that imports the phase is the consumer.
`import module` still follows the module. Relative imports are resolved
against the file's module name, so `from .zeros import` inside `zeta/` is an
import of `zeta.zeros`.

| verdict | meaning |
| --- | --- |
| `clean` | no zero-derived name reachable, directly or through the followed edges |
| `tainted (direct)` | the defining file names one |
| `tainted (reachable)` | a name it imports is zero-derived, and the path is printed |
| `provider` | this file manufactures a zero-derived quantity |
| `undecided` | dynamic execution, a syntax error, or a name that cannot be resolved |

The first rule set called a coefficient-only import tainted because the
imported module used `hardy_Z` in another function. That is the false positive
the kill condition forbids. Symbol-level resolution is what the scanner does
now. Frame 07 is clean. It is not left in the table as tainted.

## 2. The table: the laboratory's own candidate frames

Run on the fifteen numbered prototypes in `ontology/`. The verdict is what the
scan reports. The reading column is a reading of the source, not a second
verdict: the scan does not decide definitional use.

| frame | scan | witness | reading |
| --- | --- | --- | --- |
| `01_f1_geometry` | clean | | |
| `02_acoustic_f1_matrix` | clean | | |
| `03_inverse_spectral_geometry` | **tainted (direct)** | imports `zeta.zeros` | constructs a matrix from `first_n_zeros` |
| `04_transcendental_matrix` | clean | | |
| `05_berry_keating_grid` | **tainted (direct)** | imports `zeta.zeros` | operator built from primes; `first_n_zeros` only under `__main__`, to print a comparison |
| `06_the_polya_hilbert_prototype` | **tainted (direct)** | imports `zeta.zeros` | operator built from primes; `first_n_zeros` only under `__main__`, to print a comparison |
| `07_the_imposter_gauntlet` | clean | | imports only `dh_coefficient`, which reads coefficients |
| `08_riemann_beats_audio` | **tainted (direct)** | imports `zeta.zeros` | synthesizes audio from the zeros |
| `09_hermite_prime_waves` | clean | | |
| `10_geometric_dust_torus` | clean | | |
| `11_quantum_chaos_gue` | **tainted (direct)** | uses `mpmath.zetazero` | compares GUE spacings with zero spacings; not a construction |
| `13_dirichlet_polya_hilbert` | clean | | |
| `14_hunting_ln2` | clean | | |
| `15_fixing_the_density` | clean | | |
| `16_adelic_acoustic_absorber` | clean | | |

**What the scan establishes.** Five of the fifteen files reach a zero-derived
name: 03, 05, 06, 08 and 11. That is lexical and import-graph reachability.
It is not the claim that six frames are built on the zeros, and it is not
Requirement A rejecting them at the definition stage.

On reading the five files: only 03 and 08 construct from zeros. 05 and 06
build their operators from prime data and call `first_n_zeros` only to print
a comparison. 11 compares GUE spacings with zero spacings. Requirement A is a
test of constructions. A comparison is not one, and a printed column is not
the definition. Frame 07 is the case the first rule set got wrong. It is
clean. The nine other clean frames are not thereby right. Provenance is
orthogonal to truth, which is why the table says `clean` and not `good`.

Whole-package run (`ontology/` and `zeta/`, 53 modules): 27 clean, 24 tainted,
1 provider, 1 undecided. `ontology/` alone is 28 modules: 20 clean, 7 tainted,
1 undecided. `zeta/` alone is 25 modules: 7 clean, 17 tainted, 1 provider.
The calibration rows behave: `zeta.factorization` is clean (coefficient-only
by construction), `zeta.zeros` is tainted on `mp.zetazero`, and `zeta.weil`
is tainted because it imports `zeta.statistics`.

These package totals are not the module-level totals of the first run. Two
changes moved them. Symbol-level edges cleared frame 07 and the two scouts
that import names from `ontology.knownness` other than `safe_eval_expression`.
Resolving relative imports against the file's module name flagged `zeta.li`
and `zeta.leeyang`, which a bare `from .zeros` / `from .heatflow` had missed,
and followed `first_zeros` into `zeta.quasicrystal` and `zeta.synthesis`.

## 3. Blind spots, named because they bound the table

1. **`import module` is still the whole module.** Symbol resolution applies to
   `from module import name`. A bare import of a tainted module is tainted
   even if the file only calls a clean attribute. That case is not frame 07.
2. **`undecided` is not a pass and not an accusation.** `ontology.knownness`
   evaluates a whitelisted AST through `eval`. The function that does so,
   `safe_eval_expression`, is undecided. The names the scouts actually import
   do not reach it, so those two files are clean. A name the scanner cannot
   resolve inside a tainted or unreadable module is undecided, not clean.
3. **Evasion is trivial and expected.** `getattr(mod, "zeta" + "zero")`, a data
   file of ordinates, or a formula that reconstructs them all pass. This is a
   floor of the `check_secrets.py` kind: it catches the ordinary case.
4. **Reachability is not definitional use.** The scan does not distinguish a
   name used to build the object from a name used under `__main__` to print a
   comparison. Section 2's reading column is that distinction, done by reading,
   and it is not a scanner verdict.
5. **It says nothing about Requirements B and C.** An arithmetic-provenance
   construction can still be wrong about the maths. That is what the doors, the
   battery, and the certainty ladder are for.
6. **An attribute re-export still reads clean.** `from helper import f` in an
   intermediate module is a symbol, and a consumer of that re-export is tainted
   when `f` is. `import helper` followed by `f = helper.f` is not: the
   right-hand side is an attribute, not a from-imported name, and the assigned
   name is a local definition the scanner does not follow. That is the residual
   fail-open. It is not the fifteen-frame table, and it is not closed here.

## 4. The doors

Doors here are limits of the instrument, not a queue of work. This scan does
not optimize a bound. The three parts below say what actually binds, what was
chosen and not optimized, and whether closing a door would require data this
scan does not already read.

### Active constraints at the optimum

There is no numerical optimum, so there is no shadow price and no
saturation-curve slope to rank. What binds the published table is the rule
set, ranked by which column moves if the rule is relaxed.

1. **Banned modules and banned names.** Importing `zeta.zeros` flags frames
   03, 05, 06 and 08. Using `mpmath.zetazero` flags frame 11. Relaxing the
   banned-module entry moves those four; relaxing the banned name moves 11.
   That is the constraint the tainted column sits on.
2. **Symbol-level resolution, including every name reference, not only a
   call.** Frame 07 imports only `dh_coefficient`. A module-level read of
   `zeta.epstein` flagged it; following the imported name, and every load of
   a name, keeps it clean. Relaxing this back to a whole-module hit moves 07,
   and the two scouts that import a clean name from `ontology.knownness`,
   from clean to tainted. That is the constraint the clean column sits on.
3. **A bare `import module` follows the whole module.** None of the fifteen
   frames is tainted only by that coarser edge. It does not bind this table.
   It is still the constraint that would flag a file which imports a tainted
   module and uses only a clean attribute.

### The frozen-constant inventory

This scan has no chosen numeric constant: no cutoff, no height, no working
precision. The frozen constants are membership decisions, each chosen and not
optimized.

| constant | frozen as | what relaxing it trades against |
| --- | --- | --- |
| `BANNED_NAMES` and `BANNED_MODULES` | the rule set in `provenance.py` | dropping a name misses that ingredient, which is a fail-open; adding a homonym false-flags a prime-side use. The word "zero" in an identifier is already not a hit. |
| `import module` granularity | the whole module, not the attribute | attribute tracking would clear a file that imports a tainted module only to use a clean name, and would cost a walker this hunt does not build. Fewer coarse hits, against a new miss if the walker drops a load. |
| dynamic execution | `exec`, `eval`, `__import__`, `importlib` and `runpy` are undecided, not clean | calling them clean fails open. Resolving them means running the file, which this scan does not do. |
| `import zeta` | not an edge into `zeta.zeros` | treating the package import as the zero module would taint every file that imports the package, including frames that never name a zero. |
| from-import re-export | followed to the source symbol | no longer frozen open. An attribute re-export, `import helper` then `f = helper.f`, is still not followed. Closing it stays inside the same AST. This hunt does not do it. |

### The information class of each door

Each door stays inside the data the current family reads: the Python source
under `ontology/` and `zeta/`, parsed as an AST. None of them requires a zero
table, a numerical sweep, or a new family of inputs.

- **Whole-module imports.** Closing the gap is a finer read of the same
  source. It does not require reading more. This hunt does not build that
  walker.
- **A declared-exemption channel.** An in-file annotation would still be
  static source, not a new measurement, and it is also a bypass. It needs a
  policy before it exists. This hunt does not add one.
- **Not wired into the funnel.** `ontology/registry.py` already refuses a
  generator that grades its own candidates. Making this scan blocking would
  be a change to `ontology/`, which this hunt does not make. The scan stays
  advisory. That change is the same information class: static source, not a
  new datum.
- **Attribute re-export.** Following `f = helper.f` is again a read of source
  already in the tree. The residual is named in the blind spots. This hunt
  does not close it: the from-import case was the one that could be closed
  without moving the 53 published verdicts.

## Reproduce

```bash
python hunts/ontology_provenance/provenance.py ontology --root .
python hunts/ontology_provenance/provenance.py zeta --root .
python -m pytest hunts/ontology_provenance/test_provenance.py -q
```

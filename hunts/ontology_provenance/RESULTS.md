# RESULTS: Requirement A, scanned

> Bounded outcome of `hunts/ontology_provenance/`, 2026-10-24, on
> `swarm-trial-b2-120`. Acceptance: `20 passed` on `test_provenance.py`,
> including ten planted violations that must go red and a `clean` case whose only
> crime is the word "zero" in an identifier.
>
> **Nothing here is a proof, a certificate, or evidence for RH.** It is a
> static name and import-graph analysis with stated blind spots.

## 1. What was built

`provenance.py` answers one question about a proposed frame: is anything it is
built from zero-derived? It parses the file, classifies the names it uses against
a rule set of zero-derived quantities (ordinates, xi-phases, zero finders,
zero counters, zero tables, ordinate statistics), and then walks the
repository's own import graph to find taint the defining file does not show.

Four verdicts, and the fourth exists because of a false positive this scan
produced on its own first run:

| verdict | meaning |
| --- | --- |
| `clean` | no zero-derived name reachable, directly or through the import graph |
| `tainted (direct)` | the defining file names one |
| `tainted (reachable)` | a file it imports does, and the path is printed |
| `provider` | this file *manufactures* a zero-derived quantity |
| `undecided` | dynamic execution or a syntax error makes a static read worthless |

`provider` was added because the first rule set called `zeta.core` tainted for
defining `rs_theta`, which is the opposite of the intent: a file that defines a
xi-phase is where that phase lives, not a construction that consumes it. Names
defined in the file are now exempt from its own taint, and only consumers are
flagged.

## 2. The table: the laboratory's own candidate frames

Run on the fifteen numbered prototypes in `ontology/`:

| frame | verdict | witness |
| --- | --- | --- |
| `01_f1_geometry` | clean | |
| `02_acoustic_f1_matrix` | clean | |
| `03_inverse_spectral_geometry` | **tainted (direct)** | imports `zeta.zeros` |
| `04_transcendental_matrix` | clean | |
| `05_berry_keating_grid` | **tainted (direct)** | imports `zeta.zeros` |
| `06_the_polya_hilbert_prototype` | **tainted (direct)** | imports `zeta.zeros` |
| `07_the_imposter_gauntlet` | **tainted (reachable)** | via `zeta.epstein`, which uses `hardy_Z` |
| `08_riemann_beats_audio` | **tainted (direct)** | imports `zeta.zeros` |
| `09_hermite_prime_waves` | clean | |
| `10_geometric_dust_torus` | clean | |
| `11_quantum_chaos_gue` | **tainted (direct)** | uses `mpmath.zetazero` |
| `13_dirichlet_polya_hilbert` | clean | |
| `14_hunting_ln2` | clean | |
| `15_fixing_the_density` | clean | |
| `16_adelic_acoustic_absorber` | clean | |

**Six of fifteen frames are built on the zeros.** They are candidates by the
laboratory's own definition, and Requirement A rejects them at the definition
stage, before any computation: a frame handed the answer cannot explain it. The
six are not thereby wrong in what they compute, and none of the nine clean frames
is thereby right. Provenance is orthogonal to truth, which is why the table says
`clean` and not `good`.

Whole-package run (`ontology/` and `zeta/`, 53 modules): 28 clean, 21 tainted,
1 provider, 3 undecided. The calibration rows behave: `zeta.factorization` is
clean (coefficient-only by construction), `zeta.zeros` is tainted on
`mp.zetazero`, and `zeta.weil` is tainted through the ordinate statistics its zero
side uses.

## 3. Blind spots, named because they bound the table

1. **Module granularity.** Taint is per file, except for names a file defines.
   A clean function housed in a module that also contains zero machinery is
   flagged `reachable`. `07_the_imposter_gauntlet` is that case: it imports
   `dh_coefficient`, which reads only coefficients, from a module that uses
   `hardy_Z` elsewhere. The verdict is honest for a module-level read and
   pessimistic for the function actually used.
2. **`undecided` is not a pass and not an accusation.** `ontology.knownness`
   evaluates a whitelisted AST through `eval`, which is safe by inspection and
   invisible to static reading, so it and the two scouts that depend on it are
   reported `undecided`. A reader should read those three files, not assume
   either verdict.
3. **Evasion is trivial and expected.** `getattr(mod, "zeta" + "zero")`, a data
   file of ordinates, or a formula that reconstructs them all pass. This is a
   floor of the `check_secrets.py` kind: it catches the ordinary case, which is
   the case that occurs, because nobody writes a zero-importing frame on purpose.
4. **It says nothing about Requirements B and C.** An arithmetic-provenance
   construction can still be wrong about the maths. That is what the doors, the
   battery, and the certainty ladder are for.

## 4. The doors

- **Symbol-level precision.** The obvious improvement is per-function taint so
  `07` resolves to clean or tainted on `dh_coefficient` alone. It is a bounded
  change to the same module and it removes blind spot 1.
- **A declared-exemption channel.** Blind spot 2 could be narrowed by an explicit
  in-file annotation (`# provenance: whitelisted-eval`) that records a decision
  instead of hiding it. It also creates a bypass, so it needs an operator policy
  before it exists.
- **Wire it into the funnel.** `ontology/registry.py` already refuses a generator
  that grades its own candidates. The same seam could refuse a frame that fails
  Requirement A, which would make the scan blocking rather than advisory. That is
  a change to `ontology/`, which this hunt is not permitted to make.
- **Retrofit or retire the six.** Each of `03`, `05`, `06`, `08`, `11` and `07`
  is either rebuilt from coefficient and prime-power data or retired. That is an
  allocation decision, and it is the owner's.

## Reproduce

```bash
python hunts/ontology_provenance/provenance.py ontology --root .
python hunts/ontology_provenance/provenance.py zeta --root .
python -m pytest hunts/ontology_provenance/test_provenance.py -q
```

# Hunt #75: pitch classes against the colour wheel

Is there any mathematically nontrivial correspondence between the twelve
chromatic pitch classes and the colour wheel, beyond the fact that both can be
drawn on a circle? The operator's starting formulation was a bijection from
Z_12 to twelve equally spaced hues, with rotations, reflections and
alternative orderings allowed, and a standing instruction to prefer finding
the premise wrong over making it look good. Write-up: `docs/33-chroma-hue.md`.

```huntspec
id: chroma_hue
question: Does any bijection from Z_12 to twelve hue classes preserve a relation, metric, symmetry or spectrum that is not already a consequence of Z_12 acting on a circle?
frontier: no prior claim in this tree; the literature has the DFT of pitch-class sets (Lewin, Quinn, Amiot) and the opponent-channel geometry of hue (CIELAB, OKLab), and no published bridge between them that survives a null model
proposed_attack: formalise the equivariance constraint, enumerate every bijection against a consonance objective with a random-permutation null, and measure whether the perceptual hue circle is even a metric 12-gon
dead_routes:
  - rotating an HSL wheel against the chromatic scale by eye, since HSL hue steps are not perceptually equal
  - Newton's seven-colour spectrum matched to the diatonic scale, which was fitted by construction
required_oracles:
  - exhaustive enumeration of all 12! bijections with f(0) fixed
  - published CIEDE2000 test pairs (Sharma, Wu, Dalal 2005)
  - the Clough-Douthett maximally even sets recomputed by enumeration
  - uniformly random permutations as the null distribution
kill_conditions:
  - a random bijection reaches the score of the best structured one
  - the best structured bijection is not invariant under the symmetries that motivated it
  - the perceptual hue circle fails to be a metric 12-gon at the level of its own adjacent-step spread
agents_may:
  - search
  - derive
  - code
  - attack
  - formalize
agents_may_not:
  - declare novelty
  - declare theorem status
  - promote their own claim
```

## Files

| file | what it does |
| --- | --- |
| `colorspace.py` | sRGB, CIELAB, OKLab/OKLCH, HSL, CIEDE2000, pinned to Sharma's 34 test pairs |
| `pc.py` | Z_n machinery: affine maps, DFT, three dissonance measures, circulant builders |
| `probe_consonance.py` | exhaustive search of all bijections against Spearman(hue distance, dissonance), with the random null; writes `results_consonance.json` |
| `probe_perceptual.py` | is the colour side a metric 12-gon: HSL, OKLCH fixed and full chroma, CIELAB; writes `results_perceptual.json` |
| `probe_spectrum.py` | the wave version: 12-TET steps of light frequency across the visible octave; writes `results_spectrum.json` |
| `probe_fourier.py` | the Fourier formulation checked by enumeration, and the dominant dissonance mode for n = 5..31; writes `results_fourier.json` |
| `probe_round2.py` | metamer counts, orbifold radius vs chroma, the CRT torus, bijection search with real CIEDE2000 geometry; writes `results_round2.json` |
| `probe_cyclotomic.py` | the cyclotomic ontology: Galois conjugacy of the two wheels, integrality of the norm, the ten norms and 84 unit classes; writes `results_cyclotomic.json` |
| `make_figures.py` | the four figures under `figures/chroma_hue_*.png` |
| `make_figure_norm.py` | `figures/chroma_hue_norm.png`, the 224 set classes on ten hyperbolas |

Tests: `tests/test_chroma_hue.py`. Everything is reproducible from the repo
root with `.venv/bin/python hunts/chroma_hue/probe_*.py` (the exhaustive
search takes about four minutes).

## Scope

This hunt touches nothing in `zeta/`, `ontology/` or `harness/`. It does not
borrow the zeta battery because it makes no claim about zeta; its controls are
the random-permutation null and the circulant structure of its own objective,
both stated in the doc. Nothing here is evidence about RH or about anything
in `docs/08`.

## Run manifest

```runmanifest
id: chroma_hue-2026-08-22-first
hunt: chroma_hue
started: 2026-08-22T18:40-05:00
finished: 2026-08-22T20:10-05:00
ran:
  - .venv/bin/python hunts/chroma_hue/probe_consonance.py
  - .venv/bin/python hunts/chroma_hue/probe_perceptual.py
  - .venv/bin/python hunts/chroma_hue/probe_spectrum.py
  - .venv/bin/python hunts/chroma_hue/probe_fourier.py
  - .venv/bin/python hunts/chroma_hue/probe_round2.py
  - .venv/bin/python hunts/chroma_hue/probe_cyclotomic.py
  - .venv/bin/python hunts/chroma_hue/make_figures.py
  - .venv/bin/python hunts/chroma_hue/make_figure_norm.py
  - .venv/bin/python -m pytest -q tests/test_chroma_hue.py
outcome: the only structure a note-to-hue bijection can carry is a character of Z_12, the circle of fifths is the unique argmax of every consonance objective over all 12! maps, the perceptual hue circle is not a 12-gon, and the round-two reformulation makes a colour wheel a complex place of Q(zeta_12) with chromatic times fifths saturation an integer norm taking ten values; verdict pretty but trivial
artifacts:
  - hunts/chroma_hue/results_consonance.json
  - hunts/chroma_hue/results_perceptual.json
  - hunts/chroma_hue/results_spectrum.json
  - hunts/chroma_hue/results_fourier.json
  - hunts/chroma_hue/results_round2.json
  - hunts/chroma_hue/results_cyclotomic.json
  - figures/chroma_hue_norm.png
  - figures/chroma_hue_wheels.png
  - figures/chroma_hue_consonance.png
  - figures/chroma_hue_perceptual.png
  - figures/chroma_hue_spectrum.png
  - docs/33-chroma-hue.md
```

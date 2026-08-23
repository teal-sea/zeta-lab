# 33. Pitch classes against the colour wheel

**Hunt #75 (`hunts/chroma_hue/`). Verdict: PRETTY BUT TRIVIAL for the
note-to-hue question; the reformulation in section 9 is the one worth
keeping.** The whole
correspondence reduces to one statement: a note-to-hue bijection can carry
exactly one piece of structure, the choice of a character of Z_12, and Z_12
has two injective characters up to symmetry, chromatic and fifths. Everything
interesting that follows is a fact about Z_12 and about hearing, with the
colour wheel serving as a set of twelve labels. The colour side, measured in
a perceptual space, is not a 12-gon and has no 12-fold structure to match.

Nothing here is evidence about RH or about anything in `docs/08`. This
document keeps the operator's requested separation: definitions, derivable
facts, empirical results, candidate patterns, failed ideas, speculation.

## 1. Definitions

* **Pitch classes.** Z_12 with transposition T_c(x) = x + c and inversion
  I(x) = -x; together the dihedral group D_12 of order 24. Interval class
  ic(d) = min(d mod 12, -d mod 12), six values.
* **Hue 12-gon.** Twelve equally spaced points on the circle, with the cyclic
  metric d(i, j) = min(|i - j|, 12 - |i - j|) and its own D_12 of rotations
  and reflections.
* **Wheel.** A bijection f : Z_12 -> hue 12-gon. Two wheels are *equivalent*
  if they differ by a hue rotation or reflection. The operator's question
  asks which wheels preserve something.
* **Affine wheels.** f(x) = u x + c with u a unit mod 12, u in {1, 5, 7, 11}.
  u = 1 is chromatic order, u = 7 (equivalently 5) is the circle of fifths,
  u = 11 is inversion. 48 maps; two equivalence classes.
* **Colour of a chord.** Under wheel f, the colour of a pitch-class set S is
  the centroid (1/|S|) sum_{x in S} e^{i theta(f(x))} in the chroma plane.
  This is the additive mixture of the notes' hues at equal chroma, which is
  what the eye does to superposed lights and what the ear does not do to
  superposed tones.
* **Dissonance measures** on interval classes, kept separate and never
  averaged: Sethares' roughness curve for harmonic complex tones (six partials,
  0.88 decay, computed), Tenney height log2(pq) of the textbook just ratio,
  and the plain ordinal ranking P5 < M3 < m3 < M2 < m2 < tritone. Their
  consonance orders agree except on the tritone (Sethares places it between
  the thirds and the whole tone).
* **Perceptual hue.** The OKLCH hue angle (Ottosson 2020), with CIEDE2000
  (Sharma, Wu, Dalal 2005) as the difference formula. Both are implemented in
  `hunts/chroma_hue/colorspace.py` and pinned: all 34 published CIEDE2000
  test pairs reproduce to 5e-4.

## 2. Derivable facts

Each of these is an elementary argument, and each is re-derived by
enumeration in `tests/test_chroma_hue.py` so the document cannot drift.

**F1. A wheel makes hue distance a function of interval class if and only if
it is affine.** If d(f(x), f(y)) depends only on x - y, the adjacency graph
of the hue 12-gon pulled back to Z_12 is a translation-invariant 2-regular
graph, i.e. a Cayley graph Cay(Z_12, {g, -g}), and it is a single 12-cycle
only when gcd(g, 12) = 1. Then f maps consecutive multiples of g to
consecutive hues, so f(x) = ±g^{-1} x + c. Backtracking over all 12!
bijections finds exactly 48, and they are the affine set. So there are
exactly **two** wheels up to symmetry with any transposition-invariant
meaning: chromatic and fifths. Every other bijection assigns different hue
distances to the same interval in different keys.

**F2. Every transposition-invariant circular embedding is a Fourier mode.**
A dissimilarity on Z_12 that depends only on interval class is a circulant
matrix; classical MDS doubly centres it and the result is still circulant,
so its eigenvectors are the DFT modes. The best two-dimensional embedding is
therefore the wheel x -> kx for the mode k with the largest eigenvalue, and
it is a regular 12-gon if k is a unit and a collapsed polygon otherwise. This
is why "rotate the wheel until structure appears" cannot work: the only
knob is k.

**F3. The colour of a chord under wheel k is its k-th Fourier coefficient.**
Centroid of {e^{2 pi i k x / 12} : x in S} = f_k(S) / |S| with f_k the DFT
of the indicator of S. Chroma of the mixed colour = |f_k| / |S|; hue of the
mixed colour = Fourier phase. The whole DFT of a pitch-class set is the list
of its colours under the six wheels k = 1..6, of which only k = 1 and k = 5
are injective. Under the chromatic wheel, "grey" chords (f_1 = 0) are the
balanced sets; under the fifths wheel they are the sets with f_5 = 0.
Counted by enumeration: 98 subsets are grey under each injective wheel, 922
under k = 6 (the whole-tone wheel, two hues).

**F4. The tritone is complementary under every affine wheel.** 6 is the
unique element of order 2, fixed by every automorphism, so u·6 = 6 and the
tritone lands opposite on every wheel. Checked for all 48.

**F5. Injective wheels for n-TET number phi(n)/2 up to symmetry.** n = 3, 4,
6 have one; n = 5, 8, 10, 12 have two; every n > 12 has at least three. So
12 is the largest equal temperament whose circle admits exactly one
non-chromatic arrangement. This is a fact about phi(n) = 4, not about
music or colour.

**F6. Maximally even sets are the most saturated chord colours** (Clough and
Douthett 1991; Amiot 2007, 2016). Among 7-note sets the diatonic scale is
the unique maximiser of |f_5|; among 5-note sets the pentatonic; among 7-note
sets the chromatic cluster uniquely maximises |f_1|. Reproduced by exhaustive
enumeration of all subsets. Under the fifths wheel the diatonic scale is the
most vivid seven-note colour and a whole-tone scale is grey; under the
chromatic wheel the cluster is the most vivid and the diatonic scale is dull.

## 3. Empirical results

**E1. Exhaustive consonance search** (`probe_consonance.py`). Objective:
Spearman correlation over the 66 unordered pairs between hue distance
d(f(x), f(y)) and dissonance of ic(x - y). All bijections with f(0) = 0 and
f(1) <= 6 (21,772,800 maps, every equivalence class under hue rotation and
reflection) were scored exactly, against 200,000 uniformly random bijections.

| measure | chromatic | fifths | best over all 12! | best non-affine | null mean (sd) | null max |
| --- | --- | --- | --- | --- | --- | --- |
| Sethares | -0.730 | **0.609** | 0.609 (= fifths) | 0.570 | 0.000 (0.136) | 0.504 |
| Tenney | -0.488 | **0.702** | 0.702 (= fifths) | 0.646 | 0.001 (0.136) | 0.571 |
| ordinal | -0.488 | **0.702** | 0.702 (= fifths) | 0.646 | 0.001 (0.136) | 0.571 |

The circle of fifths is the unique argmax under all three measures, 4.5 to
5.2 null standard deviations above the mean, and no map of the other
21,772,799 reaches it. The 48 affine maps take exactly two scores. The
chromatic wheel is the *worst* structured choice: adjacent hues are the most
dissonant intervals. MDS (F2) says the same in the continuous setting: the
mode-5 eigenvalue dominates in every measure and the mode-1 eigenvalue is
negative for two of three and below 3 percent of mode 5 for the third.

**E2. The colour side is not a metric 12-gon** (`probe_perceptual.py`).

| wheel | adjacent CIEDE2000 max/min | non-circulant energy fraction | notes |
| --- | --- | --- | --- |
| HSL, 30° steps, s = 1, l = 0.5 | **8.49** | 0.070 | the 12 HSL hues land 6.5° to 61.4° apart in OKLCH hue (ratio 9.4); OKLab radius spread 63 percent; lightness 0.45 to 0.97 |
| OKLCH, 30° steps, L = 0.7, fixed C | 1.49 | 0.013 | a circle by construction; its perceptual steps still vary by half |
| OKLCH, 30° steps, L = 0.7, max chroma | 1.46 | 0.034 | attainable chroma varies 2.6x with hue (blue and magenta vivid, cyan and green weak) |
| CIELAB, 30° steps, L = 65, C = 30 | 1.49 | 0.014 | same protocol, same spread |

The wheel a colour picker draws (HSL) is far from any regular polygon in a
perceptual space. A wheel built to be regular in OKLCH is regular only
because it was built so, and even then its twelve steps are not perceptually
equal. The sRGB primaries and secondaries sit at OKLCH hues 29, 110, 143,
195, 264, 328 degrees: gaps of 81, 33, 52, 69, 64, 61. There is no
12-fold, 6-fold or even 4-fold symmetry in perceptual hue; the four unique
hues of opponent theory are irregularly spaced and Munsell's perceptually
spaced circle is 5-fold and 10-fold, not 12.

**E3. The wave version** (`probe_spectrum.py`). Visible light, 380 to 750
nm, spans 0.98 octaves of frequency, the coincidence Newton used. Twelve
equal-tempered steps of light frequency mapped to monochromatic hue (CIE
1931 colour matching functions via the Wyman, Sloan, Shirley 2013 analytic
fit, validated on the equal-energy white, the luminous-efficiency peak and
the sRGB dominant wavelengths 611, 549, 463 nm) give, across the 7.8
semitones from 660 to 420 nm where the fit is trustworthy and hue is
monotone: hue steps per semitone of 1.4, 38.6, 71.8, 21.5, 27.4, 55.5, 54.1
degrees (ratio 50), a total hue span of about 275 degrees, and a non-spectral
purple arc of about 85 degrees that no wavelength produces. So the physical
octave of light is not a circle (it is an interval, closed only by the
purple line that the eye invents), and equal steps in log-frequency are
nowhere near equal steps in hue. The ear keeps the spectrum; the eye projects
it onto three broad cones and discards the rest. That projection is the
reason F3 holds: colour mixing is linear and sound is not mixed at all.

**E4. Other temperaments** (`probe_fourier.py`). For n = 5..31 the dominant
MDS mode of the Sethares dissonance curve was computed. The chromatic mode is
the worst embedding for every n >= 9 and its eigenvalue grows more negative
with n. The dominant mode is injective and generated by the best fifth for
n in {5, 12, 13, 16, 17, 19, 23, 26}; for n in {6, 8, 10, 14, 20, 21, 28}
the best circular embedding of consonance collapses pitch classes (in 24-TET
the fifth is 14 steps and gcd(14, 24) = 2, so no bijective wheel puts
fifths adjacent). 12 is in the good set; so are 19 and 5. This is one
objective and one roughness model, and it says 12 is unremarkable within
that set.

## 4. Candidate patterns, and what killed them

* *"Rotate the colour wheel against the chromatic scale until structure
  appears."* There is nothing to rotate into: by F1, the hue side sees only
  the choice of character, and rotation is a symmetry of the objective.
  Killed by F1 and by the 48 affine maps taking exactly two scores.
* *"The circle of fifths fits colour better than the chromatic scale."* It
  fits *dissonance* better, uniquely and decisively (E1), and this is a
  statement about the harmonic series (3/2 is the simplest non-octave ratio)
  with no colour in it. Replace the hue 12-gon by any twelve labels on a
  circle and the result is unchanged.
* *"Complementary colours are the tritone, triadic harmony the augmented
  triad, analogous colours the cluster."* True under every wheel (F4 and the
  k = 4 wheel), and empty: regular polygons on a circle are regular polygons
  on a circle. Itten's colour-harmony polygons were borrowed from music in
  the first place, and the empirical colour-harmony literature (Ou and Luo;
  Schloss and Palmer) finds preference driven by hue similarity and lightness
  contrast, not by polygons.
* *"Equal hue steps match equal semitones because both are waves."* Killed
  by E3: hue per semitone of light varies fiftyfold and the spectrum covers
  three quarters of the wheel.
* *"Maybe a non-affine bijection encodes consonance better than fifths."*
  Searched exhaustively; none does (E1). The best non-affine map trails by
  0.04 to 0.06 and is not invariant under transposition, so it would assign
  different colours to the same interval in different keys.

## 5. The strongest reason it is trivial

Both objects are circles, and that is the entire overlap. The music side is
a *group*: Z_12 is homogeneous, every pitch class looks like every other, and
its representation theory (six Fourier modes, two of them faithful) is the
complete list of ways to draw it on a circle. The colour side is not a group:
perceptual hue has four irregularly spaced unique hues, a 2.6-fold variation
in attainable chroma, an 85-degree arc of non-spectral purples, and no
rotation symmetry at all. A bijection between them can only transport the
group structure onto the labels. Any pattern you find is a pattern of Z_12,
and all of those were already in the DFT literature (Lewin 1959, Quinn 2006,
Amiot 2016, Tymoczko and Yust 2019 on phase as pitch-class sum).

## 6. What survived adversarial testing

Two things, both about hearing rather than colour, and both rediscoveries
in substance if not in this exact form:

1. **The circle of fifths is the unique bijection of Z_12 onto a 12-gon that
   maximises rank agreement between cyclic distance and dissonance**, over
   all 12! maps and under three unrelated dissonance measures. Original
   computation; the continuous version (F2, mode 5 dominates) is a
   two-line consequence of circulant structure and is well known to the DFT
   school in the form "the fifth Fourier coefficient measures diatonicity".
2. **The colour of a chord is its Fourier coefficient** (F3). This is the one
   formulation in which colour adds something real: the eye's linear mixing
   is exactly the operation that turns a pitch-class set into a Fourier
   coefficient, and the twelve-bin wheel is exactly a character. It makes
   Amiot's maximal-evenness theorem a statement about saturation: the
   diatonic scale is the most vivid seven-note colour under the fifths wheel.
   Good for teaching the DFT of pitch-class sets; not new mathematics.

## 7. Speculation and follow-up hunts

* **Fourier-phase colouring of real music** (Tymoczko and Yust 2019 note
  that the k-th phase of a transposition orbit is the pitch-class sum). Hue
  = phase under the fifths wheel, chroma = |f_5|, lightness = |f_1| or
  cardinality gives a three-channel colour for any chord or windowed passage,
  with key changes as hue rotations and chromaticism as desaturation. That is
  a visualisation, not a theorem, and it should be built as one.
* **n-TET and the injective-generator set** {5, 12, 13, 16, 17, 19, 23, 26}
  from E4 is one roughness model away from meaning anything. A hunt with
  Plomp-Levelt, Vassilakis and Hutchinson-Knopoff curves and a stated
  objective could say whether that set is stable. Cheap, probably empty.
* **Perceptual colour harmony as a dissimilarity on the hue circle** could be
  run through the same circulant test: if a measured hue-harmony matrix is
  far from circulant (E2 says the distance matrices are), there is no
  "circle of fifths for colour", which would close the analogy from the
  colour side as E1 closes it from the music side.

## 9. Round two: the cyclotomic ontology, and the paths first skipped

The operator pushed back on the first verdict and asked for bolder
reformulation. Four skipped paths were run (`probe_round2.py`,
`probe_cyclotomic.py`); one of them changed the language.

**R1. Metamerism.** If the eye is a linear projector, chords with equal
Fourier coefficient are metamers. Over all 4096 subsets, the chromatic wheel
distinguishes 1763 (cardinality, colour) pairs, the fifths wheel 1763, the
six-hue wheel k = 2 347, k = 3 175, k = 4 125, k = 6 49, and the full DFT all
4096. **The two injective wheels together also distinguish exactly 1763.**
The fifths wheel carries no information the chromatic wheel lacks. The
largest metamer class is the 24 grey hexachords (three tritone pairs, or two
augmented triads).

**R2. Why: the two wheels are Galois conjugates.** Write a chord as the
cyclotomic integer a(S) = sum_{x in S} zeta^x in Z[zeta_12], zeta =
e^{2 pi i/12}. Then f_k(S) is the image of a(S) under zeta -> zeta^k, and for
k a unit mod 12 that is an element of Gal(Q(zeta_12)/Q) = (Z/12)^x. So
**a colour wheel is a complex place of the cyclotomic field Q(zeta_12), and
chromatic versus fifths is the Galois group modulo complex conjugation.**
Q(zeta_12) has degree phi(12) = 4, hence two complex places, hence two
wheels; the largest n with [Q(zeta_n):Q] = 4 is 12 (F5); the collapsed
wheels k = 2, 4, 3, 6 are the places of the subfields Q(omega), Q(omega),
Q(i), Q; the tritone is complementary because zeta^6 = -1 in every place
(F4); transposition is multiplication by the unit zeta^c; inversion is
complex conjugation. Checked: f_5(S) = sigma_5(f_1(S)) for all 4096 subsets.
Every result of sections 2 and 3 is a sentence in this language.

**R3. The prediction it makes: chromatic saturation times fifths saturation
is a rational integer.** |f_1(S)|^2 |f_5(S)|^2 = N(a(S)), the field norm
from Q(zeta_12) to Q of an algebraic integer, so it is a non-negative integer
for every chord. In interval-vector terms, with iv_d the number of pairs at
interval class d,

    |f_1|^2 = a + b sqrt(3),  |f_5|^2 = a - b sqrt(3),
    a = |S| + iv_2 - iv_4 - 2 iv_6,  b = iv_1 - iv_5,  N = a^2 - 3 b^2.

Checked for all 4096 subsets. Consequences, enumerated over the 224 set
classes under D_12: only **ten** norms occur, {0, 1, 4, 9, 13, 16, 25, 36,
37, 64}; 18 classes are grey (N = 0, the sets with f_1 = 0); **84 classes are
units** (N = 1), among them the major and minor triads, the diminished triad,
the pentatonic and the diatonic scale, the semitone and the major third.
Units are the classes with (a, b) in {(1, 0), (2, 1), (7, 4)} up to sign, so
a unit chord either has iv_1 = iv_5 and a = 1, or one more semitone than
fifth (or the reverse) and a = 2. The invariant is coarse: the interval
vector takes 200 values on the 224 classes, the norm ten, and nine norm
values are shared by different interval vectors. The pair (|f_1|^2, |f_5|^2)
lies on the hyperbola xy = N (`figures/chroma_hue_norm.png`): a chord vivid
under one wheel is dull under the other unless its norm is large, and the
pentatonic (0.07 against 13.9) is the extreme case with N = 1.

So "the major triad is a unit of Z[zeta_12]" is true and not special; 37
percent of set classes are. The honest grade: a derivable fact, checked by
enumeration, whose knownness was searched once (section 8) without finding
the norm stated as a chord invariant; Amiot's book places the coefficients
in cyclotomic fields and Z-related sets share the norm trivially (same
interval vector), so the framing is probably folklore to the DFT school.

**R4. Orbifold radius against chroma.** Tymoczko's voice-leading distance
from a chord to the nearest perfectly even chord of its cardinality, against
|f_1| (chroma under the chromatic wheel): Spearman 0.955 for trichords,
0.913 for tetrachords, 0.917 for hexachords, and in no cardinality is |f_1|
a function of the radius (two to six distinct values per radius). Tymoczko
2008 ("Set-class similarity, voice leading, and the Fourier transform")
already makes this connection; this is a rediscovery with numbers.

**R5. The torus: two collapsed wheels at once.** Z_12 = Z_3 x Z_4 by the
Chinese remainder theorem, so the k = 4 wheel (three values, the augmented
cosets) and the k = 3 wheel (four hues, the diminished-seventh cosets) are
jointly injective. That embeds Z_12 in a torus, which is the neo-Riemannian
Tonnetz rather than a circle, and it is the one note-to-colour code in
which the four opponent unique hues get a job (hue = dim-7 coset, lightness
= augmented coset). The 24 major and minor triads get 24 distinct codes.
Pretty; no theorem.

**R6. Real perceptual geometry.** Replacing the cyclic metric by the measured
CIEDE2000 matrix of a perceptual wheel (OKLCH fixed chroma, and HSL) and
searching bijections again (hill climb with 40 restarts, 100,000-map null):
fifths remains best on five of six (wheel, measure) pairs; on HSL with
Sethares a non-affine map gains 0.018 (0.506 against 0.488), below the
null's standard deviation of 0.134. And a small theorem fell out: for any
affine wheel and *any* distance matrix on the hues, every transposition-
invariant objective is invariant under hue rotation, because each hue pair
is paired with a function of its hue difference. Rotating the wheel does
nothing even when the wheel is irregular.

**Verdict after round two.** Unchanged for the question as posed. The better
question is R2: a colour wheel is a complex place of Q(zeta_12), which turns
the note-to-colour story into the arithmetic of Z[zeta_12] and produces one
integer invariant (R3) that is true, cheap, and coarse. Not a pursuit; a
paragraph worth keeping.

## 8. What was searched

The knownness check is partial. Consulted from memory and confirmed by one
web search on 2026-08-22: Amiot, *Music through Fourier Space* (2016);
Quinn, "General equal-tempered harmony" (2006-07); Clough and Douthett,
"Maximally even sets" (1991); Tymoczko and Yust, "Fourier phase and
pitch-class sum" (2019); Yust's review of Amiot (MTO 23.3). None of these
discusses hue; the search found no published bridge between Fourier phase
of pitch-class sets and a perceptual hue circle, which is weak evidence of
absence and is reported as such. The colour-side references (Ottosson 2020
for OKLab; Sharma, Wu and Dalal 2005 for CIEDE2000; Wyman, Sloan and
Shirley 2013 for the CMF fit) are used as published and pinned by tests.

## Reproduce

```bash
.venv/bin/python hunts/chroma_hue/probe_consonance.py   # ~4 min, exhaustive
.venv/bin/python hunts/chroma_hue/probe_perceptual.py
.venv/bin/python hunts/chroma_hue/probe_spectrum.py
.venv/bin/python hunts/chroma_hue/probe_fourier.py
.venv/bin/python hunts/chroma_hue/probe_round2.py      # ~3 min
.venv/bin/python hunts/chroma_hue/probe_cyclotomic.py
.venv/bin/python hunts/chroma_hue/make_figures.py
.venv/bin/python hunts/chroma_hue/make_figure_norm.py
.venv/bin/python -m pytest -q tests/test_chroma_hue.py
```

Figures: `figures/chroma_hue_wheels.png` (Z_12 painted by its six
characters), `chroma_hue_consonance.png` (the exhaustive score distribution
with fifths and chromatic marked), `chroma_hue_perceptual.png` (the HSL hues
in the OKLab plane, and the spectral octave), `chroma_hue_spectrum.png`
(MDS eigenvalue by Fourier mode, three measures), `chroma_hue_norm.png`
(the 224 set classes on ten hyperbolas xy = N).

# VERIFICATION: every exact number by a second implementation, and planted faults

**Hunt #148. Status: the cross-check run reproduces every exact number quoted in this
hunt's documents; files produced on branch `hunt/ff-probe`, not landed.** Every count on
this page is read from `results_second.json` (written by `crosscheck.py`) or measured by
`test_ffprobe.py`, and pinned there. Grades as in `MISSION.md`.

## 1. The second implementation

`ffprobe_pari.py` writes the arithmetic again in PARI/GP, through cypari2, and imports
nothing from `ffprobe.py`: residue symbols by resultant and by Frobenius at each prime
factor, Gauss sums by enumeration of the residues, by the Davenport-Hasse closed form and by
the prime-power reduction, cyclotomic numbers as polmods modulo polcyclo(N), Patterson's C
and rho_0, the probe's weights and its direct sum, the local factor of eq. (local-P) by its
definition, and the rival's L-polynomials, whose roots come from PARI's `polroots`. Python
and numpy only add up integer exponent histograms (counts of roots of unity). The
conventions are read again from the sources, not from `ffprobe.py`.

`crosscheck.py` runs it over the ranges of the primary run. Where the documents quote a
value, PARI recomputes the value and the two are compared as exact elements of Q(zeta_N);
where they quote a count of checks, PARI recomputes the count on its own. The identities
the second implementation uses beyond the definitions (the Chinese remainder theorem for
Gauss sums, Davenport-Hasse, the prime-power reduction, Gamma(c) = gamma_3(c) for squarefree
c, which it uses at degree 5) are each checked inside PARI against enumeration at smaller
degree (item `pari_internal`, and the Davenport-Hasse and C_p items).

## 2. What was reproduced

RESULTS_TABLE

## 3. Planted faults

`ffprobe.FAULTS` switches on eight planted faults, four wrong Gauss-sum signs and four wrong
residue symbols, each at a different place, and `test_ffprobe.py` checks which of six quick
equality checks each one turns red: the two symbol routes, Davenport-Hasse against
enumeration, the structural route against enumeration, Lemma 7.1 locally (definition
against closed form at T + 1 for j = 0..5 and at T^2 + 1 for j = 0, 3), the probe's direct
and Euler representations at (0,2,1), and the PARI implementation against `ffprobe`. Without
a plant all six are green.

| plant | what is wrong | checks turned red |
|---|---|---|
| `gauss_sign` | G_1(P) negated at every prime of degree 2 (structural route) | structural, Lemma 7.1, probe, PARI |
| `gauss_brute_sign` | every enumerated Gauss sum negated | Davenport-Hasse, structural, probe, PARI |
| `dh_sign` | the Davenport-Hasse closed form negated | Davenport-Hasse |
| `prime_gauss_all` | every prime Gauss sum G_m(P) negated (structural route) | structural, Lemma 7.1, probe, PARI |
| `tau_sign` | every tau(eps chi^j) negated | all but the symbol routes |
| `symbol` | the Frobenius-route symbol modulo T + 1 one step off | all but Davenport-Hasse |
| `symbol_res` | the resultant-route symbol modulo T + 1 one step off | all six |
| `dlog` | the discrete logarithm of 2, which both symbol routes share, one step off | all six |

Every plant turns at least one check red. The Davenport-Hasse closed form of `gauss_dh`
feeds nothing else (the structural route has its own prime formula), so its sign is caught
by its own check alone. A fault in a component that both of `ffprobe`'s own routes share is
what the PARI comparison is for: it goes red for six of the eight plants.

## 4. Reproduce

```
.venv/bin/python hunts/ff_probe/crosscheck.py                 # results_second.json, checkpointed per item
.venv/bin/python -m pytest -q -n0 hunts/ff_probe/test_ffprobe.py -k "plant or lesion or second"
```

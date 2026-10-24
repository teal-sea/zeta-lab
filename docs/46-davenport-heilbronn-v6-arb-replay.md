# 46. The Davenport-Heilbronn v6 census: a same-verifier Arb replay

> On 2026-10-24 this laboratory re-ran the published verifier of Nathan Berzai's
> v6 census of Davenport-Heilbronn zeros (Zenodo, version DOI
> 10.5281/zenodo.23585903) from scratch on a 32-core Linux host, after replacing
> its one binary64 step, the disc majorant `M_bound`, by an Arb outward enclosure.
> All 400 windows and all 1,268 listed off-line zeros recomputed with zero
> failures and reproduced the census exactly: 1,268 pairs off the line, 25,078
> zeros on it, 27,614 in total for 0 < Im s < 20,000. This is a full replay with
> the author's own code, one repaired function, and the same ball-arithmetic
> library. It is **not** a second independent implementation, not a kernel-checked
> theorem, and the word this repository reserves for `zeta/rigor.py` does not apply.

## 1. What was replayed, exactly

Upstream artifact. `DH_census_v6_package.zip`, SHA-256
`c50c0bcef907daa2fdfa30c92f6011edf4ef87eadd6467cf1b6e34eb0565355f`, the single
file of Zenodo record 23585903 (published 2026-10-23, title "A Certified Census
of Davenport-Heilbronn Zeros to Height 20,000", v6). Its `CITATION.cff` gives
`doi: 10.5281/zenodo.21910254`; that is the **concept DOI** resolving to the
latest version, confirmed against the Zenodo API on 2026-10-24
(`conceptdoi` 21910254, `doi` 23585903). Cite the version DOI for the bytes
replayed here and the concept DOI for the catalogue as a living record. Code is
MIT, data CC-BY 4.0, both (c) 2026 Nathan Berzai; the receipts and tables kept
here are redistributed under those terms with this attribution.

Inputs pinned. `dh_zeros_master_v6.csv` SHA-256
`1ce493501c9356cf7bbb433add0a5120b0fed87bc7acdbaedb93e286e8ba4050` (1,268 rows);
`closure_table.csv` `f4c2601ee5f68eb773c3b73ee293c4b05749898e031b2135b2838cf8094aaf1a`
(400 windows of height 50); `verify/vdh.py`
`f8e03d7e69035682d6e574e0f3ac7b5e1b8ffb2247dbae1713efc4a97a964398`;
`verify/vwin.py` `80b6f9919cc8a0eb1ccae5f1c9c1dd96e10c564f50e23ac60316914a7649e913`.

Environment. Python 3.11.17, python-flint 0.9.0 (Arb/FLINT), mpmath 1.4.1,
numpy 2.4.6, Linux x86-64, `OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1`, eight
worker processes. The package scripts carry three hard-coded Windows path
literals (v6 CSV, closure CSV, v5 CSV); only those were changed in the copy that
ran. The package ships no v5 file, so the v5 input was a proxy derived from the
1,232 v6 rows carrying a nonempty `n`; it feeds only the descriptive
"new since v5" flag, never a count.

The one source change. `vdh.py:74-82` computed the Cauchy-disc majorant
`M_bound` in binary64 (`math.hypot`, `4.0 ** (-smin)`, a `1.001` margin) and
converted the float to Arb afterwards. A float is not an upper bound. The
repaired `vdh.py` (SHA-256
`471bc0ec9f4d85f92d84e0bf9211eb684f0d5aa8fd705233b1eaedf05dec6666`, 71-line
normalized diff kept as `vdh_arb_majorant.patch` inside the receipts tarball)
evaluates the same displayed expression in Arb from the exact centre ball,
lower-encloses `smin`, proves `smin > -19/20` and `kappa < 2840791/10^7` as
interval facts, and returns an Arb endpoint enclosure; the Taylor error balls
are then built from `abs_upper()` of that enclosure, so no Arb value is treated
as an exact scalar. Every guard and bisection decision in `vwin.py` is
untouched (`vwin.py` byte-identical to the package copy up to the path
literals). A descriptive comparison over all 20,000 interior, 401 edge and
1,268 row centres put the repaired/original ratio in
[0.999999999999999, 1.0000000000000009]; the ratio is a diagnostic, never a
certificate of anything.

## 2. What ran and what came out

```
.venv/bin/python gates.py                                    # exit 0, G0..G3 true
.venv/bin/python check_bound.py                              # exit 0, 21,669 centres, 0 exceptions
.venv/bin/python lesion.py                                   # exit 0, fault rejected (section 4)
.venv/bin/python -u run_fresh.py --workers 8 --seconds 850   # exit 0, wall 729.33 s, 400 receipts
.venv/bin/python -u certify_rows.py 950 rows_cert.jsonl      # exit 0, wall 173.40 s (after a 60 s first pass)
python3 summarize.py                                         # exit 0, assertions passed
```

Results, re-derived in this repository from the raw receipts by
`scripts/dh_v6_replay_audit.py` (not copied from the worker's summary):

| quantity | value |
|---|---|
| window receipts, distinct, `status == computed`, runner exit 0 | 400 / 400 |
| windows with `N_S != S`, undecided separator sign, or `imag_not_zero` | 0, 0, 0 |
| sum of `N_R` (off-line pairs by the argument principle) | 1,268 |
| sum of `N_S` (on-line zeros by sign changes of Z) | 25,078 |
| total multiplicity `N_S + 2 N_R` | 27,614 |
| row receipts, distinct, `winding == 1`, verdict confirmed, Rouche radius present | 1,268 / 1,268 |
| listed rows per window equal to that window's `N_R`, and to `offline_pairs_v6` | 400 / 400 |
| disagreements with the v6 CSV or closure table | 0 |
| retries, errors, timeouts, memory stops | 0 |

Every number agrees with the census and with the earlier fresh replays
(21 + 379 windows without the bound repair, and 1,268 rows). Agreement of
same-code runs across two majorant implementations is evidence that the float
majorant was not the weak point in practice; it is not independent validation
of the algorithm.

## 3. The exact evidence rung

Enclosure-carrying for every numeric step of one verifier: the finite-window
counts now carry Arb enclosures through the one step that previously did not.
It stops short of the hardened rung as this repository uses it, because no
independent route agrees with it, and far short of kernel-checked. Every
statement below is conditional on the items in section 5.

- Finite range only: `0 < Im s < 20,000`. Nothing above, nothing about any
  conjecture, and nothing about zeros on `Re s = 1/2` beyond their count.
- Same verifier, not a second one. The replay exercised the author's
  `vwin.window` and row routines with one function replaced. There is no
  independent interval implementation, and the receipts hold aggregate counts
  and radii, not every accepted contour segment.
- The analytic majorant is a derived Euler-Maclaurin bound, checked by hand:
  with `a = m/5`, coefficients `(1, k, -k, -1)` and the periodic-`B2` form of
  the Hurwitz zeta, the pole terms pair into `(1/5)[int_1^4 x^-s dx + k int_2^3 x^-s dx]`,
  of modulus at most `(3 + k) J / 5 < 1.4 J` for `0 < k < 0.2840791`, and the
  remaining terms give the code's bracket with `|B2| <= 1/6` and `|s| <= S`.
  This derivation lives in a review note, not a proof kernel. The lab checked
  the pole-pairing arithmetic and the sign of `smin` on the finite domain; it
  did not formalize the Euler-Maclaurin identity.
- Boxes versus windows. Each listed zero has a winding box of half-side
  `0.0199995...` and a smaller Rouche disc. Two of the 1,268 boxes cross a
  horizontal window border: row 615 (`t = 10700.01932412`, Rouche radius 1e-8)
  and row 655 (`t = 11299.99212323`, Rouche radius 3e-9). Both Rouche discs lie
  strictly inside their window, and the audit script checks this for all
  1,268 rows. Window counts `N_R` come from the window contour, never from the
  boxes, so box counts must not be equated with window counts; the script would
  report a third border crossing as a failure.
- The functional equation `Lambda_f(s) = Lambda_f(1-s)` with `Lambda_f = D f`,
  `D(s) = (5/pi)^((s+1)/2) Gamma((s+1)/2)`, and the reality of `e^{i theta(t)} f(1/2+it)`
  are what let on-line sign changes count zeros and let right-side zeros reflect
  to the left. They follow from the Dirichlet functional equation for the odd
  primitive characters mod 5 together with the exact identity
  `(1 + i kappa)/(1 - i kappa) = epsilon_chi`, which reduces to
  `kappa = (sqrt(10 - 2 sqrt 5) - 2)/(sqrt 5 - 1) = Im eps/(1 + Re eps)`. The
  verifier only samples `imag.contains(0)` at separators; that sample is a
  regression gate, not a proof of global reality. The identity above was
  checked algebraically in review and numerically to 1.6e-16; it is cited here
  as classical, not established by this repository's tests.

## 4. The fault the pipeline rejects

`lesion.py` loads the **original** package `vdh.py` by path and divides its
`M_bound(0.5, 0.5, 1.25)` by 1,000. At `s = 7/4 + i/2` on that disc Arb proves
`|f| > 0.99971325...` while the shrunken bound is `< 0.08366309...`; the
assertion `fails_upper_bound` is true and recorded with the source hash. That
shows a substantially too-small original majorant is caught; it does not
exercise the 400-window runner.

In this repository the receipts themselves get lesions: `scripts/dh_v6_replay_audit.py
--lesion {drop-row,shift-count,dup-window}` deletes a row receipt, decrements
one window's `N_R` with a consistent ball, or duplicates a window under another
index, and the process exits 0 only if the audit fails. `tests/test_dh_v6_replay_audit.py`
pins the clean counts and all three failures.

## 5. Limitations, stated once

1. Not an independent implementation; same Arb library, same contour logic.
2. The majorant's analytic derivation is reviewed prose, not kernel-checked.
3. The global functional equation and reality lemma are cited classical
   results, sampled by the verifier, not proved by it.
4. Float-to-Arb coordinate handling and contour guard choices outside
   `M_bound` were not exhaustively audited.
5. Receipts record counts, balls and radii per window and row, not every
   accepted segment; a reader cannot re-check a single contour step from them.
6. The v5 input is a proxy; it affects only descriptive flags.
7. Nothing here speaks to `Im s >= 20,000` or to zeros other than those counted.

## 6. Reproduce or audit

Audit the receipts (stdlib only, seconds):

```bash
.venv/bin/python scripts/dh_v6_replay_audit.py          # exit 0: 400/400, 1268/1268, 27,614
.venv/bin/python scripts/dh_v6_replay_audit.py --lesion drop-row
.venv/bin/python -m pytest -q tests/test_dh_v6_replay_audit.py
```

`data/dh_v6_replay/manifest.json` pins the tarball hash, every member hash, the
upstream hashes, the repaired-verifier hash, library versions, wall times and
exits. `data/dh_v6_replay/receipts.tar.gz` holds the 400 window receipts, the
1,268 row receipts, the v6 CSV and closure table (CC-BY 4.0, Berzai) and the
71-line majorant patch (MIT).

Re-run the verifier: download the Zenodo zip, confirm its SHA-256, unzip, point
the three path literals in `verify/*.py` at the extracted CSVs, apply
`vdh_arb_majorant.patch` to `verify/vdh.py`, install
`python-flint==0.9.0 numpy<3 mpmath` in a Python 3.11 environment, then run
the package's `gates.py`, window and row drivers; the 400 windows took about
5,600 CPU-core-seconds (wall 729 s at eight workers) and the rows about 230. The complete worker tree (drivers,
`summarize.py`, logs, timings) is archived outside the repository as
`replay-evidence.tar.gz`, SHA-256
`92e67a3797ee455bc348ff7c79db98e9aa706f36335fcd3fc81fd18ed3895b48`.

Related: [docs/08](08-why-it-is-hard.md) section 4 on why Davenport-Heilbronn
is a rival and not a counterexample; `hunts/README.md` for the lab's own
Davenport-Heilbronn scans, which treat these catalogue coordinates as external
input.

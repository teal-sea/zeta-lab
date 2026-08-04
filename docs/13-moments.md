# 13 — Moments: External Windows, Finite Estimates, Honest Scorecards

The moments programme starts with a data contract, not a formula. The lab's
local cache reaches only the low thousands in height; the external tables that
matter live at much larger indices and heights. `zeta/moments.py` is the first
increment: it ingests those published tables without recomputing their zeros or
destroying their local spacing information. The second increment estimates
finite moments from a *separate* table of sampled critical-line values, derives
the standard leading constants, and gates the conjectural sixth/eighth rows on
calibration against the proved second/fourth rows. The third increment adds the
auditable file boundary for that second table: exact decimal rows, raw-byte
checksums, and a mandatory link to the imported zero-window digest.

It does not infer values of `ζ` from its zeros, endorse a moment conjecture, or
provide evidence for RH. A finite-window comparison is an instrument check.

---

## 1. Why ordinary floats are the wrong storage type

Odlyzko's table `zeros5` contains zeros numbered `10^22 + 1` through
`10^22 + 10^4`. Its first two published ordinates are represented as offsets
from the integer base `1370919909931995300000`:

```text
8226.68016095
8226.77659152
```

Their gap is `0.09643057`. A float64 near the full ordinate has a unit in the
last place millions of times larger than that gap, so converting the two full
ordinates to float64 makes them equal. `tests/test_moments.py` pins this failure
mode directly.

`ExternalZeroTable` therefore stores

```text
absolute ordinate = Decimal(base) + Decimal(offset)
```

and performs reconstruction and subtraction in a local decimal context large
enough to retain every supplied digit. This means exact reproduction of the
source text, **not** exact knowledge of the mathematical zero. The source's
accuracy statement remains attached as `accuracy_note`.

---

## 2. Supported sources and formats

### 2.1 Odlyzko's six public text tables

The pinned catalogue `ODLYZKO_TABLES` covers `zeros1` through `zeros6` from
[Andrew Odlyzko's official table index][odlyzko-index]. It records each table's
first zero index, declared row count, decimal base, source URL, and published
accuracy wording.

The three high-index tables contain prose headers. The loader parses and checks
their base and index range:

| Table | Indices | Representation |
| --- | ---: | --- |
| `zeros3` | `10^12 + 1` … `10^12 + 10^4` | offsets from `267653395647` |
| `zeros4` | `10^21 + 1` … `10^21 + 10^4` | offsets from `144176897509546973000` |
| `zeros5` | `10^22 + 1` … `10^22 + 10^4` | offsets from `1370919909931995300000` |

The wording matters: `zeros4` and `zeros5` explicitly say their values are not
guaranteed and are probably accurate within `10^-6`. The loader preserves that
qualification and does not upgrade it.

### 2.2 LMFDB plain-text exports

The LMFDB list endpoint emits one indexed zero per line:

```text
1 14.1347251417346937904572519835625
2 21.0220396387715549926284795938969
```

That `index ordinate` contract is visible in the [LMFDB route source][lmfdb-route].
The underlying data were produced by David Platt; the [LMFDB source note][lmfdb-source]
describes their provenance and precision.

`load_lmfdb_zeros` supports this plain-text export. It deliberately does not
support the separate compressed bulk binary representation; LMFDB's own
[binary reader][lmfdb-reader] is the specification for that format, and adding
it should be a separate, fixture-backed increment.

Both loaders detect gzip by its magic bytes, so a `.gz` suffix is optional.

### 2.3 Critical-line value samples

`load_critical_line_samples` reads an ASCII table with three whitespace-separated
columns:

```text
# illustrative synthetic rows: offset abs-zeta absolute-error
8226.0 2.000 0.001
8227.0 2.000 0.001
```

Offsets use the paired `ExternalZeroTable.base`; absolute ordinates are forbidden
at this boundary because they would lose the local grid at high height. Blank
lines and `#` comments are ignored. Gzip is detected by magic bytes.

The resulting `CriticalLineSampleTable` stores the exact decimal tokens, the
raw-file SHA-256, the value source and URL, the error classification, and the
paired zero-table SHA-256. `estimate_moment_from_samples` refuses a different
zero table even when its numerical window happens to overlap.

---

## 3. Validation contract

An import fails with `ZeroTableError` if any checked invariant fails:

- the file is unreadable, non-ASCII, or a damaged gzip stream;
- a token is malformed, non-finite, non-positive, duplicated, or out of order;
- LMFDB indices are non-positive or non-contiguous;
- an expected first index or row count does not match;
- an Odlyzko table is unknown, truncated, or disagrees with its pinned header;
- a caller-supplied SHA-256 digest does not match the supplied bytes.

The stored `sha256` is always the digest of the bytes the caller supplied. For
a gzip file that means the compressed bytes, not the decompressed text. A
checksum proves which file was processed; it does not prove the source's
mathematics or provenance by itself.

---

## 4. Operator workflow

Always run from the repository root with the project virtual environment.

### Odlyzko

```python
from zeta.moments import load_odlyzko_zeros

table = load_odlyzko_zeros(
    "data/external/zeros5",
    expected_sha256="<64 hex digits from the acquisition record>",
)

first = table.ordinate(table.first_index)
first_gap = table.spacing_after(table.first_index)
print(table.first_index, first, first_gap, table.accuracy_note)
```

The basename identifies the table. For a renamed download, pass
`table_id="zeros5"` explicitly.

### LMFDB

```python
from zeta.moments import load_lmfdb_zeros

table = load_lmfdb_zeros(
    "data/external/zetazeros",
    expected_first_index=1,
    expected_count=100_000,
    expected_sha256="<64 hex digits from the acquisition record>",
    source_url="<the exact LMFDB query URL used>",
)
```

Supply both the expected count and checksum for a durable acquisition record.
Index continuity alone cannot detect a cleanly truncated tail when the desired
end index is unknown.

### Critical-line values

```python
from zeta.moments import load_critical_line_samples

samples = load_critical_line_samples(
    "data/external/critical-line-values.txt.gz",
    table=table,
    error_kind="estimate",
    value_source="<evaluator, version, parameters, and accuracy method>",
    source_url="<exact value-table URL>",
    expected_count=declared_count,
    expected_sha256="<64 hex digits from the acquisition record>",
)
```

Do not write `float(table.ordinate(...))` for high tables. Downstream code must
either operate on `Decimal`, operate on local offsets, or explicitly convert to
an arbitrary-precision type at enough precision for the full height plus the
published fractional digits.

---

## 5. Reproducibility record

External datasets are not committed to the repository by this module. For each
acquisition, record at least:

1. the exact source URL and retrieval date;
2. the byte length and SHA-256 digest;
3. the table identifier or LMFDB query bounds;
4. the loader's first index, last index, count, base, and `accuracy_note`;
5. the zeta-lab commit that consumed it.

For a value table, also record its evaluator and version, its pointwise error
method, and the SHA-256 of the zero table used to define its decimal origin.

The private or local data file and the code that interprets it are separate
objects. Keeping the acquisition record makes a later scorecard auditable even
if a host replaces a download in place.

---

## 6. The finite statistic and its two input datasets

For an integer `k ≥ 1` and a sampled interval `[A,B]`, the estimator reports

```text
M̂₂ₖ[A,B] = 1/(B-A) · trapezoid ∫ₐᵇ |ζ(1/2 + it)|²ᵏ dt.
```

This requires two logically different inputs:

1. an `ExternalZeroTable`, which fixes the high-height window and carries the
   source URL, digest, index range, base, and accuracy wording;
2. explicit sampled values of `|ζ(1/2+it)|`, with offsets relative to the same
   decimal base, a pointwise error claim, and a separate `value_source` note.

The second input cannot be reconstructed from the first. A list of zero
ordinates tells us where `ζ` vanishes, not its scale between zeros. In
particular, multiplying an entire function by a nonzero factor can preserve its
zeros and change every moment. `estimate_moment` therefore has no fallback that
evaluates or manufactures missing values.

The sample grid must contain an odd number of at least five points. The full
composite trapezoid and its every-other nested grid have the same endpoints.
Their absolute difference is returned as `sampling_error_estimate`; it is a
resolution diagnostic, not a rigorous quadrature bound. Caller-supplied
absolute value errors are propagated monotonically through the `2k`-th power
and returned separately as `value_error`, with `value_error_kind` preserving
whether the caller called them a `bound` or an `estimate`.

Every estimate also carries `sample_sha256`, a digest of the exact decimal
offsets, values, errors, error-kind, and value-source note. Because `k` is not
part of that digest, the scorecard can mechanically require its second through
eighth moments to come from the identical sample contract.

Binary floats are rejected at this boundary. At the `10^22` landmark, even the
sample abscissae—not only the imported zeros—must remain decimal offsets.

---

## 7. Leading references: theorem and conjecture are different fields

Write

```text
∫₀ᵀ |ζ(1/2+it)|²ᵏ dt  ~  Cₖ T (log T)ᵏ²,
        Cₖ = aₖ gₖ/(k²)!.
```

For integer `k`, the [Keating–Snaith][keating-snaith] leading convention and
the [CFKRS][cfkrs] arithmetic factor are

```text
aₖ = ∏ₚ (1-1/p)ᵏ² Σₘ≥₀ binom(m+k-1,k-1)² p⁻ᵐ,
gₖ = (k²)! ∏ⱼ₌₀ᵏ⁻¹ j!/(k+j)!.
```

`moment_reference` derives these conventions rather than storing four decimal
constants. The tests pin `g₁,…,g₄ = 1, 2, 42, 24024` and the resulting table:

| `k` | moment | literature status | leading coefficient |
| ---: | ---: | --- | --- |
| 1 | 2nd | theorem (Hardy–Littlewood) | `1` |
| 2 | 4th | theorem (Ingham) | `1/(2π²)` |
| 3 | 6th | conjecture | `a₃/8640` |
| 4 | 8th | conjecture | `24024·a₄/16!` |

For `k=3,4`, the Euler product is finite. The exact integer-`k` local identity

```text
(1-x)ᵏ² Σₘ≥₀ binom(m+k-1,k-1)²xᵐ
  = (1-x)⁽ᵏ⁻¹⁾² Σⱼ₌₀ᵏ⁻¹ binom(k-1,j)²xʲ
```

makes each prime factor finite. The omitted-factor estimate is carried as
`coefficient_truncation_error`; guarded mpmath rounding is not enclosed, so the
result is accurate rather than certified. `tests/test_moments.py` checks a
later prime cutoff lies inside the earlier conservative tail allowance.

The proved labels refer to the global `[0,T]` asymptotics. For a shifted or
short interval, `leading_moment_mean` averages
`Cₖ log(t/(2π))ᵏ²` over `[A,B]` as an explicit normalization convention. It
does **not** promote a global theorem into a short-interval theorem.

---

## 8. The scorecard gate

`moment_scorecard` requires estimates for `k=1` and `k=2`, all sharing the same
window, sample count, value source, and input-table digest. It compares both to
their proved leading references using a caller-stated relative tolerance.

- If both pass, supplied `k=3` and `k=4` rows receive their conjectural leading
  predictions.
- If either fails, the high-order finite-window predictions are `None` and the
  rows are listed in `withheld_k`.
- Sampling error, value error, and arithmetic truncation remain separate. They
  are not subtracted from the residual to manufacture a pass.

This is an instrument gate, not a statistical hypothesis test. Heavy-tailed
high moments can require far denser and longer sampling than low moments, and a
passing low-order calibration does not validate the open formulas.

The standing mutation test replaces the proved fourth-moment coefficient by a
value 2% too large. The calibration must fail and the sixth/eighth predictions
must remain withheld. That test checks the gate has teeth rather than merely
printing a warning beside the same output.

---

## 9. Operator sketch

```python
from zeta.moments import estimate_moment_from_samples, moment_scorecard

# `table` and `samples` came from the two independent loaders above.
estimates = [
    estimate_moment_from_samples(
        table,
        samples,
        k=k,
    )
    for k in (1, 2, 3, 4)
]

card = moment_scorecard(
    estimates,
    calibration_relative_tolerance="0.25",
)
```

No external critical-line value dataset is bundled. Acquiring and documenting
one is an operator/data task; the zero tables are not relabelled as value data.
No finite computation settles, supports, or weakens RH.

### Source audit, 2026-08-04

The public sources located do not provide a dense downloadable value table that
meets this contract. [LMFDB's auxiliary dataset][lmfdb-datasets] lists zeta
zeros, not sampled values. [Hiary and Odlyzko][hiary-odlyzko] document dense
Odlyzko–Schönhage evaluations in a high window, but their paper and indexed
author page expose results rather than the underlying rows. [Bober and
Hiary][bober-hiary] publish selected extreme values and plots at still greater
heights, which are deliberately biased observations and cannot estimate an
interval moment. The loader is therefore shipped without a fixture masquerading
as research data.

[odlyzko-index]: https://www-users.cse.umn.edu/~odlyzko/zeta_tables/index.html
[lmfdb-route]: https://github.com/LMFDB/lmfdb/blob/main/lmfdb/zeros/zeta/zetazeros.py
[lmfdb-reader]: https://github.com/LMFDB/lmfdb/blob/main/lmfdb/zeros/zeta/platt_zeros.py
[lmfdb-source]: https://www.lmfdb.org/knowledge/show/rcs.source.zeros.zeta
[keating-snaith]: https://people.maths.bris.ac.uk/~mancs/papers/RMTzeta.pdf
[cfkrs]: https://arxiv.org/abs/math/0206018
[hiary-odlyzko]: https://www-users.cse.umn.edu/~odlyzko/doc/zeta.moments.pdf
[lmfdb-datasets]: https://www.lmfdb.org/datasets/
[bober-hiary]: https://people.maths.bris.ac.uk/~jb12407/data/zeta/index_Z11.html

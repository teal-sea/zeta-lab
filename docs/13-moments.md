# 13 — Moments: External Zero Data Before Estimation

The moments programme starts with a data contract, not a formula. The lab's
local cache reaches only the low thousands in height; the external tables that
matter live at much larger indices and heights. `zeta/moments.py` is the first
increment: it ingests those published tables without recomputing their zeros or
destroying their local spacing information.

This is infrastructure for later experiments. It does **not** estimate a zeta
moment yet, endorse a moment conjecture, or provide evidence for RH.

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

The private or local data file and the code that interprets it are separate
objects. Keeping the acquisition record makes a later scorecard auditable even
if a host replaces a download in place.

---

## 6. What comes next

The next increment is the estimator and scorecard described in `ROADMAP.md`:

- state the finite statistic and normalization before implementing it;
- recover the proven second- and fourth-moment leading terms in controlled
  ranges before displaying sixth- or eighth-moment predictions;
- keep theorem, conjectural prediction, finite-height measurement, truncation
  error, and sampling error in separate fields;
- mutation-test the scorecard so a deliberately wrong constant fails;
- consume external ordinates through this module—never silently fall back to
  computing a replacement zero table.

No finite computation settles, supports, or weakens RH. The purpose is to test
the numerical instrument and compare finite data with clearly labelled
theorems and conjectures.

[odlyzko-index]: https://www-users.cse.umn.edu/~odlyzko/zeta_tables/index.html
[lmfdb-route]: https://github.com/LMFDB/lmfdb/blob/main/lmfdb/zeros/zeta/zetazeros.py
[lmfdb-reader]: https://github.com/LMFDB/lmfdb/blob/main/lmfdb/zeros/zeta/platt_zeros.py
[lmfdb-source]: https://www.lmfdb.org/knowledge/show/rcs.source.zeros.zeta

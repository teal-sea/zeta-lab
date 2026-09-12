# Recorded arXiv responses for `scripts/literature_monitor.py`

**TODO: these are PLACEHOLDERS, not recordings.** The `PLACEHOLDER` marker file in
this directory says so, and `tests/test_literature_monitor.py::test_fixtures_are_real_recordings_not_placeholders`
skips loudly while it exists.

On 2026-09-12 the arXiv API returned HTTP 429 to every request for the whole build
session (a recording attempt with 3 second spacing and exponential backoff ran for
eighteen minutes and landed nothing). The files here were written by hand in the exact
shape of an arXiv Atom response, with the identifiers, dates and authorship the brief
records (`meta/literature-monitor.md` sections 1 and 2) and `PLACEHOLDER` wherever a
fact was not in the brief. They let the tests pin the query-level facts of section 2
and the section 4 gate *against the fixture shape*; they do not demonstrate that the
live queries return those papers. That demonstration is still owed.

## How to record the real thing

From the repository root, when `https://export.arxiv.org/api/query` answers 200:

```bash
rm tests/fixtures/literature_monitor/q-*.xml tests/fixtures/literature_monitor/manifest.json \
   tests/fixtures/literature_monitor/baseline.json
python scripts/literature_monitor.py --record tests/fixtures/literature_monitor \
    --since 2026-09-01 --until 2026-09-12 --no-version-check
rm tests/fixtures/literature_monitor/PLACEHOLDER
python -m pytest tests/test_literature_monitor.py -q
```

`--record` is resumable: a query that fails is retried on the next run and the
manifest keeps what already landed. Then run `--verify-authors` and promote any
author query that returns its known paper into `QUERIES` (see the note at
`AUTHOR_WATCH_UNVERIFIED` in the script).

## Layout

- `manifest.json`: request key (sha256 of the sorted, urlencoded params, first 16 hex
  digits; `_request_key` in the script) to `{file, status, params}`. A status other
  than 200 is replayed as that HTTP error.
- `q-<query>-start<N>-<key>.xml`: one Atom page per request.
- `baseline.json`: query name to entry count on the first page. A query with a
  positive baseline that returns zero entries live fails the run (brief, section 5).

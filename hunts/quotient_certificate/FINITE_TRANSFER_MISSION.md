# Finite weighted transfer continuation

Input: main `880ec07ae605d93f4c49e4464d8b4526457cfb65`, after PRs
#203, #205 and #206. This continues the existing mission; #203 is complete.

Question: can the exact common-period correlations control the finite,
attainable-cell, prime-weighted certificate, with its actual drift retained?
Deliver one precisely quantified transfer or an exact feasible obstruction,
and account separately for the passage from variance to linear excess.

Ownership: Codex, finite correlations. Write new files in this directory and
one focused test file; regenerate CONTEXT.md if the test inventory changes.
Preserve all earlier outputs. Claude owns the dual-witness and barrier work
in certificate_lp_frontier; read its comparison table only.

Use exact small controls and the three saved rational feasible vectors.
Prime data evaluate the measure, not a prime-blind coefficient construction.
No new optimization, large search, CI experiment, or formalization. Run
numerical libraries with one thread and pytest with `-n 0 -m "not slow"`.
The milestone ships as an open PR for cross-review, without merging.

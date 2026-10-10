"""Collection rules for `pytest hunts`.

The nightly runs every hunt's own tests (`full.yml`). One file here is named
like a test but is an archived script: importing
`prime_pair_error/frontier/2026-09-06/joint_support_analysis/test_q20_direction.py`
runs its computation and overwrites the committed `q20_direction_results.json`.
The archive is checksummed (`SHA256SUMS.json`) and its file count is pinned by
`tests/test_adaptive_freeze_archive.py`, so it is excluded here rather than
renamed or given a conftest of its own.
"""

collect_ignore = [
    "prime_pair_error/frontier/2026-09-06/joint_support_analysis/test_q20_direction.py",
]

# depth_bound_selfterm: runs

Estimate written before launch: the probe reads one existing JSON artifact and
evaluates a finite cosine-hyperbolic sum on a grid of a few hundred depths, so
seconds on a laptop, no checkpointing needed.

```runmanifest
id: depth_bound_selfterm-2026-09-15-probe
hunt: depth_bound_selfterm
started: 2026-09-14T22:44-05:00
finished: 2026-09-15T00:05-05:00
ran:
  - .venv/bin/python hunts/depth_bound_selfterm/probe.py
  - .venv/bin/python -m pytest -n0 hunts/depth_bound_selfterm/test_probe.py tests/test_hunt_probe_discipline.py tests/test_docs_numbering.py tests/test_doors.py tests/test_huntspec.py
outcome: dual kernel S(y) < r(0) first at y ~ 0.9198925 and S(y) < 0 first at y ~ 0.9528774, numpy and mp.workdps(40) agreeing; in-band control has no crossing on [0, 1.5]; an independent review rescan at mp.dps 60 on step 0.025 reproduced both crossings and the control; the depth-frame verdict of the first draft was withdrawn in review (see RESULTS.md)
artifacts:
  - hunts/depth_bound_selfterm/probe.py
  - hunts/depth_bound_selfterm/test_probe.py
  - hunts/depth_bound_selfterm/RESULTS.md
```

Provenance: the first draft was written by Gemini 3.1 Pro through the
Antigravity CLI, corrected by Grok 4.6, and reviewed with the depth-frame
section rewritten by Claude. Two review defects were fixed before landing: a
control whose crossings had been typed in rather than computed, and a depth
range borrowed from a raw-coordinate frame for a kernel stated in unfolded
coordinates.

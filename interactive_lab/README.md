# interactive_lab — browser visualizations

Standalone HTML pages that animate what the laboratory computes. They are
illustrations, not results: nothing here is measured, tested for mathematical
content, or cited by any claim. The numbers they display are hard-coded from
the ground-truth values pinned in `tests/` — if a page and the suite ever
disagree, the suite is right.

| Page | What it shows | Open with |
|---|---|---|
| [prime_genesis.html](prime_genesis.html) | the sieve, the staircase and the zero spectrum as one animated story | any browser, no server needed |

Pages must stay single-file and dependency-light so "open the file" keeps
being the whole instruction. `tests/test_doors.py` pins that much (the file
exists, parses as HTML, and pulls no external scripts).

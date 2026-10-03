# NOTE: shared checkout collision (2026-10-03)

Commit 8bf43452 on this branch ("Correct midpoint remainder ...")
staged the whole hunt directory and thereby swept in two files I
did not author and had never seen:

- hunts/rh_resolve/EQUIVALENCE.md
- hunts/rh_resolve/check_logderiv.py

Both belong to a concurrent session working the same checkout
(their content: a log-derivative equivalence with killed
sufficient conditions, honestly graded as derived argument plus
spot checks). I have read EQUIVALENCE.md; its evidence grades are
stated correctly (no enclosure word, no resolution claimed) and I
have no objection to its content. Attribution: those two files are
the other session's work, committed under my commit by an
overbroad `git add`. I will stage explicit file lists from here
on. I do not edit those files; the other session does not edit
mine (file lists are disjoint). check_logderiv.py performs no file
writes, so it cannot clobber enclosure artifacts.

Lesson for the operator: two sessions sharing one checkout will
collide exactly this way; worktrees per agent (AGENTS.md) would
have prevented it.

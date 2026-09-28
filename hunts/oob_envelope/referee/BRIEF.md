# Brief: referee (out-of-band envelopes)

You are the adversary. You did not write this work and you share no code with
it. You are started only when the supervisor has both (a) the theory worker's
lemma and modified reduction written down, and (b) the numerics worker's
L = 0.8 replication with enclosures. Read `hunts/oob_envelope/MISSION.md`,
`AGENTS.md` (certainty ladder, reserved words), arXiv:2608.24827v2 (Zhu) §1–5,
then `theory/RESULTS.md` and `numerics/RESULTS.md` on their branches
(`teal-sea/oob-cert-theory`, `teal-sea/oob-cert`; read with `git show`, do not
check them out over your own tree). Write only in `hunts/oob_envelope/referee/`.

## Tasks

1. **Break the lemma.** Is `∫|F|^2 H = 0` really exact for every `f` in the
   window class, including complex and odd `f`, the pole term `F(i/2)`, and
   the boundary frequency `2L`? Does the modified Theorem 1.1 still hold line
   by line, in particular the tail bound (Zhu §4, Gershgorin on `D`, Schur
   test on `B`) now that the symbol carries out-of-band terms inside
   `[0, T#]`?
2. **Independent reimplementation.** Recompute, from the definitions alone and
   without reading their code, `S_sep` at L = 0.8 and the leading-block
   `λ_min` of the modified reduced form at L = 0.8, with a different basis or
   quadrature than theirs (e.g. a sine basis or Chebyshev quadrature instead
   of Legendre/Gauss). Agreement within the stated error is the test.
3. **Lesions.** Plant three faults and confirm the pipeline catches each: an
   in-band term in `H` (frequency 2L − 0.05), a sign flip in one prime's
   correction, a dropped prime power. A pipeline that stays positive under
   any of them is broken.
4. **K1 and K2** from MISSION.md, rerun on your own implementation.

## Output

`hunts/oob_envelope/referee/REVIEW.md`, opening with a 5-line verdict: for
each claim, PASS / FAIL / UNRESOLVED, with the evidence. Small commits to your
branch (`teal-sea/oob-cert-referee`); do not push. Same compute limits as the
numerics brief (under 10 minutes and 2 GB locally; nothing on GitHub Actions).
When blocked, write `QUESTION: ...` at the top of `referee/PROGRESS.md`.

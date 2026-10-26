# PRICE: the out-of-band reduction at the Davenport-Heilbronn line

Hunt #146 (`weil_dh_line`), 2026-10-21. Question, windows and rules: `MISSION.md`.
Every number below comes from a JSON artifact in this directory and is pinned by
`test_price.py`, or is hedged where it stands. Grades follow `CLAUDE.md`:
*measured* (one float route), *hardened* (ball enclosures carry every step, or
independent routes agree). Nothing here is kernel-checked, and nothing here bears on
RH (`docs/08`).

## 1. Summary

1. **Floor.** The comb-operator floor `S*_L = λ_max(P)` (the least envelope constant
   any out-of-band `H` can reach, oob_envelope theory Theorem 2) lies in
   `[3.708999, 3.715978]` at `L = 7/5`, `[4.588862, 4.595259]` at `31/20`,
   `[5.637302, 5.643859]` at `L_DH = 1.71079` and `[5.678833, 5.685405]` at
   `L_31 = 1.71699`. Both ends are ball arithmetic: a Rayleigh quotient below and a
   Schur test evaluated on every sub-interval of the window above. *Hardened.*
2. **Per-prime.** `S_sep = Σ_p λ_max(T_p)` is `5.470224`, `6.832880`, `8.930519`,
   `8.930519` (balls of width below `1e-8`, *hardened*); the evaluable sine-kernel
   envelopes at degree 16 give `5.619106`, `7.002783`, `9.157718`, `9.157718`
   (enclosure-carrying, by the oob_envelope code).
3. **Joint, evaluable.** PENDING
4. **Go/no-go at the DH line: NO-GO.** PENDING
5. **Scout at `L = 7/5`.** PENDING
6. **K2.** PENDING

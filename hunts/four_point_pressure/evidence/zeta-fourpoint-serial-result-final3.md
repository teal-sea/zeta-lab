# Serial checkpointed-image final3 on Modal

- Verdict: **FULL PASS: every layer checkpointed, verification clean**
- Run id `20260928t220203`, Modal app id `ap-7zxzQj0YqTwlQUP6P06ecn` (profile teal-sea)
- Source HEAD `5522b96314f7f63198ae3ec4e71d954255f93d1a`; client: client exit 0
- Wall (image prep + build + teardown): 920.9 s of 9600 s bound; after teardown: none active

## Layer receipts (exact, in build order; one lake build at a time)

| # | layer | module | ok | seconds | sorry warnings | olean sha256 (first 12) | cpu.max | memory.max |
|---|---|---|---|---|---|---|---|---|
| 0 | preflight | None | True | 0 | - | - | unreadable: FileNotFoundError(2, 'No such file or directory') | unreadable: FileNotFoundError(2, 'No such file or directory') |
| 1 | Base | FourPointCand.Base | True | 67.6 | 0 | f1519e29dcde | unreadable: FileNotFoundError(2, 'No such file or directory') | unreadable: FileNotFoundError(2, 'No such file or directory') |
| 2 | Cells0 | FourPointCand.Cells0 | True | 225.2 | 0 | c2536e28ca76 | unreadable: FileNotFoundError(2, 'No such file or directory') | unreadable: FileNotFoundError(2, 'No such file or directory') |
| 3 | Cells1 | FourPointCand.Cells1 | True | 261.5 | 0 | 4f35e716faba | unreadable: FileNotFoundError(2, 'No such file or directory') | unreadable: FileNotFoundError(2, 'No such file or directory') |
| 4 | Cells2 | FourPointCand.Cells2 | True | 647.2 | 0 | c65236689366 | unreadable: FileNotFoundError(2, 'No such file or directory') | unreadable: FileNotFoundError(2, 'No such file or directory') |
| 5 | Cells3 | FourPointCand.Cells3 | True | 161.5 | 0 | d517326dd03d | unreadable: FileNotFoundError(2, 'No such file or directory') | unreadable: FileNotFoundError(2, 'No such file or directory') |
| 6 | Cells4 | FourPointCand.Cells4 | True | 242.2 | 0 | de7ae8ea3a50 | unreadable: FileNotFoundError(2, 'No such file or directory') | unreadable: FileNotFoundError(2, 'No such file or directory') |
| 7 | Cells5 | FourPointCand.Cells5 | True | 233.1 | 0 | 839d2202edff | unreadable: FileNotFoundError(2, 'No such file or directory') | unreadable: FileNotFoundError(2, 'No such file or directory') |
| 8 | Cells6 | FourPointCand.Cells6 | True | 405.2 | 0 | a744df6dbb47 | unreadable: FileNotFoundError(2, 'No such file or directory') | unreadable: FileNotFoundError(2, 'No such file or directory') |
| 9 | Cells7 | FourPointCand.Cells7 | True | 211.6 | 0 | 9eb22050dee6 | unreadable: FileNotFoundError(2, 'No such file or directory') | unreadable: FileNotFoundError(2, 'No such file or directory') |
| 10 | Cells8 | FourPointCand.Cells8 | True | 195.1 | 0 | 8645ae00e096 | unreadable: FileNotFoundError(2, 'No such file or directory') | unreadable: FileNotFoundError(2, 'No such file or directory') |
| 11 | Cells9 | FourPointCand.Cells9 | True | 235.6 | 0 | aa24b3df1273 | unreadable: FileNotFoundError(2, 'No such file or directory') | unreadable: FileNotFoundError(2, 'No such file or directory') |
| 12 | Cells10 | FourPointCand.Cells10 | True | 253.4 | 0 | 960e90ac331c | unreadable: FileNotFoundError(2, 'No such file or directory') | unreadable: FileNotFoundError(2, 'No such file or directory') |
| 13 | Cells11 | FourPointCand.Cells11 | True | 246.5 | 0 | bc2d381dc5b4 | unreadable: FileNotFoundError(2, 'No such file or directory') | unreadable: FileNotFoundError(2, 'No such file or directory') |
| 14 | Cells12 | FourPointCand.Cells12 | True | 241.8 | 0 | f0d7a2844300 | unreadable: FileNotFoundError(2, 'No such file or directory') | unreadable: FileNotFoundError(2, 'No such file or directory') |
| 15 | Cells13 | FourPointCand.Cells13 | True | 217.2 | 0 | ea2f5d328757 | unreadable: FileNotFoundError(2, 'No such file or directory') | unreadable: FileNotFoundError(2, 'No such file or directory') |
| 16 | Cells14 | FourPointCand.Cells14 | True | 192.8 | 0 | 781dd9012b9a | unreadable: FileNotFoundError(2, 'No such file or directory') | unreadable: FileNotFoundError(2, 'No such file or directory') |
| 17 | Cells15 | FourPointCand.Cells15 | True | 259.0 | 0 | ad18bb6c8ec0 | unreadable: FileNotFoundError(2, 'No such file or directory') | unreadable: FileNotFoundError(2, 'No such file or directory') |
| 18 | Cells16 | FourPointCand.Cells16 | True | 206.1 | 0 | aad89eeb2d76 | unreadable: FileNotFoundError(2, 'No such file or directory') | unreadable: FileNotFoundError(2, 'No such file or directory') |
| 19 | Cells17 | FourPointCand.Cells17 | True | 251.4 | 0 | 65f7748abf0c | unreadable: FileNotFoundError(2, 'No such file or directory') | unreadable: FileNotFoundError(2, 'No such file or directory') |
| 20 | Cells18 | FourPointCand.Cells18 | True | 234.3 | 0 | 167aa2e6cf0e | unreadable: FileNotFoundError(2, 'No such file or directory') | unreadable: FileNotFoundError(2, 'No such file or directory') |
| 21 | Cells19 | FourPointCand.Cells19 | True | 275.5 | 0 | 4d02354fb7bb | unreadable: FileNotFoundError(2, 'No such file or directory') | unreadable: FileNotFoundError(2, 'No such file or directory') |
| 22 | Cells20 | FourPointCand.Cells20 | True | 381.2 | 0 | eb7d5778f561 | unreadable: FileNotFoundError(2, 'No such file or directory') | unreadable: FileNotFoundError(2, 'No such file or directory') |
| 23 | Cells21 | FourPointCand.Cells21 | True | 224.2 | 0 | 5ec6191a1198 | unreadable: FileNotFoundError(2, 'No such file or directory') | unreadable: FileNotFoundError(2, 'No such file or directory') |
| 24 | Cells22 | FourPointCand.Cells22 | True | 247.6 | 0 | 9aeb827918ed | unreadable: FileNotFoundError(2, 'No such file or directory') | unreadable: FileNotFoundError(2, 'No such file or directory') |
| 25 | Cells23 | FourPointCand.Cells23 | True | 240.8 | 0 | a7f5fd7a4bfe | unreadable: FileNotFoundError(2, 'No such file or directory') | unreadable: FileNotFoundError(2, 'No such file or directory') |
| 26 | Cells24 | FourPointCand.Cells24 | True | 223.9 | 0 | 6bcd84ded893 | unreadable: FileNotFoundError(2, 'No such file or directory') | unreadable: FileNotFoundError(2, 'No such file or directory') |
| 27 | Cells25 | FourPointCand.Cells25 | True | 91.5 | 0 | f47d17439996 | unreadable: FileNotFoundError(2, 'No such file or directory') | unreadable: FileNotFoundError(2, 'No such file or directory') |
| 28 | Cells | FourPointCand.Cells | True | 150.8 | 0 | 6460057e5370 | unreadable: FileNotFoundError(2, 'No such file or directory') | unreadable: FileNotFoundError(2, 'No such file or directory') |
| 29 | Cover | FourPointCand.Cover | True | 120.5 | 0 | 19faa5471e27 | unreadable: FileNotFoundError(2, 'No such file or directory') | unreadable: FileNotFoundError(2, 'No such file or directory') |
| 30 | Chunks0 | FourPointCand.Chunks0 | True | 662.2 | 0 | ba6470aab112 | unreadable: FileNotFoundError(2, 'No such file or directory') | unreadable: FileNotFoundError(2, 'No such file or directory') |
| 31 | Chunks1 | FourPointCand.Chunks1 | True | 919.7 | 0 | fb4a7fd937af | unreadable: FileNotFoundError(2, 'No such file or directory') | unreadable: FileNotFoundError(2, 'No such file or directory') |
| 32 | Chunks2 | FourPointCand.Chunks2 | True | 905.6 | 0 | b8f26b5f3d33 | unreadable: FileNotFoundError(2, 'No such file or directory') | unreadable: FileNotFoundError(2, 'No such file or directory') |
| 33 | Chunks3 | FourPointCand.Chunks3 | True | 721.5 | 0 | 6a0647e939a7 | unreadable: FileNotFoundError(2, 'No such file or directory') | unreadable: FileNotFoundError(2, 'No such file or directory') |
| 34 | Chunks4 | FourPointCand.Chunks4 | True | 1519.6 | 0 | 69a01534ecd0 | unreadable: FileNotFoundError(2, 'No such file or directory') | unreadable: FileNotFoundError(2, 'No such file or directory') |
| 35 | Chunks5 | FourPointCand.Chunks5 | True | 842.1 | 0 | 83a1211da32d | unreadable: FileNotFoundError(2, 'No such file or directory') | unreadable: FileNotFoundError(2, 'No such file or directory') |
| 36 | Chunks6 | FourPointCand.Chunks6 | True | 661.7 | 0 | b173ed8e8cde | unreadable: FileNotFoundError(2, 'No such file or directory') | unreadable: FileNotFoundError(2, 'No such file or directory') |
| 37 | Chunks7 | FourPointCand.Chunks7 | True | 874.4 | 0 | 561909c016d1 | unreadable: FileNotFoundError(2, 'No such file or directory') | unreadable: FileNotFoundError(2, 'No such file or directory') |
| 38 | Chunks8 | FourPointCand.Chunks8 | True | 695.3 | 0 | 1fdf9f632529 | unreadable: FileNotFoundError(2, 'No such file or directory') | unreadable: FileNotFoundError(2, 'No such file or directory') |
| 39 | Chunks9 | FourPointCand.Chunks9 | True | 754.6 | 0 | 97b34883ba47 | unreadable: FileNotFoundError(2, 'No such file or directory') | unreadable: FileNotFoundError(2, 'No such file or directory') |
| 40 | Chunks10 | FourPointCand.Chunks10 | True | 574.9 | 0 | e31883223db2 | unreadable: FileNotFoundError(2, 'No such file or directory') | unreadable: FileNotFoundError(2, 'No such file or directory') |
| 41 | Chunks11 | FourPointCand.Chunks11 | True | 956.4 | 0 | 0a4d6067da67 | unreadable: FileNotFoundError(2, 'No such file or directory') | unreadable: FileNotFoundError(2, 'No such file or directory') |
| 42 | Chunks12 | FourPointCand.Chunks12 | True | 590.3 | 0 | 164c2944c4de | unreadable: FileNotFoundError(2, 'No such file or directory') | unreadable: FileNotFoundError(2, 'No such file or directory') |
| 43 | Chunks13 | FourPointCand.Chunks13 | True | 888.9 | 0 | 196c88cf0f2d | unreadable: FileNotFoundError(2, 'No such file or directory') | unreadable: FileNotFoundError(2, 'No such file or directory') |
| 44 | Chunks14 | FourPointCand.Chunks14 | True | 567.5 | 0 | f53fabcac4d5 | unreadable: FileNotFoundError(2, 'No such file or directory') | unreadable: FileNotFoundError(2, 'No such file or directory') |
| 45 | Chunks15 | FourPointCand.Chunks15 | True | 1036.9 | 0 | 891f15000995 | unreadable: FileNotFoundError(2, 'No such file or directory') | unreadable: FileNotFoundError(2, 'No such file or directory') |
| 46 | Boxes | FourPointCand.Boxes | True | 619.6 | 0 | dfd161dc66db | unreadable: FileNotFoundError(2, 'No such file or directory') | unreadable: FileNotFoundError(2, 'No such file or directory') |
| 47 | Main | FourPointCand.Main | True | 85.3 | 0 | ffd87085e390 | unreadable: FileNotFoundError(2, 'No such file or directory') | unreadable: FileNotFoundError(2, 'No such file or directory') |
| 48 | WholeLibrary | FourPointCand | True | 65.6 | 0 | fd6641e3e909 | unreadable: FileNotFoundError(2, 'No such file or directory') | unreadable: FileNotFoundError(2, 'No such file or directory') |

## Source hashes

- local fp `a72e89fc0b5f1d72a41d17ef5f5b7be892b238f15668384dd866382fe8962c82` / bridge `a4931d8311da41b1a41cba4f63cda6a0313167bc447ad1674d28159a92f8d2ff`
- remote (preflight, before any Lean) fp `a72e89fc0b5f1d72a41d17ef5f5b7be892b238f15668384dd866382fe8962c82` / bridge `a4931d8311da41b1a41cba4f63cda6a0313167bc447ad1674d28159a92f8d2ff`, equal: **True**
- remote token scan: {'fp_hits': [], 'bridge_hits': [], 'string_hits': [], 'unterminated': []}
- remote (final verify) fp `a72e89fc0b5f1d72a41d17ef5f5b7be892b238f15668384dd866382fe8962c82` / bridge `a4931d8311da41b1a41cba4f63cda6a0313167bc447ad1674d28159a92f8d2ff`
- toolchain file `leanprover/lean4:v4.33.0-rc2`; `lean --version`: `Lean (version 4.33.0-rc2, x86_64-unknown-linux-gnu, commit d8b18978322de05a8f3dba51ef03cf5461676c17, Release)`
- oleans unchanged since their layer: {'/repo/hunts/ainta_seven_point/lean-four-point/.lake/build/lib/lean/FourPointCand/Base.olean': True, '/repo/hunts/ainta_seven_point/lean-four-point/.lake/build/lib/lean/FourPointCand/Cells0.olean': True, '/repo/hunts/ainta_seven_point/lean-four-point/.lake/build/lib/lean/FourPointCand/Cells1.olean': True, '/repo/hunts/ainta_seven_point/lean-four-point/.lake/build/lib/lean/FourPointCand/Cells2.olean': True, '/repo/hunts/ainta_seven_point/lean-four-point/.lake/build/lib/lean/FourPointCand/Cells3.olean': True, '/repo/hunts/ainta_seven_point/lean-four-point/.lake/build/lib/lean/FourPointCand/Cells4.olean': True, '/repo/hunts/ainta_seven_point/lean-four-point/.lake/build/lib/lean/FourPointCand/Cells5.olean': True, '/repo/hunts/ainta_seven_point/lean-four-point/.lake/build/lib/lean/FourPointCand/Cells6.olean': True, '/repo/hunts/ainta_seven_point/lean-four-point/.lake/build/lib/lean/FourPointCand/Cells7.olean': True, '/repo/hunts/ainta_seven_point/lean-four-point/.lake/build/lib/lean/FourPointCand/Cells8.olean': True, '/repo/hunts/ainta_seven_point/lean-four-point/.lake/build/lib/lean/FourPointCand/Cells9.olean': True, '/repo/hunts/ainta_seven_point/lean-four-point/.lake/build/lib/lean/FourPointCand/Cells10.olean': True, '/repo/hunts/ainta_seven_point/lean-four-point/.lake/build/lib/lean/FourPointCand/Cells11.olean': True, '/repo/hunts/ainta_seven_point/lean-four-point/.lake/build/lib/lean/FourPointCand/Cells12.olean': True, '/repo/hunts/ainta_seven_point/lean-four-point/.lake/build/lib/lean/FourPointCand/Cells13.olean': True, '/repo/hunts/ainta_seven_point/lean-four-point/.lake/build/lib/lean/FourPointCand/Cells14.olean': True, '/repo/hunts/ainta_seven_point/lean-four-point/.lake/build/lib/lean/FourPointCand/Cells15.olean': True, '/repo/hunts/ainta_seven_point/lean-four-point/.lake/build/lib/lean/FourPointCand/Cells16.olean': True, '/repo/hunts/ainta_seven_point/lean-four-point/.lake/build/lib/lean/FourPointCand/Cells17.olean': True, '/repo/hunts/ainta_seven_point/lean-four-point/.lake/build/lib/lean/FourPointCand/Cells18.olean': True, '/repo/hunts/ainta_seven_point/lean-four-point/.lake/build/lib/lean/FourPointCand/Cells19.olean': True, '/repo/hunts/ainta_seven_point/lean-four-point/.lake/build/lib/lean/FourPointCand/Cells20.olean': True, '/repo/hunts/ainta_seven_point/lean-four-point/.lake/build/lib/lean/FourPointCand/Cells21.olean': True, '/repo/hunts/ainta_seven_point/lean-four-point/.lake/build/lib/lean/FourPointCand/Cells22.olean': True, '/repo/hunts/ainta_seven_point/lean-four-point/.lake/build/lib/lean/FourPointCand/Cells23.olean': True, '/repo/hunts/ainta_seven_point/lean-four-point/.lake/build/lib/lean/FourPointCand/Cells24.olean': True, '/repo/hunts/ainta_seven_point/lean-four-point/.lake/build/lib/lean/FourPointCand/Cells25.olean': True, '/repo/hunts/ainta_seven_point/lean-four-point/.lake/build/lib/lean/FourPointCand/Cells.olean': True, '/repo/hunts/ainta_seven_point/lean-four-point/.lake/build/lib/lean/FourPointCand/Cover.olean': True, '/repo/hunts/ainta_seven_point/lean-four-point/.lake/build/lib/lean/FourPointCand/Chunks0.olean': True, '/repo/hunts/ainta_seven_point/lean-four-point/.lake/build/lib/lean/FourPointCand/Chunks1.olean': True, '/repo/hunts/ainta_seven_point/lean-four-point/.lake/build/lib/lean/FourPointCand/Chunks2.olean': True, '/repo/hunts/ainta_seven_point/lean-four-point/.lake/build/lib/lean/FourPointCand/Chunks3.olean': True, '/repo/hunts/ainta_seven_point/lean-four-point/.lake/build/lib/lean/FourPointCand/Chunks4.olean': True, '/repo/hunts/ainta_seven_point/lean-four-point/.lake/build/lib/lean/FourPointCand/Chunks5.olean': True, '/repo/hunts/ainta_seven_point/lean-four-point/.lake/build/lib/lean/FourPointCand/Chunks6.olean': True, '/repo/hunts/ainta_seven_point/lean-four-point/.lake/build/lib/lean/FourPointCand/Chunks7.olean': True, '/repo/hunts/ainta_seven_point/lean-four-point/.lake/build/lib/lean/FourPointCand/Chunks8.olean': True, '/repo/hunts/ainta_seven_point/lean-four-point/.lake/build/lib/lean/FourPointCand/Chunks9.olean': True, '/repo/hunts/ainta_seven_point/lean-four-point/.lake/build/lib/lean/FourPointCand/Chunks10.olean': True, '/repo/hunts/ainta_seven_point/lean-four-point/.lake/build/lib/lean/FourPointCand/Chunks11.olean': True, '/repo/hunts/ainta_seven_point/lean-four-point/.lake/build/lib/lean/FourPointCand/Chunks12.olean': True, '/repo/hunts/ainta_seven_point/lean-four-point/.lake/build/lib/lean/FourPointCand/Chunks13.olean': True, '/repo/hunts/ainta_seven_point/lean-four-point/.lake/build/lib/lean/FourPointCand/Chunks14.olean': True, '/repo/hunts/ainta_seven_point/lean-four-point/.lake/build/lib/lean/FourPointCand/Chunks15.olean': True, '/repo/hunts/ainta_seven_point/lean-four-point/.lake/build/lib/lean/FourPointCand/Boxes.olean': True, '/repo/hunts/ainta_seven_point/lean-four-point/.lake/build/lib/lean/FourPointCand/Main.olean': True, '/repo/hunts/ainta_seven_point/lean-four-point/.lake/build/lib/lean/FourPointCand.olean': True}
- oleans for targets that should NOT exist: []
- verify problems: []
- axiom audit ok: **True**

Raw axiom lines from Main:

```
info: FourPointCand/Main.lean:206:0: 'Zeta23Ext.Bridge.FourPoint.F4_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
info: FourPointCand/Main.lean:207:0: 'Zeta23Ext.Bridge.FourPoint.cover1' depends on axioms: [propext, Classical.choice, Quot.sound]
info: FourPointCand/Main.lean:208:0: 'Zeta23Ext.Bridge.FourPoint.four_point_cert' depends on axioms: [propext, Classical.choice, Quot.sound]
info: FourPointCand/Main.lean:209:0: 'Zeta23Ext.Bridge.FourPoint.Phi_four' depends on axioms: [propext, Classical.choice, Quot.sound]
info: FourPointCand/Main.lean:210:0: 'Zeta23Ext.Bridge.FourPoint.four_point_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
info: FourPointCand/Main.lean:211:0: 'Zeta23Ext.Bridge.FourPoint.four_point_bound_ratio' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Exact Main theorem statements (from the verified sources):

```lean
-- Main.lean
theorem F4_eq (p : ℕ) (g : Fin 3 → ℝ) :
    F 4 p g = (1/(p:ℝ)) * (g 0 + g 1 + g 2)
      + 2/3 * wfun (g 0) + 2/3 * wfun (g 1) + 2/3 * wfun (g 2)
      + wfun (g 0 + g 1) + wfun (g 1 + g 2) + 2 * wfun (g 0 + g 1 + g 2)
-- Cover.lean
theorem cover1 (x : ℝ) (h0 : 0 ≤ x) (hS : x ≤ (233/40:ℝ)) :
    (699/200000:ℝ) ≤ wfun x ∨ ((63/64:ℝ) ≤ x ∧ x ≤ (73/64:ℝ)) ∨ ((121/64:ℝ) ≤ x ∧ x ≤ (141/64:ℝ)) ∨ ((179/64:ℝ) ≤ x ∧ x ≤ (105/32:ℝ)) ∨ ((237/64:ℝ) ≤ x ∧ x ≤ (233/40:ℝ))
-- Main.lean
theorem four_point_cert :
    ∀ g : Fin (4-1) → ℝ, (∀ i, 0 ≤ g i) → (2330/1000000:ℝ) ≤ F 4 2500 g
-- Main.lean
theorem Phi_four : Phi_n 4 (2330/1000000:ℝ) 432 2500 = (14400000 * HD 1 - 17240) / 14366681
-- Main.lean
theorem four_point_bound :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((14400000 * HD 1 - 17240) / 14366681 - ε) * (Ncount T (2 * T) : ℝ)
        ≤ N0simple T (2 * T)
-- Main.lean
theorem four_point_bound_ratio :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (14400000 * HD 1 - 17240) / 14366681 - ε
        ≤ (N0simple T (2 * T) : ℝ) / (Ncount T (2 * T) : ℝ)
```

## Cost

- Metered lower bound from receipts: 20886 s x $4.396e-05/s (2 cores, 8 GiB, live modal.com/pricing) = $0.918; excludes image prep and container start.
- Worst case at the wall bound: 9600 s x $4.396e-05/s = $0.422.

## Scope

Local compile record only. No publication, no PR, no public claim. Pending external verification.

Complete client stdout+stderr: `<PRIVATE-LOCAL-SCRATCH>/zeta-fourpoint-serial/logs/launch-20260928t220203.log`

## Driver

# driver 20260928t220203

- app: `fourpoint-serial-20260928t220203` id `ap-7zxzQj0YqTwlQUP6P06ecn`
- client exit 0
- wall elapsed (incl. teardown): 920.9 s (bound 9600 s)
- after teardown: none active
- full client stdout+stderr: `<PRIVATE-LOCAL-SCRATCH>/zeta-fourpoint-serial/logs/launch-20260928t220203.log`
- last receipt in log: 48 WholeLibrary
- last saved image in log: `im-6OZMQf9oFxqLnic4UBo4mf`
- FPVERIFY ok: True (client exit code alone is not proof; only FPVERIFY ok=True over all receipts is)

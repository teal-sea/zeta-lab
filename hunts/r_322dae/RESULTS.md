# Hunt R-322DAE Results: Krenn-Gu 8x3 Orbit Census and Next Exact Frontier

## Executive Summary

This hunt settles the orbit-census layer for the Krenn-Gu 8x3 instance ($n=8$ vertices, $d=3$ colors).

1. **6x3 Baseline Checksum Verified:**
   - 15 perfect matchings ($(6-1)!! = 15$).
   - $15^3 = 3375$ monochromatic matching triples.
   - Exact group action under $S_6 \times S_3$ ($|G| = 4320$).
   - Burnside orbit count: exactly 8.
   - 8 disjoint orbits with sizes $[15, 90, 120, 270, 360, 360, 1080, 1080]$, summing to 3375.
   - Fixing the first matching $M_0$ and quotienting by its stabilizer $H = S_2 \wr S_3$ ($|H| = 48$) yields 16 pair orbits (12 under $H \times S_2$).

2. **8x3 Orbit Census Settled:**
   - 105 perfect matchings ($(8-1)!! = 105$).
   - $105^3 = 1157625$ monochromatic matching triples.
   - Exact group action under $S_8 \times S_3$ ($|G| = 40320 \times 6 = 241920$).
   - Burnside orbit count: exactly 31.
   - 31 disjoint orbits covering all 1157625 triples with zero overlap and zero unvisited triples ($\sum |Orbit_i| = 1157625$).
   - For each orbit $i$, the orbit-stabilizer theorem $|Orbit_i| \times |Stab_i| = 241920$ holds exactly.
   - Fixing the first matching $M_0$ and quotienting by its wreath-product stabilizer $H = S_2 \wr S_4$ ($|H| = 384$) partitions the 11025 pairs $(M_1, M_2)$ into 86 orbits (57 orbits under $H \times S_2$).

Total runtime for the census was 13.8 seconds with peak memory well below 50 MB, far within the 45 minute and 8 GB budget limits.

---

## 1. The 6x3 Baseline Checksum

Under $G = S_6 \times S_3$ ($|G| = 4320$):

| Orbit ID | Canonical Triple | Distinct Matchings | Orbit Size | Stabilizer Size | 2-Factor Cycle Structures |
|:---:|:---:|:---:|:---:|:---:|:---:|
| 0 | `(0, 0, 0)` | 1 | 15 | 288 | `((2, 2, 2), (2, 2, 2), (2, 2, 2))` |
| 1 | `(0, 0, 1)` | 2 | 270 | 16 | `((2, 2, 2), (4, 2), (4, 2))` |
| 2 | `(0, 0, 2)` | 2 | 360 | 12 | `((2, 2, 2), (6,), (6,))` |
| 3 | `(0, 1, 2)` | 3 | 90 | 48 | `((4, 2), (4, 2), (4, 2))` |
| 4 | `(0, 1, 3)` | 3 | 1080 | 4 | `((4, 2), (4, 2), (6,))` |
| 5 | `(0, 1, 4)` | 3 | 1080 | 4 | `((4, 2), (6,), (6,))` |
| 6 | `(0, 2, 7)` | 3 | 360 | 12 | `((6,), (6,), (6,))` |
| 7 | `(0, 2, 8)` | 3 | 120 | 36 | `((6,), (6,), (6,))` |

- Total Triples Covered: $15 + 270 + 360 + 90 + 1080 + 1080 + 360 + 120 = 3375$.
- Burnside Formula Check: $\frac{1}{4320} \sum_{g \in S_6 \times S_3} |Fix(g)| = 8.0$.
- Pair Orbits under $H = S_2 \wr S_3$: 16 orbits.
- Pair Orbits under $H \times S_2$: 12 orbits.

---

## 2. The 8x3 Orbit Census Table

Under $G = S_8 \times S_3$ ($|G| = 241920$):

| Orbit | Canonical Indices | Dist | Orbit Size | Stab | Mult (3,2,1) | Components | 2-Factor Cycles $((M_0,M_1), (M_0,M_2), (M_1,M_2))$ |
|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|
| 0 | `(0, 0, 0)` | 1 | 105 | 2304 | (4, 0, 0) | (2, 2, 2, 2) | `((2, 2, 2, 2), (2, 2, 2, 2), (2, 2, 2, 2))` |
| 1 | `(0, 0, 1)` | 2 | 3780 | 64 | (2, 2, 2) | (4, 2, 2) | `((2, 2, 2, 2), (4, 2, 2), (4, 2, 2))` |
| 2 | `(0, 0, 4)` | 2 | 10080 | 24 | (1, 3, 3) | (6, 2) | `((2, 2, 2, 2), (6, 2), (6, 2))` |
| 3 | `(0, 0, 16)` | 2 | 3780 | 64 | (0, 4, 4) | (4, 4) | `((2, 2, 2, 2), (4, 4), (4, 4))` |
| 4 | `(0, 0, 19)` | 2 | 15120 | 16 | (0, 4, 4) | (8,) | `((2, 2, 2, 2), (8,), (8,))` |
| 5 | `(0, 1, 2)` | 3 | 1260 | 192 | (2, 0, 6) | (4, 2, 2) | `((4, 2, 2), (4, 2, 2), (4, 2, 2))` |
| 6 | `(0, 1, 3)` | 3 | 30240 | 8 | (1, 2, 5) | (6, 2) | `((4, 2, 2), (4, 2, 2), (6, 2))` |
| 7 | `(0, 1, 5)` | 3 | 30240 | 8 | (1, 1, 7) | (6, 2) | `((4, 2, 2), (6, 2), (6, 2))` |
| 8 | `(0, 1, 15)` | 3 | 7560 | 32 | (0, 4, 4) | (4, 4) | `((4, 2, 2), (4, 2, 2), (4, 4))` |
| 9 | `(0, 1, 17)` | 3 | 7560 | 32 | (0, 2, 8) | (4, 4) | `((4, 2, 2), (4, 4), (4, 4))` |
| 10 | `(0, 1, 18)` | 3 | 120960 | 2 | (0, 3, 6) | (8,) | `((4, 2, 2), (6, 2), (8,))` |
| 11 | `(0, 1, 20)` | 3 | 60480 | 4 | (0, 2, 8) | (8,) | `((4, 2, 2), (8,), (8,))` |
| 12 | `(0, 1, 52)` | 3 | 60480 | 4 | (0, 2, 8) | (8,) | `((4, 2, 2), (4, 4), (8,))` |
| 13 | `(0, 1, 58)` | 3 | 30240 | 8 | (0, 2, 8) | (8,) | `((4, 2, 2), (8,), (8,))` |
| 14 | `(0, 4, 8)` | 3 | 10080 | 24 | (1, 0, 9) | (6, 2) | `((6, 2), (6, 2), (6, 2))` |
| 15 | `(0, 4, 13)` | 3 | 3360 | 72 | (1, 0, 9) | (6, 2) | `((6, 2), (6, 2), (6, 2))` |
| 16 | `(0, 4, 16)` | 3 | 60480 | 4 | (0, 2, 8) | (8,) | `((4, 4), (6, 2), (6, 2))` |
| 17 | `(0, 4, 17)` | 3 | 120960 | 2 | (0, 1, 10) | (8,) | `((4, 4), (6, 2), (8,))` |
| 18 | `(0, 4, 21)` | 3 | 120960 | 2 | (0, 2, 8) | (8,) | `((6, 2), (6, 2), (8,))` |
| 19 | `(0, 4, 23)` | 3 | 120960 | 2 | (0, 1, 10) | (8,) | `((6, 2), (8,), (8,))` |
| 20 | `(0, 4, 27)` | 3 | 60480 | 4 | (0, 1, 10) | (8,) | `((6, 2), (8,), (8,))` |
| 21 | `(0, 4, 28)` | 3 | 60480 | 4 | (0, 1, 10) | (8,) | `((6, 2), (8,), (8,))` |
| 22 | `(0, 4, 29)` | 3 | 20160 | 12 | (0, 3, 6) | (8,) | `((6, 2), (6, 2), (6, 2))` |
| 23 | `(0, 16, 32)` | 3 | 1260 | 192 | (0, 0, 12) | (4, 4) | `((4, 4), (4, 4), (4, 4))` |
| 24 | `(0, 16, 35)` | 3 | 30240 | 8 | (0, 0, 12) | (8,) | `((4, 4), (8,), (8,))` |
| 25 | `(0, 16, 52)` | 3 | 5040 | 48 | (0, 0, 12) | (8,) | `((4, 4), (4, 4), (4, 4))` |
| 26 | `(0, 16, 53)` | 3 | 15120 | 16 | (0, 0, 12) | (8,) | `((4, 4), (4, 4), (8,))` |
| 27 | `(0, 16, 55)` | 3 | 15120 | 16 | (0, 0, 12) | (8,) | `((4, 4), (8,), (8,))` |
| 28 | `(0, 16, 56)` | 3 | 30240 | 8 | (0, 0, 12) | (8,) | `((4, 4), (8,), (8,))` |
| 29 | `(0, 19, 38)` | 3 | 60480 | 4 | (0, 0, 12) | (8,) | `((8,), (8,), (8,))` |
| 30 | `(0, 19, 43)` | 3 | 40320 | 6 | (0, 0, 12) | (8,) | `((8,), (8,), (8,))` |

- Total Triples Covered: exactly 1157625.
- Burnside Formula Check: $\frac{1}{241920} \sum_{g \in S_8 \times S_3} |Fix(g)| = 31.0$.
- Simple 3-regular graph orbits (no multigraph edges, Mult `(0, 0, 12)`): Orbits 23 through 30 (8 orbits).
- Orbit 23 corresponds to the disjoint union of two $K_4$ complete graphs.
- Orbits 24 to 30 represent the 3-edge-colorings of connected cubic graphs on 8 vertices (including the 3-cube $Q_3$).

---

## 3. Structural Decomposition and Stabilizer Quotients

Fixing the first matching $M_0$ (without loss of generality, $M_0 = \{(0,1), (2,3), (4,5), (6,7)\}$) restricts the vertex permutation group to the wreath product:
$$H = Stab_{S_8}(M_0) = S_2 \wr S_4 = B_4 \quad (|H| = 2^4 \times 4! = 384)$$

The remaining search space consists of $105^2 = 11025$ matching pairs $(M_1, M_2)$.

- Under $H = S_2 \wr S_4$ (order 384), the 11025 pairs partition into **86 orbits**.
- Under $H \times S_2$ (order 768, including color transposition $(M_1 \leftrightarrow M_2)$), the pairs partition into **57 orbits**.
- Under full $S_8 \times S_3$ (order 241920), the full triples partition into **31 orbits**.

These 31 classes give an exhaustive outer branch cover after choosing one supported monochromatic matching in each colour. They do not quotient the 252 edge-weight variables or the 6,561 polynomial equations: a branch still carries the full equation system. Hunt R-044DD2 records this scope correction and uses the classes only as target-support skeletons.

---

## 4. What Was Chosen and Why

- **Exhaustive array partition versus purely group-theoretic calculation:** Precomputing the $40320 \times 105$ permutation table in NumPy (4.2 MB) enabled direct vectorised orbit generation across all 1157625 triples in 0.14 seconds.
- **Burnside Lemma as independent authority:** Burnside fixed-point evaluation over the conjugacy classes of $S_n \times S_3$ served as a non-constructive oracle confirming the 8 and 31 orbit counts independently of the constructive partition map.
- **Topological invariant classification:** For each orbit representative, 2-factor cycle structures, multigraph edge multiplicities, and connected component partitions were extracted to classify the physical graph topology.

---

## 5. What Could Not Be Settled

- The existence or non-existence of a complex weight assignment on the 28 vertex pairs of $K_8$, carrying 252 endpoint-coloured entries for $d=3$, still requires ruling out or realizing the full 6,561-equation system in every one of the 31 outer branches. Per task scope, polynomial construction and weight optimization were excluded from this census scout.

---

## Loose threads

1. **Exact support and algebraic sieving over the 31 outer branches:**
   - *What it is:* Require the twelve diagonal entries of one target-matching representative, then impose the full 6,561-equation support necessities and learn exact algebraic no-goods from returned supports.
   - *Why it matters:* This preserves the valid symmetry cover without assuming that a hypothetical witness is itself symmetric.
   - *First step:* Run the support frontier and signed-Laurent sieve in Hunt R-044DD2.

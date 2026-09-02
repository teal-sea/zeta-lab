# Erdős 617, session record (2026-09-01)

**Problem.** For r >= 3, must every r-colouring of the edges of K_{r^2+1} contain r+1
vertices whose induced K_{r+1} is missing a colour? Proved for r = 3, 4 (Erdős–Gyárfás
1999). Open for r = 5, which asks about 5-colourings of K_26. A counterexample is a
colouring in which every 6-set sees all 5 colours; equivalently, every colour class has
independence number <= 5.

## Result: the affine-plane counterexample does not extend

The known extremal colourings at n = r^2 come from AG(2,r): colour a pair of points by the
parallel class of the line through them, merging two parallel classes into one colour so r
colours cover all pairs. Every colour class then has independence number exactly r.

**Claim.** For every prime power r >= 3, this colouring of K_{r^2} cannot be extended to a
counterexample on K_{r^2+1}.

**Proof.** Suppose a new vertex v is added and let A_c be the set of old vertices joined to
v in colour c. At least two colours (r-1 of them, and r-1 >= 2) are a single parallel
class, i.e. a disjoint union of r copies of K_r, whose independent r-sets are exactly the
transversals picking one point from each line. For such a colour c and any transversal S,
the (r+1)-set {v} ∪ S must see colour c, and S contains no c-edge, so A_c ∩ S ≠ ∅. A set
meeting every transversal of r disjoint lines must contain an entire line. So two different
pure-class colours c, d give lines L_c ⊆ A_c and L_d ⊆ A_d from different parallel classes.
Lines from different parallel classes of an affine plane meet in exactly one point, but A_c
and A_d are disjoint (each vertex sends v one colour). Contradiction. ∎

`ag_extension.py` verifies both halves by SAT for q = 3 and q = 5: the AG colouring is a
valid counterexample at n = q^2, and the one-vertex extension is UNSAT.

This does **not** settle r = 5: a K_26 counterexample restricts to a K_25 counterexample at
every deleted vertex, and K_25 counterexamples other than the AG one are not ruled out.

## Negative result: brute-force SAT is out of reach at r = 5

`e617_modal.py` runs a cube-and-conquer search on Modal (kissat, one container per cube; a
cube fixes how vertex 0's r^2 edges split among the r colours, plus block-sorting symmetry
breaking, plus an optional Turán cardinality bound of >= 55 edges per colour class).

- r = 3: all 12 cubes UNSAT in ~0.1 s each (reproduces Erdős–Gyárfás).
- r = 4: 63 of 64 cubes UNSAT (hardest decided cube [5,4,4,3] at 872 s); the fully
  balanced cube [4,4,4,4] was still undecided after 14,000 s on one core, with or without
  the Turán bound.
- r = 5: all 377 cubes undecided at 300 s each; 31.4 core-hours total, nothing decided.

Conclusion: r = 5 will not fall to plain SAT plus one level of splitting. Any further
attack should exploit the structure above (every colour class needs a blocking set of >= 5
vertices hitting all of its independent 5-sets, and the five blockers must exactly
partition the 25 old vertices), or classify K_25 counterexamples first.

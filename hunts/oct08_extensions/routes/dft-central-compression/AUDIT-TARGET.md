# Neutral independent review request

Starting with raw `../dft/sources/network.tex` at upstream commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, replace the complex motif's h+1 central coordinates by h coordinates. Keep coordinate gather (Gx)_j=sum_(T containing j)x_T. Replace scatter by (R'c)_S=(sum_(j in S)c_j-(sum_j c_j)/3)/2. Keep all side maps and all surviving frame labels.

Determine whether the modified eight-row circuit is correct for arbitrary initial auxiliaries; whether all physical roles receive C^(tensor mf) after frames; and whether its exact budget is W'=2v³+3v²(vd+h), Delta'=2v²(v-3h²), with admissibility h>=21. Independently check the tensor recurrence and the h24 pure-log exponent1-51/10^11 in the exact-complex DFT model.

Separately determine the exact rank of M_(S,T)=(|S intersection T|-1)/2 on all triples and what, if anything, it proves about minimal central count for the fixed side map. Check exceptional small h, especially h9. Do not assume Gaussian-dyadic restrictions survive rational1/3. Read PROOF.md only after forming the critical identities yourself. Return exact assumptions, smallest gap/counterexample if any, and claim scope. No novelty or practical speed claim is under review.

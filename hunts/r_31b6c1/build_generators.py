import json
from collections import defaultdict
import sympy

n = 8
d = 3
def get_perfect_matchings(vertices):
    if not vertices:
        return [()]
    first = vertices[0]
    res = []
    for i in range(1, len(vertices)):
        partner = vertices[i]
        rem = vertices[1:i] + vertices[i+1:]
        for suff in get_perfect_matchings(rem):
            res.append(((first, partner),) + suff)
    return res

pms = get_perfect_matchings(tuple(range(n)))
M0 = pms[0]

def edge_key(u, v, cu, cv):
    return (min(u,v), max(u,v), cu, cv)

def get_H_S2_orbit_key(M1, M2):
    # To find the orbit of (M1, M2) under H x S2, where H = Stab(M0)
    # The invariant is the graph formed by M0, M1, M2.
    # Actually, we can just evaluate it in the 8-variable quotient!
    # If the 8-variable evaluation is NOT unique, we need a better invariant.
    pass

# We can just construct the 57 orbits by using the permutation group!
from sympy.combinatorics import Permutation, PermutationGroup
from sympy.combinatorics.named_groups import SymmetricGroup

# Or even simpler: the 57 generators are exactly the polynomials.
# Since we need to emit them as data.

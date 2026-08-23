import json
import itertools

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

pms = get_perfect_matchings(tuple(range(8)))
M0 = pms[0]

def apply_perm(M, p):
    res = []
    for u, v in M:
        pu, pv = p[u], p[v]
        res.append((min(pu, pv), max(pu, pv)))
    return tuple(sorted(res))

H_gens = [
    [1, 0, 2, 3, 4, 5, 6, 7],
    [0, 1, 3, 2, 4, 5, 6, 7],
    [0, 1, 2, 3, 5, 4, 6, 7],
    [0, 1, 2, 3, 4, 5, 7, 6],
    [2, 3, 0, 1, 4, 5, 6, 7],
    [0, 1, 4, 5, 2, 3, 6, 7],
    [0, 1, 2, 3, 6, 7, 4, 5],
]

pm_idx = {M: i for i, M in enumerate(pms)}

# 57 orbits of (M1, M2) under H x S2
pairs = [(i, j) for i in range(len(pms)) for j in range(len(pms))]
visited = set()
pair_orbits = []

for p in pairs:
    if p in visited: continue
    orbit = set()
    queue = [p]
    orbit.add(p)
    while queue:
        curr = queue.pop(0)
        curr_M1, curr_M2 = pms[curr[0]], pms[curr[1]]
        for g in H_gens:
            nxt_M1 = apply_perm(curr_M1, g)
            nxt_M2 = apply_perm(curr_M2, g)
            nxt = (pm_idx[nxt_M1], pm_idx[nxt_M2])
            if nxt not in orbit:
                orbit.add(nxt)
                queue.append(nxt)
        nxt = (curr[1], curr[0])
        if nxt not in orbit:
            orbit.add(nxt)
            queue.append(nxt)
    pair_orbits.append(list(orbit))
    visited.update(orbit)

# 31 orbits of (M0, M1, M2) under G = S8 x S3
S8_gens = []
for i in range(7):
    p = list(range(8))
    p[i], p[i+1] = p[i+1], p[i]
    S8_gens.append(p)

triples = [(0, i, j) for i in range(len(pms)) for j in range(len(pms))]
visited_t = set()
triple_orbits = []

S3_perms = list(itertools.permutations([0,1,2]))

for t in triples:
    if t in visited_t: continue
    orbit = set()
    queue = [t]
    orbit.add(t)
    while queue:
        curr = queue.pop(0)
        curr_Ms = [pms[curr[0]], pms[curr[1]], pms[curr[2]]]
        
        for g in S8_gens:
            nxt_Ms = [apply_perm(M, g) for M in curr_Ms]
            for p in S3_perms:
                nxt = (pm_idx[nxt_Ms[p[0]]], pm_idx[nxt_Ms[p[1]]], pm_idx[nxt_Ms[p[2]]])
                if nxt not in orbit:
                    orbit.add(nxt)
                    queue.append(nxt)
    triple_orbits.append(list(orbit))
    visited_t.update(orbit)

print(f"57 pair orbits, {len(triple_orbits)} triple orbits.")

# Map pair orbit to triple orbit
pair_to_triple = {}
triple_orbit_id_map = {}
for idx, o in enumerate(triple_orbits):
    for t in o:
        triple_orbit_id_map[t] = idx

mapped_triple_orbits = set()
for p_idx, p_orbit in enumerate(pair_orbits):
    rep = p_orbit[0]
    t = (0, rep[0], rep[1])
    t_orbit = triple_orbit_id_map[t]
    mapped_triple_orbits.add(t_orbit)

print(f"The 57 pair orbits map to exactly {len(mapped_triple_orbits)} triple orbits out of {len(triple_orbits)}.")
if len(mapped_triple_orbits) == len(triple_orbits):
    print("CONCLUSION: The 57 pair orbits merely refine the 31 triple orbits and add no new branch coverage.")


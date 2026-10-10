"""Independent small exact checks. Does not import the producer's checker."""
from fractions import Fraction as F
from itertools import combinations, product
from math import comb
from pathlib import Path
import hashlib
import json


def scalar_three_stages(h, omit_middle_inverse=False):
    triples = tuple(map(frozenset, combinations(range(h), 3)))
    v = len(triples)
    keys = list(product(range(v), repeat=3))
    X = {k: F(3*i-5, 7) for i, k in enumerate(keys)}
    Y = {k: F(i*i+1, 11) for i, k in enumerate(keys)}
    original_X, original_Y = X.copy(), Y.copy()
    edges = [(s,t) for s in range(v) for t in range(v)
             if len(triples[s] & triples[t]) in (0,2)]
    invocations = 0
    for stage in range(3):
        for fixed in product(range(v), repeat=2):
            kk = []
            for t in range(v):
                k = list(fixed)
                k.insert(stage, t)
                kk.append(tuple(k))
            source, target = (Y, X) if stage == 1 else (X, Y)
            x, y = [source[k] for k in kk], [target[k] for k in kk]
            aux = [F(2*i+invocations+1, 13) for i in range(len(edges))]
            center = [F(5*i-invocations-2,17) for i in range(h+1)]
            old_aux, old_center = aux.copy(), center.copy()
            # Actual eight elementary updates; inverse reverses their order.
            schedule = [("side_out",-1),("center_out",-1),
                        ("side_in",1),("center_in",1),
                        ("center_out",1),("side_out",1),
                        ("center_in",-1),("side_in",-1)]
            if stage == 1 and not omit_middle_inverse:
                schedule = [(op,-sgn) for op,sgn in reversed(schedule)]
            for op,sgn in schedule:
                if op == "side_in":
                    for e,(_,t) in enumerate(edges):
                        aux[e] += sgn*x[t]
                elif op == "center_in":
                    for t,T in enumerate(triples):
                        for j in T:
                            center[j] += sgn*x[t]
                        center[h] += sgn*x[t]
                elif op == "side_out":
                    for e,(s,t) in enumerate(edges):
                        y[s] -= sgn*F(len(triples[s]&triples[t])-1,2)*aux[e]
                else:
                    for s,S in enumerate(triples):
                        y[s] += sgn*F(1,2)*(sum(center[j] for j in S)-center[h])
            assert aux == old_aux and center == old_center
            for k,value in zip(kk,y):
                target[k] = value
            invocations += 1
    assert X == {k:-original_Y[k] for k in keys}
    assert Y == original_X
    return {"h":h,"entries_per_bank":v**3,"invocations":invocations,
            "all_auxiliaries_restored":True,"signed_exchange":True}


def parameter_check(h):
    v = comb(h,3)
    degree = sum(comb(3,i)*comb(h-3,3-i) for i in (0,2))
    wires = 2*v**3 + 3*v**2*(v*degree+h+1)
    # Derive saving from terminal margin minus twice internal decreases.
    losses = 3*v**2*(h+1)*h
    saving = 2*v**3 - 2*losses
    a = (wires-1).bit_length()
    padded = 2**a
    assert padded//2 < wires <= padded
    assert (saving > 0) == (h >= 22)
    if h >= 22:
        assert 0 < saving < padded
        m = h**3
        # Boundary plus two neighboring remainder blocks; no huge arrays.
        K = m*(a+1)
        for k in [K-1,K,K+1,K+m-1,K+m,K+2*m-1]:
            if k < K:
                continue
            f,r = divmod(k,m)
            assert f >= a+1 and k-f >= a and f < k and r < m
    return h, wires, padded, saving


def main():
    cases = [parameter_check(h) for h in range(7,129)]
    h,W,P,D = next(c for c in cases if c[0]==24)
    eps = F(D,24**3*P)
    # Independently use ln(m)<9.54, giving a stronger rational margin
    # than the producer's 9.6 bound without any floating-point arithmetic.
    bound = F(477,50)
    term = total = F(1)
    for j in range(1,65):
        term *= bound/j
        total += term
    assert total > 24**3
    target = F(39,10**11)
    assert eps > target*bound
    assert not eps > F(40,10**11)*bound
    files = Path(__file__).resolve().parents[2]/"routes"/"dft"/"sources"
    hashes = {}
    for p in sorted(files.glob("*.tex")):
        data = p.read_bytes()
        hashes[p.name] = hashlib.sha256(data).hexdigest()
    try:
        scalar_three_stages(4, omit_middle_inverse=True)
    except AssertionError:
        middle_inverse_mutant_caught = True
    else:
        raise AssertionError("Wrong middle-stage chronology survived")
    result = {"checks":"passed", "parameter_test_range":[7,128],
              "negative_controls":{"wrong_middle_stage_caught":middle_inverse_mutant_caught},
              "three_stage_checks":[scalar_three_stages(3),scalar_three_stages(4)],
              "h24":{"W":W,"P":P,"Delta":D,"epsilon":str(eps),
                     "ln_m_upper":str(bound),"strict_theta_upper":"1-39/10^11"},
              "source_sha256":hashes,
              "scope":"Exact finite checks, not an executable all-length DFT or universal proof"}
    print(json.dumps(result,indent=2,sort_keys=True))


if __name__ == "__main__":
    main()

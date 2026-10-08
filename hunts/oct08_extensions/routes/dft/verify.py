#!/usr/bin/env python3
"""Exact finite evidence for the parameterized Fourier motif; no large arrays."""
from fractions import Fraction as Q
from itertools import combinations
from math import comb, factorial
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
COMMIT = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
BLOBS = {
    'network.tex': '991c7706b7a03f45fbf3ba22bfb4372bf111fb4a',
    'local.tex': '260a19bd8f7189afbe89b0af0508d979cd1e1ca6',
    'synchronization.tex': 'cdc0f6bfb8224fcdb25b08552612522555cd5f3f',
    'all-lengths.tex': '8e2281f08c336865025a3dc10b6c790e9bfc68ed',
}

def counts(h):
    v = comb(h, 3)
    d = comb(h-3, 3) + 3*(h-3)
    W = 2*v**3 + 3*v*v*(v*d+h+1)
    delta = 2*v*v*(v-3*h*(h+1))
    m = h**3
    P = 1 << (W-1).bit_length()
    return {'h': h, 'v': v, 'd': d, 'm': m, 'W': W, 'P': P,
            'delta': delta, 'a': P.bit_length()-1, 's': W*m-delta}

def orbit_check(h):
    """All T against one S; S_h transitivity supplies other S in proof."""
    S = {0, 1, 2}
    ns = [0]*4
    wrong_sign_caught = False
    for T0 in combinations(range(h), 3):
        T = set(T0)
        k = len(S & T)
        ns[k] += 1
        rg = Q(k-1, 2)
        jv = -rg if k in (0, 2) else 0
        assert rg+jv == int(S == T)
        wrong_sign_caught |= rg-jv != int(S == T)
    assert ns == [comb(h-3,3), 3*comb(h-3,2), 3*(h-3), 1]
    assert wrong_sign_caught
    return ns

def schedule_check(h=7):
    """Eight rows on deterministic arbitrary nonzero auxiliary values."""
    ts = [set(t) for t in combinations(range(h), 3)]
    edges = [(i,j) for i,S in enumerate(ts) for j,T in enumerate(ts)
             if len(S & T) in (0,2)]
    v = len(ts)
    x = [Q(3*i-17,7) for i in range(v)]
    y = [Q(i*i+3,11) for i in range(v)]
    A = [Q((k*13)%29-14,5) for k in range(len(edges))]
    c = [Q(7*j-9,13) for j in range(h+1)]
    originals = (y[:], A[:], c[:])
    def ja():
        out = [Q(0)]*v
        for a,(i,j) in zip(A,edges):
            out[i] -= Q(len(ts[i]&ts[j])-1,2)*a
        return out
    def rc():
        return [(sum(c[j] for j in S)-c[h])/2 for S in ts]
    def row(row, sign=1):
        if row in (0,5):
            s = -1 if row == 0 else 1
            y[:] = [b+sign*s*a for b,a in zip(y,ja())]
        elif row in (1,4):
            s = -1 if row == 1 else 1
            y[:] = [b+sign*s*a for b,a in zip(y,rc())]
        elif row in (2,7):
            s = 1 if row == 2 else -1
            A[:] = [a+sign*s*x[j] for a,(i,j) in zip(A,edges)]
        else:
            s = 1 if row == 3 else -1
            Gx = [sum(x[i] for i,T in enumerate(ts) if j in T) for j in range(h)]
            Gx.append(sum(x))
            c[:] = [b+sign*s*a for b,a in zip(c,Gx)]
    for j in range(8): row(j)
    assert y == [a+b for a,b in zip(originals[0],x)]
    assert (A,c) == originals[1:]
    for j in reversed(range(8)): row(j,-1)
    assert (y,A,c) == originals
    # Omit the first subtraction: arbitrary auxiliaries must expose the error.
    for j in range(1,8): row(j)
    assert y != [a+b for a,b in zip(originals[0],x)]
    return {'h':h, 'v':v, 'ordered_side_wires':len(edges),
            'forward_and_reverse':'pass','omitted_subtraction_mutant':'caught'}

def phase_check():
    """Exhaustive 7-bit phase checks for all norm-one vectors."""
    pop = int.bit_count
    n = 0
    for z in range(1,128):
        if pop(z)%2 == 0: continue
        for x in range(128):
            bit = pop(x&z)%2
            projected = z if bit else 0
            complement = x ^ projected
            assert (pop(projected)+pop(complement)-pop(x))%4 == 0
            assert (pop(complement)-pop(projected)-pop(x)-2*bit)%4 == 0
            n += 1
    return n

def main():
    source_hashes = {}
    for f, expected in BLOBS.items():
        b = (ROOT/'sources'/f).read_bytes()
        # apply_patch snapshots can carry one extra terminal newline.
        candidates = [b, b[:-1]] if b.endswith(b'\n\n') else [b]
        matches = [c for c in candidates
                   if hashlib.sha1(b'blob '+str(len(c)).encode()+b'\0'+c).hexdigest()==expected]
        assert len(matches)==1, ('source identity changed',f)
        source_hashes[f] = {'git_blob': expected, 'sha256_snapshot':hashlib.sha256(b).hexdigest()}
    x = counts(24)
    assert x == {'h':24,'v':2024,'d':1393,'m':13824,'W':34666942577344,
                 'P':35184372088832,'delta':1835266048,'a':45,
                 's':479235812353937408}
    assert counts(21)['delta'] < 0 < counts(22)['delta']
    eps = Q(x['delta'],x['P']*x['m'])
    eta = Q(39,10**11)
    log_bound = Q(48,5)
    exp_partial = sum(log_bound**j/Q(factorial(j)) for j in range(40))
    assert exp_partial > x['m']  # exp(48/5) > m, hence log(m)<48/5.
    assert eps > eta*log_bound  # Gives theta < 1-39/10^11 without floats.
    # Deliberately overstrong exponent and wrong budget must fail these tests.
    assert not eps > Q(40,10**11)*log_bound
    assert x['delta'] != 2*x['v']**3 - 3*x['v']**2*24*25
    out = {'source_commit':COMMIT,'source_hashes':source_hashes,'counts':x,
           'epsilon':str(eps),'theta_upper_bound':'1-39/10^11 (strict)',
           'pure_log_delta':'38/10^11', 'orbit_h24':orbit_check(24),
           'orbit_h7':orbit_check(7),'schedule':schedule_check(),
           'exhaustive_phase_cases':phase_check(),
           'negative_controls':['h21 no saving','wrong cancellation sign',
              'omitted initial auxiliary subtraction','overstrong rational exponent',
              'missing factor two in decrease budget'],
           'claim_scope':'exact finite checks; universal extension requires PROOF.md'}
    print(json.dumps(out,sort_keys=True,indent=2))

if __name__ == '__main__': main()

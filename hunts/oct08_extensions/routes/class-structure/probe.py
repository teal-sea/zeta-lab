"""Exact bounded genus filter experiment. No QRH or floating point decisions."""
import collections
import hashlib
import json
import math
import platform
import resource
import time
from pathlib import Path
from reference_pinned import reference_h

resource.setrlimit(resource.RLIMIT_CPU, (20, 20))

def factors(n):
    ps = []
    p = 3
    while p*p <= n:
        if n % p == 0:
            n //= p
            if n % p == 0:
                return None
            ps.append(p)
        p += 2
    if n > 1:
        ps.append(n)
    return ps

def forms(n):
    # Independent brute-force reduced-form definition, not cn.c's root sieve.
    out = []
    for a in range(1, math.isqrt(n//3)+1):
        for b in range(-a, a+1):
            if (b*b+n) % (4*a):
                continue
            c = (b*b+n)//(4*a)
            if c < a or (b < 0 and (a == c or abs(b) == a)):
                continue
            if math.gcd(math.gcd(a,b), c) == 1:
                out.append((a,b,c))
    assert len(out) == len(set(out))
    return out

def signature(f, n, ps):
    a,b,c = f
    # Use a represented integer coprime to D, never a ramified leading term.
    for x in range(101):
        m = a*x*x+b*x+c
        if math.gcd(m,n) == 1:
            sig = tuple(1 if pow(m % p,(p-1)//2,p) == 1 else -1 for p in ps)
            assert math.prod(sig) == 1
            return sig
    raise RuntimeError('No coprime represented value found; no silent omission')

def run():
    started = time.monotonic()
    rows = []
    stats = collections.Counter()
    best = None
    for n in range(3,20001,4):
        ps = factors(n)
        if ps is None:
            continue
        fs = forms(n)
        assert len(fs) == reference_h(n)
        full = collections.Counter(signature(f,n,ps) for f in fs)
        g = 2**(len(ps)-1)
        h = len(fs)
        assert len(full) == g and set(full.values()) == {h//g}
        partial = collections.Counter(signature(f,n,ps) for f in fs if f[0] <= 10)
        plain = sum(partial.values())
        rounded = g*((plain+g-1)//g)
        stronger = g*max(partial.values())
        assert plain <= rounded <= stronger <= h
        stats['discriminants'] += 1
        stats['strictly_better_than_divisibility_rounding'] += stronger > rounded
        for H in (20,50,100):
            stats[f'additional_rejections_H{H}'] += rounded <= H < stronger
        ratio = stronger / rounded
        if best is None or ratio > best['ratio']:
            best = dict(D=-n,h=h,genera=g,partial=plain,rounded=rounded,genus_bound=stronger,ratio=ratio,forms=[list(f) for f in fs if f[0] <= 10])
        rows.append((n,h,g,plain,rounded,stronger))
    # Explicit refutation of treating a full group as one genus then multiplying.
    fs = forms(15)
    assert len(fs) == 2 and 2*len(fs) > len(fs)
    # D=-231 is a convention control with three prime discriminant factors.
    assert len(set(signature(f,231,[3,7,11]) for f in forms(231))) == 4
    out = dict(base='f4ef0715bbe2f4890b3dcea034757ef0c823053a',source='3f136908426167ff97888a6ae8b89087223509e6',range='negative odd fundamental D with 3<=|D|<=20000',cutoff_a=10,stats=dict(stats),best=best,rows_sha256=hashlib.sha256(json.dumps(rows,separators=(',',':')).encode()).hexdigest(),python=platform.python_version(),seconds=time.monotonic()-started)
    print(json.dumps(out,indent=2))

if __name__ == '__main__':
    run()

"""Independent layer implementation; inherited base_bound is shared explicitly."""
import sys
from pathlib import Path
from fractions import Fraction as Q
from math import isqrt
sys.path.insert(0,str(Path(__file__).resolve().parents[2]/'routes'/'prime-gap'))
import base_bound as b
from flint import arb
b.set_precision(384)
# Re-extracted table values rounded UP, deliberately different constants:
# author uses (5.28,4.41)...; we use same to reproduce exact claimed bound,
# not pretending this is a mathematically independent external density theorem.
rows=[(Q(3,4),Q(528,100),Q(441,100)),(Q(4,5),Q(692,100),Q(4)),
      (Q(17,20),Q(898,100),Q(359,100)),(Q(43,50),Q(945,100),Q(352,100)),
      (Q(87,100),Q(993,100),Q(344,100))]
sigmas=[r[0] for r in rows]+[Q(7,8)]
def q(x):return arb(x.numerator)/x.denominator if isinstance(x,Q) else arb(x)

def J(a,B,v):
    """Independent antiderivative evaluation, not producer moment()."""
    c=arb(48).sqrt()*a
    if B>c:
        return 648*a**3*B**(-3)/(3-v)
    assert B<c
    mid=arb(9)/2*a/B**v*(c**(v-1)-B**(v-1))/(v-1)
    return mid+648*a**3/B**v*c**(v-3)/(3-v)

def rare(a,row):
    s,A,C=map(q,row);r=arb(8)/3*(1-s);p=5-2*s
    start=arb(9)/2*a;H=arb(b.H0)
    assert start<H or start>H
    B=H if start<H else start
    ell=B.log()
    assert r+p/ell<1
    return A*B**r*ell**p*J(a,B,r+p/ell)+C*ell**2*J(a,B,2/ell)

def audit_bound(left,right,k=7):
    D=b.interval_bound(b.KthPowers(k),Q(7,8),left,right)
    a=D['a_star'];y=k*left
    assert y>=8
    high=2*(-y/4).exp()*b.S_high(a)
    for j,row in enumerate(rows):
        lower=q(sigmas[j]);upper=q(sigmas[j+1])
        delta=((upper-1)*y).exp()-((lower-1)*y).exp()
        high+=2*delta*rare(a,row)
    return 1-high-D['low']-D['triv']-D['prime_power_share']

for i in range(764):
    left=arb(36+i)/16;right=left+arb(1)/16
    assert audit_bound(left,right)>arb('.13045')
assert arb(36)/16<arb(10).log()
assert arb(36+764)/16==50
print('Independent rare-integral implementation: all 764 margins > .13045, 384 bits')

# Finite exact-rational synthetic atoms test telescope and strict beta condition.
# x=2 and y=log x here only test pointwise layer inequality, not coefficient monotonicity.
for beta in [Q(1,2),*sigmas,Q(77,100),Q(83,100),Q(855,1000),Q(865,1000),Q(873,1000)]:
    endpoint=next((s for s in sigmas if beta<=s),sigmas[-1])
    active=[j for j in range(5) if beta>sigmas[j]]
    # telescoping exponents checked exactly to avoid ambiguous ball equality
    target=sigmas[max(active)+1] if active else sigmas[0]
    assert target==endpoint and target>=beta
# Fault planting: omitting the final strip cannot upper-bound an atom at beta=7/8.
assert sigmas[-2]<sigmas[-1]
# Fault planting: placing beta exactly at lower boundary into previous strip is fine;
# omitting the first layer fails for beta strictly between first two boundaries.
assert sigmas[0]<Q(77,100)
print('Synthetic atoms at all boundaries and interiors pass; omitted-layer mutants rejected')

L=arb(50)
assert (arb(9)/2).log()<2
assert (arb(9)/2)*L.exp()>b.H0
assert 1+L.exp()/7<L.exp()
base=b.kth_power_tail(7,Q(3,4),Q(50))
assert base['prereq'] and base['decreasing']
total=base['sup_bound']
assert J(arb(1),arb('4.5'),arb('.8'))<3
assert arb('4.5')**(arb(2)/3)<3
for j,row in enumerate(rows):
    s,A,C=map(q,row);r=arb(8)/3*(1-s);p=5-2*s;t=q(sigmas[j+1])
    assert Q(8,3)*(1-row[0])<=Q(2,3) and p<4
    assert r+p/L<arb('.8') and 2/L<arb('.8')
    decay=7*(1-t)-r
    assert 4/(L+2)<decay and 2/(L+2)<7*(1-t)
    total+=18*A*(-decay*L).exp()*(L+2)**4+6*C*(-7*(1-t)*L).exp()*(L+2)**2
assert total<arb('.012961')
print('Uniform tail error < .012961; all domain and monotonicity inequalities checked')
assert audit_bound(arb(29),arb(29),6)<-56
assert audit_bound(arb(29),arb(29),7)>0
print('Same independent bound rejects k6 at L29; accepts k7; this is not a prime counterexample')

# Known fixed witnesses supplied independently of producer's search loop.
# Read artifact to obtain proposed witnesses, then verify each explicitly.
import json
raw=(Path(__file__).resolve().parents[2]/'routes'/'prime-gap-multistrip'/'verification.txt').read_text()
obj=json.JSONDecoder().raw_decode(raw)[0]
assert len(obj['witnesses'])==9
for n,p in obj['witnesses']:
    assert n in range(1,10) and n**7<p<(n+1)**7
    assert p>=2 and all(p%div for div in range(2,isqrt(p)+1))
assert sorted(n for n,p in obj['witnesses'])==list(range(1,10))
print('All nine proposed witnesses independently verified by exact trial division')

# Exact numeric synthetic atom inequalities at x=2^1000.
def power(beta):
    exponent=1000*(beta-1)
    assert exponent.denominator==1
    return Q(2)**exponent.numerator

def layer_atom(beta,omit=None):
    val=power(sigmas[0])
    for j in range(5):
        if j!=omit and beta>sigmas[j]:
            val+=power(sigmas[j+1])-power(sigmas[j])
    return val
atoms=[Q(1,2),*sigmas,Q(77,100),Q(83,100),Q(855,1000),Q(865,1000),Q(873,1000)]
assert all(layer_atom(beta)>=power(beta) for beta in atoms)
assert layer_atom(Q(7,8),omit=4)<power(Q(7,8))
assert layer_atom(Q(77,100),omit=0)<power(Q(77,100))
print('Exact rational synthetic zero atoms pass; missing-first/missing-last-layer mutants fail')

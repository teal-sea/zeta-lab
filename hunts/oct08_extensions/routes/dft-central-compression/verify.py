#!/usr/bin/env python3
"""Rational checks for the new gather/scatter, not a full DFT implementation."""
from fractions import Fraction as Q
from itertools import combinations
from math import comb, factorial
from pathlib import Path
import hashlib, json

ROOT=Path(__file__).resolve().parent

def run(h):
    ts=[set(t) for t in combinations(range(h),3)]
    v=len(ts)
    edges=[(i,j) for i,S in enumerate(ts) for j,T in enumerate(ts)
           if len(S&T) in (0,2)]
    x=[Q(3*i-17,7) for i in range(v)]
    y=[Q(i*i+3,11) for i in range(v)]
    A=[Q((13*k)%29-14,5) for k in range(len(edges))]
    c=[Q(7*j-9,13) for j in range(h)]
    original=(y[:],A[:],c[:])
    def gather():
        return [sum(x[i] for i,T in enumerate(ts) if j in T) for j in range(h)]
    def scatter(c):
        return [(sum(c[j] for j in S)-sum(c)/3)/2 for S in ts]
    def side():
        z=[Q(0)]*v
        for a,(i,j) in zip(A,edges): z[i]-=Q(len(ts[i]&ts[j])-1,2)*a
        return z
    gx=gather()
    assert sum(gx)==3*sum(x)
    old=[(sum(gx[j] for j in S)-sum(x))/2 for S in ts]
    assert scatter(gx)==old
    assert any((sum(gx[j] for j in S))/2 != z for S,z in zip(ts,old))
    def row(r,sig=1):
        if r in (0,5):
            sign=-1 if r==0 else 1
            y[:]=[b+sig*sign*a for a,b in zip(side(),y)]
        elif r in (1,4):
            sign=-1 if r==1 else 1
            y[:]=[b+sig*sign*a for a,b in zip(scatter(c),y)]
        elif r in (2,7):
            sign=1 if r==2 else -1
            A[:]=[a+sig*sign*x[j] for a,(i,j) in zip(A,edges)]
        else:
            sign=1 if r==3 else -1
            c[:]=[a+sig*sign*b for a,b in zip(c,gx)]
    for r in range(8):row(r)
    assert y==[a+b for a,b in zip(original[0],x)]
    assert (A,c)==original[1:]
    for r in reversed(range(8)):row(r,-1)
    assert (y,A,c)==original
    for r in range(1,8):row(r)
    assert y!=[a+b for a,b in zip(original[0],x)]
    # Independent Gram reconstruction by literal incidence-column intersections.
    for i in range(h):
        for j in range(h):
            actual=sum(i in T and j in T for T in ts)
            alpha=Q((h-2)*(h-3),2); beta=h-2
            assert actual==alpha*(i==j)+beta
    return {'h':h,'triples':v,'ordered_edges':len(edges),'schedule_and_inverse':'passed'}

def matrix_rank(a):
    a=[list(map(Q,row)) for row in a]
    r=0
    for col in range(len(a[0])):
        p=next((i for i in range(r,len(a)) if a[i][col]),None)
        if p is None:continue
        a[r],a[p]=a[p],a[r]
        lead=a[r][col];a[r]=[x/lead for x in a[r]]
        for i in range(r+1,len(a)):
            if a[i][col]:
                q=a[i][col];a[i]=[x-q*y for x,y in zip(a[i],a[r])]
        r+=1
    return r

def main():
    blobs={'network.tex':'991c7706b7a03f45fbf3ba22bfb4372bf111fb4a',
           'local.tex':'260a19bd8f7189afbe89b0af0508d979cd1e1ca6',
           'synchronization.tex':'cdc0f6bfb8224fcdb25b08552612522555cd5f3f',
           'all-lengths.tex':'8e2281f08c336865025a3dc10b6c790e9bfc68ed'}
    for f,sha in blobs.items():
        data=(ROOT.parent/'dft'/'sources'/f).read_bytes()
        bs=[data,data[:-1]] if data.endswith(b'\n\n') else [data]
        assert any(hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==sha for b in bs)
    h=24;v=comb(h,3);d=comb(h-3,3)+3*(h-3);m=h**3
    W=2*v**3+3*v*v*(v*d+h);D=2*v*v*(v-3*h*h);P=1<<(W-1).bit_length()
    assert (W,D,P,W*m-D)==(34666930287616,2425172992,35184372088832,479235641870830592)
    assert D != 2*v*v*(v-3*h*(h+1)), 'old central-role budget must be rejected'
    eps=Q(D,m*P); eta=Q(52,10**11);logupper=Q(191,20)
    assert eps>eta*logupper
    assert sum(logupper**j/Q(factorial(j)) for j in range(40))>m
    assert not eps>Q(53,10**11)*logupper
    assert comb(20,3)<3*20**2 and comb(21,3)>3*21**2
    # Orbit coefficients without duplicating the original RG+JV formula.
    for k in (0,1,2,3):
        gathered=[int(j<k or 3<=j<6-k) for j in range(h)]
        assert sum(gathered)==3
        central=(sum(gathered[:3])-Q(sum(gathered),3))/2
        assert central==Q(k-1,2)
    ranks={}
    for H in (4,5,7,9,10):
        ts=[set(t) for t in combinations(range(H),3)]
        M=[[Q(len(S&T)-1,2) for T in ts] for S in ts]
        ranks[H]=matrix_rank(M)
        assert ranks[H]==H-(H==9)
    spectrum=(Q((h-2)*(h-3),4),Q((9-h)*(h-1)*(h-2),12))
    assert spectrum==(Q(231,2),Q(-1265,2))
    assert (h-1)*spectrum[0]+spectrum[1]==v
    out={'source_commit':'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb','source_blobs':blobs,
         'counts':{'h':h,'v':v,'m':m,'W':W,'P':P,'delta':D,'s':W*m-D},
         'epsilon':str(eps),'theta_upper_bound':'1-52/10^11 (strict)',
         'pure_log_delta':'51/10^11','small_schedules':[run(7),run(8)],
         'literal_rational_matrix_ranks':ranks,'nonzero_eigenvalues_h24':list(map(str,spectrum)),
         'negative_controls':['omitted total correction','omitted initial subtraction',
                              'old h+1 central budget','h20 no saving','overstrong exponent'],
         'scope':'Exact finite evidence; universal circuit/rank argument in PROOF.md'}
    print(json.dumps(out,indent=2,sort_keys=True))

if __name__=='__main__':main()

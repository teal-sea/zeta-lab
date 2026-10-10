"""Independent exact checks; uses no producer code."""
from fractions import Fraction as F
from itertools import combinations, product
from math import comb
from pathlib import Path
import hashlib
import json


def exchange(h, correction=F(1,3)):
    T = tuple(map(frozenset,combinations(range(h),3)))
    v = len(T)
    keys = list(product(range(v),repeat=3))
    X = {k:F(i-3,7) for i,k in enumerate(keys)}
    Y = {k:F(i*i+9,11) for i,k in enumerate(keys)}
    X0,Y0 = X.copy(),Y.copy()
    E = [(s,t) for s in range(v) for t in range(v) if len(T[s]&T[t])%2==0]
    count=0
    for stage in range(3):
        for fixed in product(range(v),repeat=2):
            indices=[]
            for i in range(v):
                key=list(fixed);key.insert(stage,i);indices.append(tuple(key))
            src,dst=(Y,X) if stage==1 else (X,Y)
            x,y=[src[k] for k in indices],[dst[k] for k in indices]
            A=[F(7*i+count+2,13) for i in range(len(E))]
            c=[F(11*j-count+5,17) for j in range(h)]
            A0,c0=A.copy(),c.copy()
            rows=[('J',-1),('R',-1),('V',1),('G',1),
                  ('R',1),('J',1),('G',-1),('V',-1)]
            if stage==1:rows=[(op,-sign) for op,sign in reversed(rows)]
            for op,sign in rows:
                if op=='J':
                    for e,(s,t) in enumerate(E):
                        y[s]-=sign*F(len(T[s]&T[t])-1,2)*A[e]
                elif op=='R':
                    total=sum(c)
                    for s,S in enumerate(T):
                        y[s]+=sign*(sum(c[j] for j in S)-correction*total)/2
                elif op=='V':
                    for e,(_,t) in enumerate(E):A[e]+=sign*x[t]
                else:
                    for t,U in enumerate(T):
                        for j in U:c[j]+=sign*x[t]
            assert A==A0 and c==c0
            for k,value in zip(indices,y):dst[k]=value
            count+=1
    assert X=={k:-Y0[k] for k in keys} and Y==X0
    return {'h':h,'bank_entries':v**3,'invocations':count,'auxiliaries_restored':True}


def rank(matrix):
    # Independent fraction-free cross-multiplication elimination.
    a=[row[:] for row in matrix]
    r=0
    for j in range(len(a[0])):
        pivot=next((i for i in range(r,len(a)) if a[i][j]),None)
        if pivot is None:continue
        a[r],a[pivot]=a[pivot],a[r]
        lead=a[r][j]
        for i in range(r+1,len(a)):
            q=a[i][j]
            if q:
                a[i]=[lead*x-q*y for x,y in zip(a[i],a[r])]
                # Divide row gcd to avoid irrelevant exponential integer growth.
                from functools import reduce
                from math import gcd
                g=reduce(gcd,a[i])
                if g:a[i]=[x//g for x in a[i]]
        r+=1
        if r==len(a):break
    return r


def main():
    ranks={}
    for h in (4,6,9):
        T=list(map(set,combinations(range(h),3)))
        # 2M has integer entries, and scaling preserves rank over C.
        ranks[h]=rank([[len(S&U)-1 for U in T] for S in T])
        assert ranks[h]==h-(h==9)
    counts=[]
    for h in range(7,129):
        v=comb(h,3);d=comb(h-3,3)+3*(h-3);m=h**3
        W=2*v**3+3*v**2*(v*d+h)
        loss=3*v**2*h*h
        D=2*v**3-2*loss
        P=1<<(W-1).bit_length()
        assert (D>0)==(h>=21)
        if D>0:
            assert 0<D<P and m-1<F(P*m-D,P)<m
            a=P.bit_length()-1;K=m*(a+1)
            for k in (K,K+1,K+m-1,K+m):
                f,r=divmod(k,m)
                assert k-f>=a and f<k and r<m
        if h in (20,21,24):counts.append({'h':h,'W':W,'P':P,'Delta':D})
    c=counts[-1];eps=F(c['Delta'],c['P']*24**3)
    # Separate certificate: 9.54 rather than producer's 9.55, 64 terms.
    b=F(477,50);term=total=F(1)
    for j in range(1,65):term*=b/j;total+=term
    assert total>24**3 and eps>F(52,10**11)*b
    assert eps<F(53,10**11)*b
    S={0,1,2}
    for U in map(set,combinations(range(24),3)):
        # Literal incidence column and scatter, including its dense correction.
        col=[F(int(j in U)) for j in range(24)]
        assert (sum(col[j] for j in S)-sum(col)/3)/2==F(len(S&U)-1,2)
    clean=exchange(4)
    mutants={}
    for bad in (F(0),F(1,2)):
        try:exchange(4,bad)
        except AssertionError:mutants[str(bad)]='caught'
        else:raise AssertionError('incorrect dense correction survived')
    root=Path(__file__).resolve().parents[2]
    hashes={}
    for rel in ('routes/dft-central-compression/PROOF.md',
                'routes/dft-central-compression/verify.py'):
        hashes[rel]=hashlib.sha256((root/rel).read_bytes()).hexdigest()
    print(json.dumps({'checks':'passed','fixed_correction_ranks':ranks,
        'parameter_range':[7,128],'boundary_counts':counts,
        'h24_epsilon':str(eps),'ln_m_upper':str(b),'theta_upper':'1-52/10^11',
        'three_stage':clean,'incorrect_correction_mutants':mutants,
        'producer_sha256':hashes,'scope':'small exact checks, not full DFT execution'},
        indent=2,sort_keys=True))


if __name__=='__main__':main()

"""Independent exact integer recheck and rational bounds on logarithmic constants.
Run probe.py first. No prime-counting data are used to choose coefficients.
"""
from pathlib import Path
from fractions import Fraction
import json, math
import mpmath as mp

ROOT=Path(__file__).resolve().parent
mp.mp.dps=60

def log_interval(n, terms=32):
    """Rational lower/upper bounds from 2*atanh((x-1)/(x+1))."""
    if not isinstance(n,int) or n<1: raise ValueError('positive integer required')
    def series(u):
        low=2*sum((u**(2*k+1)/Fraction(2*k+1) for k in range(terms)),Fraction(0))
        tail=2*u**(2*terms+1)/(Fraction(2*terms+1)*(1-u*u))
        return low,low+tail
    e=n.bit_length()-1
    r=Fraction(n,2**e)
    lo,hi=series((r-1)/(r+1)); l2,h2=series(Fraction(1,3))
    return lo+e*l2,hi+e*h2

def dec(q): return str(mp.mpf(q.numerator)/q.denominator)

def constant_interval(a,M):
    lo=hi=Fraction(0)
    for j,c in a.items():
        lj,hj=log_interval(j)
        w=-c/Fraction(j)/(1-Fraction(1,M))
        if w>=0:lo+=w*lj;hi+=w*hj
        else:lo+=w*hj;hi+=w*lj
    return lo,hi

rows=json.loads((ROOT/'results.json').read_text())
intervals=[]
for row in rows:
    L,M=row['L'],row['M']; aa={int(j):Fraction(c) for j,c in row['coefficients'].items()}
    assert all(L%j==0 for j in aa)
    assert sum((c/Fraction(j) for j,c in aa.items()),Fraction(0))==0
    den=math.lcm(*(c.denominator for c in aa.values()))
    nums={j:int(c*den) for j,c in aa.items()}
    # Python integers here, independent of the numpy matrix path in probe.py.
    for r in range(L):
        value=sum(c*(r//j) for j,c in nums.items())
        assert value>=(den if 1<=r<M else 0),(L,M,r,value)
    lo,hi=constant_interval(aa,M); intervals.append((lo,hi))
    row['independent_full_period_python_integer_checks']=L
    row['C_rational_enclosure']={'lower':str(lo),'upper':str(hi),
                                'lower_decimal':dec(lo),'upper_decimal':dec(hi)}
    def W(n):
        scale=1;s=Fraction(0)
        while scale<=n:
            s+=sum((c*(n//(j*scale)) for j,c in aa.items()),Fraction(0));scale*=M
        return s
    row['W_at_12_and_13']={'12':str(W(12)),'13':str(W(13))}
    comparisons=[]
    for N in [10**4,10**6,10**8,10**12]:
        scale=1; K=0
        while scale*M<=N:scale*=M;K+=1
        C=-sum(mp.mpf(c.numerator)/c.denominator*mp.log(j)/j for j,c in aa.items())/(1-mp.mpf(1)/M)
        A=sum(map(abs,aa.values())); Am=mp.mpf(A.numerator)/A.denominator
        B=sum(mp.mpf(c.numerator)/c.denominator*mp.loggamma(N//(j*M**k)+1) for j,c in aa.items() for k in range(K+1))
        U=C*N*(1-mp.mpf(M)**(-K-1))+Am*((K+1)*(1+mp.log(N))-mp.log(M)*K*(K+1)/2)
        comparisons.append({'N':N,'B_60digit':str(B),'U_60digit':str(U),'K':K})
    row['comparisons']=comparisons
assert intervals[1][1]<intervals[0][0], 'leading constant improvement not established'
# The finite sum is a rigorous, deliberately incomplete lower bound on
# unavoidable omitted-prime mass for the old L=2310,M=15 family.
ps=[p for p in range(13,102) if all(p%d for d in range(2,math.isqrt(p)+1))]
gap=sum((Fraction(1,p*(p+1)) for p in ps),Fraction(0))
report={'status':'finite feasibility and constant comparison; no LP optimality or new literature claim',
        'old_family_omitted_primes':ps,'old_family_gap_lower_rational':str(gap),
        'old_family_gap_lower_decimal':dec(gap),
        'leading_constant_improvement_exactly_enclosed':True,'rows':rows}
(ROOT/'checked_results.json').write_text(json.dumps(report,indent=2)+'\n')
for row in rows: print(row['L'],row['C_rational_enclosure']['lower_decimal'],row['A_exact'],row['W_at_12_and_13'])
print('ALL CHECKS PASSED; 32,340 period residues verified with Python integers.')

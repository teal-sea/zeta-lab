#!/usr/bin/env python3
"""Deterministic factorial-certificate refinement; no LP or prime-count fit.

Finite constraints and interval comparisons are exact. Analytic conclusions
depend on the argument in REFINEMENT.md; these checks are not a proof assistant.
The imported coefficient vectors are in inputs.json with their provenance.
"""
from __future__ import annotations
import argparse
from collections import defaultdict
from fractions import Fraction as F
from functools import lru_cache
import hashlib
import json
import math
from pathlib import Path
import time
import numpy as np
import mpmath as mp

M=15
R=100_000
MASK=(2,3,5,7)
PRIMES=(17,19,23,29,31)
mp.mp.dps=60

def mpf(x):
    return mp.mpf(x.numerator)/x.denominator if isinstance(x,F) else mp.mpf(x)

def balanced(c):
    return sum((a/j for j,a in c.items()),F())==0

def mass(c):
    return sum((abs(a) for a in c.values()),F())

def clean(c):
    return {j:a for j,a in c.items() if a}

def divisors_mu(primes):
    out={1:1}
    for p in primes:
        out.update({d*p:-a for d,a in list(out.items())})
    return out

def bump(n,t):
    return t//n-t//(n+1)-t//(n*(n+1))

def bump_coeff(n):
    return {n:F(1),n+1:F(-1),n*(n+1):F(-1)}

def stencil_coeff(p):
    c=defaultdict(F)
    for d,mu in divisors_mu(MASK).items():
        for j,a in bump_coeff(p).items():
            c[d*j]+=mu*a
    return clean(c)

def stencil_array(p,size):
    t=np.arange(size,dtype=np.int64)
    out=np.zeros(size,dtype=np.int64)
    for d,mu in divisors_mu(MASK).items():
        out+=mu*bump(p,t//d)
    return out

def floor_array(c,size,den=None):
    den=den or math.lcm(*(a.denominator for a in c.values()))
    t=np.arange(size,dtype=np.int64)
    out=np.zeros(size,dtype=np.int64)
    for j,a in c.items():
        assert (a*den).denominator==1
        out+=int(a*den)*(t//j)
    return out,den

def floor_value_scaled(c,t,den=3):
    return sum(int(a*den)*(t//j) for j,a in c.items())

def kappa(c):
    return -mp.fsum(mpf(a)*mp.log(j)/j for j,a in c.items())

@lru_cache(None)
def log_base_bounds(q):
    assert F(1)<=q<=F(2)
    u=(q-1)/(q+1)
    v=u
    s=F()
    for k in range(24):
        s+=2*v/(2*k+1)
        v*=u*u
    tail=2*v/(49*(1-u*u))
    return s,s+tail

@lru_cache(None)
def log_bounds(n):
    if n<1:raise ValueError('logarithm argument must be positive')
    e=n.bit_length()-1
    lo,hi=log_base_bounds(F(n,1<<e))
    a,b=log_base_bounds(F(2))
    lo+=e*a;hi+=e*b
    q=1<<64
    return F((lo.numerator*q)//lo.denominator,q),F(-((-hi.numerator*q)//hi.denominator),q)

def kappa_bounds(c):
    lo=hi=F()
    for j,a in c.items():
        ll,hh=log_bounds(j)
        w=-a/j
        lo+=w*(ll if w>=0 else hh)
        hi+=w*(hh if w>=0 else ll)
    return lo,hi

def outward_summary(bounds):
    q=10**16
    lo=F((bounds[0].numerator*q)//bounds[0].denominator,q)
    hi=F(-((-bounds[1].numerator*q)//bounds[1].denominator),q)
    return {'lower':str(lo),'upper':str(hi),
            'lower_decimal':str(mpf(lo)),'upper_decimal':str(mpf(hi))}

def add_coeff(c,other,factor=F(1)):
    out=defaultdict(F,c)
    for j,a in other.items():out[j]+=factor*a
    return clean(out)

def levels(N):
    if N<1:return -1
    k=0
    while N>=M:N//=M;k+=1
    return k

def repair_weight(star,t):
    out=0
    while t>=1:
        out+=floor_value_scaled(star,t,1)
        t//=M
    return out

def first_budget(N):
    K=levels(N)
    return (K+1)*(1+mp.log(N))-mp.log(M)*K*(K+1)/2 if K>=0 else mp.mpf(0)

def second_budget(N):
    if N<R:return mp.mpf(0)
    K=levels(N//R)
    return mp.fsum((k+1)*(1+mp.log(mp.mpf(N)/R)-k*mp.log(M)) for k in range(K+1))

@lru_cache(None)
def logfact(n):
    return mp.loggamma(n+1) if n>1 else mp.mpf(0)

def factorial_value(c,N):
    return mp.fsum(mpf(a)*logfact(N//j) for j,a in c.items() if j<=N)

def certificate(c,N):
    out=[]
    while N>=1:
        out.append(factorial_value(c,N));N//=M
    return mp.fsum(out)

def extended_certificate(c,H,star,N):
    value=certificate(c,N)
    x=N//R;k=0
    while x>=1:
        value+=H*(k+1)*factorial_value(star,x)
        x//=M;k+=1
    return value

def lifted_coeff(c,H,star,N):
    out=defaultdict(F)
    s=1
    while s<=N:
        for j,a in c.items():
            if s*j<=N:out[s*j]+=a
        s*=M
    s=R;k=0
    while s<=N:
        for j,a in star.items():
            if s*j<=N:out[s*j]+=H*(k+1)*a
        s*=M;k+=1
    return clean(out)

def prime_list(N):
    flags=np.ones(N+1,dtype=bool);flags[:2]=False
    for p in range(2,math.isqrt(N)+1):
        if flags[p]:flags[p*p::p]=False
    return np.flatnonzero(flags).tolist()

def legendre(n,p):
    s=0
    while n:
        n//=p;s+=n
    return s

def main(output):
    t0=time.perf_counter()
    inp=json.loads((Path(__file__).parent/'inputs.json').read_text())
    initial={int(j):F(a) for j,a in inp['starting_coefficients'].items()}
    star={int(j):F(a) for j,a in inp['repair_coefficients'].items()}
    assert inp['M']==M and balanced(initial) and balanced(star)
    for c,L in [(initial,inp['starting_L']),(star,inp['repair_L'])]:
        v,d=floor_array(c,L)
        assert np.min(v)>=0 and np.min(v[1:M])>=d

    den=math.lcm(*(a.denominator for a in initial.values()))
    initial_array,_=floor_array(initial,R,den)
    cur=initial_array.copy()
    direct=initial.copy()
    target=np.zeros(R,dtype=np.int64);target[1:M]=den
    Cstar_bounds=tuple(x/F(14,15) for x in kappa_bounds(star))
    Cstar=kappa(star)/mpf(F(14,15))
    prevI=tuple(x/F(14,15) for x in kappa_bounds(initial))
    totalH=0
    stages=[]
    prefix_checks=0;period_checks=0
    for p in PRIMES:
        beta=stencil_coeff(p)
        assert balanced(beta)
        period=math.prod(MASK)*p*(p+1)
        beta_period=stencil_array(p,period)
        # Exact finite period check. These floor functions all have period
        # dividing this period, by balance or by the individual bump identity.
        H=int(beta_period.max())
        assert H>=0
        # Generic upper bound (does not require the sharper enumeration).
        assert H<=2**(len(MASK)-1)
        period_checks+=period
        trial=cur-den*stencil_array(p,R)
        tt=np.arange(R,dtype=np.int64)
        repairs=[]
        for n in range(1,R):
            short=int(target[n]-trial[n])
            if short>0:
                assert n>=M and short<=H*den
                trial[n:]+=short*bump(n,tt[n:])
                repairs.append((n,F(short,den)))
        assert np.all(trial>=target)
        proposed=add_coeff(direct,beta,F(-1))
        for n,a in repairs:proposed=add_coeff(proposed,bump_coeff(n),a)
        assert balanced(proposed)
        # Rebuild from merged floor coefficients, not the construction array.
        independent,_=floor_array(proposed,R,den)
        assert np.array_equal(independent,trial)
        prefix_checks+=R
        newH=totalH+H
        ib=kappa_bounds(proposed)
        assert ib[0]>0
        CI=tuple((ib[i]+F(newH,R)*Cstar_bounds[i])/F(14,15) for i in (0,1))
        # A proof by rational inequalities that this stage lowers C.
        assert CI[1]<prevI[0]
        Cv=(kappa(proposed)+mp.mpf(newH)*Cstar/R)/mpf(F(14,15))
        stages.append({
            'p':p,'mask':list(MASK),'R':R,'H_exact':H,
            'stencil_period':period,'number_of_repairs':len(repairs),
            'repair_mass':str(sum((a for n,a in repairs),F())),
            'finite_coefficient_mass':str(mass(proposed)),
            'accumulated_tail_multiplier':newH,
            'stencil_coefficient_mass':str(mass(beta)),
            'C_approx':str(Cv),'C_interval':outward_summary(CI),
            'strict_decrease_rationally_checked':True,
            'repairs':[[n,str(a)] for n,a in repairs],
        })
        cur=trial;direct=proposed;totalH=newH;prevI=CI

    # Exact samples complement the global tail proof; not a substitute for it.
    points=[R,R+1,M*R,(M*M)*R,10**8,10**12]
    rng=np.random.default_rng(1729)
    points+=rng.integers(R,10**12,size=64).tolist()
    for t in points:
        actual=floor_value_scaled(direct,int(t),den)+den*totalH*repair_weight(star,int(t)//R)
        assert actual>=0

    # Factorial exponents checked in integers, independent of logarithms.
    exponent_cases=0
    for N in (1000,10000,1000000):
        cs=lifted_coeff(direct,totalH,star,N)
        ps=prime_list(N) if N<=10000 else [2,3,5,7,11,13,17,19,23,29,31,101,997,9973]
        for p in ps:
            left=sum(int(a*den)*legendre(N//j,p) for j,a in cs.items())
            right=0;power=p
            while power<=N:
                wt=sum(int(a*den)*((N//power)//j) for j,a in cs.items())
                assert wt>=den
                right+=wt;power*=p
            assert left==right
            exponent_cases+=1

    Cinitial=kappa(initial)/mpf(F(14,15))
    Cfinal=(kappa(direct)+mp.mpf(totalH)*Cstar/R)/mpf(F(14,15))
    comparisons=[]
    for N in (10000,1000000,100000000,10**12):
        oldval=certificate(initial,N)
        val=extended_certificate(direct,totalH,star,N)
        oldU=Cinitial*N+mpf(mass(initial))*first_budget(N)
        U=Cfinal*N+mpf(mass(direct))*first_budget(N)+totalH*mpf(mass(star))*second_budget(N)
        assert val<=U and oldval<=oldU
        comparisons.append({'N':N,'old_B':str(oldval),'new_B':str(val),
                            'old_U':str(oldU),'new_U':str(U),
                            'evaluation_status':'60-digit diagnostics, not interval enclosures'})

    result={
        'status':'explicit refinement and finite feasibility checks; no uniform RH-rate or novelty claim',
        'parameters':{'M':M,'R':R,'mask':list(MASK),'primes':list(PRIMES)},
        'algorithm':'Subtract fixed small-prime-masked carry, repair first deficient cells with nonnegative carries, cover all t>=R with H times the fixed lifted seed.',
        'stages':stages,'starting_C':str(Cinitial),'final_C':str(Cfinal),
        'final_direct_coefficients':{str(j):str(a) for j,a in sorted(direct.items())},
        'finite_coefficient_mass':str(mass(direct)),
        'tail_multiplier':totalH,
        'proof_domain':'all real t>=0 for seed positivity; all integer N for factorial majorant',
        'checks':{'seed_periods':inp['starting_L']+inp['repair_L'],
                  'perturbation_period_positions':period_checks,
                  'independent_prefix_positions':prefix_checks,
                  'tail_samples':len(points),'exact_prime_exponent_identities':exponent_cases,
                  'all_strict_C_comparisons':'exact rational log enclosures'},
        'comparisons':comparisons,
        'seconds':time.perf_counter()-t0,
        'not_proved':['No uniform contraction of C-1','No bound on coefficient mass as refinements grow','No improvement over established prime-counting theory','No RH or total-E estimate','No independent referee or formal verification'],
    }
    output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k in ('starting_C','final_C','finite_coefficient_mass','tail_multiplier','checks','seconds')},indent=2))

if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--output',type=Path,default=Path('results.json'))
    args=parser.parse_args()
    main(args.output)

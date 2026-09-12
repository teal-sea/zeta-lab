#!/usr/bin/env python3
"""Separate exact check: divisor increments and interval logs, no proposer imports."""
from __future__ import annotations
import argparse, json, math, hashlib, random, time
from pathlib import Path
from fractions import Fraction as F
from collections import defaultdict
import mpmath as mp

ROOT=Path(__file__).resolve().parent
R,M,S=100000,15,108


def coeff(x):return {int(k):F(v) for k,v in x.items()}


def combine(a,b,scale=F(1)):
    z=defaultdict(F,a)
    for j,v in b.items():z[j]+=scale*v
    return {j:v for j,v in z.items() if v}


def carry(n):
    a=defaultdict(F)
    a[n]+=1;a[n+1]-=1;a[n*(n+1)]-=1
    return dict(a)


def mu(d):
    # only divisors of 210 used here
    assert 210%d==0
    return -1 if sum(d%p==0 for p in (2,3,5,7))%2 else 1


def mask(q):
    z={}
    for d in range(1,211):
        if 210%d:continue
        z=combine(z,{d*j:v for j,v in carry(q).items()},F(mu(d)))
    return z


def table(c,stop,scale=S):
    increments=[0]*stop
    for j,v in c.items():
        u=v*scale
        assert u.denominator==1
        v=int(u)
        for k in range(j,stop,j):increments[k]+=v
    val=0;out=[]
    for x in increments:val+=x;out.append(val)
    return out


def lifted(seed,n):
    v=0
    while n:
        v+=seed[n];n//=M
    return v


def val(c,n):return sum((v*(n//j) for j,v in c.items()),F())


def int_coeff(c):
    assert all((v*S).denominator==1 for v in c.values())
    return {j:int(v*S) for j,v in c.items()}


def ivf(x):
    x=F(x)
    return mp.iv.mpf(x.numerator)/x.denominator


def ivk(c):
    z=mp.iv.mpf(0)
    for j,v in c.items():z-=ivf(v/j)*mp.iv.log(j)
    return z


def rational_mpf(v):
    sign,mant,exp,bc=v
    if bc<0:raise ValueError('nonfinite endpoint')
    x=F(-mant if sign else mant)
    return x*(1<<exp) if exp>=0 else x/F(1<<(-exp))


def ends(iv):return tuple(rational_mpf(t) for t in iv._mpi_)


def enclose(record, iv):
    lo,hi=ends(iv)
    assert F(record['lower'])<=lo<=hi<=F(record['upper'])


def greedy_independent(raw):
    events=[0]*len(raw);level=0;weights=raw.copy();patches=[]
    for n in range(1,len(raw)):
        level+=events[n]
        deficit=max(0,S-raw[n]-level)
        if deficit:
            patches.append((n,F(deficit,S)))
            level+=deficit
            for k in range(2*n,len(raw),n):events[k]+=deficit
            for k in range(n+1,len(raw),n+1):events[k]-=deficit
            for k in range(n*(n+1),len(raw),n*(n+1)):events[k]-=deficit
        weights[n]+=level
        assert weights[n]>=S
    return weights,patches


def wire_coeff(d,f,star,H0,T,N):
    z=defaultdict(F,f)
    scale=1
    while scale<=N:
        for j,v in d.items():
            if j*scale<=N:z[j*scale]+=v
        scale*=M
    scale=R;k=0
    while scale<=N:
        for j,v in star.items():
            if j*scale<=N:z[j*scale]+=(H0*(k+1)+T)*v
        scale*=M;k+=1
    return {j:v for j,v in z.items() if v and j<=N}


def lg_sum_iv(c,N):
    z=mp.iv.mpf(0)
    for j,v in c.items():
        nn=N//j
        if nn>=2:z+=ivf(v)*mp.iv.loggamma(nn+1)
    return z


def sieve_primes(n):
    a=bytearray(b'\1')*(n+1);a[:2]=b'\0\0'
    for p in range(2,math.isqrt(n)+1):
        if a[p]:a[p*p:n+1:p]=b'\0'*len(a[p*p:n+1:p])
    return [p for p in range(2,n+1) if a[p]]


def prime_exp(n,p):
    z=0
    while n:n//=p;z+=n
    return z


def verify(results_path: Path, output_path: Path):
    start=time.monotonic()
    data=json.loads(results_path.read_text())
    joint=json.loads((ROOT/'inputs/joint_results.json').read_text())
    inp=json.loads((ROOT/'inputs/seeds.json').read_text())
    d=coeff(joint['new_coefficients']);star=coeff(inp['repair_coefficients'])
    g0=coeff(inp['starting_coefficients'])
    H0=F(joint['new_tail_H'])
    assert sum((v/j for j,v in d.items()),F())==0
    s0=table(g0,30030);st=table(star,2310)
    assert min(s0)>=0 and min(st)>=0 and min(st[1:15])>=S
    for p in (ROOT/'inputs').iterdir():
        assert hashlib.sha256(p.read_bytes()).hexdigest()==data['source_checksums'][p.name]
    orig_seed=table(d,R)
    w=[lifted(orig_seed,n) for n in range(R)]
    assert min(w[1:])>=S
    cs=ivk(star)/ivf(F(14,15))
    cb=(ivk(d)+ivf(H0/R)*cs)/ivf(F(14,15))
    assert ends(ivk(d))[0]>0 and ends(ivk(star))[0]>0
    enclose(data['baseline_C'],cb)
    sumf={};T=F(0);current=cb
    total_cells=0;period_cells=0;reports=[]
    for row in data['stages']:
        q=row['q'];hc=mask(q);period=210*q*(q+1)
        assert sum((v/j for j,v in hc.items()),F())==0
        ht=table(hc,period,1)
        assert max(ht)==3 and min(ht)==-3
        period_cells+=period
        h=[ht[n%period] for n in range(R)]
        raw=[x-S*y for x,y in zip(w,h)]
        ds={n:F(S-raw[n],S) for n in range(1,R) if raw[n]<S}
        assert ds=={int(n):F(v) for n,v in row['raw_deficits']}
        potential=mp.iv.mpf(0)
        for n,v in ds.items():potential+=ivf(v)*(mp.iv.log(n+1)/n-mp.iv.log(n)/(n+1))
        gross=ivk(hc);tail=3*cs/R;gate=gross-potential-tail
        enclose(row['gross_gain'],gross);enclose(row['raw_repair_potential'],potential)
        enclose(row['tail_cost'],tail);enclose(row['guaranteed_gain'],gate)
        assert (ends(gate)[0]>0)==row['accepted']
        trial,patches=greedy_independent(raw)
        assert patches==[(int(n),F(v)) for n,v in row['patches']]
        assert all(lam<=ds[n] for n,lam in patches)
        total_cells+=R-1
        pc={}
        for n,v in patches:pc=combine(pc,carry(n),v)
        z=combine(pc,hc,F(-1))
        assert z==coeff(row['step_coefficients'])
        cost=ivk(pc);gain=gross-cost-tail
        assert ends(cost)[1]<ends(potential)[0]
        enclose(row['actual_repair_cost'],cost);enclose(row['actual_gain'],gain)
        enclose(row['trial_C'],current-gain)
        fresh=table(z,R)
        assert trial==[x+y for x,y in zip(w,fresh)]
        assert sum((v/j for j,v in z.items()),F())==0
        assert all(str(F(trial[int(n)],S))==v for n,v in row['weights'].items())
        if row['accepted']:
            w=trial;sumf=combine(sumf,z);T+=3;current-=gain
        else:assert ends(gain)[1]<0
        reports.append({'q':q,'accepted':row['accepted'],'raw_deficit_cells':len(ds),'patch_count':len(patches)})
    assert coeff(data['final_direct_coefficients'])==sumf
    assert F(data['final_extra_tail'])==T==6
    assert sum(map(abs,combine(d,sumf).values()),F())==F(91127,108)
    enclose(data['final_C'],current)

    dominance=data['eventual_envelope_dominance']
    assert dominance['N0']==10**7 and ends(cb-current)[0]>F(1,600)
    assert ends(mp.iv.log(10))[1]<F(7,3) and ends(mp.iv.log(15))[0]>2
    assert ends(mp.iv.log(100))[0]>2
    dmass=F(5797,18)
    qcap=dmass*F(52,3)+90*F(10,3)*F(17,3)
    assert qcap==F(dominance['q_N0_upper'])==F(196622,27)
    assert F(10**7,600)-qcap==F(dominance['positive_margin'])==F(253378,27)>0

    # General raw-deficit/greedy lemma checked against 120 unrelated finite arrays.
    rng=random.Random(71015)
    random_cells=0
    for length in (8,17,64,100):
        for _ in range(30):
            raw=[0]+[rng.randint(-3*S,4*S) for _ in range(length-1)]
            z,pa=greedy_independent(raw)
            df={n:max(F(0),F(S-raw[n],S)) for n in range(1,length)}
            assert all(v<=df[n] for n,v in pa)
            assert min(z[1:])>=S
            random_cells+=length-1

    # Exact factorial/prime-weight identities via two separate sums.
    exp_cases=0
    for N in (100,1000,10000):
        cc=int_coeff(wire_coeff(d,sumf,star,H0,T,N))
        for p in sieve_primes(N):
            lhs=sum(v*prime_exp(N//j,p) for j,v in cc.items())
            rhs=0;pp=p
            while pp<=N:
                weight=sum(v*((N//pp)//j) for j,v in cc.items())
                assert weight>=S
                rhs+=weight;pp*=p
            assert lhs==rhs
            exp_cases+=1

    # Sample large weights complement, but do not replace, the global tail proof.
    sample_points=[R-1,R,R+1,15*R,10**8,10**12]
    sample_points += [rng.randrange(R,10**12) for _ in range(60)]
    for n in sample_points:
        ccoef=wire_coeff(d,sumf,star,H0,T,n)
        assert sum((v*(n//j) for j,v in ccoef.items()),F())>=1

    # Interval comparisons use one combined coefficient dictionary, not per-level sums.
    comparisons=[]
    oldmass=sum(map(abs,d.values()),F());newmass=sum(map(abs,combine(d,sumf).values()),F())
    for rec in data['comparisons']:
        N=int(rec['N']);full=wire_coeff(d,sumf,star,H0,T,N);old=wire_coeff(d,{},star,H0,F(0),N)
        bv=lg_sum_iv(full,N);ob=lg_sum_iv(old,N)
        s1=mp.iv.mpf(0);ts1=mp.iv.mpf(0);s2=mp.iv.mpf(0);scale=1
        while scale<=N:s1+=1+mp.iv.log(ivf(F(N,scale)));scale*=M
        scale=R;k=0
        while scale<=N:
            tmp=1+mp.iv.log(ivf(F(N,scale)));ts1+=tmp;s2+=(k+1)*tmp;scale*=M;k+=1
        log1=1+mp.iv.log(N)
        u=current*N+ivf(newmass)*log1+ivf(oldmass)*(s1-log1)+15*(ivf(H0)*s2+ivf(T)*ts1)
        ou=cb*N+ivf(oldmass)*s1+15*ivf(H0)*s2
        assert ends(u-bv)[0]>0 and ends(ou-ob)[0]>0
        assert ends(ob-bv)[0]>0
        expected_u_positive=N>=10**8
        assert (ends(ou-u)[0]>0)==expected_u_positive
        # Saved decimal evaluations should be within their printed precision, not exact rationals.
        for key,value in [('old_B',ob),('new_B',bv),('B_saving',ob-bv),('old_U',ou),('new_U',u),('U_saving',ou-u)]:
            lo,hi=ends(value);x=F(rec[key]);tol=F(1,10**48)
            assert lo-tol<x<hi+tol
        comparisons.append({'N':N,'B_saving_positive':True,'U_saving_positive':expected_u_positive})
    output={'status':'PASS: separate-code self-check, not an independent-agent proof review',
            'full_prefix_cells':total_cells,'period_cells':period_cells,
            'random_lemma_cases':120,'random_lemma_cells':random_cells,
            'exact_prime_exponent_identities':exp_cases,'large_weight_samples':len(sample_points),
            'accepted_corrections':[x['q'] for x in reports if x['accepted']],
            'rejected_control':[x['q'] for x in reports if not x['accepted']],
            'stage_checks':reports,'interval_comparisons':comparisons,
            'new_first_level_mass':str(newmass),'eventual_envelope_threshold_checked':10**7,'seconds':time.monotonic()-start}
    output_path.write_text(json.dumps(output,indent=2)+'\n')
    print(json.dumps(output,indent=2))


if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--results',type=Path,default=ROOT/'results.json')
    ap.add_argument('--output',type=Path,default=ROOT/'rerun_checks.json')
    args=ap.parse_args()
    old=mp.iv.dps
    try:
        mp.iv.dps=85
        verify(args.results,args.output)
    finally:mp.iv.dps=old

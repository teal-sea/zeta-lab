"""Compare repairing the lifted weight with repairing every seed value.

No new LP: same input coefficients and five fixed perturbations.
Exact integer checks are not an independent proof review.
"""
from pathlib import Path
from fractions import Fraction as F
import json, math, time
import numpy as np
import mpmath as mp
import refine as r

ROOT=Path(__file__).resolve().parent
M=r.M; R=r.R

def lift_prefix(values):
    n=np.arange(len(values),dtype=np.int64)
    out=np.zeros_like(values)
    s=1
    while s<len(values):
        out+=values[n//s]
        s*=M
    return out

def independent_lifted_value(c,H,star,t,den):
    out=0
    z=t
    while z:
        seed=sum(int(a*den)*(z//j) for j,a in c.items())
        seed+=den*H*r.repair_weight(star,z//R)
        out+=seed
        z//=M
    return out

def main():
    start=time.perf_counter()
    inp=json.loads((ROOT/'inputs.json').read_text())
    orig=json.loads((ROOT/'original_results.json').read_text())
    initial={int(j):F(a) for j,a in inp['starting_coefficients'].items()}
    star={int(j):F(a) for j,a in inp['repair_coefficients'].items()}
    c=initial.copy();den=math.lcm(*(a.denominator for a in c.values()))
    Cstar=r.kappa(star)/r.mpf(F(14,15))
    Cstar_b=tuple(x/F(14,15) for x in r.kappa_bounds(star))
    prev=tuple(x/F(14,15) for x in r.kappa_bounds(c))
    totalH=0;stages=[];tt=np.arange(R,dtype=np.int64)
    input_count=0
    for coeff,L in [(initial,inp['starting_L']),(star,inp['repair_L'])]:
        vals,d=r.floor_array(coeff,L)
        assert r.balanced(coeff) and vals.min()>=0 and vals[1:M].min()>=d
        input_count+=L
    prefix_checks=0;period_checks=0
    for p in r.PRIMES:
        h=r.stencil_coeff(p)
        period=math.prod(r.MASK)*p*(p+1)
        H=int(r.stencil_array(p,period).max())
        assert H==3
        period_checks+=period
        trial_c=r.add_coeff(c,h,F(-1))
        seed_vals,_=r.floor_array(trial_c,R,den)
        W=lift_prefix(seed_vals)
        negative_but_covered=int(np.count_nonzero((seed_vals<0)&(W>=den)))
        repairs=[]
        for n in range(1,R):
            deficit=den-int(W[n])
            if deficit>0:
                assert n>=M
                a=F(deficit,den)
                repairs.append((n,a))
                trial_c=r.add_coeff(trial_c,r.bump_coeff(n),a)
                s=1
                while n*s<R:
                    W[n*s:]+=deficit*r.bump(n,tt[n*s:]//s)
                    s*=M
        assert W[1:].min()>=den
        # Independent reconstruction from combined coefficients, then floor quotient lifting.
        rebuilt_seed,_=r.floor_array(trial_c,R,den)
        rebuilt_W=lift_prefix(rebuilt_seed)
        assert np.array_equal(W,rebuilt_W)
        prefix_checks+=R
        assert r.balanced(trial_c)
        totalH+=H
        kb=r.kappa_bounds(trial_c)
        assert kb[0]>0
        Cb=tuple((kb[i]+F(totalH,R)*Cstar_b[i])/F(14,15) for i in (0,1))
        Cv=(r.kappa(trial_c)+mp.mpf(totalH)*Cstar/R)/r.mpf(F(14,15))
        stages.append({'p':p,'H':H,'repairs':[[n,str(a)] for n,a in repairs],
                       'number_of_repairs':len(repairs),'C':str(Cv),
                       'C_interval':r.outward_summary(Cb),
                       'strict_decrease_exact':Cb[1]<prev[0],
                       'seed_min_scaled':int(rebuilt_seed.min()),
                       'negative_seed_cells':int(np.count_nonzero(rebuilt_seed<0)),
                       'negative_but_covered_before_repair':negative_but_covered,
                       'lifted_min_scaled':int(rebuilt_W[1:].min()),
                       'coefficient_mass':str(r.mass(trial_c))})
        c=trial_c;prev=Cb
    rng=np.random.default_rng(6644)
    points=[R,R+1,R*M,10**8,10**12]+rng.integers(R,10**12,size=64).tolist()
    for t in points:
        # Seed nonnegative on the large argument region, and final lifted weight covers everywhere.
        seed=sum(int(a*den)*(t//j) for j,a in c.items())+den*totalH*r.repair_weight(star,t//R)
        assert seed>=0
        assert independent_lifted_value(c,totalH,star,t,den)>=den
    oldc={int(j):F(a) for j,a in orig['final_direct_coefficients'].items()}
    oldmass=r.mass(oldc);newmass=r.mass(c)
    Cfinal=(r.kappa(c)+mp.mpf(totalH)*Cstar/R)/r.mpf(F(14,15))
    exponent_count=0
    for N in (1000,10000,10**6):
        coeff=r.lifted_coeff(c,totalH,star,N)
        ps=r.prime_list(N) if N<=10000 else [2,3,5,7,11,13,17,19,23,29,31,101,997,9973]
        for p in ps:
            left=sum(int(a*den)*r.legendre(N//j,p) for j,a in coeff.items())
            right=0;power=p
            while power<=N:
                w=independent_lifted_value(c,totalH,star,N//power,den)
                assert w>=den
                right+=w;power*=p
            assert left==right
            exponent_count+=1
    compares=[]
    for N in (10**4,10**6,10**8,10**12):
        oldB=r.extended_certificate(oldc,totalH,star,N)
        newB=r.extended_certificate(c,totalH,star,N)
        newU=Cfinal*N+r.mpf(newmass)*r.first_budget(N)+totalH*r.mpf(r.mass(star))*r.second_budget(N)
        oldU=mp.mpf(orig['final_C'])*N+r.mpf(oldmass)*r.first_budget(N)+totalH*r.mpf(r.mass(star))*r.second_budget(N)
        assert newB<=newU and oldB<=oldU
        compares.append({'N':N,'old_B':str(oldB),'new_B':str(newB),'old_U':str(oldU),'new_U':str(newU)})
    # Unused-update budget: each future p>31 used at most once, nonnegative repair charges.
    # Sum over all odd n>=33, log31 < 7/2, gives total future gross saving < 33/1519.
    coarse_gain=F(33,1519)
    assert F(orig['final_C'])>F(21,20)
    proof_floor=F(21,20)-coarse_gain
    out={'status':'written rule change with exact finite feasibility; no asymptotic family rate or novelty claim',
         'parameters':{'M':M,'R':R,'mask':list(r.MASK),'primes':list(r.PRIMES)},
         'stages':stages,'new_final_C':str(Cfinal),'new_final_mass':str(newmass),
         'old_final_C':orig['final_C'],'old_final_mass':str(oldmass),'tail_multiplier':totalH,
         'fixed_future_recipe':{'max_gross_saving_upper_rational':str(coarse_gain),
           'leading_C_lower_rational':str(proof_floor),
           'leading_C_lower_decimal':str(r.mpf(proof_floor)),
           'assumptions':'start from old five-stage seed; mask 210, M=15, each new prime p>31 once, nonnegative repair and tail integral costs'},
         'new_coefficients':{str(k):str(v) for k,v in sorted(c.items())},
         'comparisons':compares,
         'checks':{'input_seed_cells':input_count,'perturbation_period_cells':period_checks,
                   'independent_lifted_prefix_cells':prefix_checks,'large_argument_samples':len(points),
                   'factorial_exponent_identities':exponent_count},
         'seconds':time.perf_counter()-start}
    (ROOT/'aggregate_results.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:out[k] for k in ['new_final_C','new_final_mass','old_final_C','old_final_mass','checks','seconds']},indent=2))
    for st in stages:print(st['p'],st['C'],st['number_of_repairs'],st['coefficient_mass'],st['negative_seed_cells'],st['strict_decrease_exact'])
    print('comparison',json.dumps(compares,indent=2))
if __name__=='__main__':main()

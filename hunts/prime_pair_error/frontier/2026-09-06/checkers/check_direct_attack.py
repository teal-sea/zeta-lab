"""Finite checks for a direct arithmetic attempt on the prime-counting remainder.

These validate identities and countermodels, NOT RH, any zero-free strip,
or an asymptotic prime-error estimate. No network access is required.
"""
from __future__ import annotations
import json, math, platform
from pathlib import Path
import numpy as np
from mpmath import mp

OUT = Path(__file__).resolve().parent


def mangoldt(N: int) -> np.ndarray:
    if N < 2: raise ValueError('N must be >= 2')
    prime=np.ones(N+1,dtype=bool);prime[:2]=False
    for p in range(2,math.isqrt(N)+1):
        if prime[p]:prime[p*p::p]=False
    a=np.zeros(N+1)
    for p0 in np.flatnonzero(prime):
        p=int(p0);t=p
        while t<=N:
            a[t]=math.log(p)
            if t>N//p:break
            t*=p
    return a


def exact_factorial_exponents()->dict:
    count=0
    for N in list(range(2,65))+[128,512,1000]:
        right={}
        for n in range(2,N+1):
            q=n;d=2
            while d*d<=q:
                while q%d==0:right[d]=right.get(d,0)+1;q//=d
                d+=1
            if q>1:right[q]=right.get(q,0)+1
        left={}
        for p in right:
            t=p;val=0
            while t<=N:val+=N//t;t*=p
            left[p]=val
        assert left==right;count+=1
    return {'integer_prime_exponent_checks':count,'largest_N':1000}


def check_factorization()->dict:
    Nmax=100_000;lam=mangoldt(Nmax);psi=np.cumsum(lam);divsum=np.zeros(Nmax+1)
    for d in np.flatnonzero(lam):divsum[d::d]+=lam[d]
    err=np.abs(divsum[1:]-np.log(np.arange(1,Nmax+1)));maxerr=float(err.max());assert maxerr<2e-13
    rows=[]
    for N in [2,3,10,100,1000,10_000,100_000]:
        vals=psi[N//np.arange(1,N+1)];left=math.fsum(vals);right=math.lgamma(N+1);diff=abs(left-right);assert diff<2e-7
        rsum=math.fsum(psi[N//np.arange(1,N+1)]-N/np.arange(1,N+1));harmonic=math.fsum(1/m for m in range(1,N+1));exact_right=math.lgamma(N+1)-N*harmonic
        assert abs(rsum-exact_right)<2e-7;rows.append({'N':N,'factorial_residual':diff,'R_divisor_residual':abs(rsum-exact_right)})
    return {'all_divisor_identities_through':Nmax,'max_divisor_error':maxerr,'factorial_rows':rows}


def check_spectral_response()->dict:
    mp.dps=55;rho0=mp.zetazero(1)
    params=[('first_critical_zero',rho0),('same_height_beta_3_4_NOT_a_zero',mp.mpf('0.75')+1j*mp.im(rho0)),('real_power_3_4_NOT_a_zero',mp.mpf('0.75'))]
    rows=[]
    for label,s in params:
        zs=mp.zeta(s)
        for N in [100,1000,10_000]:
            direct=mp.power(N,s)*mp.fsum(mp.power(m,-s) for m in range(1,N+1));comp=direct-N/(1-s)-mp.mpf('0.5');approx=zs*mp.power(N,s)-s/(12*N);err=abs(comp-approx)
            assert float(err*N**3)<20.0
            rows.append({'label':label,'N':N,'beta':float(mp.re(s)),'gamma':float(mp.im(s)),'abs_zeta':float(abs(zs)),'input_amplitude':float(mp.power(N,mp.re(s))),'compensated_output_abs':float(abs(comp)),'EM_error':float(err),'N3_times_EM_error':float(err*N**3)})
    return {'precision_decimal_digits':mp.dps,'rows':rows,'note':'Only the first parameter is a numerical zero. The others are controls.'}


def sparse_countermodel()->dict:
    n0=10_000;N=2_000_000;beta=.75;gamma=3.;c=.1;initial=mangoldt(n0);weights=np.zeros(N+1);weights[:n0+1]=initial;running=float(math.fsum(initial));offset=running-(n0+c*n0**beta*math.cos(gamma*math.log(n0)))
    logn=np.log(np.arange(n0+1,N+1,dtype=float));targets=np.arange(n0+1,N+1,dtype=float)+c*np.exp(beta*logn)*np.cos(gamma*logn)+offset
    max_tracking=0.;checkpoints={100_000,300_000,1_000_000,2_000_000};rows=[]
    for i,n in enumerate(range(n0+1,N+1)):
        target=float(targets[i])
        if math.gcd(n,30)==1 and target-running>=logn[i]:weights[n]=logn[i];running+=logn[i]
        tracking=target-running;max_tracking=max(max_tracking,tracking);assert -1e-6<=tracking<=math.log(n)+12
        if n in checkpoints:rows.append({'N':n,'weighted_total':running,'remainder':running-n,'specified_drift_plus_offset':target-n,'tracking_error':tracking,'sqrtN':math.sqrt(n)})
    witness=None
    for n in range(n0+1,min(N,n0+10000)+1):
        sd=0.
        for d in range(1,math.isqrt(n)+1):
            if n%d==0:
                sd+=weights[d]
                if d*d!=n:sd+=weights[n//d]
        gap=sd-math.log(n)
        if abs(gap)>1e-8:witness={'n':n,'divisor_sum_minus_log_n':gap};break
    assert witness is not None
    for row in rows:
        n=row['N'];row['second_moment_over_NlogN']=float(np.dot(weights[:n+1],weights[:n+1])/(n*math.log(n)))
    return {'N':N,'n0':n0,'beta':beta,'gamma':gamma,'c':c,'offset':offset,'max_tracking_error':max_tracking,'rows':rows,'first_checked_divisor_identity_failure':witness,'note':'Counterexample to generic norm/local-divisibility assumptions only; NOT actual primes.'}


def main()->None:
    res={'date':'2026-09-06','python':platform.python_version(),'numpy':np.__version__,'scope':'No new upper bound or proof of RH. Finite identities and a counterfeit-sequence diagnostic.','exact_factorial_exponents':exact_factorial_exponents(),'factorization':check_factorization(),'spectral_response':check_spectral_response(),'countermodel':sparse_countermodel()}
    (OUT/'checks.json').write_text(json.dumps(res,indent=2)+'\n');print(json.dumps(res,indent=2))

if __name__=='__main__':main()

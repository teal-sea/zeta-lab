"""Finite and symbolic checks for MULTISCALE.md.

These checks do not verify the infinite-zero estimates or an RH-level bound.
Run: python check_multiscale.py
Dependencies: numpy, sympy. No network or API keys are used.
"""
from __future__ import annotations

import json
import math
from pathlib import Path
from fractions import Fraction
from functools import lru_cache
import platform

import numpy as np
import sympy as sp

HERE = Path(__file__).resolve().parent


def energy_algebra() -> dict:
    u = sp.symbols('u', real=True)
    s = sp.symbols('s', real=True)
    a = 13 - 4*sp.sqrt(3)
    a2 = sp.Rational(21, 2) - 2*sp.sqrt(5)
    u1 = (1 + 2*sp.sqrt(3))/11
    u2 = (1 + 2*sp.sqrt(5))/19
    p1 = a*u*(1+u) - (11*u-1)
    p2 = 2*a2*u*(1+u) - (19*u-1)
    assert sp.simplify(p1-a*(u-u1)**2) == 0
    assert sp.simplify(p2-2*a2*(u-u2)**2) == 0
    assert sp.simplify(a-a2).is_positive
    assert sp.simplify(a-6).is_positive
    tau = sp.simplify(4/a)
    p = sp.simplify(3-tau)
    assert sp.simplify(2-sp.Integer(3)*tau).is_positive
    strip = 4*s-1 + tau*(a*(1-s)-1)
    assert sp.simplify(strip-p) == 0
    assert sp.simplify((1+2*tau)-p).is_negative
    mx = (-1.0, None)
    for i in range(5000, 10000):
        x = Fraction(i, 10000)
        if x <= Fraction(2,3):
            val = (10-11*x)/((2-x)*(1-x))
        elif x <= Fraction(3,4):
            val = (18-19*x)/((4-2*x)*(1-x))
        else:
            val = 12/(4*x-1)
        if float(val) > mx[0]: mx = (float(val), float(x))
        assert float(val) < float(a) + 1e-12
    return {'exact_completed_square_certificates':2,'A_star_uniform_bound':str(a),
            'A_star_decimal':float(a),'tau_star':float(tau),'frequency_decay_power':float(1-tau),
            'optimized_local_fourth_moment_power':float(p),'nonzero_rational_model_power':float(1+2*tau),
            'first_energy_maximum_sigma':float(1-u1),'grid_points':5000,
            'grid_max':{'value':mx[0],'sigma':mx[1]},
            'status':'Exact symbolic identities plus stated numerical diagnostics.'}


def convolve_int(a:list[int],b:list[int])->list[int]:
    return list(np.convolve(np.array(a,dtype=object),np.array(b,dtype=object)))


@lru_cache(None)
def reproducer(N:int,m:int)->tuple[list[int],int,int]:
    triangle=[N-abs(j) for j in range(-N+1,N)]
    coeff=[1]
    for _ in range(m): coeff=convolve_int(coeff,triangle)
    L=(m+1)*N
    coeff=convolve_int(coeff,[1]*(2*L+1))
    den=N**(2*m); degree=(len(coeff)-1)//2
    assert degree==(2*m+1)*N-m
    assert all(0<=x<=den for x in coeff)
    assert all(coeff[degree+j]==den for j in range(-N-m,N+m+1))
    assert sum(x*x for x in coeff)<=((4*m+2)*N-2*m+1)*den**2
    return coeff,den,degree


def exact_reproduction_tests()->dict:
    rng=np.random.default_rng(20260906); identities=0
    for N in range(1,33):
        tri=[N-abs(j) for j in range(-N+1,N)]
        for m in range(1,5):
            coeff,den,degree=reproducer(N,m)
            for _ in range(4):
                w=[int(x) for x in rng.integers(-4,6,size=N)]
                corr=convolve_int(w,w[::-1]); D=[corr[j]-tri[j] for j in range(len(tri))]
                integral_num=sum(D[j]*coeff[degree-(j-(N-1))] for j in range(len(D)))
                assert integral_num==den*(sum(w)**2-N**2); identities+=1
    return {'integer_weight_identities':identities,'kernel_norm_and_plateau_cases':128,
            'm_range':[1,4],'N_range':[1,32],
            'arithmetic':'Exact Python integers; signed weights permitted for the identity.'}


def mangoldt(N:int)->np.ndarray:
    if N<2:return np.zeros(N+1)
    sieve=np.ones(N+1,dtype=bool);sieve[:2]=False
    for p in range(2,math.isqrt(N)+1):
        if sieve[p]:sieve[p*p::p]=False
    out=np.zeros(N+1)
    for p in np.flatnonzero(sieve):
        r=int(p)
        while r<=N:
            out[r]=math.log(int(p))
            if r>N//int(p):break
            r*=int(p)
    return out


def series_values(c:np.ndarray,L:int)->np.ndarray:
    if len(c)>L:raise ValueError('FFT grid too short for this finite series')
    return np.fft.ifft(c,n=L)*L


def transfer_tests(tau_star:float)->dict:
    rows=[];worst=0.0
    for N in (256,729,1600):
        M=N+67;lam=mangoldt(M);weights=lam-1;weights[0]=0;n=np.arange(M+1)
        Bcoef=weights*np.exp(-n/N);Hcoef=np.zeros(N+1);Hcoef[1:]=np.exp(np.arange(1,N+1)/N)
        L=1<<max(17,int(math.ceil(math.log2(8*(M+1)))))
        B=series_values(Bcoef,L);H=series_values(Hcoef,L);S=series_values(weights[:N+1],L)
        conv=np.fft.ifft(np.fft.fft(B)*np.fft.fft(H))/L
        rel=float(np.max(np.abs(conv-S))/max(1.0,np.max(np.abs(S))));assert rel<1e-11;worst=max(worst,rel)
        x=np.arange(L)/L;B2=float(np.mean(np.abs(B)**2));LN=2*math.e+4*math.log(N);assert np.mean(np.abs(H))<=LN
        for tau in (0.4,0.5,tau_star):
            delta=N**(tau-1)/(2*math.pi);assert 0<delta<1/16
            I=(x>=delta)&(x<=2*delta);J=(x>=delta/2)&(x<=4*delta)
            near=np.fft.ifft(np.fft.fft(B*J)*np.fft.fft(H))/L;far=S-near
            actual=float(np.sum(np.abs(S[I])**4)/L);local=float(np.sum(np.abs(B[J])**4)/L)
            bound=8*LN**4*local+2048/delta*B2**2;assert actual<=bound*(1+1e-8)
            assert np.max(np.abs(far[I])**2)<=(16/delta)*B2*(1+1e-7)
            rows.append({'N':N,'tau':tau,'delta':delta,'finite_LHS':actual,'finite_LT_RHS':bound,'ratio':actual/bound})
    return {'convolution_cases':3,'localized_cases':len(rows),'max_relative_convolution_error':worst,'rows':rows,
            'scope':'Finite damped series; grid inequalities are diagnostics, not asymptotic certification.'}


def phi_mu(q:int)->tuple[int,int]:
    n=q;phi=q;mu=1;p=2
    while p*p<=n:
        if n%p==0:
            phi=phi//p*(p-1);n//=p;mu=-mu
            if n%p==0:
                mu=0
                while n%p==0:n//=p
        p+=1
    if n>1:phi=phi//n*(n-1);mu=-mu
    return phi,mu


def arc_budget_tests()->dict:
    rows=[];geometry_cases=0
    for N in (400,900,1600):
        Q=math.isqrt(N)//3;L=1<<17;alpha=np.arange(L)/L;signed=np.minimum(alpha,1-alpha)
        F=series_values(mangoldt(N),L);f2=np.abs(F)**2;major=np.zeros(L,dtype=bool);model2=np.zeros(L)
        for q in range(1,Q+1):
            ph,mu=phi_mu(q)
            for a in range(1,q+1):
                if math.gcd(a,q)>1:continue
                center=(a/q)%1;dist=np.abs((alpha-center+0.5)%1-0.5);mask=dist<=Q/(q*N)
                assert not np.any(mask & major);major|=mask
                if mu:
                    c=np.zeros(N+1,dtype=complex);c[1:]=(mu/ph)*np.exp(-2j*math.pi*np.arange(1,N+1)*center)
                    P=series_values(c,L);model2[mask]=np.abs(P[mask])**2
        M_int=np.where(major,(f2-model2)**2,0.0);I_int=np.where(~major,f2**2,0.0)
        for lo,hi in ((0.005,0.07),(0.02,0.18),(0.03,0.24)):
            B=(signed>=lo)&(signed<=hi);MB=float(np.mean(M_int*B));IB=float(np.mean(I_int*B))
            rhs=2*float(np.mean(f2**2*B))+2*float(np.mean(model2**2*B));assert MB+IB<=rhs*(1+1e-12)
            assert abs(float(np.mean(M_int))-MB-float(np.mean(M_int*~B)))<1e-8*max(1.0,MB)
            assert abs(float(np.mean(I_int))-IB-float(np.mean(I_int*~B)))<1e-8*max(1.0,IB)
            for q in range(2,Q+1):
                for a in range(1,q):
                    if math.gcd(a,q)>1:continue
                    c=min(a/q,1-a/q);radius=Q/(q*N)
                    if c-radius<=hi and c+radius>=lo:
                        assert q>=(1-Q/N)/hi-1e-12;geometry_cases+=1
            rows.append({'N':N,'Q':Q,'band':[lo,hi],'M_band':MB,'I_band':IB,'combined_elementary_RHS':rhs})
    return {'accounting_cases':len(rows),'nonzero_center_checks':geometry_cases,'rows':rows,
            'scope':'Finite Fourier-grid diagnostics; exact inequalities are proved in the note.'}


def core_tests()->dict:
    out=[]
    for N in (144,400,900):
        weights=mangoldt(N);L=1<<19;alpha=np.arange(L)/L;circ=np.minimum(alpha,1-alpha)
        F=series_values(weights,L);kk=np.ones(N+1);kk[0]=0;K=series_values(kk,L);D=np.abs(F)**2-np.abs(K)**2;psi=float(weights.sum())
        for m,tau in ((2,0.45),(3,0.3),(4,0.2)):
            R=N**tau/(2*math.pi);radius=R/N;M=float(np.sum(D[circ<=radius]**2)/L)
            rhs=math.sqrt(((4*m+2)*N-2*m+1)*M)+(psi**2+N**2)/(m*2**(2*m+1)*R**(2*m));lhs=abs(psi**2-N**2)
            assert lhs<=rhs*(1+1e-6);out.append({'N':N,'m':m,'tau':tau,'R':R,'central_M':M,'LHS':lhs,'RHS':rhs})
    return {'localized_von_mangoldt_cases':len(out),'rows':out,'scope':'Numerical quadrature diagnostics, not interval-certified inequalities.'}


def main()->None:
    res={'date':'2026-09-06','python':platform.python_version(),'numpy':np.__version__,'sympy':sp.__version__,
         'status':'Finite checks only; analytic input theorems and asymptotic deductions require written-proof review.'}
    res['energy']=energy_algebra();res['reproduction']=exact_reproduction_tests();res['transfer']=transfer_tests(res['energy']['tau_star']);res['arc_budget']=arc_budget_tests();res['core']=core_tests();res['all_checks_passed']=True
    (HERE/'checks.json').write_text(json.dumps(res,indent=2)+'\n')
    print(json.dumps({'all_checks_passed':True,'energy_constants':res['energy'],'exact_reproduction':res['reproduction'],
                      'localized_transfer_cases':res['transfer']['localized_cases'],'arc_accounting_cases':res['arc_budget']['accounting_cases'],
                      'core_cases':res['core']['localized_von_mangoldt_cases']},indent=2))

if __name__=='__main__':main()

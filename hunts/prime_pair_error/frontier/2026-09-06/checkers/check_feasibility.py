#!/usr/bin/env python3
"""Finite checks for a zero-energy transfer and sharp q=1 localization.

These verify finite identities, the change of variables, and numerical
quadrature. They do NOT prove asymptotic zero-density or prime-pair bounds.
Synthetic complex parameters in the kernel test are NOT claimed to be zeros.
Run: python check_feasibility.py
Requires numpy and scipy. Writes checks.json beside this script.
"""
from __future__ import annotations
import json
import math
from pathlib import Path
import numpy as np
from numpy.polynomial.legendre import leggauss
from scipy.special import loggamma

HERE = Path(__file__).resolve().parent


def gauss_interval(a: float, b: float, order: int = 256):
    nodes, weights = leggauss(order)
    return a + (nodes + 1) * (b-a)/2, weights*(b-a)/2


def check_localization_exact() -> dict:
    """Use integer Fourier numerators, without floating point."""
    rng = np.random.default_rng(20260906)
    cases = 0
    max_norm_over_N = 0.0
    for n in range(1, 65):
        h = np.arange(-(n-1), n, dtype=np.int64)
        triangle = n - np.abs(h)
        fourth_numerator = np.convolve(triangle, triangle)
        assert int(fourth_numerator.sum()) == n**4
        kappa_num = np.convolve(np.ones(6*n+1, dtype=np.int64), fourth_numerator)
        center = 5*n-2
        assert len(kappa_num) == 10*n-3
        assert np.all(kappa_num[center-(n+2):center+(n+2)+1] == n**4)
        assert int(kappa_num.min()) >= 0 and int(kappa_num.max()) <= n**4
        norm_num = sum(int(v)**2 for v in kappa_num)
        assert norm_num <= (10*n-3)*n**8
        max_norm_over_N = max(max_norm_over_N, norm_num/n**9)
        for _ in range(8):
            a = rng.integers(-20, 21, size=n, dtype=np.int64)
            d = np.convolve(a, a[::-1]) - triangle
            inner_num = sum(int(dj)*int(kappa_num[center+int(hj)]) for dj,hj in zip(d,h))
            at_zero = int(a.sum())**2-n*n
            assert inner_num == n**4*at_zero
            cases += 1
    return {"status":"pass", "exact_integer_weight_cases":cases,
            "N_range":[1,64], "maximum_squared_kernel_norm_divided_by_N":max_norm_over_N,
            "proved_bound_used":"||kappa_N||_2^2 <= 10N-3"}


def check_soft_energy() -> dict:
    rng = np.random.default_rng(19760906)
    ratios = []
    for _ in range(80):
        ordinates = rng.uniform(-80, 80, 9)
        pair_sums = (ordinates[:,None]+ordinates[None,:]).ravel()
        difference = np.abs(pair_sums[:,None]-pair_sums[None,:])
        energy = int(np.count_nonzero(difference <= 1))
        soft = float(np.sum((1+difference)**(-2)))
        bin_values, counts = np.unique(np.floor(pair_sums).astype(int), return_counts=True)
        del bin_values
        bnorm = int(counts @ counts)
        assert bnorm <= energy
        assert soft <= (1+math.pi**2/3)*bnorm+1e-9
        ratios.append(soft/energy)
    return {"status":"pass", "synthetic_ordinate_sets":80,
            "max_soft_energy_over_unit_energy":max(ratios),
            "proved_constant":1+math.pi**2/3}


def check_gamma_transfer() -> dict:
    beta = np.array([0.50,0.51,0.67,0.72,0.75,0.76])
    gamma = np.array([-15.2,-31.1,-31.8,-48.7,19.4,33.0])
    rho = beta+1j*gamma
    x = 10000.0
    scale = 80.0
    lg = loggamma(rho)
    t, tw = gauss_interval(1.0,2.0)
    alpha = scale*t/(2*math.pi*x)
    z = 1/x-2j*math.pi*alpha
    direct_terms = np.exp(lg[None,:]-np.log(z)[:,None]*rho[None,:])
    s = np.log(x*np.abs(z)/scale)
    theta = np.angle(z)
    b = np.exp(lg[None,:]-rho[None,:]*math.log(scale/x)
               -s[:,None]*beta[None,:]+theta[:,None]*gamma[None,:]
               -1j*theta[:,None]*beta[None,:])
    reconstructed = b*np.exp(-1j*s[:,None]*gamma[None,:])
    rel_terms = float(np.max(np.abs(direct_terms-reconstructed))/np.max(np.abs(direct_terms)))
    assert rel_terms < 1e-11
    alpha_weights = tw*scale/(2*math.pi*x)
    moment_alpha = float(alpha_weights @ np.abs(direct_terms.sum(axis=1))**4)
    slo, shi = .5*math.log(1+scale**(-2)), .5*math.log(4+scale**(-2))
    sn, sw = gauss_interval(slo,shi)
    an = np.sqrt(scale**2*np.exp(2*sn)-1)/(2*math.pi*x)
    zn = 1/x-2j*math.pi*an
    terms_s = np.exp(lg[None,:]-np.log(zn)[:,None]*rho[None,:])
    jac = scale/(2*math.pi*x)*np.exp(2*sn)/np.sqrt(np.exp(2*sn)-scale**(-2))
    moment_s = float((sw*jac) @ np.abs(terms_s.sum(axis=1))**4)
    relative_change = abs(moment_alpha-moment_s)/max(moment_alpha,1e-300)
    assert relative_change < 1e-10
    kernel = np.einsum('ai,aj,ak,al,a->ijkl',direct_terms,direct_terms,
                       np.conj(direct_terms),np.conj(direct_terms),alpha_weights,optimize=True)
    expanded = kernel.sum()
    relative_expansion = abs(expanded-moment_alpha)/max(moment_alpha,1e-300)
    assert relative_expansion < 1e-10
    return {"status":"pass", "parameters":"six synthetic complex numbers, not zeta zeros",
            "X":x,"frequency_scale_T":scale,
            "max_term_relative_difference":rel_terms,
            "fourth_moment_alpha":moment_alpha,"fourth_moment_log_radius":moment_s,
            "change_of_variables_relative_error":relative_change,
            "four_index_expansion_relative_error":float(relative_expansion)}


def mangoldt(n: int) -> np.ndarray:
    sieve = np.ones(n+1,dtype=bool)
    sieve[:2] = False
    for p in range(2,math.isqrt(n)+1):
        if sieve[p]: sieve[p*p::p] = False
    lam = np.zeros(n+1,dtype=float)
    for p0 in np.flatnonzero(sieve):
        p=int(p0); v=p
        while v<=n:
            lam[v]=math.log(p)
            v*=p
    return lam[1:]


def check_prime_localization() -> dict:
    rows=[]
    for n in (144,400,900):
        q=math.isqrt(n)//3
        delta=q/n
        lam=mangoldt(n)
        alpha,weights=gauss_interval(0,delta,order=512)
        mat=np.exp(2j*math.pi*np.outer(alpha,np.arange(1,n+1)))
        fn=mat@lam
        kn=mat.sum(axis=1)
        d=np.abs(fn)**2-np.abs(kn)**2
        m1=float(2*(weights@(d*d)))
        psi=float(lam.sum())
        tail=(psi*psi+n*n)/(64*q**4)
        lhs=abs(psi*psi-n*n)
        rhs=math.sqrt((10*n-3)*m1)+tail
        assert lhs <= rhs+1e-7
        size=16*n
        f_full=np.fft.fft(np.r_[0.,lam],n=size)
        k_full=np.fft.fft(np.r_[0.,np.ones(n)],n=size)
        grid=np.arange(size)/size
        dirichlet=np.empty(size)
        dirichlet[0]=6*n+1
        dirichlet[1:]=np.sin((6*n+1)*math.pi*grid[1:])/np.sin(math.pi*grid[1:])
        kap=dirichlet*(np.abs(k_full)/n)**4
        integral=float(np.mean((np.abs(f_full)**2-np.abs(k_full)**2)*kap))
        exact=psi*psi-n*n
        discrepancy=abs(integral-exact)
        assert discrepancy < 1e-6*max(1,abs(exact))
        rows.append({"N":n,"Q":q,"M1_quadrature":m1,"endpoint_difference":lhs,
                     "localization_upper_bound_for_endpoint":rhs,
                     "explicit_tail_allowance":tail,"reproducing_identity_abs_error":discrepancy})
    return {"status":"pass", "rows":rows,
            "qualification":"quadrature is numerical, not an interval enclosure"}


def main() -> None:
    results={"seeded_reproducible_checks":True,
             "localization":check_localization_exact(),
             "soft_energy":check_soft_energy(),
             "gamma_transfer":check_gamma_transfer(),
             "prime_localization":check_prime_localization(),
             "scope":"finite identity checks only; no asymptotic theorem is certified by these tests"}
    (HERE/'checks.json').write_text(json.dumps(results,indent=2)+'\n')
    print(json.dumps(results,indent=2))

if __name__=='__main__':
    main()

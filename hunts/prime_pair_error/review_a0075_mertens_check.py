"""
Independent check of ENDPOINT_SHARP.md section 2.1, equation (A) and the
claimed crossovers. Written from scratch for this review; does not import
or reuse endpoint_sharp_mertens_probe.py.

We work at kappa = 1/2, target decay exp(-c*sqrt(l)) with c = 1 (matching
the document's section 7 table, whose header says "target decay
exp(-sqrt(ell))").

For each l = log N in the document's table we:
  1. Get H_Z = sum_{p<Z} 1/p, Z = exp(sqrt(l)).
     - exact prime sum when Z is small enough to sieve (log Z <= ~20),
     - Mertens second theorem H_Z = loglog(Z) + M + err otherwise, since
       exact enumeration is impossible once Z = exp(1000) or bigger.
  2. Fixed cutoff m = 2*ceil(sqrt(l)); A_fixed = m*log(Z)/l.
  3. Retuned cutoff: least even m with
         (m+1)*log((m+1)/(e*H_Z)) >= c*sqrt(l)
     found by direct search (this is the exact threshold from (5'), not
     the closed-form asymptotic (A)); A_retuned = m*log(Z)/l.
  4. The closed-form asymptotic prediction from (A):
         A_pred = (2c/kappa) * l**(2*kappa-1) / log(l) = 4*c/log(l).
"""
import mpmath as mp

mp.mp.dps = 50

M_MERTENS = mp.mpf('0.2614972128476427837554268386086958590516')
EULER_GAMMA = mp.euler


import numpy as np


def sieve_primes_below(x):
    x = int(x)
    if x < 2:
        return np.array([], dtype=np.int64)
    is_comp = np.zeros(x, dtype=bool)
    is_comp[:2] = True
    for i in range(2, int(x ** 0.5) + 1):
        if not is_comp[i]:
            is_comp[i * i:x:i] = True
    return np.nonzero(~is_comp)[0]


def H_Z_exact(Z):
    primes = sieve_primes_below(Z)
    # sum 1/p in float64 is enough for a sanity comparison at these sizes
    return mp.mpf(float(np.sum(1.0 / primes.astype(np.float64))))


def H_Z_mertens(Z):
    return mp.log(mp.log(Z)) + M_MERTENS


def retuned_m(H_Z, l, c=1, kappa=mp.mpf('0.5')):
    # exponent(m) = (m+1)*log((m+1)/(e*H_Z)) is decreasing then increasing
    # in m, with its minimum where m+1 = H_Z. Bisecting naively over m
    # starting near 0 is invalid there (non-monotonic); start the search
    # strictly past the minimum, where it is monotonic increasing.
    target = c * l ** kappa

    def exponent(m):
        return (m + 1) * mp.log((m + 1) / (mp.e * H_Z))

    lo = int(mp.ceil(H_Z))  # exponent(lo) could still be negative; that's fine, it's the increasing branch
    hi = max(lo + 1, 4)
    while exponent(hi) < target:
        hi *= 2
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if exponent(mid) >= target:
            hi = mid
        else:
            lo = mid
    m = hi
    if m % 2 == 1:
        m += 1
    while exponent(m) < target:
        m += 2
    while exponent(m - 2) >= target:
        m -= 2
    return m


def main():
    rows = [
        (mp.mpf('1e2'), '10^2'),
        (mp.mpf('4e2'), '4x10^2'),
        (mp.mpf('1e4'), '10^4'),
        (mp.mpf('1e6'), '10^6'),
        (mp.mpf('1e10'), '10^10'),
        (mp.mpf('1e20'), '10^20'),
    ]
    print(f"{'l':>10} {'H_Z':>10} {'m_fixed':>12} {'A_fixed':>10} "
          f"{'m_retuned':>14} {'A_retuned':>10} {'A_pred(4/logl)':>16}")
    for l, label in rows:
        sqrt_l = mp.sqrt(l)
        logZ = sqrt_l
        Z = mp.e ** logZ
        if logZ <= 13:
            H_Z = H_Z_exact(Z)
        else:
            H_Z = H_Z_mertens(Z)
        m_fixed = 2 * mp.ceil(sqrt_l)
        A_fixed = m_fixed * logZ / l
        m_ret = retuned_m(H_Z, l)
        A_ret = m_ret * logZ / l
        A_pred = 4 / mp.log(l)
        print(f"{label:>10} {float(H_Z):10.4f} {int(m_fixed):12d} "
              f"{float(A_fixed):10.4f} {int(m_ret):14d} {float(A_ret):10.4f} "
              f"{float(A_pred):16.4f}")

    print()
    print("Crossover search for A_retuned < 1 and < 1/2 (c=1, kappa=1/2):")
    # bisection over l on a log grid, exact H_Z for logZ<=20 i.e. l<=400,
    # Mertens H_Z beyond that.
    def A_ret_of_l(l):
        sqrt_l = mp.sqrt(l)
        logZ = sqrt_l
        Z = mp.e ** logZ
        H_Z = H_Z_exact(Z) if logZ <= 13 else H_Z_mertens(Z)
        m_ret = retuned_m(H_Z, l)
        return m_ret * logZ / l

    def find_crossover(threshold, lo, hi):
        # A_ret_of_l is decreasing in l (empirically); bisect for A==threshold
        for _ in range(60):
            mid = (lo + hi) / 2
            if A_ret_of_l(mid) > threshold:
                lo = mid
            else:
                hi = mid
        return hi

    l1 = find_crossover(1, mp.mpf(1), mp.mpf(2000))
    l_half = find_crossover(mp.mpf('0.5'), mp.mpf(1), mp.mpf('2e5'))
    print(f"A_retuned < 1 first around l = {float(l1):.1f}")
    print(f"A_retuned < 1/2 first around l = {float(l_half):.1f}")

    print()
    print("Sanity: exact vs Mertens H_Z at logZ = 5,7,9,11,13 (matches doc's own table 1)")
    for logZ in [5, 7, 9, 11, 13]:
        Z = mp.e ** logZ
        exact = H_Z_exact(Z)
        mert = H_Z_mertens(Z)
        elem = 1 + logZ
        print(f"  logZ={logZ:2d}  exact={float(exact):.4f}  mertens={float(mert):.4f}  elementary(1+logZ)={elem}")


if __name__ == '__main__':
    main()

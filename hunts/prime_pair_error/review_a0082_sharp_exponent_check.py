import numpy as np
from scipy import integrate

def K_N_scalar(theta, N):
    if theta == 0:
        return complex(N)
    z = np.exp(2j*np.pi*theta)
    return z*(1-z**N)/(1-z)

def I_beta_scalar(theta, beta, N):
    # int_1^N t^(beta-1) e(t theta) dt, using QUADPACK oscillatory weight functions
    if theta == 0:
        val, _ = integrate.quad(lambda t: t**(beta-1), 1, N, limit=400)
        return complex(val)
    w = 2*np.pi*abs(theta)
    f = lambda t: t**(beta-1)
    re, _ = integrate.quad(f, 1, N, weight='cos', wvar=w, limit=2000)
    im_raw, _ = integrate.quad(f, 1, N, weight='sin', wvar=w, limit=2000)
    im = im_raw if theta > 0 else -im_raw
    return complex(re, im)

print("=== Check decay bound (6), independent script (scipy QUADPACK oscillatory) ===")
for N in [10**4, 10**6]:
    ell = np.log(N)
    for kappa in [0.1, 0.3, 1.0]:
        beta = 1 - kappa/np.sqrt(ell)
        worst_ratio = 0.0
        worst_at = None
        for Ntheta in np.linspace(1, 200, 40):
            theta = Ntheta/float(N)
            val = abs(I_beta_scalar(theta, beta, N))
            lhs = val*Ntheta/N**beta
            if lhs > worst_ratio:
                worst_ratio = lhs
                worst_at = Ntheta
        sigma_here = np.log(200)/np.sqrt(ell)
        C = np.exp(kappa*sigma_here)
        print(f"N={N}, kappa={kappa}: max |I_beta|*Ntheta/N^beta = {worst_ratio:.4f} (at Ntheta={worst_at}), bound C={C:.4f}")

print()
print("=== Check flatness in R of int |K_N|^2 |I_beta|^2 dtheta over arc R/(rN) ===")
def arc_integrand(theta, N, beta):
    return (abs(K_N_scalar(theta, N))**2) * (abs(I_beta_scalar(theta, beta, N))**2)

def arc_integral(N, beta, r, R):
    radius = R/(r*N)
    # break at multiples of 1/N since |K_N| oscillates on that scale
    breakpoints = np.linspace(0, radius, max(4, int(4*radius*N)+1))
    total = 0.0
    for i in range(len(breakpoints)-1):
        a, b = breakpoints[i], breakpoints[i+1]
        val, _ = integrate.quad(arc_integrand, a, b, args=(N, beta), limit=100)
        total += val
    return 2*total / N**(2*beta+1)

N = 10**4
for kappa in [0.3, 1.0]:
    ell = np.log(N)
    beta = 1 - kappa/np.sqrt(ell)
    for r in [1,3,7]:
        vals = []
        for R in [5,20,80]:
            vals.append(round(arc_integral(N, beta, r, R), 4))
        print(f"kappa={kappa}, r={r}: R=5,20,80 -> {vals}")

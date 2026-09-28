"""
Independent numerical check for MAJOR_ARC_EXPLICIT.md section 2, item (1) of
MAJOR_ARC_EXPLICIT_REVIEW.md. Written fresh for this review (a-0080); does not
read or import major_arc_explicit_probe.py.

Checks the two derivative-test bounds on I_rho(theta) = int_1^N t^(rho-1) e(t theta) dt,
rho = beta + i*gamma, e(x) = exp(2 pi i x), for rho on the critical line (beta=1/2)
at genuine zeros of zeta(s) from mpmath.zetazero, against:

  far range      (|gamma| >= 4 pi N |theta|, |gamma| >= 1): |I_rho| <=? A_far   * N^beta/|gamma|
  stationary rng (1 <= |gamma| <  4 pi N |theta|):           |I_rho| <=? A_stat * N^beta/sqrt(|gamma|)

Integral evaluated by composite Gauss-Legendre (float64, numpy) with panel
boundaries spaced UNIFORMLY IN PHASE (pi/2 per panel), not uniformly in t:
phi(t) = gamma*log(t) + 2*pi*theta*t is monotone increasing for gamma,theta>=0,
so its inverse is found by a few Newton steps per boundary (vectorized). This
matters: at theta=0 the leading case is exactly solvable (I_rho(0) =
(N^rho-1)/rho), and a naive t-uniform panelling badly aliases the fast
oscillation near t=1, which was caught by cross-checking against that closed
form before trusting the ratios below.
"""
import numpy as np
import mpmath as mp

GL_NODES, GL_WEIGHTS = np.polynomial.legendre.leggauss(16)


def phase(t, gamma, theta):
    return gamma * np.log(t) + 2 * np.pi * theta * t


def phase_deriv(t, gamma, theta):
    return gamma / t + 2 * np.pi * theta


def phase_uniform_edges(gamma, theta, N, step=np.pi / 2):
    p1 = phase(1.0, gamma, theta)
    pN = phase(float(N), gamma, theta)
    total = pN - p1
    npanels = max(4, int(np.ceil(total / step)))
    targets = p1 + (total / npanels) * np.arange(npanels + 1)
    # initial guess: invert the theta=0 part, gamma*log(t) = targets - p1 + gamma*log(1)
    t = np.exp((targets - p1) / max(gamma, 1e-12))
    t = np.clip(t, 1.0, float(N))
    for _ in range(6):
        t = np.clip(t - (phase(t, gamma, theta) - targets) / phase_deriv(t, gamma, theta), 1.0, float(N))
    t[0], t[-1] = 1.0, float(N)
    return t


def I_rho_numeric(beta, gamma, theta, N):
    edges = phase_uniform_edges(gamma, theta, N)
    total = 0.0 + 0.0j
    for k in range(len(edges) - 1):
        a, b = edges[k], edges[k + 1]
        if b <= a:
            continue
        mid = 0.5 * (a + b)
        half = 0.5 * (b - a)
        t = mid + half * GL_NODES
        integrand = t ** (beta - 1) * np.exp(1j * phase(t, gamma, theta))
        total += half * np.sum(GL_WEIGHTS * integrand)
    return total


def run():
    print("Fetching zeta zeros via mpmath.zetazero...")
    zeros = []
    j = 1
    while len(zeros) < 60 and j <= 200:
        z = mp.zetazero(j)
        gamma = float(mp.im(z))
        if gamma <= 163.0:
            zeros.append(gamma)
        j += 1
    print(f"Collected {len(zeros)} zeros, max gamma = {max(zeros):.3f}, min gamma = {min(zeros):.3f}")

    beta = 0.5

    # Sanity check against the closed form at theta = 0: I_rho(0) = (N^rho - 1)/rho
    print("\nSanity check vs exact closed form at theta=0:")
    for N in (1e4, 1e6):
        for gamma in (zeros[0], zeros[29], zeros[-1]):
            numeric = I_rho_numeric(beta, gamma, 0.0, N)
            rho = complex(beta, gamma)
            exact = (N ** rho - 1) / rho
            reldiff = abs(numeric - exact) / abs(exact)
            print(f"  N={N:.0e} gamma={gamma:.3f}: numeric={numeric:.6g} exact={exact:.6g} reldiff={reldiff:.2e}")

    Ns = [1e4, 1e6]
    Nthetas = [0, 1, 10, 100]

    far_ratios = []
    stat_ratios = []
    total_checked = 0

    for N in Ns:
        for Ntheta in Nthetas:
            theta = Ntheta / N
            H0 = 4 * np.pi * Ntheta
            for gamma in zeros:
                if gamma < 1:
                    continue
                total_checked += 1
                val = I_rho_numeric(beta, gamma, theta, N)
                mag = abs(val)
                Nb = N ** beta
                if gamma >= H0 and gamma >= 1:
                    bound = Nb / gamma
                    ratio = mag / bound
                    far_ratios.append((ratio, N, Ntheta, gamma, mag))
                elif 1 <= gamma < H0:
                    bound = Nb / np.sqrt(gamma)
                    ratio = mag / bound
                    stat_ratios.append((ratio, N, Ntheta, gamma, mag))

    print(f"\nTotal integrals evaluated: {total_checked}")

    far_ratios.sort(reverse=True)
    stat_ratios.sort(reverse=True)

    print(f"\nFar-range samples: {len(far_ratios)}")
    print("Top 8 far-range ratios |I_rho| / (N^beta/|gamma|):")
    for r in far_ratios[:8]:
        print(f"  ratio={r[0]:.6f}  N={r[1]:.0e}  Ntheta={r[2]}  gamma={r[3]:.3f}  |I|={r[4]:.4g}")

    print(f"\nStationary-range samples: {len(stat_ratios)}")
    print("Top 8 stationary-range ratios |I_rho| / (N^beta/sqrt|gamma|):")
    for r in stat_ratios[:8]:
        print(f"  ratio={r[0]:.6f}  N={r[1]:.0e}  Ntheta={r[2]}  gamma={r[3]:.3f}  |I|={r[4]:.4g}")

    print(f"\nMax far-range ratio: {far_ratios[0][0]:.6f}" if far_ratios else "no far-range samples")
    print(f"Max stationary-range ratio: {stat_ratios[0][0]:.6f}" if stat_ratios else "no stationary samples")


if __name__ == "__main__":
    run()

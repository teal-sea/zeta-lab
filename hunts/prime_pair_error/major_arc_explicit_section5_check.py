"""
Independent numerical check for MAJOR_ARC_EXPLICIT.md section 5, the size/phase
claims used in the proof of the Proposition:
  |K_N(theta)| >= N/2,  |I_beta(theta)| >= N^beta/4,
  arg(K_N), arg(I_beta) both within pi/8 of pi(N+1)theta,
for |theta| <= 1/(8N), a real beta in (0,1) close to 1 (as for a would-be
Siegel zero), N large. Written fresh for MAJOR_ARC_EXPLICIT_REVIEW.md item (5).
"""
import numpy as np


def K_N(theta, N):
    n = np.arange(1, N + 1)
    return np.sum(np.exp(2j * np.pi * n * theta))


def I_beta(theta, beta, N, npanels=4000):
    # I_beta(theta) = int_1^N t^(beta-1) e(t theta) dt ; theta tiny here (no
    # log-oscillation since gamma=0 for a real zero), plain Simpson is enough.
    t = np.linspace(1.0, N, npanels + 1)
    f = t ** (beta - 1) * np.exp(2j * np.pi * t * theta)
    h = (N - 1.0) / npanels
    w = np.ones(npanels + 1)
    w[1:-1:2] = 4
    w[2:-1:2] = 2
    return h / 3 * np.sum(w * f)


def run():
    print("theta ranges over |theta| <= 1/(8N); beta close to 1 (a would-be real zero)")
    for N in (1000, 20000, 500000):
        for beta in (0.9, 0.99, 0.999):
            for frac in (0.0, 0.5, 1.0, -1.0):
                theta = frac / (8 * N)
                kn = K_N(theta, N)
                ib = I_beta(theta, beta, N)
                target_phase = np.pi * (N + 1) * theta
                phase_kn = np.angle(kn)
                phase_ib = np.angle(ib)

                def wrap(x):
                    return (x + np.pi) % (2 * np.pi) - np.pi

                d_kn = abs(wrap(phase_kn - target_phase))
                d_ib = abs(wrap(phase_ib - target_phase))
                print(f"N={N:>7} beta={beta} theta*8N={frac:+.2f}: "
                      f"|K_N|/N={abs(kn)/N:.4f} (need>=0.5)  "
                      f"|I|/N^beta={abs(ib)/N**beta:.4f} (need>=0.25)  "
                      f"dphase(K_N)={d_kn:.4f}rad  dphase(I)={d_ib:.4f}rad (need<={np.pi/8:.4f})")


if __name__ == "__main__":
    run()

"""Numeric check: blockwise nonnegativity of the Frobenius zero-side expansion.

Model of the paper's Gram matrix: tau_k = k (k = 0..d-1), window transform
phihat(z) entire (raised cosine on [-1/2,1/2]), conjugate-closed multiset of
ordinates gamma with weights m. A_kl = sum_rho m phihat(gamma-tau_k)
phihat(conj(gamma)-tau_l). Claim under test: ||A||_F^2 decomposes over pairs
of conjugate classes (on-line singletons, off-line pairs) with EVERY block
sum nonnegative, even for deep off-line pairs.
"""
import numpy as np

def phihat(z):
    z = np.asarray(z, complex)
    def sc(w):
        w = np.where(np.abs(w) < 1e-9, 1e-9, w)
        return np.sin(w / 2.0) / w
    return sc(z) + 0.5 * (sc(z + 2*np.pi) + sc(z - 2*np.pi))

def gram(classes, d=48):
    """classes: list of ('on', t, m) or ('off', t, depth, m)."""
    tau = np.arange(d, dtype=float)
    pts = []   # (gamma, m)
    for c in classes:
        if c[0] == 'on':
            pts.append((complex(c[1], 0.0), c[2]))
        else:
            pts.append((complex(c[1], c[2]), c[3]))
            pts.append((complex(c[1], -c[2]), c[3]))
    A = np.zeros((d, d), complex)
    for gam, m in pts:
        A += m * np.outer(phihat(gam - tau), phihat(np.conj(gam) - tau))
    return A, pts, tau

def B(z, w, tau):
    return np.sum(phihat(z - tau) * phihat(w - tau))

def block_sums(classes, d=48):
    A, pts, tau = gram(classes, d)
    herm = np.abs(A - A.conj().T).max()
    frob = float(np.sum(np.abs(A) ** 2).real)
    # class list with member ordinates
    cls = []
    for c in classes:
        if c[0] == 'on':
            cls.append([ (complex(c[1], 0.0), c[2]) ])
        else:
            cls.append([ (complex(c[1], c[2]), c[3]), (complex(c[1], -c[2]), c[3]) ])
    blocks = np.zeros((len(cls), len(cls)))
    for i, ci in enumerate(cls):
        for j, cj in enumerate(cls):
            s = 0.0 + 0.0j
            for gi, mi in ci:
                for gj, mj in cj:
                    s += mi * mj * B(np.conj(gi), gj, tau) * B(np.conj(gj), gi, tau)
            blocks[i, j] = s.real  # imag must vanish; checked via total
    return {"hermiticity_defect": herm, "frobenius": frob,
            "block_total": float(blocks.sum()), "min_block": float(blocks.min()),
            "blocks": blocks}

if __name__ == "__main__":
    center = 24.0
    cases = {
        "all on-line": [('on', center + x, 1) for x in (-2.0, -0.7, 0.4, 1.3, 2.6)],
        "mixed shallow": [('on', center - 1.5, 1), ('on', center + 0.8, 2),
                          ('off', center, 0.05, 1), ('off', center + 2.1, 0.12, 1)],
        "deep pair": [('on', center - 1.0, 1), ('off', center + 0.5, 0.40, 1),
                      ('off', center - 2.2, 0.31, 2)],
        "DH-like (beta-1/2 = 0.283, t-spacing real DH)":
            [('on', center - 1.2, 1), ('on', center + 1.7, 1),
             ('off', center + 0.3, 0.283, 1)],
    }
    for name, cl in cases.items():
        r = block_sums(cl)
        ok = abs(r["frobenius"] - r["block_total"]) / max(r["frobenius"], 1e-30)
        print(f"{name:48s} herm={r['hermiticity_defect']:.2e} "
              f"frob-vs-blocks rel={ok:.2e} min block={r['min_block']:+.6e}")


def adversarial_scan(trials: int = 400, seed: int = 7, d: int = 48):
    """Search for a negative cross-block over random mixed configurations.

    Returns the minimum off-diagonal block found. The claim under test is
    that it is never negative; a single negative value refutes the blockwise
    lemma and with it the transplant chain in cg_transplant.py.
    """
    rng = np.random.default_rng(seed)
    center = 24.0
    worst = (np.inf, None)
    for trial in range(trials):
        kind = trial % 4
        sep = rng.uniform(0.05, 4.0)
        d1 = rng.uniform(0.0, 0.49)
        d2 = rng.uniform(0.0, 0.49)
        if kind == 0:
            cl = [('on', center, 1), ('off', center + sep, d1, 1)]
        elif kind == 1:
            cl = [('off', center, d1, 1), ('off', center + sep, d2, 1)]
        elif kind == 2:
            cl = [('on', center, 2), ('off', center + sep, d1, 3)]
        else:
            cl = [('off', center, d1, 2), ('off', center + sep, d2, 2)]
        r = block_sums(cl, d=d)
        off = r["blocks"].copy()
        np.fill_diagonal(off, np.inf)
        mo = float(off.min())
        if mo < worst[0]:
            worst = (mo, (kind, round(sep, 3), round(d1, 3), round(d2, 3)))
    return worst

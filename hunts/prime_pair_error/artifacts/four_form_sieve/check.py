"""Fixed N=32 algebra check. One thread, 30 seconds, no asymptotic experiment."""

from fractions import Fraction as F
import hashlib
import importlib.util
import json
import math
from pathlib import Path
import signal
import time

N = 32
HERE = Path(__file__).resolve().parent
HUNT = HERE.parent.parent
HELPERS = HERE.parent / "siegel_uniformity" / "check.py"
spec = importlib.util.spec_from_file_location("helpers", HELPERS)
parent = importlib.util.module_from_spec(spec)
spec.loader.exec_module(parent)  # One-thread settings, no prior diagnostic run.


def timeout(_sig, _frame):
    raise TimeoutError("Fixed 30-second limit exceeded")


def main():
    from mpmath import mp
    with mp.workdps(50):
        local = []
        for p in (2, 3, 5, 7, 11):
            good = sum(all(x % p for x in (n, n + h, m, m + h))
                       for h in range(p) for n in range(p) for m in range(p))
            assert good == p**3 - 4*p*p + 6*p - 3
            factor = F(good, p**3) / (1 - F(1, p))**4
            assert factor == 1 + F(1, (p - 1)**3)
            if p > 2:
                c2 = 1 - F(1, (p - 1)**2)
                u, v = F(1, p - 2), F(2*p - 3, (p - 2)**2)
                assert c2 * (1 + u / (p - 1)) == factor
                assert c2**2 * (1 + v / p) == factor
            local.append({"prime": p, "good_residues": good, "factor": str(factor)})

        tuples = [(h, n, m) for h in range(1, N + 1)
                  for n in range(1, N - h + 1) for m in range(1, N - h + 1)]
        assert len(tuples) == N*(N-1)*(2*N-1)//6
        crt_rows = []
        for d in (2, 3, 6):
            g = math.prod(F(4, p)-F(6, p*p)+F(3, p**3)
                          for p in parent.factors(d))
            count = sum(n*(n+h)*m*(m+h) % d == 0 for h, n, m in tuples)
            defect = abs(F(count) - F(N**3, 3)*g)
            scale = N*N*4**len(parent.factors(d))
            assert defect <= 16*scale
            crt_rows.append({"divisor": d, "count": count,
                             "remainder_over_scale": str(defect / scale)})

        lam, powers = [mp.mpf(0)], []
        for n in range(1, N + 1):
            fs = parent.factors(n)
            if len(fs) == 1:
                p, k = next(iter(fs.items()))
                lam.append(mp.log(p))
                if k > 1:
                    powers.append(n)
            else:
                lam.append(mp.mpf(0))
        assert powers == [4, 8, 9, 16, 25, 27, 32]
        pair = [mp.fsum(lam[n]*lam[n+h] for n in range(1, N-h+1))
                for h in range(1, N+1)]
        Q = mp.fsum(x*x for x in pair)
        Q_direct = mp.fsum(lam[n]*lam[n+h]*lam[m]*lam[m+h]
                           for h, n, m in tuples)
        assert abs(Q-Q_direct) < mp.mpf("1e-38")

        ps = [p for p in range(3, N+1) if parent.factors(p) == {p: 1}]
        C2 = math.prod(1-F(1, (p-1)**2) for p in ps)
        numeric = lambda r: mp.mpf(r.numerator)/r.denominator
        pred = []
        for h in range(1, N+1):
            series = F(0) if h % 2 else 2*C2*math.prod(
                F(p-1, p-2) for p in parent.factors(h) if p > 2
            )
            pred.append((N-h)*numeric(series))
        B, I = mp.fsum(t*t for t in pred), mp.fsum(x*t for x, t in zip(pair, pred))
        B_expanded, I_lower = mp.mpf(0), mp.mpf(0)
        for d in range(1, N+1, 2):
            if not parent.mobius(d):
                continue
            u = math.prod(F(1, p-2) for p in parent.factors(d))
            v = math.prod(F(2*p-3, (p-2)**2) for p in parent.factors(d))
            B_expanded += 4*numeric(C2**2*v)*sum(
                (N-h)**2 for h in range(2*d, N+1, 2*d))
            if d <= 7:
                I_lower += 2*numeric(C2*u)*mp.fsum(
                    (N-h)*pair[h-1] for h in range(2*d, N+1, 2*d))
        assert abs(B-B_expanded) < mp.mpf("1e-38")
        assert I_lower <= I

        # Exact q=3 correction formula; beta is a toy, no zero is asserted.
        Z = mp.exp(mp.log(N)**mp.mpf("0.1"))
        assert 3 < Z < 4
        chi, beta = parent.legendre(3), mp.mpf("0.99")
        correction = []
        for h in range(1, N+1):
            T = N-h
            if T == 0 or h % 2:
                correction.append(mp.mpf(0))
                continue
            j1 = 1+(mp.power(T, beta)-1)/beta
            j2 = (mp.power(N, beta)-mp.power(h, beta))/beta
            j12 = mp.quad(lambda t: mp.power(max(1, t), beta-1)
                          * mp.power(t+h, beta-1), [0, 1, T] if T > 1 else [0, 1])
            correction.append(mp.mpf(9)/2 * (
                mp.mpf(chi(-h))/3*j1 + mp.mpf(chi(h))/3*j2
                + mp.mpf(parent.ramanujan(3, h))/3*j12))
        U = mp.fsum(c*(x-t) for c, x, t in zip(correction, pair, pred))
        V = mp.fsum(c*c for c in correction)
        direct = 2*mp.fsum((x-t-c)**2 for x, t, c in zip(pair, pred, correction))
        expanded = 2*Q-4*I+2*B-4*U+2*V
        defect = abs(direct-expanded)
        assert defect < mp.mpf("1e-38")
        assert abs(U) <= (mp.sqrt(Q)+mp.sqrt(B))*mp.sqrt(V)
        return {
            "status": "PASS", "N": N, "numerical_threads": 1, "time_cap_seconds": 30,
            "scope": "finite algebra; prediction uses finite C2, not original E_corr",
            "local_factors": local, "sharp_region_size": len(tuples),
            "crt_checks": crt_rows, "proper_prime_powers": powers,
            "four_form_identity_defect": str(abs(Q-Q_direct)),
            "centered_expansion_defect": str(defect), "toy_conductor": 3,
            "toy_beta": str(beta), "Q": str(Q), "I": str(I), "B": str(B),
        }


if __name__ == "__main__":
    signal.signal(signal.SIGALRM, timeout)
    signal.alarm(30)
    started = time.monotonic()
    result = main()
    result["elapsed_seconds"] = round(time.monotonic()-started, 6)
    result["sha256"] = {
        str(path.relative_to(HUNT)): hashlib.sha256(path.read_bytes()).hexdigest()
        for path in (Path(__file__).resolve(), HUNT/"FOUR_FORM_SIEVE_ATTEMPT.md")
    }
    (HERE/"result.json").write_text(json.dumps(result, indent=2)+"\n")
    signal.alarm(0)
    print(json.dumps(result, indent=2))

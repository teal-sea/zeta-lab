from typing import Any, Callable, Sequence
import numpy as np
from mpmath import mp
from zeta.detector import bump_pair, DEFAULT_WIDTH, DEFAULT_N_MAX

def generalized_arithmetic_side(
    c: float,
    b: Sequence[float],
    archimedean_bracket_fn: Callable[[Any], Any],
    has_pole: bool = False,
    a: float = DEFAULT_WIDTH,
    n_max: int = DEFAULT_N_MAX,
) -> Any:
    h, g = bump_pair(c, a)
    lo = max(mp.mpf(0), mp.mpf(c) - 25)
    arch = mp.quad(
        lambda r: h(r) * archimedean_bracket_fn(r), [lo, mp.mpf(c), mp.mpf(c) + 25]
    ) / mp.pi

    prime = -2 * mp.fsum(
        mp.mpf(b[n]) / mp.sqrt(n) * g(mp.log(n))
        for n in range(2, min(n_max, len(b) - 1) + 1)
        if b[n] != 0
    )
    
    pole = (
        h(mp.mpc(0, mp.mpf(1) / 2)) + h(mp.mpc(0, -mp.mpf(1) / 2))
        if has_pole
        else mp.mpf(0)
    )
    return mp.re(arch + pole + prime)

def generalized_online_zero_side(c: float, online_zeros: Sequence[float], a: float = DEFAULT_WIDTH) -> Any:
    h, _ = bump_pair(c, a)
    return mp.re(mp.fsum(h(z) + h(-z) for z in online_zeros))

def generalized_offline_residue(
    c: float,
    b: Sequence[float],
    archimedean_bracket_fn: Callable[[Any], Any],
    online_zeros: Sequence[float],
    has_pole: bool = False,
    a: float = DEFAULT_WIDTH,
    n_max: int = DEFAULT_N_MAX,
) -> dict[str, Any]:
    arith = generalized_arithmetic_side(c, b, archimedean_bracket_fn, has_pole, a, n_max)
    zsum = generalized_online_zero_side(c, online_zeros, a)
    return {
        "c": float(c),
        "arithmetic": float(arith),
        "online_zeros": float(zsum),
        "residue": float(arith - zsum),
    }

def generalized_residue_scan(
    c_values: Sequence[float],
    b: Sequence[float],
    archimedean_bracket_fn: Callable[[Any], Any],
    online_zeros: Sequence[float],
    has_pole: bool = False,
    a: float = DEFAULT_WIDTH,
    n_max: int = DEFAULT_N_MAX,
) -> dict[str, Any]:
    rows = [generalized_offline_residue(c, b, archimedean_bracket_fn, online_zeros, has_pole, a, n_max) for c in c_values]
    res = np.array([r["residue"] for r in rows])
    i = int(np.argmax(np.abs(res)))
    return {
        "c_values": [float(x) for x in c_values],
        "residues": res.tolist(),
        "max_abs_residue": float(np.abs(res).max()),
        "argmax_c": float(rows[i]["c"]),
    }

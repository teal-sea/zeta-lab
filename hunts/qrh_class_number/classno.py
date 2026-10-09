"""Class numbers of imaginary quadratic fields: reference code and the C driver.

`reference_h` counts reduced forms by brute force (no shortcuts) and is the
independent check on `cn.c`.  `pari_h` calls PARI's `qfbclassno` through
cypari2 as a second, unrelated implementation.  Neither assumes GRH for the
ranges where they are used here (reduced-form counting is exact; PARI is used
only for |D| below 10^7 as a cross-check, never as the search engine).
"""

from __future__ import annotations

import hashlib
import math
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
BUILD = HERE / 'build'
SRC = HERE / 'cn.c'
BIN = BUILD / 'cn'


def is_fundamental_negative(n: int) -> bool:
    """True iff D = -n is a fundamental discriminant (n > 0)."""
    if n <= 0:
        return False

    def squarefree(m: int) -> bool:
        k = 2
        while k * k <= m:
            if m % (k * k) == 0:
                return False
            k += 1
        return True

    if n % 4 == 3:
        return squarefree(n)
    if n % 16 in (4, 8):
        return squarefree(n // 4)
    return False


def reference_h(n: int) -> int:
    """Number of reduced primitive forms of discriminant -n (brute force)."""
    D = -n
    h = 0
    a = 1
    while 3 * a * a <= n:
        for b in range(-a + 1, a + 1):
            if (b * b - D) % (4 * a):
                continue
            c = (b * b - D) // (4 * a)
            if c < a:
                continue
            if (b < 0) and (c == a):
                continue
            if math.gcd(math.gcd(a, abs(b)), c) != 1:
                continue
            h += 1
        a += 1
    return h


_PARI = None


def pari_h(n: int) -> int:
    global _PARI
    if _PARI is None:
        import cypari2
        _PARI = cypari2.Pari()
    return int(_PARI.qfbclassno(-n))


def build(force: bool = False) -> Path:
    BUILD.mkdir(exist_ok=True)
    if force or not BIN.exists() or BIN.stat().st_mtime < SRC.stat().st_mtime:
        subprocess.run(['gcc', '-O3', '-march=native', '-Wall', '-o', str(BIN),
                        str(SRC), '-lm'], check=True)
    return BIN


def run(lo: int, hi: int, H: int, out: Path, seg: int | None = None) -> dict:
    """Run cn.c on [lo, hi] and parse its output."""
    build()
    cmd = [str(BIN), str(lo), str(hi), str(H), str(out)]
    if seg:
        cmd.append(str(seg))
    subprocess.run(cmd, check=True)
    return parse(out)


def parse(path: Path) -> dict:
    rows = []
    stats = {}
    for line in Path(path).read_text().splitlines():
        if line.startswith('# stats'):
            for tok in line.split()[2:]:
                k, v = tok.split('=')
                stats[k] = int(v)
            continue
        n, h = line.split()
        rows.append((int(n), int(h)))
    if not stats:
        raise RuntimeError(f'{path}: no stats line, run incomplete')
    return {'rows': rows, 'stats': stats}


def digest(rows) -> str:
    """sha256 of the sorted 'n h' list, the identity of a run's output."""
    text = ''.join(f'{n} {h}\n' for n, h in sorted(rows))
    return hashlib.sha256(text.encode()).hexdigest()

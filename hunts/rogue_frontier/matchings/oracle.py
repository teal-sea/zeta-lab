"""Independent enumeration oracle for the perfect-matching count.

Target lemma: the number of fixed-point-free involutions of a set of size
2m (equivalently, partitions of that set into m blocks of size 2) is the
double factorial (2m-1)!!.

Three routes, deliberately independent: literal enumeration over all
permutations, the partner-of-the-first-element recursion, and the closed
form (2m)!/(2^m m!).  This is the oracle the Lean development is checked
against.
"""

from itertools import permutations
from math import factorial


def double_factorial_odd(m: int) -> int:
    """(2m-1)!! as (2m)!/(2^m m!)."""
    return factorial(2 * m) // (2 ** m * factorial(m))


def brute_force_ffi(n: int) -> int:
    """Fixed-point-free involutions of {0..n-1}, by literal enumeration."""
    count = 0
    for p in permutations(range(n)):
        if all(p[p[i]] == i for i in range(n)) and all(p[i] != i for i in range(n)):
            count += 1
    return count


def recursive_pairings(elems: tuple) -> int:
    """The same count by the partner-of-the-first-element recursion."""
    if not elems:
        return 1
    rest = elems[1:]
    return sum(recursive_pairings(rest[:i] + rest[i + 1:]) for i in range(len(rest)))


if __name__ == "__main__":
    print(" n   brute force   recursion    (n/2-1)!!")
    ok = True
    for n in range(0, 11):
        bf = brute_force_ffi(n)
        rec = recursive_pairings(tuple(range(n)))
        formula = double_factorial_odd(n // 2) if n % 2 == 0 else 0
        agree = bf == rec == formula
        ok &= agree
        print(f"{n:2d}  {bf:11d}  {rec:10d}  {formula:11d}   {'OK' if agree else 'MISMATCH'}")
    print("\nall three routes agree:", ok)

"""Exact checks of claims in the preserved, unaccepted research response."""
def strong_pass(n, a):
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    x = pow(a, d, n)
    if x in (1, n - 1):
        return True
    for _ in range(s - 1):
        x = x * x % n
        if x == n - 1:
            return True
    return False

if __name__ == '__main__':
    n = 3317044064679887385961981
    assert all(strong_pass(n, p) for p in (2, 3, 5, 7, 11, 13, 17, 19))
    assert all(strong_pass(n, a) for a in range(2, 22))
    assert not strong_pass(n, 22)
    assert (3 - 1) * (3 - 2) // 2 == 1
    assert (5 - 1) * (5 - 2) // 2 == 6
    assert 3 * 6**3 == 648 and 5 * 10**5 == 500000
    print('Exact witness-cutoff and parameter checks passed; no algorithmic improvement established.')

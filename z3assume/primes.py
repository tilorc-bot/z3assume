"""Primality of an integer literal, by a proven deterministic test."""

# Miller-Rabin with the first 13 primes as bases is deterministic below
# 3317044064679887385961981 (Sorenson and Webster, 2015).
_BASES = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41)
_BOUND = 3317044064679887385961981


def is_prime(n: int):
    """True or False for ``n`` below the bound, None above it."""
    if n < 2:
        return False
    for p in _BASES:
        if n % p == 0:
            return n == p
    if n >= _BOUND:
        return None
    d, s = n - 1, 0
    while d % 2 == 0:
        d, s = d // 2, s + 1
    for a in _BASES:
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True

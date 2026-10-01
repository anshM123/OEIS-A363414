"""Exact checks for OEIS A363414: a(n) = Im(prod_{k=0..n} (1 + 2k i)) / 2.

For every odd prime p < 20000: prod_{k<p} (1 + 2k i) is congruent mod p to the rational integer
1 - (-1)^((p-1)/2) (so its imaginary part is divisible by p). For odd primes p < 400 the
divisibility p | a(p-1) is also checked with exact Gaussian integers. a(3) = -18 covers p = 2.

Usage: python verify.py
"""


def is_prime(n):
    if n < 2:
        return False
    i = 2
    while i * i <= n:
        if n % i == 0:
            return False
        i += 1
    return True


def gauss_prod_mod(n, p):
    """prod_{k=0..n} (1 + 2k i) mod p, as a pair (re, im)."""
    x, y = 1, 0
    for k in range(n + 1):
        c = (2 * k) % p
        x, y = (x - y * c) % p, (x * c + y) % p
    return x, y


def a_exact(n):
    x, y = 1, 0
    for k in range(n + 1):
        x, y = x - y * 2 * k, x * 2 * k + y
    assert y % 2 == 0
    return y // 2


ok = a_exact(3) == -18
for p in range(3, 20000):
    if is_prime(p):
        re, im = gauss_prod_mod(p - 1, p)
        ok &= im == 0 and re == (1 - (-1) ** ((p - 1) // 2)) % p
for p in range(3, 400):
    if is_prime(p):
        ok &= a_exact(p - 1) % p == 0
print("a(3) = -18; identity mod p for odd p < 20000; p | a(p-1) exactly for odd p < 400:", "OK" if ok else "FAILED")

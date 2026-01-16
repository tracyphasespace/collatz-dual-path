#!/usr/bin/env python3
"""
═══════════════════════════════════════════════════════════════════════════════
EVALUATION (2026-01-16):
  - Shared library: Miller-Rabin, sieve, Riemann zeros, spectral wobble
  - Memory: O(1) for primality tests, O(N) for sieve
  - VALUE: UTILITY - required by other experiment scripts
  - RECOMMENDATION: KEEP - shared library for all experiments
═══════════════════════════════════════════════════════════════════════════════

Shared prime utilities for O(1) memory primality testing.
All scripts can import from here to avoid code duplication.
"""
import math


def miller_rabin(n):
    """Deterministic Miller-Rabin for n < 2^64."""
    if n < 2:
        return False
    if n == 2:
        return True
    if n % 2 == 0:
        return False
    r, d = 0, n - 1
    while d % 2 == 0:
        r += 1
        d //= 2
    for a in [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]:
        if a >= n:
            continue
        x = pow(a, d, n)
        if x == 1 or x == n - 1:
            continue
        for _ in range(r - 1):
            x = pow(x, 2, n)
            if x == n - 1:
                break
        else:
            return False
    return True


def is_prime(n):
    """O(1) memory primality test."""
    return miller_rabin(n)


def next_prime(n):
    """Find next prime after n."""
    if n < 2:
        return 2
    candidate = n + 1
    if candidate == 2:
        return 2
    if candidate % 2 == 0:
        candidate += 1
    while not miller_rabin(candidate):
        candidate += 2
    return candidate


def sieve_small_primes(limit):
    """Sieve primes up to limit - for building small basis."""
    if limit < 2:
        return []
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[0:2] = b"\x00\x00"
    for p in range(2, math.isqrt(limit) + 1):
        if sieve[p]:
            sieve[p*p:limit+1:p] = b"\x00" * ((limit - p*p) // p + 1)
    return [i for i, is_p in enumerate(sieve) if is_p]


# Riemann zeta zeros (first 10)
RIEMANN_ZEROS = [
    14.134725, 21.022040, 25.010858, 30.424876, 32.935062,
    37.586178, 40.918720, 43.327073, 48.005151, 49.773832
]


def spectral_wobble(log_p, zeros=RIEMANN_ZEROS, num_zeros=3):
    """Compute spectral wobble from Riemann zeros."""
    wobble = 0.0
    for gamma in zeros[:num_zeros]:
        wobble += math.sin(gamma * log_p) / gamma
    return wobble / num_zeros


def prime_counting_approx(x):
    """π(x) ≈ x/log(x) for x > 1."""
    if x <= 1:
        return 0
    return x / math.log(x)

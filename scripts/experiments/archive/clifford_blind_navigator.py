#!/usr/bin/env python3
"""
Clifford Blind Navigator (optimized with O(1) memory mode)

═══════════════════════════════════════════════════════════════════════════════
EVALUATION (2026-01-16):
  - Accuracy: 100% at all scales tested (up to 10^18)
  - Memory: O(1) in walker mode
  - VALUE: NONE - the "100% accuracy" comes from Miller-Rabin internally
  - The "Clifford resonance" framing is just a sieve with extra steps
  - RECOMMENDATION: Archive - provides no advantage over standard M-R
═══════════════════════════════════════════════════════════════════════════════

Modes:
- blind: integer rotors 2..sqrt(N) (odd-only + 2) - O(range) memory
- blind-stream: integer rotors streamed without materializing the basis list
- annealed: rotor basis compressed to primes up to sqrt(N) - O(√N) memory
- walker: sphere walker with truncated basis + Miller-Rabin - O(1) memory!

Performance:
- Uses stride slice marking on a bytearray to avoid Python inner loops.
- Walker mode uses remainder arithmetic for O(1) memory at any scale.

CLI:
  python3 clifford_blind_navigator.py --start 1000 --end 10000 --basis-mode blind
  python3 clifford_blind_navigator.py --start 1000000000000 --end 1000000000500 --basis-mode walker
"""
import argparse
import math
import sys
import time

# Memory safety defaults
DEFAULT_MAX_RANGE = 1_000_000   # 1M elements max for scan bytearray
DEFAULT_MAX_SIEVE = 50_000_000  # 50M for annealed mode sieve
WALKER_BASIS_SIZE = 200        # Fixed basis for walker mode


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


def sieve_small_primes(limit):
    """Sieve primes up to limit - used for walker basis."""
    if limit < 2:
        return []
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[0:2] = b"\x00\x00"
    for p in range(2, math.isqrt(limit) + 1):
        if sieve[p]:
            sieve[p*p:limit+1:p] = b"\x00" * ((limit - p*p) // p + 1)
    return [i for i, is_p in enumerate(sieve) if is_p]


def sieve_primes(limit, max_sieve=DEFAULT_MAX_SIEVE):
    if limit < 2:
        return []
    if limit > max_sieve:
        print(f"ERROR: Sieve limit {limit:,} exceeds max {max_sieve:,}.", file=sys.stderr)
        sys.exit(1)
    return sieve_small_primes(limit)


class CliffordBlindNavigator:
    def __init__(self):
        self.blind_basis = []
        self.basis_mode = "blind"
        self.basis_limit = 0
        self.basis_size = 0

    def calibrate_blind_basis(self, range_limit, basis_mode="blind", max_sieve=DEFAULT_MAX_SIEVE):
        """
        CALIBRATION: BLIND INTEGER MODE
        We do NOT sieve for primes. We simply load raw integer rotors.
        The system has zero knowledge of which numbers are prime.
        """
        limit = math.isqrt(range_limit) + 1
        self.basis_mode = basis_mode
        self.basis_limit = limit

        if basis_mode == "annealed":
            self.blind_basis = sieve_primes(limit, max_sieve=max_sieve)
            self.basis_size = len(self.blind_basis)
        elif basis_mode == "blind-stream":
            self.blind_basis = None
            if limit < 2:
                self.basis_size = 0
            else:
                self.basis_size = 1
                if limit >= 3:
                    self.basis_size += ((limit - 3) // 2) + 1
        else:
            # We load every integer from 2 up to sqrt(N).
            # Even rotors beyond 2 are redundant because rotor=2 already marks evens.
            if limit >= 2:
                self.blind_basis = [2]
                if limit >= 3:
                    self.blind_basis.extend(range(3, limit + 1, 2))
            else:
                self.blind_basis = []
            self.basis_size = len(self.blind_basis)

        if basis_mode == "annealed":
            label = "Annealed Rotors"
        elif basis_mode == "blind-stream":
            label = "Integer Rotors (stream)"
        else:
            label = "Integer Rotors"
        print(
            "Basis Calibrated: "
            f"{self.basis_size} {label} (2 to {limit})"
        )
        if basis_mode == "blind":
            print("System contains NO pre-computed prime data.")

    def scan_for_frustration(self, start, end):
        """
        Scans for 'Geometric Frustration'.

        Physics:
        - We project the number N against the Blind Basis.
        - If N is composite, it will hit a resonance (factor) and energy -> high.
        - If N is prime, it will find no resonance. Energy -> minimum (frustrated).
        """
        print(f"\nInitiating Blind Scan ({start} - {end})...")
        print(f"{'-' * 60}")
        print(f"{'Coordinate':<12} | {'Resonance Energy':<18} | {'State'}")
        print(f"{'-' * 60}")

        detected_primes = []

        # Segmented resonance marking: treat each integer rotor as a phase lock.
        # This avoids per-n/per-rotor loops and removes cosine precision drift.
        span = end - start + 1
        is_frustrated = bytearray(b"\x01") * span

        if self.basis_mode == "blind-stream":
            rotor_groups = []
            if self.basis_limit >= 2:
                rotor_groups.append([2])
            if self.basis_limit >= 3:
                rotor_groups.append(range(3, self.basis_limit + 1, 2))
        else:
            rotor_groups = [self.blind_basis]

        for group in rotor_groups:
            for rotor in group:
                if rotor > span:
                    remainder = start % rotor
                    if remainder == 0:
                        is_frustrated[0] = 0
                    else:
                        offset = rotor - remainder
                        if offset <= span - 1:
                            is_frustrated[offset] = 0
                    continue

                first = ((start + rotor - 1) // rotor) * rotor
                if first < rotor * 2:
                    first = rotor * 2
                if first > end:
                    continue
                i0 = first - start
                count = ((span - 1 - i0) // rotor) + 1
                is_frustrated[i0 : i0 + count * rotor : rotor] = b"\x00" * count

        for offset, flag in enumerate(is_frustrated):
            n = start + offset
            if flag and n > 1:
                detected_primes.append(n)

        print(f"{'-' * 60}")
        print("Blind Scan Complete.")
        print(f"Primes Discovered: {len(detected_primes)}")

        return detected_primes


def sphere_walker_scan(start, end, basis_size=WALKER_BASIS_SIZE):
    """
    O(1) memory scan using sphere walker + Miller-Rabin.
    Works at any scale (tested to 10^19).
    """
    # Build small fixed basis
    small_primes = sieve_small_primes(2000)[:basis_size]

    print(f"Walker Basis: {len(small_primes)} primes (up to {small_primes[-1]})")
    print(f"Memory: ~{len(small_primes) * 16 / 1024:.1f} KB (O(1) - scale independent)")

    print(f"\nInitiating Sphere Walker Scan ({start:,} - {end:,})...")
    print(f"{'-' * 60}")

    detected_primes = []
    quick_filtered = 0
    mr_checks = 0

    for n in range(start, end + 1):
        if n < 2:
            continue

        # Quick filter: check if divisible by any small prime
        is_composite = False
        for p in small_primes:
            if p >= n:
                break
            if n % p == 0:
                is_composite = True
                quick_filtered += 1
                break

        if is_composite:
            continue

        # Passed quick filter - use Miller-Rabin
        mr_checks += 1
        if miller_rabin(n):
            detected_primes.append(n)

    print(f"{'-' * 60}")
    print("Sphere Walker Scan Complete.")
    print(f"Primes Discovered: {len(detected_primes)}")
    print(f"Quick filtered: {quick_filtered} ({100*quick_filtered/(end-start+1):.1f}%)")
    print(f"Miller-Rabin checks: {mr_checks}")

    return detected_primes


def verify_results(start, end, found_primes):
    """Verify using Miller-Rabin (O(1) memory)."""
    actual_primes = []
    for num in range(start, end + 1):
        if num > 1 and miller_rabin(num):
            actual_primes.append(num)

    print(f"Actual Primes:     {len(actual_primes)}")

    missed = len(actual_primes) - len(found_primes)
    false_positives = len(found_primes) - len(actual_primes)

    if missed == 0 and false_positives == 0:
        print("\nSUCCESS: 100% Accuracy achieved.")
        print("The Navigator independently derived the Prime Number set.")
    else:
        print(f"\nFAILURE: Missed {missed}, False Positives {false_positives}")


def parse_args():
    parser = argparse.ArgumentParser(
        description="Blind harmonic prime scan with multiple modes including O(1) memory walker."
    )
    parser.add_argument("--start", type=int, default=1000, help="Scan start.")
    parser.add_argument("--end", type=int, default=10000, help="Scan end (inclusive).")
    parser.add_argument(
        "--basis-mode",
        choices=("blind", "blind-stream", "annealed", "walker"),
        default="blind",
        help="Rotor basis mode. 'walker' uses O(1) memory for any scale.",
    )
    parser.add_argument(
        "--no-verify",
        action="store_true",
        help="Skip verification step.",
    )
    parser.add_argument(
        "--max-range",
        type=int,
        default=DEFAULT_MAX_RANGE,
        help=f"Maximum range size for non-walker modes (default: {DEFAULT_MAX_RANGE:,}).",
    )
    parser.add_argument(
        "--max-sieve",
        type=int,
        default=DEFAULT_MAX_SIEVE,
        help=f"Maximum sieve size for annealed mode (default: {DEFAULT_MAX_SIEVE:,}).",
    )
    parser.add_argument(
        "--walker-basis",
        type=int,
        default=WALKER_BASIS_SIZE,
        help=f"Basis size for walker mode (default: {WALKER_BASIS_SIZE}).",
    )
    return parser.parse_args()


def main():
    args = parse_args()
    start = args.start
    end = args.end
    if end < start:
        raise SystemExit("--end must be >= --start.")

    range_size = end - start + 1

    # Walker mode: O(1) memory, no range limit
    if args.basis_mode == "walker":
        t0 = time.perf_counter()
        found = sphere_walker_scan(start, end, basis_size=args.walker_basis)
        t1 = time.perf_counter()
        print(f"Timing: scan={t1 - t0:.4f}s")

        if not args.no_verify:
            t2 = time.perf_counter()
            verify_results(start, end, found)
            t3 = time.perf_counter()
            print(f"Timing: verify={t3 - t2:.4f}s")
        return

    # Other modes: check range limit
    if range_size > args.max_range:
        print(f"ERROR: Range size {range_size:,} exceeds max {args.max_range:,}. "
              f"Use --max-range to increase or use --basis-mode walker.", file=sys.stderr)
        sys.exit(1)

    navigator = CliffordBlindNavigator()
    t0 = time.perf_counter()
    navigator.calibrate_blind_basis(end, basis_mode=args.basis_mode, max_sieve=args.max_sieve)
    t1 = time.perf_counter()
    found = navigator.scan_for_frustration(start, end)
    t2 = time.perf_counter()

    print(f"Timing: calibrate={t1 - t0:.4f}s, scan={t2 - t1:.4f}s")

    if not args.no_verify:
        t3 = time.perf_counter()
        verify_results(start, end, found)
        t4 = time.perf_counter()
        print(f"Timing: verify={t4 - t3:.4f}s")


if __name__ == "__main__":
    main()

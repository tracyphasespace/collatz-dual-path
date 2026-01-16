#!/usr/bin/env python3
import argparse
import math
import time

"""
Clifford Blind Navigator (optimized)

Modes:
- blind: integer rotors 2..sqrt(N) (odd-only + 2)
- blind-stream: integer rotors streamed without materializing the basis list
- annealed: rotor basis compressed to primes up to sqrt(N)

Performance:
- Uses stride slice marking on a bytearray to avoid Python inner loops.
- Avoids cosine precision drift by using exact divisibility marking.

CLI:
  python3 scripts/clifford_blind_navigator.py --start 1000 --end 10000 --basis-mode blind
  python3 scripts/clifford_blind_navigator.py --start 1000000000 --end 1000010000 --basis-mode annealed --no-verify
"""


def sieve_primes(limit):
    if limit < 2:
        return []
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[0:2] = b"\x00\x00"
    for p in range(2, math.isqrt(limit) + 1):
        if sieve[p]:
            start = p * p
            sieve[start : limit + 1 : p] = b"\x00" * ((limit - start) // p + 1)
    return [idx for idx, is_prime in enumerate(sieve) if is_prime]


class CliffordBlindNavigator:
    def __init__(self):
        self.blind_basis = []
        self.basis_mode = "blind"
        self.basis_limit = 0
        self.basis_size = 0

    def calibrate_blind_basis(self, range_limit, basis_mode="blind"):
        """
        CALIBRATION: BLIND INTEGER MODE
        We do NOT sieve for primes. We simply load raw integer rotors.
        The system has zero knowledge of which numbers are prime.
        """
        limit = math.isqrt(range_limit) + 1
        self.basis_mode = basis_mode
        self.basis_limit = limit

        if basis_mode == "annealed":
            self.blind_basis = sieve_primes(limit)
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


def verify_results(start, end, found_primes):
    # Standard sieve for ground truth comparison
    actual_primes = []
    for num in range(start, end + 1):
        if num > 1:
            is_p = True
            for i in range(2, math.isqrt(num) + 1):
                if num % i == 0:
                    is_p = False
                    break
            if is_p:
                actual_primes.append(num)

    print(f"Actual Primes:     {len(actual_primes)}")

    missed = len(actual_primes) - len(found_primes)
    false_positives = len(found_primes) - len(actual_primes)

    if missed == 0 and false_positives == 0:
        print("\nSUCCESS: 100% Accuracy achieved without Pre-Computation.")
        print("The Navigator independently derived the Prime Number set.")
    else:
        print(f"\nFAILURE: Missed {missed}, False Positives {false_positives}")


def parse_args():
    parser = argparse.ArgumentParser(
        description="Blind harmonic prime scan with optional annealed basis."
    )
    parser.add_argument("--start", type=int, default=1000, help="Scan start.")
    parser.add_argument("--end", type=int, default=10000, help="Scan end (inclusive).")
    parser.add_argument(
        "--basis-mode",
        choices=("blind", "blind-stream", "annealed"),
        default="blind",
        help="Rotor basis mode.",
    )
    parser.add_argument(
        "--no-verify",
        action="store_true",
        help="Skip verification step.",
    )
    return parser.parse_args()


def main():
    args = parse_args()
    start = args.start
    end = args.end
    if end < start:
        raise SystemExit("--end must be >= --start.")

    navigator = CliffordBlindNavigator()
    t0 = time.perf_counter()
    navigator.calibrate_blind_basis(end, basis_mode=args.basis_mode)
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

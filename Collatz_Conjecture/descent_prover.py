# The Recursive Certificate Finder
# This proves UDL for a range of integers by covering the residue line.

from math import gcd


class DescentProver:
    def __init__(self, max_m=60, max_steps=200):
        self.certificates = []
        self.max_depth_reached = 0
        self.max_m = max_m
        self.max_steps = max_steps

    def get_next_state(self, a, b, d, r, M):
        """
        Calculates the next affine state given current map (ax+b)/d
        for input of form M*k + r.
        Returns: (is_valid, new_a, new_b, new_d, type)
        """
        # We need to know if (a*n + b)/d is even or odd.
        # n = M*k + r
        # Val = (a(Mk+r) + b)/d = (aMk + ar + b)/d

        # 1. Constant part check: (ar+b) must be divisible by d
        if (a * r + b) % d != 0:
            return False, 0, 0, 0, "Fractional"

        # 2. Parity check
        # Constant term of result: C = (ar+b)/d
        # Variable term of result: V = (aM)/d * k

        # If (aM)/d is even, parity depends only on C.
        # If (aM)/d is odd, parity flips with k -> Indeterminate -> SPLIT needed.

        if (a * M) % (2 * d) != 0:
            return False, 0, 0, 0, "Split"

        val_r = (a * r + b) // d
        is_odd = (val_r % 2 != 0)

        if is_odd:
            # (3x+1)/2 -> New map is (3 * old + 1) / 2
            # (3 * ( (an+b)/d ) + 1) / 2 = (3an + 3b + d) / 2d
            return True, 3*a, 3*b + d, 2*d, "Odd"
        else:
            # x/2 -> New map is old / 2
            # (an+b)/2d
            return True, a, b, 2*d, "Even"

    def simplify(self, a, b, d):
        """Reduce affine map by GCD to prevent coefficient explosion."""
        g = gcd(gcd(a, b), d)
        if g > 1:
            return a // g, b // g, d // g
        return a, b, d

    def get_n_min(self, r, M):
        """
        Get minimum n > 1 in residue class r mod M.
        - r = 0: smallest is M
        - r = 1: n=1 is goal state, use M+1
        - r > 1: smallest is r
        """
        if r == 0:
            return M
        elif r == 1:
            return M + 1
        else:
            return r

    def prove_residue(self, r, m, path=""):
        M = 2**m

        # Affine map parameters: T(n) = (a*n + b) / d
        a, b, d = 1, 0, 1

        # Trace trajectory
        for step in range(self.max_steps):
            # Check Descent Condition: (a n + b)/d < n
            # a/d < 1 AND offset check
            if a < d:
                # Check offset for smallest n > 1 in class
                n_min = self.get_n_min(r, M)
                if (a * n_min + b) < d * n_min:
                    # PROVEN
                    self.certificates.append({
                        "r": r, "m": m, "path": path,
                        "map": f"({a}n+{b})/{d}",
                        "a": a, "b": b, "d": d
                    })
                    self.max_depth_reached = max(self.max_depth_reached, m)
                    return True

            # Step forward
            valid, na, nb, nd, type_str = self.get_next_state(a, b, d, r, M)

            if not valid:
                if type_str == "Split":
                    # Parity depends on k. Split residue class into r and r + M
                    # New modulus will be 2^(m+1)
                    if m >= self.max_m:
                        print(f"  WARNING: Hit max depth {self.max_m} at residue {r}")
                        return False

                    # Recurse on refined residue classes
                    left = self.prove_residue(r, m+1, "")
                    right = self.prove_residue(r + M, m+1, "")
                    return left and right
                else:
                    print(f"  ERROR: Fractional state at r={r}, m={m}")
                    return False

            a, b, d = self.simplify(na, nb, nd)
            path += "O" if type_str == "Odd" else "E"

        print(f"  WARNING: Hit max steps {self.max_steps} at r={r}, m={m}")
        return False

    def run(self):
        print("Starting Uniform Descent Verification...")
        print(f"  Max modulus: 2^{self.max_m}")
        print(f"  Max steps per class: {self.max_steps}")
        print()

        # Start with trivial modulus 1 (covering all integers)
        # It will immediately split, building the tree naturally.
        success = self.prove_residue(0, 0, "")

        if success:
            print(f"\nSUCCESS: Uniform Descent Lemma Verified.")
            print(f"Total Certificates: {len(self.certificates)}")
            print(f"Max Modulus Reached: 2^{self.max_depth_reached}")
            print(f"\nExample Certificates:")
            for c in self.certificates[:5]:
                print(f"  Residue {c['r']} mod 2^{c['m']}: {c['path']} -> {c['map']} < n")

            # Show the hardest one
            if self.certificates:
                deepest = max(self.certificates, key=lambda x: x['m'])
                print(f"\nDeepest Split Required: 2^{deepest['m']} for residue {deepest['r']}")
        else:
            print("\nVerification Failed (Depth limit or logic error).")

        return success

    def export_certificates(self, filename):
        """Export certificates to JSON for independent verification."""
        import json
        with open(filename, 'w') as f:
            json.dump({
                "certificates": self.certificates,
                "max_depth": self.max_depth_reached,
                "total": len(self.certificates)
            }, f, indent=2)
        print(f"Exported {len(self.certificates)} certificates to {filename}")


if __name__ == "__main__":
    prover = DescentProver(max_m=18, max_steps=150)
    success = prover.run()

    if success:
        prover.export_certificates("descent_certificates.json")

(* FREDHOLM DETERMINANT TEST *)
(* Tests: det(I - R) =? 1/ζ(s) *)

(* Prime rotor at s = σ + it *)
primeRotor[p_, sigma_, t_] := p^(-(sigma - 1/2)) *
  {{Cos[t*Log[p]], -Sin[t*Log[p]]}, {Sin[t*Log[p]], Cos[t*Log[p]]}};

(* Cumulative rotor product *)
rotorProduct[maxP_, sigma_, t_] := Module[{primes, R},
  primes = Select[Range[2, maxP], PrimeQ];
  R = IdentityMatrix[2];
  Do[R = R . primeRotor[p, sigma, t], {p, primes}];
  R];

(* Partial inverse zeta: ∏_{p≤B} (1 - p^{-s}) *)
partialInvZeta[maxP_, sigma_, t_] := Module[{primes, s = sigma + I*t},
  primes = Select[Range[2, maxP], PrimeQ];
  Product[1 - p^(-s), {p, primes}]];

(* === TEST AT FIRST ZETA ZERO === *)
t0 = 14.1347;
maxP = 50;

R = rotorProduct[maxP, 0.5, t0];
detImR = Det[IdentityMatrix[2] - R];
invZeta = partialInvZeta[maxP, 0.5, t0];

Print["At first zeta zero (t=14.1347, σ=1/2):"];
Print["det(I-R) = ", detImR // N];
Print["|det(I-R)| = ", Abs[detImR] // N];
Print["1/ζ_B = ", invZeta // N];
Print["|1/ζ_B| = ", Abs[invZeta] // N];
Print["Ratio det(I-R)/(1/ζ_B) = ", detImR/invZeta // N];

(* === EIGENVALUE TEST: Does R have eigenvalue near 1 at zeros? === *)
Print["\n=== EIGENVALUE NEAR 1 AT ZEROS ==="];
zetaZeros = {14.1347, 21.0220, 25.0109, 30.4249, 32.9351};

Do[
  R = rotorProduct[maxP, 0.5, t];
  eigs = Eigenvalues[R];
  distFrom1 = Min[Abs[eigs - 1]];
  Print["t=", t, ": eigenvalues=", eigs // N, ", min|λ-1|=", distFrom1 // N];
, {t, zetaZeros}];

(* === SCAN: How does det(I-R) behave near zeros? === *)
Print["\n=== det(I-R) NEAR FIRST ZERO ==="];
tScan = Range[13.5, 15.0, 0.1];
Do[
  R = rotorProduct[maxP, 0.5, t];
  d = Det[IdentityMatrix[2] - R];
  Print["t=", t // N, ": |det(I-R)|=", Abs[d] // N];
, {t, tScan}];

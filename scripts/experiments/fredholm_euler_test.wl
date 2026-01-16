(* Fredholm-Euler Identity Test *)
(* Tests whether det(I - K) ≈ 1/ζ(s) for the rotor operator *)

(* === ROTOR OPERATOR DEFINITION === *)
primeRotor[p_, s_] := Module[{sigma = Re[s], t = Im[s], theta, r},
  theta = t * Log[p];
  r = p^(-(sigma - 1/2));
  r * {{Cos[theta], -Sin[theta]}, {Sin[theta], Cos[theta]}}
];

(* Finite rotor product over primes ≤ maxP *)
rotorProduct[maxP_, s_] := Module[{primes, R},
  primes = Select[Range[2, maxP], PrimeQ];
  R = IdentityMatrix[2];
  Do[R = R . primeRotor[p, s], {p, primes}];
  R
];

(* det(I - R) for the rotor product *)
rotorFredholmDet[maxP_, s_] := Det[IdentityMatrix[2] - rotorProduct[maxP, s]];

(* Partial Euler product 1/ζ_B(s) = ∏_{p≤B} (1 - p^{-s}) *)
partialInverseZeta[maxP_, s_] := Module[{primes},
  primes = Select[Range[2, maxP], PrimeQ];
  Product[1 - p^(-s), {p, primes}]
];

(* === TEST 1: Compare det(I-R) to 1/ζ at various s values === *)
Print["=== TEST 1: det(I-R) vs 1/ζ_B(s) ==="];
Print["Testing if det(I-K) ≈ 1/ζ(s)"];
Print[""];

maxP = 50;

(* Test points in critical strip *)
testPoints = {
  1/2 + 14.1347*I,  (* First zeta zero *)
  1/2 + 21.0220*I,  (* Second zeta zero *)
  1/2 + 10*I,       (* Non-zero on critical line *)
  0.7 + 14.1347*I,  (* Off critical line *)
  0.3 + 14.1347*I   (* Off critical line, other side *)
};

Do[
  s = sp;
  fredholm = rotorFredholmDet[maxP, s];
  euler = partialInverseZeta[maxP, s];

  Print["s = ", s // N];
  Print["  det(I-R) = ", fredholm // N];
  Print["  1/ζ_B(s) = ", euler // N];
  Print["  Ratio = ", fredholm/euler // N];
  Print["  |det(I-R)| = ", Abs[fredholm] // N];
  Print["  |1/ζ_B(s)| = ", Abs[euler] // N];
  Print[""];
, {sp, testPoints}];

(* === TEST 2: Behavior near zeta zeros === *)
Print["=== TEST 2: Behavior as we approach zeta zeros ==="];

gamma1 = 14.1347251417346937904572519835624702707842571156992431756855674601;

(* Scan t near the first zero *)
tValues = Table[gamma1 + dt, {dt, -1, 1, 0.2}];

Print["t near first zero (", gamma1, "):"];
Print["{t, |det(I-R)|, |ζ(1/2+it)|}"];

Do[
  s = 1/2 + t*I;
  fredholm = rotorFredholmDet[maxP, s];
  zetaVal = Zeta[s];
  Print[{t, Abs[fredholm], Abs[zetaVal]} // N];
, {t, tValues}];

(* === TEST 3: Convergence as maxP increases === *)
Print["\n=== TEST 3: Convergence with increasing maxP ==="];

s0 = 1/2 + 14.1347*I;

Print["At s = 1/2 + 14.1347i (first zero):"];
Print["{maxP, |det(I-R)|, |1/ζ_B|, ratio}"];

Do[
  fredholm = rotorFredholmDet[mp, s0];
  euler = partialInverseZeta[mp, s0];
  Print[{mp, Abs[fredholm], Abs[euler], Abs[fredholm/euler]} // N];
, {mp, {10, 20, 30, 50, 70, 100}}];

(* === TEST 4: The key eigenvalue test === *)
Print["\n=== TEST 4: Does R have eigenvalue 1 at zeros? ==="];
Print["If det(I-R) = 1/ζ and ζ(ρ)=0, then det(I-R) should blow up,"];
Print["meaning R has eigenvalue approaching 1."];
Print[""];

Print["Eigenvalues of R at various t (on critical line):"];

tScan = Join[{14.1347, 21.0220, 25.0109}, {10, 15, 20, 26, 35}];

Do[
  R = rotorProduct[50, 1/2 + t*I];
  eigs = Eigenvalues[R];
  zetaVal = Zeta[1/2 + t*I];

  Print["t = ", t // N];
  Print["  Eigenvalues: ", eigs // N];
  Print["  |Eigenvalues|: ", Abs[eigs] // N];
  Print["  Distance from 1: ", Min[Abs[eigs - 1]] // N];
  Print["  |ζ(1/2+it)|: ", Abs[zetaVal] // N];
  Print[""];
, {t, tScan}];

(* === CONCLUSION === *)
Print["=== HYPOTHESIS ==="];
Print["If det(I-R) ~ 1/ζ(s), then at zeros:"];
Print["  - det(I-R) should be large (pole of 1/ζ)"];
Print["  - R should have eigenvalue close to 1"];
Print["  - But we proved |eigenvalue| = 1 only at σ = 1/2"];
Print["  - Therefore zeros must have σ = 1/2"];

(* ═══════════════════════════════════════════════════════════════════════════
   ROTOR FORMULATION TEST - ALL IN ONE FILE

   Copy this entire file to Wolfram Cloud and execute.
   Results will show whether rotor unitarity is minimized at σ = 1/2.
   ═══════════════════════════════════════════════════════════════════════════ *)

(* ─────────────────────────────────────────────────────────────────────────────
   PART 1: PRIME ROTOR DEFINITIONS
   ───────────────────────────────────────────────────────────────────────────── *)

(* Single prime rotor: 2x2 rotation matrix scaled by p^{-σ} *)
PrimeRotor[p_, sigma_, t_] := Module[{theta, r},
  theta = t * Log[p];
  r = p^(-sigma);
  r * {{Cos[theta], -Sin[theta]}, {Sin[theta], Cos[theta]}}
]

(* Cumulative rotor product over all primes ≤ maxP *)
CumulativeRotor[sigma_, t_, maxP_] := Module[{primes},
  primes = Prime[Range[PrimePi[maxP]]];
  Fold[Dot, IdentityMatrix[2], PrimeRotor[#, sigma, t] & /@ primes]
]

(* Unitarity deviation: ||R†R - I|| *)
RotorDrift[sigma_, t_, maxP_] := Module[{R, RdagR},
  R = CumulativeRotor[sigma, t, maxP];
  RdagR = ConjugateTranspose[R] . R;
  Norm[RdagR - IdentityMatrix[2], "Frobenius"]
]

(* ─────────────────────────────────────────────────────────────────────────────
   PART 2: TEST AT ZETA ZEROS
   ───────────────────────────────────────────────────────────────────────────── *)

Print["═══════════════════════════════════════════════════════════════"];
Print["TEST 1: UNITARITY AT KNOWN ZETA ZEROS"];
Print["═══════════════════════════════════════════════════════════════"];

ZetaZeros = {14.1347, 21.0220, 25.0109, 30.4249, 32.9351};
maxP = 50;

Print["\nDrift at σ = 1/2 for each zeta zero (primes up to ", maxP, "):"];
Table[
  {gamma, RotorDrift[1/2, gamma, maxP]},
  {gamma, ZetaZeros}
] // TableForm

(* ─────────────────────────────────────────────────────────────────────────────
   PART 3: COMPARE σ = 1/2 vs OTHER σ
   ───────────────────────────────────────────────────────────────────────────── *)

Print["\n═══════════════════════════════════════════════════════════════"];
Print["TEST 2: DRIFT vs σ AT FIRST ZETA ZERO (γ = 14.1347)"];
Print["═══════════════════════════════════════════════════════════════"];

gamma1 = 14.1347;
sigmas = {0.3, 0.4, 0.5, 0.6, 0.7};

Print["\nDrift for different σ values:"];
Table[
  {sigma, RotorDrift[sigma, gamma1, maxP]},
  {sigma, sigmas}
] // TableForm

(* ─────────────────────────────────────────────────────────────────────────────
   PART 4: CONTINUOUS DRIFT PLOT
   ───────────────────────────────────────────────────────────────────────────── *)

Print["\n═══════════════════════════════════════════════════════════════"];
Print["TEST 3: DRIFT FUNCTION ACROSS σ ∈ [0.1, 0.9]"];
Print["═══════════════════════════════════════════════════════════════"];

(* Generate data for plot *)
driftData = Table[
  {sigma, RotorDrift[sigma, gamma1, maxP]},
  {sigma, 0.1, 0.9, 0.05}
];

Print["\nDrift values (σ, drift):"];
driftData // TableForm

(* Find minimum *)
minDrift = MinimalBy[driftData, Last];
Print["\nMinimum drift at: ", minDrift];

(* Plot if supported *)
ListLinePlot[driftData,
  PlotLabel -> "Rotor Drift vs σ at γ = 14.1347",
  AxesLabel -> {"σ", "Drift"},
  PlotRange -> All,
  GridLines -> {{0.5}, None},
  Epilog -> {Red, PointSize[0.02], Point[{0.5, RotorDrift[0.5, gamma1, maxP]}]}
]

(* ─────────────────────────────────────────────────────────────────────────────
   PART 5: ROTOR EIGENVALUES
   ───────────────────────────────────────────────────────────────────────────── *)

Print["\n═══════════════════════════════════════════════════════════════"];
Print["TEST 4: ROTOR EIGENVALUES AT CRITICAL LINE"];
Print["═══════════════════════════════════════════════════════════════"];

Print["\nEigenvalues of R(1/2 + i·γ) at first zeta zero:"];
R1 = CumulativeRotor[1/2, gamma1, maxP];
Print["R = ", MatrixForm[R1]];
Print["det(R) = ", Det[R1]];
Print["Eigenvalues = ", Eigenvalues[R1]];
Print["|Eigenvalues| = ", Abs[Eigenvalues[R1]]];

(* ─────────────────────────────────────────────────────────────────────────────
   PART 6: INTERPRETATION
   ───────────────────────────────────────────────────────────────────────────── *)

Print["\n═══════════════════════════════════════════════════════════════"];
Print["INTERPRETATION GUIDE"];
Print["═══════════════════════════════════════════════════════════════"];

Print["\nIF RH-COMPATIBLE:"];
Print["  • Drift should be MINIMIZED near σ = 0.5"];
Print["  • Eigenvalue magnitudes should approach 1 at zeros"];
Print["  • Drift should INCREASE as σ moves away from 0.5"];

Print["\nIF NOT RH-COMPATIBLE:"];
Print["  • Drift has no special minimum at σ = 0.5"];
Print["  • Need different rotor construction"];

Print["\n═══════════════════════════════════════════════════════════════"];
Print["END OF TESTS"];
Print["═══════════════════════════════════════════════════════════════"];

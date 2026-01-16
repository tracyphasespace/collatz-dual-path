(* ═══════════════════════════════════════════════════════════════════════════
   ROTOR-BASED OPERATOR FORMULATION

   Replacing the failed diagonal K(s) with dynamic rotor phase-locking.

   Core idea: RH holds iff rotor product becomes unitary only at σ = 1/2
   ═══════════════════════════════════════════════════════════════════════════ *)

(* ─────────────────────────────────────────────────────────────────────────────
   SECTION 1: Cl(3,3) Basis and Bivectors
   ───────────────────────────────────────────────────────────────────────────── *)

Print["═══════════════════════════════════════════════════════════════"];
Print["CLIFFORD ALGEBRA Cl(3,3) ROTOR OPERATORS"];
Print["═══════════════════════════════════════════════════════════════\n"];

(* Cl(3,3) has signature (+,+,+,-,-,-)
   Generators: e1, e2, e3 with ei^2 = +1
              f1, f2, f3 with fi^2 = -1

   Bivectors span a 15-dimensional space.
   We use specific bivectors for prime encoding. *)

(* For computational simplicity, represent rotors as matrices.
   In Cl(3,3), the even subalgebra (containing rotors) is 32-dimensional.
   We use a simplified 4x4 representation capturing key structure. *)

(* ─────────────────────────────────────────────────────────────────────────────
   SECTION 2: Prime Rotor Definition
   ───────────────────────────────────────────────────────────────────────────── *)

Print["PRIME ROTOR DEFINITION\n"];

Print["For prime p at s = σ + it, define rotor:"];
Print["  R_p(s) = exp(θ_p · B_p)"];
Print["where:"];
Print["  θ_p = t · log(p)  (rotation angle)"];
Print["  B_p = bivector encoding prime p"];
Print[""];

(* Simplified model: 2x2 complex rotation matrix
   This captures the essential phase dynamics *)

PrimeRotor2D[p_, s_] := Module[{sigma, t, theta, r},
  sigma = Re[s];
  t = Im[s];
  theta = t * Log[p];
  r = p^(-sigma);  (* Radial scaling *)
  (* Rotation with scaling *)
  r * {{Cos[theta], -Sin[theta]}, {Sin[theta], Cos[theta]}}
]

(* Full model: 4x4 representation in split basis *)
PrimeRotor4D[p_, s_] := Module[{sigma, t, theta, r, block},
  sigma = Re[s];
  t = Im[s];
  theta = t * Log[p];
  r = p^(-sigma);
  block = r * {{Cos[theta], -Sin[theta]}, {Sin[theta], Cos[theta]}};
  (* Block diagonal: positive and negative signature parts *)
  ArrayFlatten[{{block, 0}, {0, Conjugate[block]}}]
]

(* ─────────────────────────────────────────────────────────────────────────────
   SECTION 3: Total Rotor Product
   ───────────────────────────────────────────────────────────────────────────── *)

Print["═══════════════════════════════════════════════════════════════"];
Print["TOTAL ROTOR PRODUCT"];
Print["═══════════════════════════════════════════════════════════════\n"];

TotalRotor2D[s_, maxPrime_] := Module[{primes, rotors},
  primes = Prime[Range[PrimePi[maxPrime]]];
  rotors = PrimeRotor2D[#, s] & /@ primes;
  Fold[Dot, IdentityMatrix[2], rotors]
]

TotalRotor4D[s_, maxPrime_] := Module[{primes, rotors},
  primes = Prime[Range[PrimePi[maxPrime]]];
  rotors = PrimeRotor4D[#, s] & /@ primes;
  Fold[Dot, IdentityMatrix[4], rotors]
]

(* ─────────────────────────────────────────────────────────────────────────────
   SECTION 4: Unitarity Test
   ───────────────────────────────────────────────────────────────────────────── *)

Print["UNITARITY TEST\n"];

Print["At a zeta zero, we expect R(s) to be 'nearly unitary'"];
Print["Measure: ||R(s)^† R(s) - I|| should be small\n"];

UnitarityDeviation[s_, maxPrime_, dim_:2] := Module[{R, RdagR, dev},
  R = If[dim == 2, TotalRotor2D[s, maxPrime], TotalRotor4D[s, maxPrime]];
  RdagR = ConjugateTranspose[R] . R;
  dev = RdagR - IdentityMatrix[dim];
  Norm[dev, "Frobenius"]
]

(* ─────────────────────────────────────────────────────────────────────────────
   SECTION 5: Test at Zeta Zeros
   ───────────────────────────────────────────────────────────────────────────── *)

Print["═══════════════════════════════════════════════════════════════"];
Print["TEST AT KNOWN ZETA ZEROS"];
Print["═══════════════════════════════════════════════════════════════\n"];

ZetaZeros = {14.1347, 21.0220, 25.0109, 30.4249, 32.9351};

Print["Testing unitarity deviation at first 5 zeta zeros:\n"];

TestAtZetaZeros[maxP_] := Module[{results},
  results = Table[
    {gamma, UnitarityDeviation[1/2 + I*gamma, maxP]},
    {gamma, ZetaZeros}
  ];
  TableForm[results, TableHeadings -> {None, {"γ", "||R†R - I||"}}]
]

(* ─────────────────────────────────────────────────────────────────────────────
   SECTION 6: Off-Critical Comparison
   ───────────────────────────────────────────────────────────────────────────── *)

Print["═══════════════════════════════════════════════════════════════"];
Print["OFF-CRITICAL LINE COMPARISON"];
Print["═══════════════════════════════════════════════════════════════\n"];

Print["Compare unitarity at σ = 1/2 vs σ ≠ 1/2:\n"];

OffCriticalComparison[gamma_, maxP_] := Module[{sigmas, results},
  sigmas = {0.3, 0.4, 0.5, 0.6, 0.7};
  results = Table[
    {sigma, UnitarityDeviation[sigma + I*gamma, maxP]},
    {sigma, sigmas}
  ];
  TableForm[results, TableHeadings -> {None, {"σ", "||R†R - I||"}}]
]

(* ─────────────────────────────────────────────────────────────────────────────
   SECTION 7: Rotor Zeta Function
   ───────────────────────────────────────────────────────────────────────────── *)

Print["═══════════════════════════════════════════════════════════════"];
Print["ROTOR ZETA FUNCTION"];
Print["═══════════════════════════════════════════════════════════════\n"];

Print["Define: Z_rotor(s) = ⟨v, R(s)v⟩ for test vector v\n"];

RotorZeta[s_, maxPrime_, v_] := Module[{R},
  R = TotalRotor2D[s, maxPrime];
  Conjugate[v] . R . v
]

(* Use standard test vector *)
TestVector = {1, 1}/Sqrt[2];

PlotRotorZetaAlongCriticalLine[tRange_, maxP_] := Module[{data},
  data = Table[
    {t, Abs[RotorZeta[1/2 + I*t, maxP, TestVector]]},
    {t, tRange[[1]], tRange[[2]], 0.5}
  ];
  ListLinePlot[data,
    PlotLabel -> "Rotor Zeta |Z_rotor(1/2 + it)|",
    AxesLabel -> {"t", "|Z_rotor|"},
    PlotRange -> All
  ]
]

(* ─────────────────────────────────────────────────────────────────────────────
   SECTION 8: Execute Tests
   ───────────────────────────────────────────────────────────────────────────── *)

Print["═══════════════════════════════════════════════════════════════"];
Print["EXECUTING TESTS"];
Print["═══════════════════════════════════════════════════════════════\n"];

(* Run with small maxP first for quick results *)
maxPrime = 50;

Print["Using primes up to ", maxPrime, "\n"];
Print["-------------------------------------------\n"];

Print["Test 1: Unitarity at zeta zeros"];
Print[TestAtZetaZeros[maxPrime]];

Print["\n-------------------------------------------\n"];

Print["Test 2: Off-critical comparison at γ = 14.1347"];
Print[OffCriticalComparison[14.1347, maxPrime]];

Print["\n-------------------------------------------\n"];

Print["Test 3: Rotor product structure at first zero"];
R1 = TotalRotor2D[1/2 + I*14.1347, maxPrime];
Print["R(1/2 + 14.1347i) = "];
Print[MatrixForm[R1]];
Print["Determinant = ", Det[R1]];
Print["Eigenvalues = ", Eigenvalues[R1]];

(* ─────────────────────────────────────────────────────────────────────────────
   SECTION 9: Interpretation Guide
   ───────────────────────────────────────────────────────────────────────────── *)

Print["\n═══════════════════════════════════════════════════════════════"];
Print["INTERPRETATION"];
Print["═══════════════════════════════════════════════════════════════\n"];

Print["IF RH-compatible behavior:"];
Print["  - Unitarity deviation SMALLER at σ = 1/2 than off-critical"];
Print["  - Rotor eigenvalues approach unit circle at zeros"];
Print["  - Z_rotor has minima near classical ζ zeros"];
Print[""];
Print["IF NOT RH-compatible:"];
Print["  - No special behavior at σ = 1/2"];
Print["  - Need different rotor construction"];
Print[""];
Print["KEY INSIGHT:"];
Print["  The rotor approach replaces 'kernel existence' (always true for K)"];
Print["  with 'unitarity' (only true at special points)."];
Print["  This is a more selective condition."];

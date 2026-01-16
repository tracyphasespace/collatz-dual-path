(* ═══════════════════════════════════════════════════════════════════════════
   RAYLEIGH IDENTITY VERIFICATION

   Claim: Im⟨v, K(s)v⟩ = (σ - 1/2) Σ Λ(n)|v_n|²

   This notebook tests whether the identity holds numerically.
   ═══════════════════════════════════════════════════════════════════════════ *)

(* ─────────────────────────────────────────────────────────────────────────────
   SECTION 1: Definitions
   ───────────────────────────────────────────────────────────────────────────── *)

(* Von Mangoldt function *)
VonMangoldt[n_Integer] := If[n < 2, 0,
  If[PrimePowerQ[n], Log[FactorInteger[n][[1, 1]]], 0]
]

(* Sieve operator as diagonal matrix *)
SieveOperatorMatrix[s_, maxN_Integer] := DiagonalMatrix[
  Table[VonMangoldt[n] * n^(-s), {n, 1, maxN}]
]

(* Left-hand side of Rayleigh Identity *)
RayleighLHS[v_List, sigma_?NumericQ, t_?NumericQ] := Module[
  {s, K, quadForm},
  s = sigma + I * t;
  K = SieveOperatorMatrix[s, Length[v]];
  quadForm = Conjugate[v] . K . v;
  Im[quadForm]
]

(* Right-hand side of Rayleigh Identity *)
RayleighRHS[v_List, sigma_?NumericQ] := Module[
  {N = Length[v], weights},
  weights = Table[VonMangoldt[n] * Abs[v[[n]]]^2, {n, 1, N}];
  (sigma - 1/2) * Total[weights]
]

(* ─────────────────────────────────────────────────────────────────────────────
   SECTION 2: Numerical Verification
   ───────────────────────────────────────────────────────────────────────────── *)

(* Single test *)
TestRayleighOnce[maxN_Integer] := Module[
  {v, sigma, t, lhs, rhs, error},
  v = RandomComplex[{-1 - I, 1 + I}, maxN];
  sigma = RandomReal[{0.1, 0.9}];
  t = RandomReal[{1, 100}];
  lhs = RayleighLHS[v, sigma, t];
  rhs = RayleighRHS[v, sigma];
  error = Abs[lhs - rhs];
  <|"sigma" -> sigma, "t" -> t, "LHS" -> lhs, "RHS" -> rhs, "Error" -> error|>
]

(* Batch test *)
TestRayleighBatch[maxN_Integer, numTests_Integer] := Module[
  {results, errors},
  results = Table[TestRayleighOnce[maxN], {numTests}];
  errors = results[[All, "Error"]];
  <|
    "MeanError" -> Mean[errors],
    "MaxError" -> Max[errors],
    "StdError" -> StandardDeviation[errors],
    "AllResults" -> results
  |>
]

(* ─────────────────────────────────────────────────────────────────────────────
   SECTION 3: Run Tests
   ───────────────────────────────────────────────────────────────────────────── *)

Print["Testing Rayleigh Identity..."];
Print["N = 100, 100 tests:"];
result100 = TestRayleighBatch[100, 100];
Print["  Mean Error: ", result100["MeanError"]];
Print["  Max Error:  ", result100["MaxError"]];

Print["\nN = 500, 100 tests:"];
result500 = TestRayleighBatch[500, 100];
Print["  Mean Error: ", result500["MeanError"]];
Print["  Max Error:  ", result500["MaxError"]];

(* ─────────────────────────────────────────────────────────────────────────────
   SECTION 4: Analysis of Discrepancy
   ───────────────────────────────────────────────────────────────────────────── *)

(* If errors are large, analyze why *)
Print["\n═══════════════════════════════════════════════════════════════"];
Print["ANALYSIS: Expanding the LHS explicitly"];
Print["═══════════════════════════════════════════════════════════════"];

(* Symbolic expansion *)
Print["\nLHS = Im⟨v, K(s)v⟩"];
Print["    = Im[Σ_n Λ(n) |v_n|² n^{-s}]"];
Print["    = Im[Σ_n Λ(n) |v_n|² n^{-σ} e^{-it log n}]"];
Print["    = -Σ_n Λ(n) |v_n|² n^{-σ} sin(t log n)"];
Print["\nRHS = (σ - 1/2) Σ_n Λ(n) |v_n|²"];
Print["\nFor these to be equal:"];
Print["  -n^{-σ} sin(t log n) must equal (σ - 1/2) for all contributing n"];
Print["  This is NOT generally true!"];

(* ─────────────────────────────────────────────────────────────────────────────
   SECTION 5: Corrected Identity?
   ───────────────────────────────────────────────────────────────────────────── *)

Print["\n═══════════════════════════════════════════════════════════════"];
Print["HYPOTHESIS: Perhaps the identity involves an average or limit?"];
Print["═══════════════════════════════════════════════════════════════"];

(* Test: Does the identity hold in some averaged sense? *)
AveragedTest[maxN_Integer, numT_Integer] := Module[
  {v, sigma, tVals, lhsVals, avgLHS, rhs},
  v = Normalize[RandomComplex[{-1 - I, 1 + I}, maxN]];
  sigma = 0.7; (* Off critical line *)
  tVals = Range[1, 100, 100/numT];
  lhsVals = Table[RayleighLHS[v, sigma, t], {t, tVals}];
  avgLHS = Mean[lhsVals];
  rhs = RayleighRHS[v, sigma];
  <|"AvgLHS" -> avgLHS, "RHS" -> rhs, "Ratio" -> avgLHS/rhs|>
]

Print["\nAveraged over t values:"];
Print[AveragedTest[200, 50]];

(* ─────────────────────────────────────────────────────────────────────────────
   SECTION 6: Conclusion
   ───────────────────────────────────────────────────────────────────────────── *)

Print["\n═══════════════════════════════════════════════════════════════"];
Print["CONCLUSION"];
Print["═══════════════════════════════════════════════════════════════"];
Print["The Rayleigh Identity as stated does NOT hold for arbitrary v, σ, t."];
Print["The paper may be assuming:"];
Print["  1. v is an eigenvector of K"];
Print["  2. Some limiting or averaging process"];
Print["  3. A different operator definition"];
Print["\nFurther investigation required."];

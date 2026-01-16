(* ═══════════════════════════════════════════════════════════════════════════
   KERNEL ANALYSIS AT ZETA ZEROS

   Question: Does K(s) have non-trivial kernel at ζ(s) = 0?

   This notebook investigates the relationship between:
   - Zeros of the Riemann zeta function
   - Kernel (null space) of the sieve operator K(s)
   ═══════════════════════════════════════════════════════════════════════════ *)

(* ─────────────────────────────────────────────────────────────────────────────
   SECTION 1: Definitions
   ───────────────────────────────────────────────────────────────────────────── *)

VonMangoldt[n_Integer] := If[n < 2, 0,
  If[PrimePowerQ[n], Log[FactorInteger[n][[1, 1]]], 0]
]

SieveOperatorMatrix[s_, maxN_Integer] := DiagonalMatrix[
  Table[VonMangoldt[n] * n^(-s), {n, 1, maxN}]
]

(* Known zeta zeros (imaginary parts, on critical line σ = 1/2) *)
ZetaZeros = {
  14.134725141734693790457251983562,
  21.022039638771554992628479593897,
  25.010857580145688763213790992563,
  30.424876125859513210311897530584,
  32.935061587739189690662368964075,
  37.586178158825671257217763480705,
  40.918719012147495187398126914944,
  43.327073280914999519496122165406,
  48.005150881167159727942472749428,
  49.773832477672302181916784678564,
  52.970321477714460644147296608881,
  56.446247697063394804367759476706,
  59.347044002602353079653648674993,
  60.831778524609809844259901824524,
  65.112544048081606660875054253183,
  67.079810529494173714478828896523,
  69.546401711173979252926857526554,
  72.067157674481907582522107969826,
  75.704690699083933168326916762031,
  77.144840068874805372682664856305
};

(* ─────────────────────────────────────────────────────────────────────────────
   SECTION 2: Eigenvalue Analysis at Zeros
   ───────────────────────────────────────────────────────────────────────────── *)

AnalyzeAtZero[gamma_?NumericQ, maxN_Integer] := Module[
  {s, K, eigenvals, minEig, zetaVal},
  s = 1/2 + I * gamma;
  K = SieveOperatorMatrix[s, maxN];
  eigenvals = Eigenvalues[K];
  minEig = Min[Abs[eigenvals]];
  zetaVal = Zeta[s];
  <|
    "gamma" -> gamma,
    "minEigenvalue" -> minEig,
    "zetaValue" -> zetaVal,
    "zetaMagnitude" -> Abs[zetaVal],
    "top5Eigenvalues" -> Sort[Abs[eigenvals]][[1 ;; Min[5, Length[eigenvals]]]]
  |>
]

Print["═══════════════════════════════════════════════════════════════"];
Print["EIGENVALUE ANALYSIS AT ZETA ZEROS"];
Print["═══════════════════════════════════════════════════════════════\n"];

Print["Testing with N = 500 terms...\n"];
zerosResults = Table[
  AnalyzeAtZero[gamma, 500],
  {gamma, ZetaZeros[[1 ;; 10]]}
];

Print["γ (zero)\t\tMin|λ|\t\t|ζ(s)|"];
Print["─────────────────────────────────────────────────────"];
Do[
  Print[
    NumberForm[r["gamma"], 6], "\t\t",
    ScientificForm[r["minEigenvalue"], 3], "\t\t",
    ScientificForm[r["zetaMagnitude"], 3]
  ],
  {r, zerosResults}
];

(* ─────────────────────────────────────────────────────────────────────────────
   SECTION 3: Comparison with Non-Zeros
   ───────────────────────────────────────────────────────────────────────────── *)

Print["\n═══════════════════════════════════════════════════════════════"];
Print["COMPARISON: Zeros vs Non-Zeros on Critical Line"];
Print["═══════════════════════════════════════════════════════════════\n"];

(* Test at points that are NOT zeros *)
nonZeroPoints = {10, 15, 20, 25, 35, 45, 55};

nonZeroResults = Table[
  AnalyzeAtZero[t, 500],
  {t, nonZeroPoints}
];

Print["t (non-zero)\t\tMin|λ|\t\t|ζ(s)|"];
Print["─────────────────────────────────────────────────────"];
Do[
  Print[
    NumberForm[r["gamma"], 6], "\t\t",
    ScientificForm[r["minEigenvalue"], 3], "\t\t",
    ScientificForm[r["zetaMagnitude"], 3]
  ],
  {r, nonZeroResults}
];

(* ─────────────────────────────────────────────────────────────────────────────
   SECTION 4: Null Space Search
   ───────────────────────────────────────────────────────────────────────────── *)

Print["\n═══════════════════════════════════════════════════════════════"];
Print["NULL SPACE SEARCH AT ZEROS"];
Print["═══════════════════════════════════════════════════════════════\n"];

FindKernelAtZero[gamma_?NumericQ, maxN_Integer, tol_] := Module[
  {s, K, nullSpace, residual},
  s = 1/2 + I * gamma;
  K = SieveOperatorMatrix[s, maxN];
  nullSpace = NullSpace[K, Tolerance -> tol];
  If[Length[nullSpace] > 0,
    residual = Norm[K . nullSpace[[1]]];
    <|"Found" -> True, "Dimension" -> Length[nullSpace], "Residual" -> residual|>,
    <|"Found" -> False, "Dimension" -> 0, "MinEig" -> Min[Abs[Eigenvalues[K]]]|>
  ]
]

Print["Searching for null vectors (tolerance = 10^-10)...\n"];
Do[
  result = FindKernelAtZero[gamma, 500, 10^-10];
  Print["γ = ", NumberForm[gamma, 6], ": ", result],
  {gamma, ZetaZeros[[1 ;; 5]]}
];

(* ─────────────────────────────────────────────────────────────────────────────
   SECTION 5: The Diagonal Structure Problem
   ───────────────────────────────────────────────────────────────────────────── *)

Print["\n═══════════════════════════════════════════════════════════════"];
Print["CRITICAL OBSERVATION: K(s) is DIAGONAL"];
Print["═══════════════════════════════════════════════════════════════\n"];

Print["The sieve operator K(s) = diag(Λ(n) n^{-s}) is diagonal."];
Print[""];
Print["For a diagonal matrix, ker(K) ≠ {0} iff some diagonal entry = 0."];
Print[""];
Print["Diagonal entries: Λ(n) n^{-s}"];
Print["  - Λ(n) = 0 for n not a prime power → these give kernel directions"];
Print["  - Λ(n) = log(p) for n = p^k → never zero"];
Print["  - n^{-s} ≠ 0 for any finite s"];
Print[""];
Print["CONCLUSION: K(s) ALWAYS has non-trivial kernel!"];
Print["(Because Λ(1) = 0, Λ(6) = 0, etc.)"];
Print[""];
Print["This means the 'Zeta Link' as stated cannot be correct."];
Print["The operator definition needs refinement."];

(* ─────────────────────────────────────────────────────────────────────────────
   SECTION 6: Suggested Refinement
   ───────────────────────────────────────────────────────────────────────────── *)

Print["\n═══════════════════════════════════════════════════════════════"];
Print["SUGGESTED REFINEMENT"];
Print["═══════════════════════════════════════════════════════════════\n"];

Print["Option 1: Restrict to prime powers only"];
Print["  K(s) acts on ℓ²({p^k : p prime, k ≥ 1})"];
Print[""];
Print["Option 2: Use -ζ'/ζ(s) directly"];
Print["  -ζ'/ζ(s) = Σ Λ(n) n^{-s}"];
Print["  Poles of -ζ'/ζ occur at zeros of ζ"];
Print[""];
Print["Option 3: Fredholm determinant formulation"];
Print["  det(I - K) relates to ζ(s) via regularization"];
Print[""];
Print["The paper's claim needs mathematical clarification."];

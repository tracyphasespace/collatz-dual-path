(* ═══════════════════════════════════════════════════════════════════════════
   COUNTEREXAMPLE SEARCH

   Question: Is there any s with σ ≠ 1/2 where the "tension" vanishes?

   If we find such points, it would refute the geometric stability theory.
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

(* Tension measure: should be zero only at σ = 1/2 according to theory *)
GeometricTension[v_List, sigma_?NumericQ, t_?NumericQ] := Module[
  {s, K, quadForm},
  s = sigma + I * t;
  K = SieveOperatorMatrix[s, Length[v]];
  quadForm = Conjugate[v] . K . v;
  Im[quadForm]
]

(* ─────────────────────────────────────────────────────────────────────────────
   SECTION 2: Grid Search Off Critical Line
   ───────────────────────────────────────────────────────────────────────────── *)

Print["═══════════════════════════════════════════════════════════════"];
Print["SEARCHING FOR TENSION ZEROS OFF CRITICAL LINE"];
Print["═══════════════════════════════════════════════════════════════\n"];

SearchTensionZeros[maxN_Integer, sigmaRange_, tRange_, gridSize_Integer] :=
Module[
  {v, results, sigmaVals, tVals},

  (* Use fixed test vector *)
  v = Normalize[Table[1/n, {n, 1, maxN}]];

  sigmaVals = Subdivide[sigmaRange[[1]], sigmaRange[[2]], gridSize];
  tVals = Subdivide[tRange[[1]], tRange[[2]], gridSize];

  results = Flatten[Table[
    Module[{tension},
      tension = GeometricTension[v, sigma, t];
      If[Abs[tension] < 10^-6 && Abs[sigma - 0.5] > 0.01,
        {sigma, t, tension},
        Nothing
      ]
    ],
    {sigma, sigmaVals}, {t, tVals}
  ], 1];

  results
]

Print["Searching σ ∈ [0.1, 0.9], t ∈ [1, 50], grid 50×50..."];
nearZeros = SearchTensionZeros[200, {0.1, 0.9}, {1, 50}, 50];
Print["Found ", Length[nearZeros], " near-zero tension points off critical line."];

If[Length[nearZeros] > 0,
  Print["\nSuspicious points (σ ≠ 1/2 with tension ≈ 0):"];
  Print["σ\t\tt\t\tTension"];
  Print["─────────────────────────────────────────"];
  Do[Print[pt[[1]], "\t\t", pt[[2]], "\t\t", ScientificForm[pt[[3]], 3]],
    {pt, nearZeros[[1 ;; Min[10, Length[nearZeros]]]]}
  ],
  Print["\nNo counterexamples found in this region."]
];

(* ─────────────────────────────────────────────────────────────────────────────
   SECTION 3: Tension Profile Along σ
   ───────────────────────────────────────────────────────────────────────────── *)

Print["\n═══════════════════════════════════════════════════════════════"];
Print["TENSION PROFILE vs σ (fixed t)"];
Print["═══════════════════════════════════════════════════════════════\n"];

PlotTensionVsSigma[t_?NumericQ, maxN_Integer] := Module[
  {v, sigmaVals, tensions},
  v = Normalize[Table[1/n, {n, 1, maxN}]];
  sigmaVals = Subdivide[0.1, 0.9, 100];
  tensions = Table[GeometricTension[v, sigma, t], {sigma, sigmaVals}];

  (* Find zero crossing *)
  zeroCrossings = Select[
    Partition[Transpose[{sigmaVals, tensions}], 2, 1],
    #[[1, 2]] * #[[2, 2]] < 0 &
  ];

  Print["t = ", t];
  If[Length[zeroCrossings] > 0,
    Print["  Zero crossing near σ = ", Mean[zeroCrossings[[1, All, 1]]]],
    Print["  No zero crossing found"]
  ];
  Print["  Tension at σ=0.5: ", GeometricTension[v, 0.5, t]];
]

Do[PlotTensionVsSigma[t, 200], {t, {10, 14.1347, 20, 30}}];

(* ─────────────────────────────────────────────────────────────────────────────
   SECTION 4: Critical Analysis
   ───────────────────────────────────────────────────────────────────────────── *)

Print["\n═══════════════════════════════════════════════════════════════"];
Print["CRITICAL ANALYSIS"];
Print["═══════════════════════════════════════════════════════════════\n"];

Print["The 'tension' Im⟨v, K(s)v⟩ = -Σ Λ(n)|v_n|² n^{-σ} sin(t log n)"];
Print[""];
Print["This is a sum of sinusoids with incommensurate frequencies."];
Print["It will have many zeros as a function of t for ANY σ."];
Print["It will also have zeros as a function of σ for most t."];
Print[""];
Print["The claim that tension = 0 ONLY at σ = 1/2 appears FALSE"];
Print["for the naive definition of tension."];
Print[""];
Print["The paper likely means something more subtle:"];
Print["  - Perhaps an averaged or integrated tension"];
Print["  - Perhaps a different inner product"];
Print["  - Perhaps the tension of specific eigenvectors"];

(* ─────────────────────────────────────────────────────────────────────────────
   SECTION 5: Alternative Interpretation
   ───────────────────────────────────────────────────────────────────────────── *)

Print["\n═══════════════════════════════════════════════════════════════"];
Print["ALTERNATIVE: The RHS Interpretation"];
Print["═══════════════════════════════════════════════════════════════\n"];

Print["If the Rayleigh Identity held:"];
Print["  Im⟨v, K(s)v⟩ = (σ - 1/2) Σ Λ(n)|v_n|²"];
Print[""];
Print["Then tension = 0 iff σ = 1/2 OR v = 0 (trivially)"];
Print[""];
Print["But we showed the identity does NOT hold as stated."];
Print[""];
Print["Perhaps the correct statement is:"];
Print["  At σ = 1/2, K(s) is 'self-adjoint up to phase'"];
Print["  meaning Im⟨v, Kv⟩ = 0 for all real v"];
Print[""];
Print["Let's test this...\n"];

TestSelfAdjointAtHalf[t_?NumericQ, maxN_Integer] := Module[
  {s, K, v, quadForm},
  s = 1/2 + I * t;
  K = SieveOperatorMatrix[s, maxN];
  v = RandomReal[{-1, 1}, maxN]; (* Real vector *)
  quadForm = v . K . v; (* Real inner product *)
  <|"t" -> t, "ImQuadForm" -> Im[quadForm], "ReQuadForm" -> Re[quadForm]|>
]

Print["Testing Im⟨v, Kv⟩ for real v at σ = 1/2:"];
Do[Print[TestSelfAdjointAtHalf[t, 200]], {t, {10, 14.1347, 20, 30}}];

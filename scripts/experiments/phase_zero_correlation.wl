(* PHASE ZERO-CROSSING CORRELATION TEST *)
(* Quantifies how well φ''(t) = 0 matches actual zeta zeros *)
(* Copy each block separately to ChatGPT-Wolfram *)

(* ═══════════════════════════════════════════════════════════════ *)
(* BLOCK 1: Define rotor and phase function *)
(* ═══════════════════════════════════════════════════════════════ *)

Module[{PR, CR, phase, mP = 50},
  PR[p_, t_] := p^0 * {{Cos[t*Log[p]], -Sin[t*Log[p]]}, {Sin[t*Log[p]], Cos[t*Log[p]]}};
  CR[t_?NumericQ] := Fold[Dot, IdentityMatrix[2], PR[#, t] & /@ Prime[Range[PrimePi[mP]]]];
  phase[t_?NumericQ] := Arg[Det[CR[t]]];
  (* Test: phase at a few points *)
  Table[{t, phase[t]}, {t, 10, 15, 1}]
]

(* ═══════════════════════════════════════════════════════════════ *)
(* BLOCK 2: Find φ''(t) zero-crossings numerically *)
(* ═══════════════════════════════════════════════════════════════ *)

Module[{PR, CR, phase, d2phase, crossings, mP = 50, tmin = 10, tmax = 50, dt = 0.1},
  PR[p_, t_] := {{Cos[t*Log[p]], -Sin[t*Log[p]]}, {Sin[t*Log[p]], Cos[t*Log[p]]}};
  CR[t_?NumericQ] := Fold[Dot, IdentityMatrix[2], PR[#, t] & /@ Prime[Range[PrimePi[mP]]]];
  phase[t_?NumericQ] := Arg[Det[CR[t]]];
  d2phase[t_?NumericQ] := (phase[t + dt] - 2*phase[t] + phase[t - dt])/dt^2;
  (* Find sign changes in d2phase *)
  crossings = {};
  Do[
    If[d2phase[t] * d2phase[t + dt] < 0,
      AppendTo[crossings, t + dt/2]
    ],
    {t, tmin, tmax - dt, dt}
  ];
  {"Crossings found", Length[crossings], "First 10", crossings[[1 ;; Min[10, Length[crossings]]]]}
]

(* ═══════════════════════════════════════════════════════════════ *)
(* BLOCK 3: Known zeta zeros for comparison *)
(* ═══════════════════════════════════════════════════════════════ *)

zetaZeros = {14.1347, 21.0220, 25.0109, 30.4249, 32.9351, 37.5862, 40.9187, 43.3271, 48.0052};
{"Known zeta zeros in [10,50]", zetaZeros}

(* ═══════════════════════════════════════════════════════════════ *)
(* BLOCK 4: FULL CORRELATION TEST - Run this one *)
(* ═══════════════════════════════════════════════════════════════ *)

Module[{PR, CR, phase, d2phase, crossings, zetaZeros, matches, mP = 50, dt = 0.05, tol = 0.5},
  PR[p_, t_] := {{Cos[t*Log[p]], -Sin[t*Log[p]]}, {Sin[t*Log[p]], Cos[t*Log[p]]}};
  CR[t_?NumericQ] := Fold[Dot, IdentityMatrix[2], PR[#, t] & /@ Prime[Range[PrimePi[mP]]]];
  phase[t_?NumericQ] := Arg[Det[CR[t]]];
  d2phase[t_?NumericQ] := (phase[t + dt] - 2*phase[t] + phase[t - dt])/dt^2;
  (* Find zero-crossings *)
  crossings = {};
  Do[If[d2phase[t]*d2phase[t + dt] < 0, AppendTo[crossings, t + dt/2]], {t, 10, 50, dt}];
  (* Known zeros *)
  zetaZeros = {14.1347, 21.0220, 25.0109, 30.4249, 32.9351, 37.5862, 40.9187, 43.3271, 48.0052};
  (* For each zeta zero, find nearest crossing *)
  matches = Table[
    {z, Min[Abs[crossings - z]], SelectFirst[crossings, Abs[# - z] < tol &, "None"]},
    {z, zetaZeros}
  ];
  {"ZetaZero", "MinDist", "NearestCrossing"} -> matches
]

(* ═══════════════════════════════════════════════════════════════ *)
(* BLOCK 5: SUMMARY STATISTICS *)
(* ═══════════════════════════════════════════════════════════════ *)

Module[{PR, CR, phase, d2phase, crossings, zetaZeros, dists, mP = 50, dt = 0.05},
  PR[p_, t_] := {{Cos[t*Log[p]], -Sin[t*Log[p]]}, {Sin[t*Log[p]], Cos[t*Log[p]]}};
  CR[t_?NumericQ] := Fold[Dot, IdentityMatrix[2], PR[#, t] & /@ Prime[Range[PrimePi[mP]]]];
  phase[t_?NumericQ] := Arg[Det[CR[t]]];
  d2phase[t_?NumericQ] := (phase[t + dt] - 2*phase[t] + phase[t - dt])/dt^2;
  crossings = {};
  Do[If[d2phase[t]*d2phase[t + dt] < 0, AppendTo[crossings, t + dt/2]], {t, 10, 50, dt}];
  zetaZeros = {14.1347, 21.0220, 25.0109, 30.4249, 32.9351, 37.5862, 40.9187, 43.3271, 48.0052};
  dists = Table[Min[Abs[crossings - z]], {z, zetaZeros}];
  {
    "NumZetaZeros" -> Length[zetaZeros],
    "NumCrossings" -> Length[crossings],
    "MeanDistToNearestCrossing" -> Mean[dists],
    "MaxDistToNearestCrossing" -> Max[dists],
    "AllDistances" -> dists
  }
]

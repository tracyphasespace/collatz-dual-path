(* Composite vs Prime Rotor Comparison *)
(* Tests whether prime irreducibility is essential for rotor structure *)

(* === PRIME-BASED ROTOR (our standard) === *)
primeRotor[p_, sigma_, t_] := p^(-(sigma - 1/2)) * {{Cos[t*Log[p]], -Sin[t*Log[p]]}, {Sin[t*Log[p]], Cos[t*Log[p]]}};

primeProduct[maxP_, sigma_, t_] := Module[{primes, result},
  primes = Select[Range[2, maxP], PrimeQ];
  result = IdentityMatrix[2];
  Do[result = result . primeRotor[p, sigma, t], {p, primes}];
  result
];

(* === COMPOSITE-BASED ROTOR (test of irreducibility) === *)
(* Use composites instead of primes *)
compositeRotor[n_, sigma_, t_] := n^(-(sigma - 1/2)) * {{Cos[t*Log[n]], -Sin[t*Log[n]]}, {Sin[t*Log[n]], Cos[t*Log[n]]}};

compositeProduct[maxN_, sigma_, t_] := Module[{composites, result},
  composites = Select[Range[4, maxN], Not@*PrimeQ]; (* 4,6,8,9,10,... *)
  result = IdentityMatrix[2];
  Do[result = result . compositeRotor[n, sigma, t], {n, Take[composites, 25]}]; (* First 25 composites *)
  result
];

(* === RATIONAL FREQUENCY ROTOR (test of incommensurability) === *)
(* Use rational multiples of log 2 instead of independent log p *)
rationalRotor[k_, sigma_, t_] := Module[{freq = k * Log[2]}, (* All frequencies are k*log(2) *)
  2^(-(sigma - 1/2)) * {{Cos[t*freq], -Sin[t*freq]}, {Sin[t*freq], Cos[t*freq]}}
];

rationalProduct[maxK_, sigma_, t_] := Module[{result},
  result = IdentityMatrix[2];
  Do[result = result . rationalRotor[k, sigma, t], {k, 1, maxK}];
  result
];

(* === TEST 1: Unitarity drift at sigma = 0.5 === *)
Print["=== TEST 1: Unitarity at sigma = 0.5 ==="];

drift[R_] := Norm[R . Transpose[R] - IdentityMatrix[2], "Frobenius"];

t0 = 14.1347; (* First zeta zero *)

primeDrift = drift[primeProduct[50, 0.5, t0]];
compositeDrift = drift[compositeProduct[50, 0.5, t0]];
rationalDrift = drift[rationalProduct[25, 0.5, t0]];

Print["Prime rotor drift at sigma=0.5: ", primeDrift];
Print["Composite rotor drift at sigma=0.5: ", compositeDrift];
Print["Rational-freq rotor drift at sigma=0.5: ", rationalDrift];

(* === TEST 2: Drift vs sigma curves === *)
Print["\n=== TEST 2: Drift vs sigma ==="];

sigmaRange = Range[0.1, 0.9, 0.1];

primeDrifts = Table[drift[primeProduct[50, s, t0]], {s, sigmaRange}];
compositeDrifts = Table[drift[compositeProduct[50, s, t0]], {s, sigmaRange}];
rationalDrifts = Table[drift[rationalProduct[25, s, t0]], {s, sigmaRange}];

Print["Sigma values: ", sigmaRange];
Print["Prime drifts: ", primeDrifts];
Print["Composite drifts: ", compositeDrifts];
Print["Rational drifts: ", rationalDrifts];

(* === TEST 3: Eigenvalue magnitudes === *)
Print["\n=== TEST 3: Eigenvalue magnitudes at sigma=0.5 ==="];

primeEigs = Eigenvalues[primeProduct[50, 0.5, t0]];
compositeEigs = Eigenvalues[compositeProduct[50, 0.5, t0]];
rationalEigs = Eigenvalues[rationalProduct[25, 0.5, t0]];

Print["Prime eigenvalue magnitudes: ", Abs[primeEigs]];
Print["Composite eigenvalue magnitudes: ", Abs[compositeEigs]];
Print["Rational eigenvalue magnitudes: ", Abs[rationalEigs]];

(* === TEST 4: Phase behavior near zeta zeros === *)
Print["\n=== TEST 4: Phase at zeta zeros vs non-zeros ==="];

zetaZeros = {14.1347, 21.0220, 25.0109, 30.4249, 32.9351};
nonZeros = {10.0, 15.0, 20.0, 26.0, 35.0};

phaseOf[R_] := Arg[Det[R]];

primePhaseAtZeros = Table[phaseOf[primeProduct[50, 0.5, t]], {t, zetaZeros}];
primePhaseAtNonZeros = Table[phaseOf[primeProduct[50, 0.5, t]], {t, nonZeros}];

compositePhaseAtZeros = Table[phaseOf[compositeProduct[50, 0.5, t]], {t, zetaZeros}];
compositePhaseAtNonZeros = Table[phaseOf[compositeProduct[50, 0.5, t]], {t, nonZeros}];

Print["Prime rotor phase at zeta zeros: ", primePhaseAtZeros];
Print["Prime rotor phase at non-zeros: ", primePhaseAtNonZeros];
Print["Composite rotor phase at zeta zeros: ", compositePhaseAtZeros];
Print["Composite rotor phase at non-zeros: ", compositePhaseAtNonZeros];

(* === KEY QUESTION === *)
Print["\n=== KEY QUESTION ==="];
Print["Does the PRIME rotor show special structure that COMPOSITE/RATIONAL rotors lack?"];
Print["If yes: Prime irreducibility is essential for the geometric encoding of zeros."];
Print["If no: The rotor structure is more general than prime-specific."];

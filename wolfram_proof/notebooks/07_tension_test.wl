(* ROTOR TENSION TEST - Simplified for speed *)
(* Tests if ||R(t) - I|| shows special behavior at zeta zeros *)

(* Use only 5 primes for speed *)
maxP = 5;
primes = {2, 3, 5, 7, 11};

(* Single rotor *)
rotor[p_, t_] := {{Cos[t*Log[p]], -Sin[t*Log[p]]}, {Sin[t*Log[p]], Cos[t*Log[p]]}};

(* Product of rotors *)
R[t_] := Fold[Dot, IdentityMatrix[2], Table[rotor[p, t], {p, primes}]];

(* Tension = ||R - I|| *)
tension[t_] := Sqrt[Total[Flatten[(R[t] - IdentityMatrix[2])^2]]];

(* Test at zeta zeros *)
Print["Tension at zeta zeros:"];
Print["t=14.1347: ", tension[14.1347] // N];
Print["t=21.0220: ", tension[21.0220] // N];
Print["t=25.0109: ", tension[25.0109] // N];

(* Test at non-zeros *)
Print["\nTension at non-zeros:"];
Print["t=10: ", tension[10] // N];
Print["t=15: ", tension[15] // N];
Print["t=20: ", tension[20] // N];

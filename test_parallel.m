(* Test script for parallel FOL decider *)
(* This script demonstrates the parallelization features added to the QL package *)

(* Load the QL package *)
Get["ql.m"]

(* Print current parallelization status *)
Print["Parallelization enabled: ", GetParallelization[]]
If[GetParallelization[], 
  Print["Number of parallel kernels: ", Length[Kernels[]]],
  Print["Running in sequential mode"]
]

(* Set print level to see some output *)
printproofstepslevel = 2;

(* Test 1: Simple satisfiable formula *)
Print["\n=== Test 1: Simple satisfiable formula ==="]
test1 = ein[{y}, p[y]]
result1 = decide[test1]
Print["Result: ", result1]

(* Test 2: Simple unsatisfiable formula *)
Print["\n=== Test 2: Simple unsatisfiable formula ==="]
test2 = alle[{x}, p[x] && Not[p[x]]]
result2 = decide[test2]
Print["Result: ", result2]

(* Test 3: More complex formula with multiple quantifiers *)
Print["\n=== Test 3: Formula with multiple quantifiers ==="]
test3 = alle[{x}, ein[{y}, p[x, y]]]
result3 = decide[test3]
Print["Result: ", result3]

(* Test 4: Disable parallelization and run again *)
Print["\n=== Test 4: Running with parallelization disabled ==="]
SetParallelization[False]
Print["Parallelization enabled: ", GetParallelization[]]
result4 = decide[test3]
Print["Result: ", result4]

(* Re-enable parallelization *)
SetParallelization[True]
Print["\nParallelization re-enabled: ", GetParallelization[]]

Print["\n=== All tests completed ==="]

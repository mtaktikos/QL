(* Performance comparison example for parallel FOL decider *)
(* This demonstrates the performance benefits of parallelization *)

Get["ql.m"]

printproofstepslevel = 1; (* Minimal output for cleaner benchmark *)

Print["==============================================="]
Print["FOL Decider Parallelization Performance Demo"]
Print["==============================================="]
Print[]

(* Test case: A formula that generates multiple disjuncts *)
(* This type of formula benefits most from parallelization *)
testFormula = alle[{x}, ein[{y}, (p[x,y] || q[x,y]) && (r[x] || s[y])]]

Print["Test formula: ", tradi[testFormula]]
Print[]

(* Run with parallelization enabled *)
Print["--- Running with PARALLELIZATION ENABLED ---"]
SetParallelization[True]
Print["Parallelization status: ", GetParallelization[]]
If[GetParallelization[] && Length[Kernels[]] > 0,
  Print["Number of parallel kernels: ", Length[Kernels[]]],
  Print["Running in sequential mode (no parallel kernels available)"]
]
Print[]
Print["Starting evaluation..."]
startTime = AbsoluteTime[]
result1 = decide[testFormula]
elapsedParallel = AbsoluteTime[] - startTime
Print["Result: ", result1]
Print["Time elapsed: ", elapsedParallel, " seconds"]
Print[]

(* Run with parallelization disabled for comparison *)
Print["--- Running with PARALLELIZATION DISABLED ---"]
SetParallelization[False]
Print["Parallelization status: ", GetParallelization[]]
Print[]
Print["Starting evaluation..."]
startTime = AbsoluteTime[]
result2 = decide[testFormula]
elapsedSequential = AbsoluteTime[] - startTime
Print["Result: ", result2]
Print["Time elapsed: ", elapsedSequential, " seconds"]
Print[]

(* Compare results *)
Print["==============================================="]
Print["PERFORMANCE COMPARISON"]
Print["==============================================="]
Print["Parallel time:   ", elapsedParallel, " seconds"]
Print["Sequential time: ", elapsedSequential, " seconds"]
If[elapsedSequential > elapsedParallel,
  Print["Speedup: ", N[elapsedSequential/elapsedParallel], "x faster with parallelization"],
  Print["Note: Sequential was faster - parallelization overhead may exceed benefits for simple formulas"]
]
Print[]
Print["Results match: ", result1 === result2]
Print[]

(* Re-enable parallelization *)
SetParallelization[True]

Print["==============================================="]
Print["NOTES ON PARALLELIZATION BENEFITS"]
Print["==============================================="]
Print["Parallelization provides the most benefit for:"]
Print["  - Formulas with many disjuncts (satDisjunktion)"]
Print["  - Large numbers of literals (kparts K-pair formation)"]
Print["  - Multiple partial expressions in iteration"]
Print[]
Print["For very simple formulas, sequential processing may be"]
Print["faster due to parallel overhead. The implementation"]
Print["automatically uses sequential processing when there is"]
Print["insufficient work to parallelize effectively."]
Print[]

# QL - Universal Quantifier Elimination with Parallel Processing

This is a Mathematica package implementing a decider for First-Order Logic (FOL) formulas, originally developed by Dr. Timm Lampert and implemented by Michael Taktikos.

## New Feature: Parallelization

The package now includes parallel processing capabilities to significantly improve performance on multi-core systems when evaluating complex FOL formulas.

### Parallelized Operations

The following key operations have been enhanced with parallel processing:

1. **satDisjunktion**: Parallel evaluation of disjuncts in disjunctive normal forms
2. **kparts**: Parallel formation of K-pairs from positive and negative literals
3. **decideIterativerTeil**: Parallel processing of multiple partial expressions during iteration
4. **qe** and **em**: Parallel application of standardization to multiple results

### Usage

#### Enabling/Disabling Parallelization

By default, parallelization is enabled if the Mathematica parallel computing functionality is available. You can control it using:

```mathematica
(* Check current parallelization status *)
GetParallelization[]

(* Enable parallelization *)
SetParallelization[True]

(* Disable parallelization (use sequential processing) *)
SetParallelization[False]
```

#### Basic Usage

```mathematica
(* Load the package *)
Get["ql.m"]

(* Set the print level for proof steps *)
printproofstepslevel = 2;

(* Decide if a formula is satisfiable *)
result = decide[alle[{x}, ein[{y}, p[x, y]]]]
```

### Performance Considerations

- Parallelization provides the most benefit for:
  - Formulas with multiple disjuncts that can be evaluated independently
  - Large numbers of literals requiring K-pair formation
  - Multiple partial expressions during iterative evaluation
  
- For simple formulas, the overhead of parallel processing may exceed the benefits. The implementation automatically falls back to sequential processing when there is insufficient work to parallelize.

- The number of parallel kernels used depends on your system's CPU cores. Mathematica automatically manages kernel allocation.

### Example

See `test_parallel.m` for example usage demonstrating both parallel and sequential modes.

```mathematica
(* Load and run tests *)
Get["test_parallel.m"]
```

### Technical Details

The parallelization uses Mathematica's `Parallel` package features:
- `ParallelTable` for independent iterations
- `ParallelMap` for applying functions to list elements
- Automatic distribution of definitions to parallel kernels

When parallelization is enabled:
- Kernels are launched automatically on first use
- All necessary function definitions are distributed to parallel kernels
- Parallel operations maintain the same semantics as sequential versions

### Original Copyright

- :Copyright 2009, 2011 Dr. Timm Lampert
- :Implemented by Michael Taktikos

### Acknowledgments

Thanks to Dr. Karsten Mueller for giving important ideas in general programming, and to Mrs. Lampert and Mrs. Taktikos for their patience.

# Fixed-denominator streaming tensor and finite-jet heights

Implemented only the authorized new module `RiemannGaussian/SemiprimeStreamingTensorHeight.lean`; existing evaluator and external build were untouched.

Strict build PASS using absolute `/home/dbsanfte/.elan/bin/lake env lean -DautoImplicit=false -DwarningAsError=true`, isolated output `SemiprimeStreamingTensorHeight.olean` and `height-build.log` in this scratch directory. All twelve final theorem axiom reports contain exactly `propext, Classical.choice, Quot.sound`; no `sorryAx`, custom axiom or native decision procedure.

## Actual evaluator identities

`numerator d` follows the original evaluator's branches, replacing rational weights `1-x/d,x/d` by integer weights `d-x,x`. `numerator_cast` proves its rational embedding is exactly `d^w * evaluate(T,x/d)` for nonzero integer d. This is an equality about the existing recursive evaluator, not a supplied-value oracle.

`product_numerator_cast` and `sum_product_numerator_cast` prove that all assignment terms share denominator `d^(sum arities)`. Summing exponentially many assignments does not multiply their denominators. `abs_numerator_le` bounds local numerator by `(|d|+2B)^w` for Boolean/absolute-value-at-most-one entries and port numerators bounded by B. `abs_sum_product_numerator_le` gives whole finite assignment-sum height at most `card(X)*(|d|+2B)^(sum arities)`.

## Genuine polynomial / jet lift

`polynomialNumerator` is the same branch recursion on integer polynomials. `eval_polynomialNumerator` specializes it to the integer evaluator. More strongly, `polynomialNumerator_map` proves the entire rational polynomial identity:

`map_Q polynomialNumerator = C(d^w) * evaluate(C T, C(1/d)*map_Q portNumerators)`.

Thus d^w is a common denominator for every polynomial coefficient, before truncation, and hence for every finite jet.

`abs_coeff_mul_le` proves the actual convolution estimate: if all retained coefficients of p and q have absolute bounds B and C, then coefficient k<M of pq has absolute value at most M*B*C. No hypothesis about high unretained coefficients or global polynomial degree is needed.

`abs_coeff_polynomialNumerator_le` then proves, for every k<M,

`|coeff_k polynomialNumerator| <= [M*(|d|+2B)]^w`

when all retained port coefficients have absolute value at most B and all local entries at most 1. This is a finite-coefficient bound, not an informal substitution of a scalar norm for a jet norm. It adds only `O(w*(log M + log(|d|+2B)))` numerator bits. Coefficients at and above M cannot flow down to lower coefficients under the additions and products used here.

## Scope and remaining boundary

The module discharges exact common-denominator and local/global retained-coefficient-height obligations. The final global polynomial theorem below uses the conservative factor `M^(card factors)`, covering empty products as well. The scalar global sum/product estimate is also formalized. Denominators remain shared across assignments.

Still separate: conversion of the proved coefficient bounds into the implementation's bit costs; the actual row-construction coefficient bound; assignment/summary-loop cardinalities; the low-space truncated-polynomial implementation; entry-oracle runtime/workspace; and composition into a primitive-machine theorem. `polynomialNumerator` uses Mathlib's noncomputable polynomial representation for algebraic verification, so it is not itself asserted to be the compiled streaming jet machine. These are remaining compiler/resource obligations rather than hidden exponent gains or claims of a finished factoring algorithm.

## Global polynomial accumulator completion

The previous remaining *global polynomial* estimate is now formalized, not just explained:

* `abs_coeff_prod_le`: finite product jet bound `M^(card factors) * product heights`, valid for M>=1 and including empty products.
* `sum_product_polynomialNumerator_map`: full polynomial assignment accumulator has the exact shared denominator `d^(sum arities)` after rational embedding.
* `abs_coeff_sum_product_polynomialNumerator_le`: with integer assignment weights of absolute value at most 1, every retained coefficient k<M is bounded by
  `card(assignments) * M^(card factors) * [M*(|d|+2B)]^(sum arities)`.
  Thus signed Möbius sums are covered by the same theorem. No total truth-table or assignment list appears in these height bounds.

Standard copyright and module documentation added. Strict module compilation again PASS, now writing the repository build artifact `.lake/build/lib/lean/RiemannGaussian/SemiprimeStreamingTensorHeight.olean` and copying the identical artifact to this scratch directory. All twelve printed theorem axiom reports are standard only. The module source remains the sole repository file edited by this agent.

These theorems complete the algebraic accumulator denominator/retained-coefficient growth piece. The actual list/array truncated-jet compiler and its operation/space bounds, plus construction-specific input coefficient heights and the complete machine composition, remain separate.

Root-import audit PASS: `height-root-audit.lean` imports existing `RiemannGaussian` plus this module, runs `#lint- in RiemannGaussian.SemiprimeStreamingTensorHeight`, and audits both final global theorem axioms. Strict Lean exits 0 with silent lint and standard-only axiom output (`height-root-audit.log`). This was a scoped check, not a broad project build.

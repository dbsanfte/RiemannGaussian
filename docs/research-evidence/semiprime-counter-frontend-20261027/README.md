# Executed coefficient-to-count frontend

Status: **PROGRESS; the whole-family guaranteed factoring bit-time theorem remains open.** This slice advances the shared-summary route from the ETH paper. It does not improve the older native long-residue query's soft-K^(5/4) acquisition bound.

The user's Lean-source lead is confirmed by the pinned [fixed-width counting/SAT machine theorem](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/Final.lean). That endpoint and its source closure were already independently audited in the preceding work. Its fixed-width interface does not itself give a growing-scope factoring machine, and no new external rebuild is claimed here.

## What changes

The new coefficient-to-count program computes the missing intermediate values: representative searches, local corrected inputs, local truth interpolation, group products, forced measurement fibres, all summary labels, signed support sums, and Hermite scalar recovery. Its runtime inputs are source row coefficient arrays, an indexed native row design, and paid local Boolean entry evaluators. No Taylor packet, whole-fibre value, group product or final count is supplied as an answer.

An executable caller check exposed a proof-only polynomial index leaking into the first count interface. The repaired interface uses `RuntimeDesign`, containing only finite dimensions, integer rows, ownership and a partition; native polynomials occur only in correctness theorems. The actual Lean evaluator now runs the complete coefficient-to-count path on diagnostic one-variable tables (counts 1, 2 and 0). These controls check executability, not asymptotic coverage.

`SemiprimeNodeArrayExecution.count_correct` identifies the executed scalar with the original Boolean contraction, using source coefficient correctness, row-degree/restoration bounds, native design certificates and sufficient Hermite precision. The design and source coefficient acquisition are separate inputs, so this is a genuine execution composition but not yet an original-integer-to-factor machine theorem.

The row design also has a computed route. The new selector performs finite rational elimination, records ORIGINAL integer row indices, proves their span/independence and exact rank cardinality, and provides an actual rational span test. A tracked implementation returns exactly the same state with at most `8*m*(n+1)^2` rational arithmetic calls and `m*n` pivot tests. Its completed-row and scratch bit-height argument is [reviewed separately](row-height-cost.md); it is not yet a Lean primitive-bit clock.

Explicit source enumerations and finite mixed-radix decoding remove earlier chosen-enumeration interfaces. Summary tuples are decoded one at a time. Source alphabets of sizes r^Q and r^(2Q) really are materialized; they are polynomial under the scheduled parameter bound, not for arbitrary r,Q.

## Work and storage scope

The composed acquisition ledger retains the previously proposed envelope

`poly(public dimensions) * Cq * Y * 2^H * 2^W`,

where Cq is the complete bounded signed-support menu, Y the full summary box, H the largest local group and W the largest factor scope. Group searches contribute a sum of local exponential scans, never a Cartesian enumeration of all original assignments. Hermite recovery adds Q node acquisitions and polynomial reconstruction work. No full Y-sized summary table or all-assignment table is retained.

The ledger counts actual rational/integer scalar operations, declared entry work, coefficient reads and selected branch/allocation charges. It does **not** yet count every concrete encoding operation: mixed-radix division, finite-set manipulation, function-encoded indexing, row/design generation and physical rational bits require their own attachment. Independent [controller](review-controller-execution.md), [enumeration/design](review-enumeration-design.md), and [acquired-counter](review-acquired-counter.md) reviews distinguish these costs. A polynomial-overhead simulation is constructively supported; an exact primitive-step identity is not asserted.

With the preceding scheduled parameter/height argument, this remains a candidate N^o(1) route. Its new accomplishment is closing the supplied-H execution gap at the coefficient-array interface, not establishing the final asymptotic factoring guarantee. See [the remaining frontier](research-frontier.md).

## Verification

The packet records strict compilation, ordinary-root scoped 15-linter checks and transitive axiom checks for every generated declaration in the new modules. Exact counts, source/object hashes and preservation results are in `verification.json`; `manifest.json` seals the packet. Existing frozen files and concurrent work are preserved. No commit or push is performed in this slice.

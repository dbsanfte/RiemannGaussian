# Actual selector prefix heights

NEW `RiemannGaussian/SemiprimeMaterializedSelectionHeight.lean`; old selector/tracked/runtime sources untouched.

## Closed result

For the ACTUAL frozen `SemiprimeRowSelectionExecution.run C ids`, for EVERY input list/prefix (including repeats, all-zero input, empty input, rank zero), if each original integer coefficient satisfies `|C j v| <= 2^bits`, then EVERY stored rational entry has

    numerator.natAbs <= 2^[n*(n+bits)],
    denominator     <= 2^[n*(n+bits)].

This is `state_binary_bounds`; no minor, inverse, selected basis, rational-representation relation or desired height is supplied as a premise. `n` is the original column count. Thus the canonical stored rational binary widths are at most n(n+bits)+1.

## Proof through actual state

`selectedMatrix` contains the literal original rows in the actual selected-ID list. `pivotEquiv` only reindexes these by the actual active pivot columns; it is proof-only bookkeeping, not a second basis selection or executable inverse. `pivotMatrix` is the corresponding ORIGINAL INTEGER minor.

Existing exact run invariants prove selected-row span, rank/cardinality, and normalized active pivots. The new proof derives selected independence for every prefix, proves that active-coordinate evaluation is injective on the computed workspace (`zero_of_active_zero`), and proves the square pivot minor is nonsingular. This uses no assumed minor-answer theorem.

`workingMatrix` is the actual stored active matrix. `pivot_mul_working` derives A*T=S by exact workspace membership and identity pivot coordinates. `working_cramer` then applies the adjugate identity. Integer-cast compatibility proves `working_integer_ratio`: every actual entry is the ratio of an integer replaced-column determinant and ONE common nonzero pivot determinant. Both determinant matrices use original input entries only.

Leibniz determinant bound yields canonical numerator/denominator <= r!*height^r; reducing the rational fraction cannot increase them. `minorBound_le_two_pow` derives the explicit binary envelope 2^[r(r+bits)] using r!<=r^r and r<=2^r. The actual rank r<=n, and inactive slots are literal zero. No exponential generic arithmetic-circuit bound is used.

## Execution and source join

The theorem applies immediately to the literal matrices constructed by RuntimeDesignAcquisition, once their existing input-integer-height bound is instantiated. It also applies to each recursive prefix of run, so it is not merely a final-output estimate. The existing RowSelectionTracked operation counts still describe the actual rational residual/normalize/back-update operations.

Not yet formalized here: binary bounds for every internal scalar temporary in the residual sum, normalization and back elimination, the creation-time rational arithmetic clock, source byte/word acquisition, and a complete primitive bit-runtime theorem. The minor relation supplies a common denominator for stored state; mathematically the finite sum of n terms then has polynomial binary height, and constant-length multiply/divide updates preserve polynomial height. Those remaining execution-prefix bounds need explicit connector theorems before a kernel whole-clock claim. This report does not label the state bound as a fully compiled bit selector.

## Gates

Strict ordinary Lean compile passed with autoImplicit=false/warningAsError=true. Ordinary root import plus all15 scoped linters passed. Every generated declaration audited:37 declarations/29 theorem constants, only propext/Classical.choice/Quot.sound transitively. No sorry/custom axioms. Logs: selection-build.log, selection-audit.log, SelectionHeightAudit.lean. Isolated build and hashes recorded separately.

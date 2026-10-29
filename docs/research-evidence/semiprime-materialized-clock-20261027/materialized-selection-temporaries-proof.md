# Actual RREF temporary heights and paid normalization

NEW `SemiprimeMaterializedSelectionTemporaries.lean`; Rate, SelectionHeight and all earlier modules remain unchanged.

## Closed scalar-temporary invariant

The module defines literal finite scalar expressions matching the actual frozen tracked residual recursion. `residualExpr_run` identifies the complete scalar operation data path with `sub (scalar row[v]) (sumRun ...)`, not merely its final algebraic answer. `residualExpr_value`, `normalizeExpr_value` and `updateExpr_value` identify the cached actual row/matrix values. Expression traces contain cached operands and every rational operation result, including every finite-sum suffix. Cached leaves do NOT recursively expand the entire earlier row history.

The canonical rational bounds are proved from tested integer fraction representations: multiplication/division multiply operand magnitude bounds; addition/subtraction add one bit; sign/reciprocal do not increase canonical magnitudes (the reciprocal-zero convention is handled). No arbitrary circuit-height assertion is assumed. An expression with bounded leaves has a bit exponent linear in its ACTUAL finite syntax count. Residual syntax has at most 4n+3 nodes, normalization3 and back-update at most5.

For original coefficients bounded by 2^b, let

    P = n(n+b), leaf=P+b,
    R = (leaf+1)(4n+3),
    N = 3(R+1), U=5(P+N+1),
    W = leaf+R+N+U+1.

All are explicit fixed polynomials. Existing SelectionHeight supplies the actual state bound P. The new theorems `residual_trace_bounds`, `normalize_trace_bounds`, `update_trace_bounds` then bound EVERY actual scalar temporary by2^R,2^N,2^U respectively. This includes both actual residual passes in insertRun and all branches of the back update. No nonzero future pivot or cancellation-dependent small output is used as advice. The corresponding `_trace_fits` theorems derive strict RationalBits.Fits at the single width W; output fit is not an input promise.

## Concrete bit execution closed locally

`normalizeWords` actually calls existing physical Boolean `executeOperation .inv` on the cached pivot words, then `.mul` on the cached residual coordinate and computed reciprocal. Its returned clock is the sum of those actual instruction clocks plus2. `normalizeWords_correct_cost` proves exact equality to the frozen tracked normalization cache, legality/physical width and clock <=40002(W+1)^3. The inputs are physical cached words with the usual value/Valid/Width refinement; no output-height or normalized answer is supplied. Reciprocal/output Fits are derived from the actual prefix invariant and temporary trace theorem. Existing RationalBits contracts already include raw Boolean arithmetic, GCD/reduction, full scans and fixed-width copying.

## Exact remaining scope

The module does NOT yet implement a full physical-word residual dot loop, back-elimination matrix loop, pivot zero-scan, selection ID list/control or whole-selector array cache. Nor does it construct physical encodings of all source integers/stored states or join them to `RuntimeDesignAcquisition.build`. The trace invariants now supply the previously missing local arithmetic widths. Existing RowSelectionTracked gives the rational-operation count, but multiplying that count by a bit-instruction cost is not labelled a compiled whole-selector clock without the actual word-loop refinement. Full source/prefix/factor whole-clock work remains separate.

## Gates and pins

Strict ordinary Lean compilation passed (autoImplicit=false, warningAsError=true). Ordinary-root audit: all15 linters,190 generated declarations/122 theorem constants, only propext/Classical.choice/Quot.sound transitively. Isolated strict object is byte-identical. Full logs and hash pins are in this scratch directory: temporary-build.log, temporary-audit.log, temporary-isolated.log, SelectionTemporaryAudit.lean, materialized-selection-temporary-pins.json. No numerical experiments or code tests were used to establish these symbolic invariants.

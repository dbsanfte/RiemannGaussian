# Actual public materialization rate

NEW source: `RiemannGaussian/SemiprimeMaterializedRate.lean`. No previous source or frozen packet was modified.

The module supplies the analytic half of the proposed materialized clock join. It proves no statement that an executed program's clock has this bound.

## Acquired components, not independent asymptotic assumptions

`budget d n` is the sum of the degree-d polynomial, the LITERAL `weightedCount n (cutoff n)` with the proved inclusive scheduled cutoff, the explicit scheduled summary envelope, the explicit head envelope, and the truth-table scope envelope exp(512 n^(3/4) log2).

The new proof `decay_zero` handles the exact integer ceiling-log expression `(clog2 lambda)^2/sqrt(lambda)`. `summary_subexponential` uses it for the actual source rank envelope. `eventually_head_le_summary` uses the proved inverse-floor group-count budget, without substituting a real group schedule. Support growth invokes the existing literal scheduled-support theorem. Arity invokes the proved growing-scope estimate. Summing five terms and absorbing the fixed factor proves `budget_subexponential`.

`public_summary_le` instantiates `public_summary_log_bound` for the ACTUAL source parameters/summary cardinality. `public_head_card_le` instantiates `builtLayout_head_bound` and the public packing guard, with original graph occurrence/scopes/incidence proved in the old modules. No separate small-summary/head premise is assumed. `actualBudget` uses literal finite summaryCount, literal original-coordinate head cardinality and literal public scopeBound; `actualBudget_le` dominates it by the numerical budget uniformly over all actual nodes/heads. The uniform component bounds also cover independent maxima of summaries and heads even when their maxima occur at different nodes. This module does not materialize those maxima.

## Fixed polynomial closure and original input

`fixed_polynomial_subexponential` allows ANY fixed natural powers d,a,k and fixed leading real C: `C*n^a*(budget d n)^k <= exp(epsilon*n)` eventually. Consequently polynomial bit widths, fixed-depth extra loops and fixed polynomial time simulations retain the rate once their actual clock ledger is bounded by this expression.

`public_size_atTop` is derived from the real compiler input-edge injection `L <= variableCount L`. `public_fixed_polynomial_subexponential` additionally uses `variableCount L <=6400L`, so no independent Theta-size assumption enters the formal statement.

`public_fixed_polynomial_subpower` instantiates at the ACTUAL natural input bit length N.size. The exact inequality `2^(N.size-1)<=N` gives `N.size*log2<=2logN` for N>=2. It yields every positive power N^epsilon. `public_fixed_polynomial_sixth` sets epsilon=1/6. The literal finite-resource counterparts `actual_fixed_polynomial_subpower` and `actual_fixed_polynomial_sixth` are uniform over the actual source guards, nodes and heads and require only the natural nonnegative leading constant when applying monotonicity.

## Limits of the conclusion

All results are numerical rate theorems. A complete execution proof still must construct source/data, justify coefficient heights and primitive bit operations, bound the actual controller's loops by a fixed polynomial in these resource sums, and account for recovery/fallback. This module does NOT import an arbitrary runtime bound as a hypothesis and does NOT claim that the mathematical budget is already an actual clock. Existing source/bit-height work can later discharge the execution join. The polynomial exponent is an arbitrary FIXED natural, never input-dependent.

## Verification

Strict ordinary Lean compilation with autoImplicit=false and warningAsError=true passed. Ordinary-root scoped audit ran all15 linters:35 total generated declarations/30 theorem constants, only propext/Classical.choice/Quot.sound transitively. No custom axiom or sorry. Full logs are `rate-build.log` and `rate-audit.log`; isolated build and hashes are recorded separately.

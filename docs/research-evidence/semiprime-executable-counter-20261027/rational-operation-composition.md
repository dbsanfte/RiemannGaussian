# Concrete composition of the rational-operation exponent

**The exponential factors compose to o(L), where L is the bit length of N.** This is a paper-level operation ledger for the actual source constructor and frozen streamed counter, supported by the cited finite Lean bounds; it is not yet a theorem relating the whole executed program to primitive bit time or space. In particular the summary-cardinality theorem alone is not described as a runtime theorem.

Put n=the actual Boolean edge count, M=2n, maximum local arity w, lambda=ceil(log2 n), nu=ceil(log2 lambda), and use the actual schedule

`r=floor(sqrt(lambda))/nu², Q=floor(lambda/(128nu)), R=4ceil(sqrt(lambda)), q=floor(2nR/Q), J=q+1`.

All estimates below are eventual estimates in the accepted strong-guard branch. The formal `eventually_public_executable_guards` supplies eventual acceptance at actual public graph sizes; this is not assumed for the small diagnostic fixtures.

## 1. Actual exponential loop factors

1. **Möbius pairs.** `SemiprimeCounterEnumeration.tracked_menu` gives exactly
   `Cq=sum_(j≤q) 2^j choose(n,j)` callbacks, at most `(n+1)Cq` traversal nodes, and depth n. The callback includes the sign. This charges all sub-support choices, not only `choose(n,j)`.
2. **Summary labels.** `SemiprimeScheduledCounter.actual_summary_log_bound` / `public_summary_log_bound` gives, at each of the Q actual nodes,
   `summaryCount <= 2^[48 n nu²/sqrt(lambda)]`.
   This applies to the whole selected integer summary box, not just attained signatures. The frozen counter actually uses each literal row's L1 range, which is no larger than the corresponding head-cardinality/source-height box. Its API's coarse `layout.D` does not force it to use that coarse radius for every coordinate: `measurement_vectors` receives the actual per-row bounds.
3. **Within each label.** The actual `separated_fibre_sum` scans each head group separately to find its first representative and to sum its fibre. At most a polynomial factor times `2^max_g |head_g|` assignments are inspected; it does **not** take the Cartesian product of all head-group assignments. The source head bound gives `max|head_g| <=3n/(2r)`. Multiplying the group subtotals costs polynomially many jet operations.
4. **Local callback.** Each local multilinear extension inspects `2^arity` Boolean entries, so all factors together cost at most `#factors * 2^w` times polynomial arithmetic in n,J,R,Q. The graph has polynomially many nonempty factors (indeed total incidence 2n bounds their number). Its actual empty-factor count is also polynomial. A generic network with arbitrarily many empty factors would need that extra input-size parameter.
5. **Interpolation and prefixes.** Q nodes, degree/jet arrays of width J, polynomial Hermite assembly, and L+1 prefix queries add polynomial factors. Cached inverse and multiplication are now attached quadratic rational-operation loops. Setup is reused across prefix queries; the counter algebra itself is rerun.

Thus a safe rational-operation envelope for one counter execution is

`poly(n) * Cq * 2^[48 n nu²/sqrt(lambda)] * 2^[3n/(2r)] * 2^w`.

It includes representative scans as well as fibre scans. Array/loop/index/allocation costs are not literally rational operations, but contribute polynomial control factors if separately implemented/charged; they are not silently set to zero in a bit-time assertion.

## 2. Explicit eventual cutoff arithmetic

For sufficiently large lambda, the floor bounds give

`Q >=lambda/(256nu), R<=8sqrt(lambda), r>=sqrt(lambda)/(2nu²)`.

Consequently `q <=4096 n nu/sqrt(lambda)`. Let `u=4096 n nu/sqrt(lambda)`. Eventually `0<u<=n` and q<=u. The newly proved finite entropy estimate gives

`Cq <=(q+1)(8n/u)^u`.

Since `8n/u<=8sqrt(lambda)<=8lambda`, one has

`log2 Cq <=log2(q+1)+16384 n nu²/sqrt(lambda)`

for nu>=1 (using log2(lambda)<=nu and `3+nu<=4nu`). Also `3n/(2r)<=3n nu²/sqrt(lambda)`. Combining these with the summary bound yields, for example,

`poly(n) * 2^[16435 n nu²/sqrt(lambda) + w]`.

The constant is deliberately loose and not asserted to be a new formal named theorem. The leading finite inequalities and the finite weighted entropy theorem are explicit; formalizing this short numerical assembly remains straightforward work, not a hidden new algorithmic hypothesis.

## 3. Construction is polynomial setup, not another exponential in n

The source universal dimension is `D=r^(2Q)`. `SemiprimeCounterRate.scheduled_dimension_square_le` proves `D²<=2 n^(1/64)` at n>1. Computed conditional expectations try `(n+#factors)r^Q` words and recompute polynomially many incidence/head terms. The literal subset expansion costs at most `3^(Q−1)` per universal input/node; since r>=2 this is bounded by a polynomial in D. Dense universal matrices, interpolation, complete buckets, owner sums and exact integer-row selection are all polynomially many arithmetic operations in n,D,Q,R. Temporary rational pivots do not change the selected measurement rows.

The source numerical width/height bound and preservation of actual integer measurement rows are essential here: arbitrary normalized rational row bases would not automatically preserve the summary-range exponent. This implementation avoids that replacement. The setup exponent is only O(log n) in base 2, hence absorbed by the polynomial prefactor.

## 4. Transfer to public input length

The public macro graph has `L<=n<=C L` for a fixed constant C and `w<=C' L^(3/4)`; the formal public parameters provide these size/arity bounds. Hence lambda=Theta(log L), nu=Theta(log log L), and

`n nu²/sqrt(lambda) = O(L (log log L)²/sqrt(log L)) = o(L)`,

while `w=O(L^(3/4))=o(L)`. Prefix recovery adds only a polynomial factor. Therefore the composed **rational-operation envelope** is `2^o(L)` (and eventually smaller than `2^(epsilon L)` for each fixed epsilon>0), including enumeration, local table expansion, head scans, summary boxes, and actual source construction.

`SemiprimeCounterRate.eventually_constant_polynomial_counter_with_arity_le` already formalizes the final analytic absorption for expressions `C*x^d*exp(A*x*rho(x)+B*x^(3/4))`, with rho tending to zero. It does not on its own assert that this expression counts the executed program; the preceding loop ledger is the needed concrete handoff.

The explicit trial-division branch is used only when the guard fails. Since guard acceptance is eventual, those inputs lie below a fixed finite threshold for the public graph family and do not change the asymptotic envelope; no practical threshold or fast finite fallback is claimed.

## 5. Remaining primitive execution bridge

The final JetArrayHeight extension proves polynomial numerator/denominator heights for actual cached inverse outputs, all inverse dot-prefix accumulators, and quotient outputs, **given normalized input common denominators/numerator bounds**. The source rows and actual Hermite packets must instantiate those hypotheses, and every global sum/product/shift plus partial convolution and interpolation accumulation needs its corresponding bounded-height attachment. Polynomial-bit rational operations, index/record access, closure/Finset construction, array allocation and callback verification must then be implemented and charged on the chosen primitive machine. The present result neither assumes a free rational oracle nor declares that full bridge completed.

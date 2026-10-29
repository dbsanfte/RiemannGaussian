# Computed row selection: scratch height and bit-cost audit

This note concerns the **new executed RREF selector**, not the old sorted selector's literal intermediate matrices. The source is `SemiprimeRowSelectionExecution.lean` and its actual paired arithmetic implementation `SemiprimeRowSelectionTracked.lean`. It is a constructive mathematical bit-complexity argument; the minor-height and final flat-tape simulation are not yet Lean machine/resource theorems.

## Actual algorithm and arithmetic work

Input is an explicitly enumerated m-by-n INTEGER matrix C, |C_jv|<=A, A>=1. The code processes its supplied index list from the tail. It caches every residual and completed matrix with Vector.ofFn. It tests the first nonzero residual coordinate by a finite exact rational scan. On a nonzero pivot it divides by that COMPUTED value, back-eliminates the new pivot from old working rows, and records the ORIGINAL integer-row index. Output measurement rows are never rescaled: rational values are scratch only.

The tracked implementation evaluates actual products/additions/subtractions/divisions and materializes each coordinate once; scalar results carry their operation counts. Its residual bound is n*(2n+1), normalization n, update 2n². It deliberately pays a SECOND residual evaluation in an accepted insertion, matching the original pure insertion instead of assuming free common-subexpression elimination. Hence the source proves <=8*(n+1)² rational arithmetic calls per row and <=8*m*(n+1)² for the full original input list. The tracked output equals the complete proved selector state, not merely its rank. Find-pivot uses at most n exact zero tests per candidate; active-column tests, coordinate reads/stores and finite-list operations are polynomial too.

## Why completed RREF rows have bounded minors

Let k be the current number of accepted original rows and P the k-by-k matrix of those ORIGINAL rows restricted to the active pivot columns, ordered in any fixed way. The proved invariants give: active working rows have Kronecker pivot coordinates; they span exactly the selected original rows; and both families have size k and are independent. Thus restriction to the active pivot coordinates is an isomorphism on this k-dimensional span, and P is nonsingular.

For active pivot c, the stored normalized working row has pivot restriction e_c. Its coefficients in the selected ORIGINAL row basis therefore solve lambda*P=e_c. Cramer's rule shows its v-coordinate is

`det(P with column c replaced by the original selected rows' v-column) / det(P)`.

Both determinants have order k and entries bounded by A. This establishes the minor formula for every COMPLETED working RREF row at the current state, including old rows after a new back-elimination. It does not incorrectly identify a partial scratch row with ordinary elimination on a reordered input.

With K=min(m,n), every such determinant has absolute value <=k!*A^k <=[K*(A+1)]^K (k=0 handled by determinant 1). Put

`H0 = 2 + K*(clog2(K+1)+clog2(A+1))`.

The signed numerator and nonzero denominator have <=H0 bits up to a fixed sign bit. Canonical rational reduction can only decrease their absolute numerator/denominator sizes. All active rows at a COMPLETED state admit the same signed denominator det(P), though their canonical reduced denominators can differ.

At creation, the new residual at v equals the bordered (k+1)-minor for v divided by det(P). Dividing by its nonzero pivot cancels the old common determinant. The new normalized row consequently has the next-stage minor bound H0. Back-elimination gives exactly the unique Kronecker-normalized basis for the enlarged pivot matrix, so completed updated old rows also return to that same bound.

## Partial scratch and primitive rational operations

Do NOT bound scratch just by the final stored-row minor size. A residual is computed as an integer input coordinate minus a partial sum of at most k terms `C_jc * basis_c(v)`. One conservative common denominator is the product of the k stored-row denominators, of <=k*H0 bits. Each magnitude is bounded by A*(1+k*2^H0), so the canonical partial numerator has O(k*H0+log(A+1)+log(k+1)) bits. This conservative bound avoids relying on cancellation in a particular sum order. The sharper shared-det(P) denominator is available but unnecessary.

For a rational test row whose coordinates have a known common denominator delta and numerator height Hinput, use delta times that product of basis denominators. This gives O(Hinput+k*(H0+1)) denominator/numerator bits (enlarging by another fixed Hinput term, if using a magnitude rather than a numerator-height convention, is still polynomial). Thus the same elimination supplies an exact paid `_in_span`-type test for the actual replacement rows with their proved source common denominator.

Each raw rational multiplication/subtraction/division before gcd normalization uses only a constant number of these bounded input numerators/denominators. For example, an updated basis coordinate is one old value minus one product of old/new normalized coordinates, so its raw pre-reduction height is <=3H0+O(1). Residual partial sums retain the stated common-denominator bound after each canonical normalization; a naive recurrence that repeatedly squares the height is not the actual invariant. The computed nonzero pivot is the only divisor; zero candidates are rejected before division.

Schoolbook integer multiplication and restoring division plus Euclidean gcd on these polynomial-bit integers give deterministic polynomial bit cost per rational arithmetic call. One may use the existing exact bit backend/canonical-reduction proofs rather than a unit-cost rational oracle. No factoring, unknown prime field, modular inverse, positivity of a PDE norm, or number-theoretic assumption is involved.

## Storage, column order and attachment

Cache materialization ensures later matrix reads do not recursively recompute earlier elimination formulas. The output rows are literal original indices; a live updated matrix uses O(n²) rational entries. Even if the functional active-column history retains prior states, at most m successful updates retain O((m+1)n²) matrix/history entries, alongside the input m*n integers, selected index list and polynomial stack/descriptor. No constant-time active-column lookup or immediate garbage collection is required for the polynomial bound. Flat binary lists with linear lookup suffice: matrix lookup and index arithmetic multiply the operation bound by another polynomial, not by an exponential. The algorithm therefore has polynomial bit time and space in m,n,log(A+1), and the test-row input height when relevant.

`selectedRowsWithColumns C columns` accepts an explicit finite column equivalence; it does not use Fintype.equivFin choice. The actual source constraints already have Fin(rowCount) row indices. The enumerated-layout adapter obtains its head-column equivalence by filtering the supplied original variable enumeration (the separate MixedRadix.filtered helper), and may pass it directly to this selector. The returned structure proves literal original-row injection, full rational span and exact rowRank cardinal; existing kernel-locality and summary-size theorems then apply to these COMPUTED selected rows. The old Classical.choice selector is not assumed equal as a list of indices—only the required semantic certificate is replaced.

The remaining formal resource attachment is the minor/scratch bit-height proof and a machine interpretation of the paired rational operation/control program. The new Lean proofs close computed selection/span/rank/independence and the actual rational-operation count, not the whole counter's final runtime theorem.

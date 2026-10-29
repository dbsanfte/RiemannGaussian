# Independent integration review: exact counter and factor wrapper

26 October 2026. **PASS for the actual Boolean macro-FFT input family at the mathematical algorithm/ordinary bit-complexity level.** No source edits were made in this review. This is not a completed Lean end-to-end runtime theorem or primitive-machine compilation.

Reviewed current `shared_parameters.py`, `factor_solver.py`, `test_parameters_solver.py`, `shared_counter.py`, and `resource-derivation.md`, using the independently audited factor-network correctness and constructive Section 4 layout as baseline. The wrapper now explicitly calls `count(..., validate_design=True, require_quantitative=True)`.

## 1. Parameter choice and finite fallback

`ceil_log2` and integer-square-root arithmetic implement the stated r,Q,R schedule without floating-point approximation. The interval uses the single floor

`A0=(Q*(r-1)-r*(R-1)) // (2*r)`.

`scope_statistics` examines actual port scopes, rejects duplicate ports/invalid indices, and computes actual maximum scope and occurrence. The factor wrapper insists on M=2n and occurrence exactly two. It does not substitute the bounded width of the original SAT application for the actual macro-FFT scope width.

`binomial_tail` uses the exact recurrence for `comb(Q,k)*(r-1)^k*(r+1)^(Q-k)`. Each recurrence division is exact; the routine checks the total numerator equals `(2r)^Q`. Its fraction comparison is precisely tail <=1/(tau_denominator*r*b). Zero-range and invalid interval inputs cannot accidentally pass. The schedule also checks R>=32 and 6R<=Q before using the asymptotic branch.

The resource derivation correctly avoids invoking Lemma 4.8 under its original polylog-scope premise. Instead, it verifies Lemma 4.7's numerical hypotheses for the actual w<=C n^(3/4). With D^2=O(n^(1/64)), the first balance term is O(n^(49/64))=o(n); the group balance is polylogarithmic. R^2/(8Q)>=256nu and the centered interval eventually justify the exact tail threshold. For fixed network constants, only finitely many input lengths fail.

On failure the production wrapper really calls exact divisor scanning, including correct handling of even N, squares and primes, and explicitly returns its fallback method. There is no diagnostic-counter shortcut in the accepted branch. The finite fallback costs exponential time in bit length but polynomial space; because n=Theta(L) and the failed-length set is finite, it can be absorbed in a single asymptotic multiplicative constant. This is a mathematical eventual bound, not a practical or numerically demonstrated threshold.

## 2. Prefix recovery

`recover_from_counter` performs one initial exact count and one zero-child count for each of P's original L bits. It keeps the positive parent count. If the zero child is empty, the one child has the entire parent count by an actual partition of the same assignments. Otherwise it replaces the parent count by the positive zero count. The final P is checked to be a proper divisor.

Restrictions modify existing vertex predicates and preserve all variables, port scopes and factor indexing. Therefore one constructed layout remains valid for all queries; no new design or independent internal assignments are introduced. The uniqueness of the original network's internal extension is essential and was already audited. Negative/nonintegral or out-of-parent counter answers are rejected, not coerced. Tests' divisor-enumeration callback is explicitly diagnostic and is never used by `factor`'s accepted branch.

## 3. Counter algebra

The counter constructs the actual multilinear extension by streaming all Boolean assignments on a scope. It does not apply the Boolean entry predicate to non-Boolean jet values. Scope size w is fully charged as 2^w local calls.

At node t, its input jet is exactly

`P_fv(t) dot x + (P_fv(t+z)-P_fv(t)) dot 1_U`.

The perturbation has zero constant term. Truncating at J=q+1 allows the finite Boolean Möbius expansion over |E|<=min(q,n), U subset E, sign `(-1)^(|E|-|U|)`, with x_i=1 enforced for i in E. Each perturbation occurrence contributes positive z degree, so discarded terms cannot affect the retained coefficients. The code uses the actual unsigned scopes to bound total multilinear degree M, chooses q=floor(MR/Q), and has QJ>MR; overestimating the implemented row degree R-1 by R is safe.

For each measurement tuple, it finds one unforced representative in every group. This is correct: the kernel condition makes every factor assigned to one group invariant under changing any other group's assignment within the same measurement fibre, including after adding the fixed U correction. Forced E bits are imposed only while summing the corresponding group, not while selecting the arbitrary representatives. Each active group is reset to its representative after its subtotal, so later groups are evaluated against a consistent reference assignment. Empty-scope factors are evaluated once in their assigned group and are not lost.

The exact rational row-space validator checks restoration, degree, integer measurement ranges, partitions and kernel invariance. Quantitative conditions are additionally enforced on the production path. It is not an oracle supplying fibre counts or unknown row kernels.

The Hermite implementation forms `L_t(T)=prod_(s!=t)((T-s)/(t-s))^J`, computes the truncated inverse of `L_t(t+z)` (constant one), multiplies it by H_t(z), evaluates that quotient at z=-t, and multiplies by L_t(0). Summing these contributions is the ordinary finite CRT/Hermite recovery of H(0), since deg H<QJ. Signs, powers of differences and normalization are correct. All divisions are by explicit nonzero rational scalars; there is no finite-field inversion or modular nonunit branch hidden here.

## 4. Actual space and bit complexity

The resource derivation's fixed-denominator argument applies to the production **0/1 local entries**. All layout coefficients have denominator dividing delta=(R-1)!Q!. A scope extension has denominator dividing delta^w_f. Partial group products have denominator delta to their accumulated port count, and complete contributions share delta^M. Signed sums of exponentially many contributions do not multiply one fresh denominator per term. The norm bound `(delta+2B)^w_f` follows by summing the absolute multilinear basis products, and partial sums obey the same bound. The stated compiled alternative J^(M+|F|) coefficient bound is also polynomial in bits.

Reduced Fraction operations may transiently form products of two already polynomial-bit denominators; this remains polynomial, and every retained result again has the fixed-denominator divisibility. Möbius and measurement sums add only the logarithm of their number of terms to the numerator height. The Hermite inverse's negative-binomial expansion, or confluent Vandermonde minor bounds, gives polynomial-bit coefficients in Q,J; the implementation uses the same exact scalar operations. Thus ordinary integer arithmetic can be charged polynomial bit cost per recorded operation.

`boolean_vectors`, `measurement_vectors`, and combinations stream their states. The code retains only polynomial-size design data, current E/U, one representative per group, one current full assignment, current measurement coordinates, polynomial-size form/jet data, and Q Taylor jets. It stores no truth tables, fibre lists, or exponential list of Möbius terms. Instrumentation keeps fixed many counters whose bit lengths are logarithms of executed work. The 2^w local enumeration is time, not storage.

The loops give the stated bound

`poly(n+description) * 2^[O(n*(R/Q)*log(2Q/R)+n*tau*log(2D+1)+n/r)+O(w)]`.

For accepted scheduled network inputs this is `poly(L)*2^O(L*(log log L)^2/sqrt(log L))`, with polynomial ordinary bit space, including polynomially many prefix calls. Layout creation and rational rank validation are polynomial overhead, not uncharged preprocessing.

**Scope qualification:** the generic Python API permits arbitrary rational entry callbacks. Polynomial bit space for *every* such callback does not follow merely from a polynomial per-entry bit bound: exponentially many unrelated denominators can have an exponentially large lcm. The actual factor wrapper has 0/1 entries, so this issue does not affect its theorem. More general resource claims require a supplied common polynomial-bit denominator (and bounded entry heights). `resource-derivation.md` correctly states the Boolean input contract.

## 5. Independent execution and formal boundary

Replayed all nine `test_parameters_solver.py` tests: PASS. The ninth test executes the actual production adapter and shared counter on an explicitly described tiny direct-multiplication network, then performs live prefix recovery. Its constant replacement rows give q=0; the other group is fully measured, both quantitative promises pass, and no diagnostic counting callback is used. It tests adapter/composition correctness, not accepted-schedule macro-FFT performance. Additional independent exact controls are saved in `independent-counter-controls.json`: three variables, genuinely T-dependent replacement forms, two nonlinear scopes, and a rational factor give count 3, agreeing with a separate direct Boolean sum. Independent polynomial Taylor samples recover both expected constants through Hermite interpolation. These tests are small algebra checks, not rate evidence or factor-search experiments.

The compiled Lean height module and existing fixed-width SAT theorem do not by themselves identify this Python execution, its scope-dependent layout, the generic Möbius/Hermite counter, or its prefix wrapper with a kernel-checked primitive machine. The packet explicitly retains that integration obligation. This review finds no additional all-input correctness, Boolean/canonical/carry, fallback, or ordinary bit-space gap in the reviewed production path; it does not close that remaining formal obligation.


## Final source checkpoint

Counter author declared `shared_counter.py` stable. Re-read its exact-entry type checks and explicit rational-resource qualification; these preserve the reviewed algebra. Replayed all 10 counter-specific tests in addition to the nine wrapper tests: PASS. `review-source-hashes.json` records SHA-256 and byte length for the final reviewed Python implementation/tests and resource derivation. The live-adapter test uses the real counter and production adapter, with a small labeled direct-multiplication network; it makes no accepted-schedule or runtime claim.

Final documentation precision: reviewed the compiled coefficientwise factor J^(M+|F|), replacing J^M. Its logarithm is (M+|F|)log J, polynomial for the actual explicit network; the algorithm-level bound and disposition are unchanged. Refreshed only the resource-derivation source hash and verified all eight Python hashes remain unchanged.

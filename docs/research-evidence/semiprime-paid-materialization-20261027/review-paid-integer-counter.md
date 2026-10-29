# Independent audit: actual paid integer counter

## Verdict

PASS for the mathematical algorithm and its fixed-polynomial materialization bound, under the acquired valid source-layout contract. No code correction was required. I read the complete new `paid_integer_counter.py`, its seven tests, the actual pinned `source_layout.py`/`source_parameters.py`/`source_factor_search.py`, and the pinned reference counter and prefix wrapper. Replayed the seven tests: all pass. These are algebra/control tests, not an asymptotic or semiprime-success campaign.

## Exact data path

Each original predicate is called exactly once for every local Boolean word, so original calls are sum_f 2^w_f <=F*2^w. The little-endian tensor reduction pairs truth-table entries at bit0 first, then bit1, etc.; its complement is Delta-P, and its declared denominator degree increases by exactly one per actual port. Zero-arity factors retain degree0. Every group product has degree equal to its assigned port incidence; all groups together have degree exactly M. Zero subtotals and full accumulators are allocated at those degrees, so addition never silently mixes denominators. The common source denominator is acquired from the finite actual coefficient list by LCM; scaling by it is exact.

At a sample node, the shifted arrays contain the integer coefficients of Delta*P(t+z). The port constant uses the actual current Boolean x; its positive coefficients are the sum over U, exactly the Boolean diagonal substitution. Forced-one filtering uses S (the outer support), while the correction uses U subset S; the sign is (-1)^(|S|-|U|). This matches the reference formula.

For each group the program materializes all its Boolean words, keyed by the exact INTEGER measurement vector. It iterates the Cartesian product of ATTAINED measurement keys, not the Cartesian product of group words. This is a subset of the full joint summary box, hence <=Y. It uses the first word in each unforced fibre as the other-groups representative, processes the current group's words, then resets that group to its representative. The original invariance theorem is exactly what permits that representative substitution. Empty groups have the single empty word, so empty/zero-arity cases remain well-defined.

The final packets are decoded only once per node from the homogeneous denominator Delta^M. Rational Hermite recovery calls the pinned exact routine with known distinct integer sample nodes and precision J=floor(MR/Q)+1. There is no direct-count diagnostic or full n-bit assignment enumeration anywhere in this execution path.

## Source-specific bit-loop accounting

The actual source is the complete-block/cleared-defect source, not the older spectral constructor. Its D=r^(2Q) universal dimension controls source setup; the counter measurement radius is separately n*B*2*(8Q)^(2R), and selected rows are original integer rows. Full summary box cardinality Y must use this latter radius (or the exact attained ranges).

Source words are acquired by a fixed-depth conditional-expectation calculation depending on at most four word labels per score term. Universal subset/swap expansion costs <=3^Q<=D per entry. Interpolation degrees are O(Q+R), and all source matrices have polynomial-in-S dimensions. Actual cached/lazy Python dictionaries can be simulated by linear scans at a fixed polynomial overhead. No source stage enumerates A^(n+F) label assignments.

The pinned source currently uses rational Gaussian elimination, not Bareiss. It nevertheless has polynomial bit complexity: clear the polynomial-size input coefficient denominators once; each successive echelon reduction is a Schur-complement/elimination prefix relative to a nonsingular pivot minor, so its retained entries are ratios of minors of the original integer matrix (with appropriate row/column permutation). Normalizing a pivot or forming the next subtraction uses products/differences of such polynomial-height quantities. The partial reduced row after any prefix of basis rows has the same interpretation. Hadamard bounds therefore give polynomial bit lengths throughout, including the exact R-by-R binomial solve. This verifies the ACTUAL rational implementation; it does not pretend that it already runs the report's optional Bareiss alternative.

The acquired coefficient list has polynomially many polynomial-bit entries, so even its denominator PRODUCT (and hence its LCM) has polynomial bit length. Powers through Delta^M likewise have polynomial bit length. Counter numerators are sums of products of at most M corrected-port coefficients; the number of summands contributes only logCq+logY+O(n+M logJ) bits. Actual multiplication/addition temporaries have the corresponding doubled/additive bounds. Tensor interpolation evaluates Boolean truth entries only, avoiding the arbitrary-rational-callback LCM failure. Hermite inverse recurrence is on a local polynomial of constant1, so its coefficients have polynomial-height negative-binomial/common-denominator bounds.

Consequently the actual finite loops use

    S^O(1) * (1+Cq*Y*2^(h+w))^O(1)

ordinary exact bit operations, with fixed exponents, when S includes public/source dimensions and the local polynomial entry-check cost. Source setup, LCM/gcd, row elimination, list allocation, copying and lookup are included by fixed-polynomial bounds; the diagnostic Meter is not the proof of this assertion. Its maximum recorded bit size does not observe every multiplication inside Python builtins, source setup, or Hermite; this is harmless because the independent prefix-height proof covers those operations.

## N-only wrapper and remaining scope

`factor(N)` loads exact pinned source and compiler files, acquires the actual graph and unchanged scopes, checks the exact scheduled source guard, and constructs the source internally. There is no layout/count/order oracle or optional runtime cap. Guard failure goes to the explicitly labelled finite-size trial division branch. The accepted branch reuses the acquired layout for all prefix queries and verifies scopes remain literally identical. Rebuilding the cached truth tables per query costs only the input-bitlength+1 multiplier. Integer/nonnegative recovered counts are checked before prefix recovery; the inherited false-first routine preserves a positive parent branch and verifies the final proper divisor.

The fast accepted branch remains conditional on the actual public schedule passing, with eventual validity supplied by the existing size/rank/guard proof, not by these small tests. The wrapper's finite smoke exercises fallback only. This audit proves no end-to-end Lean primitive-machine clock, and the implementation docstrings correctly avoid that claim. It also does not claim the materialized path retains polynomial space.

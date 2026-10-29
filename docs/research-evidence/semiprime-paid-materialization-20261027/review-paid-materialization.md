# Independent time-only materialization audit

## Verdict

The concrete rational algorithms support the constructive mathematical bit-time bound

    S^O(1) * (1 + Cq * Y * 2^(h+w))^O(1),

with a FIXED exponent, provided S includes the public descriptor, auxiliary/source dimensions, jet precision and polynomial coefficient-height bounds; h is maximum group size, w maximum factor scope, Cq=sum_(s<=q)2^s binom(n,s), and Y bounds the full joint measurement-value enumeration. This is an ordinary exact bit-algorithm conclusion, not a kernel theorem about a compiled Turing-machine clock. It applies to Boolean local predicates with a polynomial-time actual entry checker. Arbitrary rational callbacks need an additional common-denominator contract and are not covered merely by a per-entry bit bound.

## Concrete loops checked

I inspected `/tmp/semiprime-executable-counter-20261027/source_layout.py` and `source_parameters.py`, and `/tmp/semiprime-counter-20261026/shared_counter.py` and `factor_solver.py`. The source algorithm constructs whole words of size r^Q, pairs of words D=r^(2Q), conditional scores, numerator differences, interpolation rows, complete blocks, leftovers, and rational row elimination. These are fixed-nesting polynomial work in S, not enumeration of all n-bit assignments. Difference expansion has sum_j binom(Q-1,j)2^j <=3^Q <=D for r>=2. Cached/lazy dictionary lookups can be replaced by linear scans and repeated polynomially sized constructions without changing the form of the bound.

The counter has exactly the following large loops: Q nodes; Cq Boolean Möbius pairs; Y joint measurement values; group representative/fibre scans of at most r*2^h assignments; factor extension scans of at most 2^w truth entries. The inner product of group subtotals does NOT enumerate the Cartesian product of all group assignments. `direct_count` does enumerate 2^n but is a separate diagnostic and is not invoked by `count`. Materializing these existing finite loops instead of streaming them is allowed by the stated time-only bound, even though it can lose polynomial space.

The current complete-block source uses measurement radius

    D_measure <= max(1,n*B*2*(8Q)^(2R)),

not the auxiliary dimension r^(2Q). Consequently use Y=product_rows(2*L1radius+1), or the upper bound (2D_measure+1)^c, c<=2 epsilon M. This distinction matters quantitatively. Under the displayed schedule, log D_measure=O(log n+R log Q), h<=3n/(2r), and epsilon=1/(r ceil_log2 n); hence log Y=O(n/r), including the R log Q term. Together with log Cq=O(n(R/Q)log(2Q/R)) and w=O(n^(3/4)), all large factors remain 2^o(n). Source guard checks are exact integer/rational operations on polynomial-bit inputs.

## Rational-height check

No exponential least-common-multiple issue arises for Boolean truth entries. All acquired source coefficients are a finite polynomial-size list of rational numbers, so the product of their denominators is a polynomial-bit common denominator Delta (even a loose product bound suffices). Source elimination scratch height is controlled by minors of polynomial-dimensional integer matrices after clearing denominators; choosing original integer constraint rows does not import normalized scratch fractions into measurements.

After shifting at integer nodes and applying Boolean Möbius corrections, each input jet has denominator dividing Delta and polynomial-bit numerator coefficient bounds. A factor uses each port once, so every partial factor product has denominator dividing Delta^w_f; every partial group/full product divides Delta^M. Summing assignments, measurements and Möbius terms preserves that same denominator. Numerator magnitudes acquire only logarithms of their numbers of summands: O(log Cq+log Y+n) plus polynomial source/degree terms. Reduced Fraction additions temporarily double the bit bound at most before reduction. There is no multiplication of all previous accumulated denominators over the enumeration length.

Hermite recovery uses only nonzero integer node differences. Its normalized local polynomial has constant coefficient one; truncated inverse coefficients have polynomial bit size via the negative-binomial expansion, or the confluent Vandermonde minor bound. Precision J and Q are polynomial. Thus all executed rational operations have polynomial bit cost in S. There is no positivity or finite-field division assumption in this rational algorithm.

## Recovery, limits and formal scope

False-first prefix recovery makes at most input-bitlength+1 exact count calls. It restricts existing predicates, preserving scopes, occurrence two, the layout, and Boolean-valuedness. It maintains one positive parent branch rather than combining inconsistent witnesses. Final integer division is checked. Public input/guard/precision bits and exact source generation must be included in S; they are not free advice. The finite guard-failure branch is an explicit divisor scan, whose eventual asymptotic absorption requires the proved eventual guard for this actual network family.

The route therefore has a constructive paper-level bit-runtime proof once the scheduled source and network hypotheses are supplied. It does NOT follow merely from an abstract Lean function's termination, nor does it certify a full original-OAI machine compiler. Existing semantic source-to-count and prefix-height theorems justify mathematical values and common-height invariants; they do not themselves add an actual machine clock to the Python implementation. No uniform sharp polynomial exponent is asserted here.

## Direct review of the companion proposal

Final reread: PASS. The companion report removed all unproved numerical polynomial envelopes and now asserts only the justified fixed-polynomial conclusion S^O(1). Its actual rational elimination ledger, finite-source LCM, independent-group evaluation, fixed-denominator packets, Hermite denominators, and prefix recovery agree with this audit and the new paid integer implementation. The attained-key and streamed-support wording distinguishes the literal code from optional equivalent materialization; either retains the same bound. No correction request remains on mathematics or runtime scope. Source/program refinement remains unproved as a complete kernel machine-clock theorem.

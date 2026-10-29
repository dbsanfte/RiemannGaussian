# Independent semantic review: actual source and Taylor heights

**PASS.** Final strict/audit logs observed: SourceRowHeight 92 declarations/84 theorem constants; TaylorHeight 13 declarations/12 theorem constants, standard axioms only. This is an independent semantic review, not a replacement compiler audit. Reviewed source hashes are recorded separately.

## One denominator for actual rows

`Clears d p` means the entire polynomial `C(d)*p` lies in the image of integer polynomials. The common denominator is

`rowDenominator(Q,R)=2^(R−1)*(Q!)^(Q+1)`.

The factorial power is coarse but valid. Every nonzero integer sample node/difference denominator has absolute value at most Q and divides Q!; products over at most Q sample factors are cleared by the common factorial power. The denominator does **not** multiply once per universal row, owner, incidence or coefficient. Finite sums preserve one d. The spectral prescription contributes only the one shared power of two.

`sourceRow_clears` applies this to the actual scaled integer-matrix prescriptions and mismatch interpolation. `assembled_row_clears` handles complete copies and identity leftovers; `pullback_row_clears` preserves d through literal owner sums. Thus `builtLayout_row_clears` concerns the actual searched-packing/universal/complete-block/original-owner constructor, rather than a supplied row representation.

## Heights and degree without a hidden dimension factor

The rational coefficient bound is

`B*[1+Q*(8Q)^(2R)*(Q+1)^Q]`.

Its proof uses bounded spectral numerator entries, inverses of nonzero integer nodes/differences of magnitude at most one, and bounded-degree products. A complete-copy embedding is injective, so assembly introduces no sum over the universal dimension. Only original-owner fibres can sum, and their supplied occurrence bound is B (B=2 for the public graph). Identity leftovers obey the same envelope. This is the key reason no enormous alphabet cardinality is hidden in the row height.

`builtLayout_integer_polynomial_bounded` combines that coefficient bound with the same denominator-cleared integer polynomial; it does not select a different favorable numerator per coefficient. `builtLayout_row_representation` also proves its integer numerator polynomial degree at most R by injectivity of integer-to-rational polynomial mapping and the actual constructor degree theorem. Zero rows cause no degree exception. `rowNumeratorExponent` and `rowDenominator_le_power` bound logarithmic magnitudes polynomially in Q,R and log B; since Q,R are polylogarithmic in n, these are polynomial-bit bounds independent of universal dimension.

## Actual Taylor packet

`integer_taylor_formula` is the exact Hasse/Taylor binomial coefficient formula, including i<k terms (their binomial is zero). `integer_taylor_bound` is uniform over every output coefficient and uses the coarse valid envelope

`shiftBound(R,B,T)=(R+1)*B*[2(T+1)]^R`.

Integer shift commutes with the actual denominator-cleared identity (`map_taylor_cleared`), so shifting preserves **the same denominator**. `taylor_representation` supplies a literal integer numerator, and `builtLayout_taylor_representation` obtains all premises from the actual native constructor. For sample nodes 1..Q take T=Q. No factorial division/ordinary-derivative normalization is silently introduced.

This closes the actual source-row and shifted row-coefficient inputs to finite rational arithmetic, not merely a scalar absolute bound. It does not yet, by itself, instantiate the common denominator/height of every global streamed tensor jet or normalized Hermite denominator packet. Those use the existing sum/product/global-height and cached quotient lemmas plus further adapters. It also does not attach height bounds to every intermediate of the row-construction algorithm or prove primitive arithmetic/allocation costs. None of those stronger claims should be credited to these two files alone.

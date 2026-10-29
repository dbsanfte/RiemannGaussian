# Independent semantic review: actual Hermite cardinal input

**PASS.** Read-only review of `SemiprimeCardinalHeight.lean`; exact hash in `review-cardinal-height-source.json`. No source edits or numerical tests.

`taylor_cardinal_product` expands the actual normalized Hermite cardinal polynomial at its own sample t into

`product_(s in points, s!=t) [1+X/(t−s)]^J`.

The signs and normalization are correct: `(t+X−s)/(t−s)=1+X/(t−s)`. Every retained s is distinct from t, so no zero difference is inverted. For integer sample nodes 1..Q, every nonzero difference has absolute value at most Q, its inverse has absolute value at most 1, and Q! clears its denominator.

`taylor_cardinal_clears` clears each factor power and then their product with the single public

`deltaL=(Q!)^(QJ)`.

Actual factor count is at most Q (indeed Q−1 at a sample); this overestimate is harmless. The denominator is shared across all coefficients. It does not multiply per output coefficient, inverse coefficient, universal row, or algebraic term in an expanded series.

The coefficient proof multiplies affine factors iteratively, doubling a uniform coefficient envelope once per affine factor. Thus `taylor_cardinal_coeffBound <=2^(QJ)` is coarse but valid, including all coefficient indices and the zero tail. `taylor_cardinal_representation` combines the SAME denominator-cleared integer polynomial with that rational coefficient bound, giving literal integer numerator magnitude at most `deltaL*2^(QJ)`. It does not assume the desired integer numerator bound or a cached inverse result.

`taylor_cardinal_constant` proves the actual input coefficient at zero is 1, so the normalized cached inverse hypotheses are truly supplied. The identity remains well-defined at J=0 and empty products; the representation theorem's sample-membership premise prevents any false sample inverse claim when Q=0. `cardinalDenominator_pos` discharges denominator nonzeroness.

`cardinalDenominator_le_power` gives binary exponent `clog2(Q)*Q*(QJ)`. This is polynomial in Q,J and therefore polynomial in the public dimensions; it contains no universal-alphabet cardinality. Combining numerator and denominator bounds supplies the actual local normalized Hermite denominator packet inputs to JetArrayHeight. The subsequent inverse may raise this denominator to the Jth power, still with polynomial logarithmic height; no assertion is made that its numerical value itself is polynomial.

Scope: this closes the cardinal-denominator packet, not the entire global H_t numerator packet, every intermediate of cardinal polynomial construction, or a primitive bit-time/allocation theorem. Those execution attachments remain separate from the exact input-height result.

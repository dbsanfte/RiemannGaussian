# Independent proof/source addendum

2026-10-16. PASS for the exact files below. The earlier `uniform-barrier-review-A.md` is unchanged.

## Exact targets

- `source-pins.json`: 2299 bytes, SHA256 `8bdcb404f3129f32586c6db2970d98b898bc2efc1d296c679b8e7cc5e0d01cd9`.
- `constant-recurrence-obstruction.md`: 6998 bytes, SHA256 `2ccc4c6c730cbe77cdb1bf55b996a7571e86ad16ae28a64b7bf9210cfd19fb5c`.
- `general-q-recurrence.md`: 5582 bytes, SHA256 `36070d66b167ac8b15fb2e05402e4a3a2c43b32dd0fc081df06e85dfa15b552f`.
- `q-stream-obstruction.md`: 4919 bytes, SHA256 `012c8ca2d71100b5edd40bbe247fde5dbb0942462e0efbfdc819786b5dc64f8d`.
- `constant-recurrence-source-pins.json`: 520 bytes, SHA256 `24e8b4d2fa5a577815808fdf7f05f53feebd738322ccc76b24d518ca7c827d44`.

All seven raw source pins in the first metadata file match actual bytes and SHA256, including all three gzip payloads' uncompressed lengths and hashes. Both constant-recurrence source pins also match. The actual-family source explicitly supplies the original balanced supply, kappa=677/1000, prime local orders and cofactor bound O(M^.969). These are inherited classical source facts, not newly established prime distribution.

## Constant coefficients, composite local orders

The ratio, chirp sign and cleared B_t factors are correct. Grouping at most (r+1)² numerical frequencies and using the first that many equations gives zero coefficient sum in every actual group. Any two short alias differences have determinant divisible by R and absolute value <=2r²<R, so all aliases are collinear. Axis aliases are excluded by the stated orders. The report uses an actual nonzero direction (s_0,v_0), with v_0>0, and the correct Laurent convention Y^(-t): X=x^(v_0),Y=x^(s_0) makes each actual frequency group one formal exponent. Additional merging of groups is harmless. No primitive-lattice saturation assumption is needed.

After division by D_r, the largest nonzero shift has a genuine pole at x^(v_0)=q^(-t_*), while all smaller shifts are regular. Numerator factors cannot vanish because their q-exponents lie between L+1 and L+r<ord(q). This remains true when the characteristic divides v_0: pole multiplicity may increase but no numerator cancellation occurs. The t_*=0 case is immediate. Thus the field theorem is valid for composite orders. For m>=3 and r<=m, all three numerical hypotheses follow from the paid beta/q order bounds. The conclusion excludes order <=m only, not order 2m or all nearlinear-order recurrences.

## Original-family q-recurrence statements

For the first-order q-stream argument the two frequency families have no internal aliases, and a cross alias would solve d(v-u)=1 mod R within distance r+1<rho. The number 2r+4 of bases fits within L when r<d. Thus the claimed r>=min(d,rho-1) follows. Removing all prime divisors of m²s-1, |s|<=m, costs O(M^5.969) pairs by the stated cofactor count and all-comparable-m overcount; rho>m then implies r>=m.

For the positive-order generalization, clearing denominators gives bases g^(du-t) with u<=D+r and t<=r. A mixed alias belongs to the signed hyperbolic catalog because |(u-u')(t-t')|<=r(D+r)<=m. Its size is O(m log m), every catalog integer is nonzero, and each has O(1) eligible large prime divisors. The all-m, opposite-factor and cofactor count is soft O(M^5.969). Axis aliases use the prime-order condition gcd(R,d)=1 and |u-u'|<=m<R; one must not instead infer |d(u-u')|<R. The report correctly uses the former argument. There are <=4m bases, fewer than the available L-r+1 equations for large m. Vandermonde then forces every polynomial coefficient to vanish. All leading/endpoint coefficient degeneracies allowed in the report are handled by this proof.

These two deletion arguments apply only to the original prime-order family and all current candidates, with counting over all comparable m an overestimate. The uniform certified beta theorem is a separate stronger paid regime, and does not silently inherit the literal source's collision coverage.

## Scope and provenance

The primary Bostan–Yurkevich fingerprint and exact Theorem 5 contract were checked in review A. Its growing-parameter cost is an upper bound, never a computational lower bound. The older generic recurrence proof concerns U_n=product_i F(theta^i); the present chirped coefficient stream A_k is different. Classical pole arguments, finite q-binomial ratios and old prime-divisor counting remain credited. The new conclusions are specified representation obstructions and paid certification composition; none acquires the whole-family norm, proves a general algorithm lower bound or supplies a new Lean theorem. No reports/repository files were edited, no broad build was run, and the earlier review remains frozen.

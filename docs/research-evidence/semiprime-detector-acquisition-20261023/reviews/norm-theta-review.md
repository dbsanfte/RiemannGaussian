# Independent final audit: full orbit norm and finite theta

23 October 2026. Verdict: **PASS after one minor qualifier was repaired.** No full-product evaluator, detector, or improved factoring exponent is established by either report. No repository files were changed.

Reviewed final SHA256:

- `norm-detector.md`: `76eb4616864bd506d78e1c9bbf877e62877b3f47b79b4d2e6ee243a45e664131`
- `theta-displacement-check.md`: `32f295a3c11bd0acb546b279b0edf82deda156302f81a4cbe1a16a94d4a22168`

## Norm word and compiler

The commuting automorphisms give Phi^c(W)=beta0^(c^2) W V^c and Psi^sigma(W)=Q^(-sigma)W, including signed indices. Expanding `(fT)^ell T^(-ell)` gives the seed product with sigma=a,...,b. Conjugating by S^c0 and expanding `(CS)^n S^(-n)` then gives precisely c=c0,...,c0+n-1. Thus (4)-(5) encode the FULL product, not a prefix; coefficient commutativity makes the ordering harmless. Its short noncommutative circuit is only a descriptor. The original row algebra has not been shown invariant under either shift, so the report correctly leaves moving-fiber specialization unpaid.

The compiler's essential hypotheses are sufficient and correctly explicit: rowwise zero support must agree separately over BOTH hidden fields; every inversion must have its certified short-binomial guard factorization; every guard exponent J_v must be nonzero with O(log N) bits; and only soft-O(1) algebra operations/guard types are allowed. An aggregate or adjacent-window cancellation lacking these support/guard properties does not qualify. Guard gcd scans either factor, give a legal short global annihilator, or certify all inversions. Final saturated row values are not themselves treated as short annihilators: they trigger ONE paid one-row product-tree search, whose source leaf has the actual short nonzero K.

The one-row search costs soft O(r), including O(r) acquired targets/seeds and localization. Across G=soft O(r) rows, interpolation/algebra operations cost softly linear in G, and row-clock/guard powers have the stated extra logarithms. Executing r algebra operations would instead cost soft O(rG). Partitioned metadata interpolation is legal because within-block differences are <r^2<P,Q. The public N>5r^5 guard makes every latest-source K nonzero; its complementary bounded-input fallback is valid under the given scale bound. The older exceptional-row peeling is correctly restricted to the old source and actually queries each deleted row. No arbitrary untested zero row is removed.

The fixed-a C-AP, W-GP, and cubic centered-B clock are retained; they are not replaced by arbitrary interpolated clocks or an unproved cross-a W relation. Caruso–Le Borgne's finite-field finite-order setting does not provide the missing representation or its cost. I checked this source restriction directly in its author PDF introduction and reduced-norm setup.

## Finite theta, endpoints and displacement

Direct finite cancellation gives exactly the sign `-x^(-1)` and boundary quotient in the one-step theta ratio. Iteration gives `(-x)^(-c) p^(-c(c-1)/2) B_c`, with numerator indices L+j and denominator indices L-j for j=0,...,c-1. Substituting x=-beta V and p=beta^2 therefore yields the stated chirp identity and the mixed numerator (3). Every theta/boundary factor is 1+rho^J, hence a unit in the odd-characteristic local fields because rho has odd order. This unit proof is independent of local-order aliasing.

The aggregate B_c formula has multiplicities n-j and precisely the points p^(L+j), p^(L-j). The theta aggregate ranges 1,...,n+L-1 and 1-n,...,L-1 are correct, with the stated triangular weights. Degree-G row polynomials and O(n+L) points give the stated softly linear cost; evaluation uses monic node divisors even though the input F_+,F_- need not themselves be monic. Negative powers and repeated nodes cause no illegal inversions. Repeating over sigma raises these units to the seed-interval length. None of this removes B_c from inside the mixed differences.

Frobenius specialization a_c=p^c makes the column dependence exactly t^(-c), and its theta Vandermonde factors vanish. This does not evaluate the required entry product. The weighted shift orientation is also correct: MZ agrees with D_V M in every interior column, leaving one boundary column. Adding the all-ones matrix gives the rank-at-most-three displacement for L. The displayed reciprocal displacement numerator and paired leaf denominators are exact; ordinary matrix inversion is not entrywise inversion or an entry-product detector.

I checked Corollary4.7/quasiperiodicity in the local Rosengren–Schlosser PDF and the generator/ordinary-inverse definitions in the local Bostan–Jeannerod–Mouilleron–Schost PDF. Their hashes match the report: `6ce3745572b1729bc79faa429fc4053aca09cd349ce00b0b08244ceb2d442273` and `466d9112461876577fd631808b37f3fab3150d621ba7518b29aef85f1075ee3b`.

## Correction and scope

The first theta version said no finite rational function satisfies the exact theta equation, overlooking the zero function. The author repaired this to “over a field with p!=0, no NONZERO rational function.” I re-read and hashed that repaired version above; the degree-at-infinity proof is then correct. No other correction is required.

The legally acquired coefficient roots, odd-order unit gauges and endpoint factors remain inherited or auxiliary operations. Both reports explicitly avoid presenting them as a new detector. The missing operation remains the support-preserving whole moving-fiber norm evaluation. This audit is symbolic/source inspection, not a new coverage or performance validation campaign.

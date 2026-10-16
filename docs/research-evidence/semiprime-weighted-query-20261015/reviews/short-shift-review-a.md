# Independent review: actual short-shift nonoverlap theorem

2026-10-15. Verdict: PASS. No substantive correction requested. This is a classical arithmetic/scope review, not a Lean build or a circuit lower bound.

## Exact reviewed pins and source-byte validation

- source/actual-short-shift-nonoverlap.md SHA256 2f0d7c10fe5b15c80961e37ca0b878006b663993ec924df7f9747fcaf03dbe60.
- source/source-pins.json SHA256 37956a2c9caf54976d47c80f54bc01a764a6f2bf4ad48bfeb27cb4cf5d40da00.

Independently reread and SHA256-hashed ALL SIX paths in source-pins.json. Every byte pin matches:

1. Durable high-digit-folding-obstruction.md: df7e67583b43d3daff78a581ca86f5d10a68cd9e3c922ed5e95d7f95042db3f7.
2. Durable transform-interface.md: 5c8b4d56f2ee00e59b608fb1a15ae7baefee8af02acaba4655f5aa930c0505ae.
3. Durable full-euclid-all-hit-obstruction.md: fb77b60fcf84ffad92c535bd6a0a3d9cc2434beadf48bbf86a39a2a2c8358bb0.
4. Durable charged-skipped-ray-obstruction.md: ca92ab638d96409cc0dadb822ce3fcf31ac77d637b37020f81a19e1462568fae.
5. Native SemiprimeGlobalPhaseCancellation.lean: 9e061d01e511f908a33256c229ca87aab1a3401077e63941f6fc2cf025720a1a.
6. Native SemiprimeSeedSumAcquisition.lean: 6223962bcacaf9f3325e3838fe221f8cf69f3b5e4c865d3e3d1335b0a039273e.

The two restored historical reports were also independently decompressed and matched to the archive index in the prior endpoint review. Their actual prime-order supply and projected-base facts, together with journal J4 menu telescoping, were previously read directly. The present proof inherits those order-qualified premises explicitly; it does not assign them to excluded inputs or add a new prime-distribution hypothesis.

## Nonzero exponents and divisor enumeration

The prescribed shifts obey d not dividing h. Therefore h+dk cannot be zero for any integer k, including k=0 and either sign. The bound |h|<=C m^2 and |k|<=4m^2 gives |h+dk|=O(M^4), with fixed constants. Every relation gamma^(h+dk)=1 in the P field makes the actual prime order R_P divide this nonzero integer. It has O(1) distinct prime divisors larger than cM^2.031 by the elementary product-size argument. Counting negative n via |n| is legitimate.

For each possible R, the retained relation P=1+vR, 1<=v<=V=O(M^.969), leaves O(V) candidates. Counting nonprimes or out-of-bin candidates only enlarges the count. To count partner Q for such a candidate, retain the historical P-bin restriction P=Theta(M^3); outside that bin it contributes no actual input. The selector interval has width O(M^2 G_m), hence O(M^2(G_m+1)) integers including endpoints. No short arithmetic-progression prime-density assertion is used.

## Menu count and joint surviving family

For fixed m there are at most H_* shifts and O(M^2) integers k. Multiplying by the divisor/P possibilities and Q interval bound gives O(V H_* M^4(G_m+1)). The frozen sum_m(G_m+1)=O(K_*M) yields O(K_*V H_*M^5), exactly as stated. Switching hidden fields only doubles the upper bound.

At K_*=O(M^.020), H_*=O(M^.004) and V=O(M^.969), the exponent is 5.993. The old soft M^5.994 deletions and digit-folding M^5.993 deletions are united directly on the same original order-qualified supply, so their total remains o(M^6/log^2 M). There is no invalid intersection of separately constructed thin families. For polylogarithmic H_* the new term has soft exponent 5.989. The report correctly identifies these as input-exception counts rather than acquisition clocks.

The shift sets are fixed at m while N varies. Adaptive choice WITHIN a simultaneously granted set is allowed, but N-dependent generation of an uncounted new shift support is not. The report states this quantifier correctly and does not grant all source-offset differences.

## Actual polynomial consequence for every searched length

For large M the prime local R exceeds 16m^2, in particular 4m^2, and cannot divide m^2. Thus q=gamma^(m^2) has the same order R. For every 1<=L<=4m^2, the roots inside P_L and its gamma^h translate are individually distinct and nonzero.

A cross overlap gives gamma^(-h-di)=gamma^(-dj), equivalently R divides h+d(i-j), with |i-j|<L<=4m^2. This is one of the simultaneously deleted relations. Hence the two degree-L polynomials are coprime on every surviving input in both fields, for all permitted h and all L in the range. No extra union over lengths is needed because the relation catalog already grants every |k|<=4m^2. Their leading coefficients are nonzero field units, so both reduced degrees are exactly L.

## Functional finite-subgroup obstruction

The extension from rational identity to equality as functions on the full subgroup is correct under R>4L, which holds eventually uniformly. If nonzero B and deg A,deg B<L agreed with the true quotient wherever both denominators are nonzero, at most L+deg B<=2L-1 subgroup points would be excluded. Thus more than 2L-1 points remain, while B P_L(gamma^h Z)-A P_L(Z) has degree at most 2L-1. It must vanish identically over the field. Coprimality then forces P_L to divide B, contradicting deg B<L. Denominator zeros and finite-field polynomial/function aliasing are therefore correctly handled by the explicit point-count bound.

This conclusion does not apply to matching a small selected canonical target set, nor does full rational degree imply Omega(L) arithmetic evaluation time. Those exclusions are explicit in the report. The theorem closes the earlier generic-versus-actual root-cancellation gap only for the specified prescribed sparse shift family. It does not block compressed q-product evaluation, addition-based identities, norm-only acquisition or arbitrary circuits.

Existing native whole-seed coverage and global-leaf recovery remain intact. No fast weighted straight-line program or nearlinear long-query evaluator is supplied by this obstruction.

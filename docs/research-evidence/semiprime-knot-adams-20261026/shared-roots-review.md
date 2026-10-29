# Independent review: shared acquired-label roots

26 October 2026. PASS scoped. Exact algebra and bit-cost review; no experiments or repository edits.

## Valuation margin and initialized exponent tree

Let M=product|e_j|, T=ceil(log_2 N). Every original beta order r divides p-1<N/A with A=16H+1>16, so for any prime ell, v_ell(r)<=log_2 r<log_2 N-log_2 A<T-1. Thus the stated T-1 margin is sufficient, including a leaf containing all of a prime's M-valuation. For ell|M, T v_ell(M)-v_ell(|e_j|)>v_ell(r); for ell not dividing M, all relevant powers leave that valuation unchanged. Consequently b=beta^(M^T) and every signed beta_j=beta^(M^T/e_j) have exactly the same retained local orders and generate the same local subgroups. Their labels are coprime to those orders, so the signed root is unique inside that retained subgroup. A negative exponent only inverts the element and does not change its order.

The complement-tree initialization is correct: w=beta^(M^(T-1)), and the leaf complement exponent M/|e_j| gives beta^(M^T/|e_j|). At each tree depth, sibling-product exponent bitwidths sum to O(log M+L); there are logarithmically many depths. The one initial exponent M^(T-1) has O(L log² N) bits. Fast integer products and modular powering therefore cost soft L, not L separate exponentiations of that full bitwidth. R itself can be represented/acquired at soft L bit scale if needed. The M=1 and unit-label cases are covered.

## First-drop factor return

The schedule of L labels repeated T times has product R. Local orders of q_D decrease monotonically; they stay odd and coprime. Prefix exponents can be acquired on demand from the original product tree plus complete M powers, with O(L log² N) bitwidth and soft L work per requested prefix, rather than storing LT wide prefixes. Binary search uses only logarithmically many separator calls, each soft k, so total is soft k.

If a separator returns a proper gcd, factoring is done. Otherwise a small exact common order must be1 by coprimality. At the first such step, the PREVIOUS q_D has both odd local orders>16H, and (q_D)^|e_j|=1 globally. This is exactly the licensed extractor contract with short nonzero O(log N)-bit annihilator |e_j| and base q_D. It would be wrong to use beta^D without the extra H-primary justification; the report explicitly avoids that mistake. The wide D and R are never passed as short annihilators. Labels1 cannot be first-drop steps. The extractor cost soft N^(31/192) is below soft k. No hidden factorization of M is used.

## Separation and original labels

Derivative multipoint values test the product of pair differences excluding the self factor. On a nonunit derivative, scan that row's other L-1 differences: a proper gcd factors, while any globally equal distinct-label pair gives beta_j^(e_j-e_l)=1. Deduplication excludes zero exponent differences; beta_j has both large odd local orders, so this is again the short-label extractor. Saturation from different factors at the two primes simply causes a proper gcd somewhere in the scan, rather than licensing an incorrect common-order inference. The same reasoning for q_j is valid because its local orders equal those of q_b>16H. Total cost includes at most one scan and one paid extractor, hence soft k.

The native application uses e_j=E_j!=0 with stored original metadata. Raising an original collision by the known signed integer R/e_j proves b=q_j^i. Accidental projected collisions are safe for the stated consumer: a saturated leaf gives beta_j^(E_j-Hi)=1, and the OLD WHOLE-ROW integer-zero deletion guarantees E_j-Hi is nonzero throughout the original searched interval. Its bitwidth stays O(log N); it is not multiplied by the wide R. Proper gcds return factors directly. This must retain the original interval/deletion metadata, as the report states; it is not a new license to enlarge the index window arbitrarily. If an i=0 original collision were killed into b=1 locally, the retained large-order q_b screen cannot continue on that component, so it is handled by the factor-returning prepass rather than silently losing coverage.

## Query scope

The continued root acquisition is real, but the transformed family has different row bases q_j. Fixed i evaluation costs soft(L log i) by explicit powering, with the conventional resultant sign, while the product of X^i-b over i<=m has degree m(m+1)/2. A short descriptor of that polynomial is not an acquired scalar resultant. The report correctly refuses to reuse the common-base baby polynomial across these new row clocks or infer a full prefix from a single cyclic/cabling winding. No full-query rate improvement is claimed. No material gap found.

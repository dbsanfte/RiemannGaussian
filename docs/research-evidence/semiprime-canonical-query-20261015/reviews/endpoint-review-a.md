# Independent review: actual canonical endpoint-band counterfamily

2026-10-15. Verdict: PASS on the exact report bytes below. This is independent arithmetic/provenance review, not a new Lean theorem or reproof of the historical prime-distribution inputs.

## Reviewed pins

- cancellations/endpoint-band-counterfamily.md SHA256 6e906928b99645254ed640877d5bf1085be4142d436d5e6b3e68908d3ddcc1f1.
- cancellations/endpoint-band-source-pins.json SHA256 e88355469a35e7880e89d816f7ef6f0e29afc267cafaedacd44c97f387f4a83c.
- Restored /tmp/semiprime-next-covered-acquisition-20261008/full-euclid-all-hit-obstruction.md SHA256 fb77b60fcf84ffad92c535bd6a0a3d9cc2434beadf48bbf86a39a2a2c8358bb0.
- Restored /tmp/semiprime-long-norm-frontier-20261008/charged-skipped-ray-obstruction.md SHA256 ca92ab638d96409cc0dadb822ce3fcf31ac77d637b37020f81a19e1462568fae.
- Current docs/semiprime-factorisation-investigation.md SHA256 fe463f81d9a429a8199a60d39d629fb4bab732d4b9f4e5a327b13f4a95db7286 at review time.

I independently located both original_path entries in research-checkpoint-20261012/index.json, decompressed their referenced gzip objects and checked byte equality with the restored copies AND equality of SHA256 with both index entries and endpoint-band-source-pins.json. Both passed. This is stronger than merely trusting the adjacent pins file.

The restored full-Euclid report section 2 explicitly supplies the fixed ratio<=3/2 prime bin, Omega(M^6/log^2 M) pair supply, P-1=v_P R_P, exponent .677, actual projected gamma with exact prime local orders, uniform R>16m^2, and selector-strip telescoping. The current journal lines 29120--29185 supply the first B^.020 consecutive-prime menu, fixed dominating K_*, p_(-K_*) envelope, sum(G_m+1)=O(K_*M), and direct joint loss soft O(M^5.994). Lines 29420 onward reuse the same menu envelope. No short-residue-class prime-density premise is added in the new report.

## Fixed P,m,Q-box false-tag count

The reduction of N+delta_j-m^2i modulo R_P is exactly Q+delta_j-m^2i, because P=1 modulo R_P. For a fixed index i, varying Q in one width-m^2 box and delta_j in [-3m^2,m^2] spans length at most 5m^2. Since R_P>16m^2, O(1) values of the INTEGER multiplier K suffice across the entire box and every tag. This does not depend on the large magnitude or sign of i.

With a fixed slope a, reducing the zero equation modulo m and multiplying by P gives precisely

a j^2-2aPj+aP-P K R_P=0 modulo m.

Its leading coefficient a is nonzero, so it has at most two tags. Fixing one such state (a,K,j), the two possible Q values have the same slope condition and therefore differ by a multiple of m. The literal lift then gives

m Delta b=-I_j P Delta Q modulo m^2.

Subtracting the exact zero equations gives (1-I_jP)Delta Q=0 modulo m^2. For a false tag j!=P modulo m, this coefficient is nonzero modulo prime m, hence a unit modulo m^2. Thus Q=Q' modulo m^2. A half-open real interval of width at most m^2 contains at most one integer in that class. The O(m) state bound per box/index follows.

For each actual allowed P its R_P is fixed. The proof uses only that there are O(X) such P; it does not require choosing a large prime order for arbitrary integer P. Summing the valid per-prime-P bound using the O(X) cardinal upper bound is legitimate.

## Summation and joint loss

There are O(G_m+1) boxes per selector strip and 4w+2 indices in the two disjoint bands. Therefore the bound is

O((w+1) X sum_m m(G_m+1))=O(K_*(w+1)M^5).

Switching hidden fields only doubles it. With K_*=O(M^.020), w<=M^.970, this is O(M^5.990). The claim correctly gives polynomial menus and large w for coverage only; it does not assign them a nearlinear acquisition clock. Adding this loss directly to the frozen soft O(M^5.994) deletions remains o(M^6/log^2 M). There is no invalid intersection of two unrelated infinite sparse families and no extra multiplication of the frozen loss by the menu size.

## Own tags and both endpoint bands

The integrality calculation for I=(aP+ell+Q)/m^2 is correct: multiply by the unit P modulo m^2 and use P-j divisible by m, N-a j^2=mD, and bP=-D modulo m. At the own tag the local zero equation becomes m^2(I-i)-a(P-1)=K R_P; since R_P divides P-1 and is coprime to m, it forces R_P dividing I-i.

The bounds follow from the retained source offset bound and fixed ratio bin:

I>=Q/m^2-3-1/m=Omega(M),
I<=P/m+Q/m^2+1<=sqrt(3/2)m^2+O(m).

These estimates hold uniformly for either ordering of P,Q. Since w=o(M), the first gives I>w. Since sqrt(3/2)<2, the second gives I<L_m-w. For every queried endpoint index, including negative indices near zero and indices above L_m, |I-i|<4m^2<R_P eventually. Thus divisibility forces I=i, contradicting either band's location. No own-tag hit was omitted from the false-tag count without a separate exclusion.

## Simultaneous signed-stencil consequence

For shifts in [-w,w], every length-L interval contains [w,L-w), and every support label outside this common interior lies in the two stated bands. Any finite signed stencil with total weight zero cancels on the entire common interior. All remaining atomic factors are units on the same surviving family. Negative powers are therefore legitimate and every multiplicative numerator/denominator boundary observable remains a unit, simultaneously for every integer coefficient choice. This is a support statement, so no union bound over weights or stencils is needed.

The report correctly excludes arbitrary additions, unrelated public starts, larger shifts, nonzero-augmentation stencils retaining long interior support, and arbitrary implicit/gcd-only algorithms. The full canonical rectangle still has its known native hit; this is a new obstruction to the specified endpoint-only acquisition route, not a claim that original long coverage fails.

No substantive correction requested. Core long-query acquisition remains unpaid.

## Final v2 extension review (preserving the original review pin above)

Reviewed appended corollary and final report SHA256 882bbf2500add5deec9f90e0e46630b55a8c0a3f8e5ad72e8bc7bd68d4e2269e. PASS. The original report pin 6e906928... remains the reviewed base version; this section extends that verdict to v2 rather than replacing its history.

The corollary fixes ONE prescribed m-only length function L_m in [2m^2+2,4m^2]. Consequently its endpoint indices stay fixed while Q varies in a P,m selector box, exactly the premise needed by the multiplier/state count. Its cardinality is still at most 4w+2, and false-tag bound (3) is unchanged. For own tags, the lower bound on L_m preserves the strict upper-band gap and the upper bound gives |I-i|<5m^2<R_P. The common-interior cancellation argument is unchanged. The explicit no-free-union qualification over all length functions is mathematically necessary and correctly included.

The current native seedLength is an m-only function, so it fits this contract. Re-read SeedSumAcquisition.seedLength_bounds, which states 2m^2+2<=seedLength(m)<=4m^2 for m>=4. Independently checked native source SHA256 6223962bcacaf9f3325e3838fe221f8cf69f3b5e4c865d3e3d1335b0a039273e against the newly appended adjacent source-pin entry. The final adjacent endpoint-band-source-pins.json hash is e18f27dce2da1c427c7b5c741f2b0b9a4cbe45e0c38f2f679b31d6896feca2e2; the earlier two restored-source entries remain unchanged. The corrected coverage/recovery working report remains unchanged at SHA256 2e5015278da165b55d4f92f51b39ba1fb3262d51c42201bf2bada91d2304bb22, confirmed by fresh hashing.

No new native theorem or arithmetic-coverage advance is claimed by this corollary. The new classical obstruction now also covers the already established native padded length, under one prescribed family at a time.

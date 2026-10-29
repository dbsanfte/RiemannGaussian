# Independent review: colour symmetry and enlarged scale range

26 October 2026. Bounded paper review; no tests, new research or repository edits. **Scoped PASS.** The swap quotient preserves factor-oriented NONUNIT coverage, and the sign discussion does not overclaim a phase-index gain. The enlarged label bound and cell-count qualification below should be made explicit when integrating this result.

## Symmetric scales and either-factor guarantee

The new range[8H,N/(8H)] is valid for every enumerated public scale: both p0 and q0=N/p0 are at least8H. Nonaxis norm²>=2N and both lattice-axis norms>=8kH>=8sqrt N remain true. Hence all Gauss covolume/product, dimension and AB=Theta(k) bounds survive, not just the bounds at a correct scale.

For either actual factor S=P or Q, choose the dyadic floor p0 of S. Then S/2<p0<=S, p0>8H since S>16H, and p0<=S<N/(16H)<N/(8H). Thus the scale is actually enumerated, even for S=Q>sqrt N. Its actual orientation norm is at most twice the public norm, so the stationary-span/gap proof remains valid. The filter proof uses g=gcd(S-1,k)<S/(16H) and a_span<8k sqrt N/S, giving a_span<H/2 and g*a_span<H/2. Therefore the correct orientation passes.

The actual colours P mod k and Q mod k form one orbit of j->N/j. Retaining one orbit representative guarantees that at least one actual factor orientation has all its required scales retained. This is a NONUNIT coverage argument, not numerical equality between swapped scalar products. The set of dyadic scales need not be exactly closed under p0->N/p0; independent dyadic coverage of each retained orientation is sufficient. The at-most-two fixed colours and k/6+O(1) orbit count are correct.

## All-public-cell labels after p0 exceeds sqrt N

The OLD bound b_span<=4k must not be reused over this enlarged range. Direct public-coordinate estimates give

    a_span<2R/p0,
    b_span<2R*p0/N=4k*p0/sqrt N
       <=sqrt N/(2k)<=H/2,

where R=2k sqrt N. Also a_span<=H after filtering (indeed the public lower scale bound already gives a_span<H/2). Unwrapped point-phase carries are still in[0,4k). Thus all difference exponents have size O(HN+kH), rather than the original O(kN+kH). They still have O(log N) bits. The existing nonliteral proof is unchanged: for different b it only needs nonzero integer Delta b, a_span<=H and the carry bound; it does not need b_span<=4k. For equal b the strict H/g filter excludes every multiple of H.

The enlarged label size is licensed by the actual inherited extractor: the 2026-10-16 journal entry "balance removed from the short-annihilator extractor" assumes a nonzero global annihilator of polylogarithmic binary length, not the old individual index or O(kN) magnitude bound. Therefore once-only T_ext=soft N^(31/192) remains valid. Gcd/nonunit prefix localization and exact monic polynomial evaluation introduce no new inversion or factor of the number of calls in this terminating cost.

## Sign transport and cost scope

The signed-baseline identities E_signed=-E_j+H*epsilon and I_signed=-I_j+epsilon are correct, including lambda=0. For Cartesian signed differences, the generator correction has absolute value<A+B<4k. Covering signed indices in[-8k,8k] and mapping them back gives ordinary shifts of magnitude<12k. Added leaves remain nonliteral by the same-b filter and the different-b bound N-(16k+2)H>0. The resulting character is -chi_j, so its phase image index is unchanged; using the ordinary baseline at colour -j would be a different, unjustified assertion. No zero/nonunit-preserving numerical division is performed.

This halves the number of distinct colour query families asymptotically, NOT necessarily total cell work. The logarithmic length of the enlarged scale interval is twice that of[8H,sqrt N], up to endpoint rounding. Consequently the constant saving in colours can be offset by the extra scale cells. The report correctly retains soft-k descriptors and soft-k² explicit completion; no total factor-two runtime saving or exponent gain should be inferred. Prefixes over the actually retained cell list have the same nonunit recovery contract.

The N=1 mod3 high-index branch, the ordinary/signed baseline distinction and the restricted use of the phase-index result are accurately scoped. No general obstruction to implicit/shared scalar algorithms, and no new complete-query improvement, is asserted.

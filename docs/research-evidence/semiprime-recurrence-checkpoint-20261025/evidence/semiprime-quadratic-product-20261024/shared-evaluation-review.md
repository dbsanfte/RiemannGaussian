# Independent review of shared-evaluation.md

24 October 2026. Verdict: **PASS**. Exact final source reviewed: `/tmp/semiprime-quadratic-product-20261024/shared-evaluation.md`, SHA256 `d3df0e461a41583dfa60d4272d44174abd4ca3b05a0c730d31ede0dc06903f4b`. The original requested pin was `2e3088dd591b25bccca30cd6f686871c58103ccff15c600f8243eb718288a2be`; its two missing theorem-hypothesis qualifications were supplied by the author before this final review. No required correction remains. No source or repository edits were made by this reviewer.

## Exact initialized cut

The universal identity is correct over the actual composite quadratic algebra, without diagonalization: each factor of K_b is `(X-z^i)(Y-bar(z)^i)` because z^i bar(z)^i=Norm(z)^i. Thus its coefficient matrix is an outer product, and the two full degree-b univariate factors are acquired by a monic product tree in soft b. This is actual block coefficient acquisition, not a free implicit polynomial.

The shifted block phase checks exactly. Factoring z^(ab) out of each of b differences contributes z^(ab²), and taking its norm contributes t^(ab²) for each row. Summing a=0,...,r-1 and multiplying J rows gives the exponent J b² r(r-1)/2 in equation (3). The remaining nodes are the actual Jr elements z^(-ab)V_j. Their initialization and monic evaluation cost soft(Jr+b); the final shorter block and row-restriction product trees are included. Minimizing b+JL/b gives the stated soft(J+sqrt(JL)), not soft(J+sqrt L). Neither growing J nor block starts are omitted.

The auxiliary monic R_r has degree Jr, with exactly those scaled roots. The sign/order convention Res(R_r,P_b)=product_(roots R_r)P_b is correct. An ordinary coefficient-vector resultant needs acquired degree-Jr input; the report properly declines to turn that particular observation into a lower bound for another scalar-only algorithm.

## Primary theorem checks and exponents

I checked the cached primary text against its four PDF fingerprints; all PDF hashes match the source ledger.

* van der Hoeven--Lecerf, Theorem 8: hereditary genericity, each pi_i>=delta_(d,i), pi=product pi_i, a supplied element of order at least (n+1)!pi, and O(d^omega) tree preparation are now explicit. Remark 9's alternate bivariate preprocessing is expected and has extra hypotheses. The native unit screen proves neither hereditary genericity nor the field/input requirements. The point count is Jr, and a dense block coefficient vector has size (b+1)^2 even though this particular block has a better rank-one implementation.
* Harvey--Sutherland, Theorem 4.1: its stated bound includes the bit sizes of the explicit integer matrices, modulus product and initial vector; log r0=O(h) is now stated and is automatic at r0=4. A linear companion transport is not an acquired linear transport for its multiplicative accumulator. The source does not apply the theorem to that nonlinear state.
* Bostan--Schost, Section 5: fast geometric evaluation/basis conversion concerns explicit polynomial vectors and point sets. The report uses monic evaluation over B rather than transferring unguarded field interpolation inverses.
* Nuesken--Ziegler, Result 4: the field, supplied coefficient vector, and pairwise distinct FIRST coordinates are the correct hypotheses. Its ring-safe Theorem 3 has the separate cubic balanced-degree estimate. Neither is stated as an implicit product-only algorithm.

For the first rectangular substitution, native J~k and L~k² give `(L+J²)J^(omega2/2-1+epsilon)`. Even the ideal value omega2=3 yields k^(5/2+epsilon), with dense acquisition J² separately charged. For the second, `(b²+JL/b)b^(1/2)` is minimized at b of order (JL)^(1/3), giving (JL)^(5/6)=k^(5/2). These are correctly identified as optimistic comparisons of theorem guarantees; no generic lower bound or current matrix-exponent claim is inferred. The distinction between k^(1+o(1)) and a soft-k guarantee is also preserved.

## Zero support, restrictions, and scope

All actual block identities multiply by known units only and remain valid when leaves vanish, targets repeat, or spectral values coincide. Monic product/remainder trees over B do not invert target differences. Norm multiplicativity preserves the original row/index restrictions. Saturated products are localized before applying the predecessor's same-leaf paired beta identity; cross-leaf pairing is not substituted for that operation. No endpoint, leaf, or singular target is divided out.

The common four-start recurrence is not mispriced as a common-family low-degree recurrence: its outer-product spectral description has (J+1)^2 labeled bases, and the report does not claim an acquired minimal annihilator or all its starts for free. Formula (1) gives a real rank-one universal-block compression, credited as an implementation of the old rectangular cut. The unpaid object remains the restricted scalar contraction across all Jr scaled row states. Full-query acquisition and the factoring exponent are unchanged. The positive identity and this precise limitation are both correctly scoped.

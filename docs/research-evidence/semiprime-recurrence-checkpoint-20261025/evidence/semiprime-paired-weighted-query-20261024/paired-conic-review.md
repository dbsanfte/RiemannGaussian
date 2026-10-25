# Root independent review of the paired conic calculation

24 October 2026. **PASS**, for exact `paired-conic.md`, SHA256 `3ced9caac158ea4f6c4093f38a6ab94e86ceaba8a59012877242c3a0d99ca4fb`. This accepts the exact normalization and scoped attempted basis calculation, not a faster index selector.

I checked the affine inverse and all content arguments. The row congruences make R0,S0 integral with residues j,N/j modulo k. Quadratic terms carry H; the linear coefficients carry H by a_n*j^2=b_n*N modulo k; and the row polynomials at R0, together with gcd(b1,b2)=1, make the constant divisible by H. Before reduction the homogeneous part after division is I1*(-s*I1+k*I2), primitive because s is a unit modulo k. Unimodular Gauss basis change induces a unimodular linear change on this homogeneous part, so the content is EXACTLY H. The full normalized conic is primitive and irreducible by the invertible rational affine map to XY-N.

The certified rectangle is honestly charged. Gauss angle control bounds lambda1*lambda2 between the determinant and 2/sqrt(3) times it. Every nonzero lattice vector has lambda/(BH)>8 on B>8H and N/B>16H, so ceilings do not alter the constant-factor product Theta(N/k^3). This is a containing rectangle, not a count of independent feasible roots.

I also checked the hard second-vector cases. A nonaxis first vector gives lambda1>=sqrt(B^4+N^2), hence lambda2/B<=sqrt(2/3)*k*sqrt(N). If the first vector is (±k,0), reduction gives |a2|<=k/2, |b2|=1 and B^2<=2N/(sqrt(3)k); using B>8H and N<=k^6 bounds lambda2/B<k sqrt(N). The other axis follows using the reciprocal aspect-ratio bound and B<N/(16H). Thus no uniform conditioning premise was smuggled into the height estimate.

Centered ell bounds give |R0|<=k lambda2/N<B/16 and |S0|<=k lambda2/B^2<(N/B)/16, since sqrt(N)>16H. Each scaled affine contribution has sizes O(B) and O(N/B) by the product-of-norms bound. After division by H this gives W=O(N/H), and the constant term has magnitude greater than (255/256)N/H. The claimed primitive height Theta(N/H) therefore follows for the specified rectangle.

The determinant of the homogeneous degree-d symmetric power of the linear-form map is k^(d(d+1)/2); summing these exponents through D gives D(D+1)(D+2)/6. This is only the determinant of that explicitly tested integer monomial transformation. The source correctly does not call it a complete auxiliary-lattice determinant or infer a general impossibility theorem.

I read the cached primary text at Theorem 1.1, Lemma 4.4 and Proposition 4.5. Their balanced fifth-rate logarithmic refinement, parameter restrictions, explicit shortest vector and remaining small-multiple BSGS scale match the report. That source does not give an immediate paired-conic root selector. No source or shared repository file was edited by this review.

# Paid translation to two common character-period products

This reduction retains the original scalar q=gamma^(m^2). Assume gamma and q units, m odd prime, a_j j=N/j mod m, and a native interval 0<=i<L. Put

    x_j=gamma^E_j,
    kappa_j=-Delta_j/(4*a_j*j) mod m, in [0,m),
    sign_j=Legendre(a_j/j,m)=Legendre(N*j,m),
    R_+={0} union nonzero squares modulo m,
    R_-={0} union nonsquares modulo m.

The exact quadratic mask is i mod m in kappa_j+R_(sign_j). Both universal palettes contain (m+1)/2 residues. The row descriptors and the two ordered lists cost soft O(m+J); no individual h is supplied.

Write L=mK+t, 0<=t<m, set y_j=x_j*q^(-kappa_j), and define two COMMON polynomials

    H_e(X)=prod_(r in R_e) prod_(0<=n<K) (X-q^(r+mn)).

These are the unresolved long products; the following boundary work does not assume their coefficients are acquired.

For row j write kappa=kappa_j, R=R_(sign_j), S=kappa+r. Its translated index intervals are exactly obtained from n=0,...,K-1 by:

    A: add n=-1 for S>=m;
    B: add n= K for S<t;
    C: remove n=K-1 for S>=m+t.

For K>=1 these statements are literal set additions/removals. If

    A_j(X)=prod_(r in R, r>=m-kappa) (X-q^(r-m)),
    B_j(X)=prod_(r in R, r<t-kappa) (X-q^(r+mK)),
    C_j(X)=prod_(r in R, r>=m+t-kappa) (X-q^(r+m(K-1))),

with thresholds clipped to [0,m], the row product obeys the polynomial identity

    C_j(y_j)*native_masked_product_j
      =q^(kappa*D_j)*H_(sign_j)(y_j)*A_j(y_j)*B_j(y_j),

where D_j=K*|R|+deg A_j+deg B_j-deg C_j is the exact number of selected native indices. If C_j(y_j) is a unit this is an evaluable quotient identity.

## All boundary values are jointly paid

There are only three boundary channels, two residue palettes, and O(m) explicitly known roots q^(r-m), q^(r+mK), q^(r+m(K-1)). These roots, the y_j, and the scaling factors are acquired in soft O(m+J) native work (integer exponents have O(log N) bits). For each channel/palette build a balanced product tree on its ordered roots. Every row requests one prefix or suffix, hence O(log m) tree nodes. Batch multipoint evaluation separately at each requested node. At each depth, the sum of polynomial degrees is O(m), and the total requested evaluation points is O(J). Thus all boundary values cost soft O(m+J), including polynomial construction, not O(mJ).

A nonunit boundary value is localized in its requested tree to an original scalar leaf. Numerator leaves belong to the actual native interval. Denominator leaves have original index i'=kappa+r+m(K-1), lying in [L,L+m-2]. They are useful auxiliary collisions if their exponent ledger E_j-m^2*i' is nonzero. This ledger is public: the sufficient bound min E_j>m^2*(L+m) certifies all such leaves at once, and holds in the large canonical regime. Under that check, a proper gcd factors N, while a saturated leaf supplies the original prepared-gamma annihilator with that nonzero exponent. Its bit length is O(log N). If no boundary collision occurs, all divisions are by certified units. Without a nonzero ledger certificate, do not silently call an integer-trivial denominator zero useful; that requires the inherited finite handling or explicit symbolic cancellation.

For K=0 there are no common long products. Cancel C symbolically against A before evaluation. The desired native roots are the A-channel residues with m<=S<m+t plus the B-channel residues with S<t. These are intervals in the same two ordered palettes, so the same product-tree method alone pays soft O(m+J). No denominator or 0/0 is needed.

## Exact remaining observable

The reduction leaves evaluation of H_+ and H_- at the assigned O(J) points y_j. Their degree is K(m+1)/2, about L/2. Their root descriptors are shared, but their coefficients have not been acquired in soft O(m).

For comparison, exactly

    H_+(X)*H_-(X)
       = [prod_(i=0 to mK-1)(X-q^i)]
         [prod_(n=0 to K-1)(X-q^(mn))].

The second polynomial has degree K and is cheap at all y_j. The first is the ordinary full geometric long query at those J points. Their ratio is the character-weighted multiplicative period product

    H_+(X)/H_-(X)
       =prod_(n<K) prod_(1<=r<m) (X-q^(r+mn))^Legendre(r,m),

where interpreted only after nonunit localization. Neither this weighted ratio nor the full long-query values have been acquired by the boundary reduction. A quadratic Gauss period in zeta_m alone is not this product, because q is the original prepared scalar and q^m is not assumed 1.

Conclusion: native quadratic masks reduce EXACTLY to two shared character-period products, with all row-dependent translations, partial-block corrections, unit checks and bounded nonzero-annihilator recovery paid in soft O(m+J). This is a concrete shared construction. A faster evaluator for the two remaining products has not been proved, so the known soft sqrt(JL) dominant query cost remains.

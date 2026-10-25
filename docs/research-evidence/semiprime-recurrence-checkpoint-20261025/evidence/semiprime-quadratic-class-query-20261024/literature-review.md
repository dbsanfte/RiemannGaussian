# Independent review: finite class q-Casoratian

24 October 2026. **PASS**, with no source corrections requested.

Reviewed exact source /tmp/semiprime-quadratic-class-query-20261024/literature.md SHA256
`5aa07471d0d2c514b62eff39c1b5f77eb247632cc15c0907eef82dff32f6bea4`.

Read cached primary /tmp/semiprime-quadratic-class-query-20261024/sources/warnaar-2002.pdf, SHA256
`b10e186718a6019ca599a8d2c9cd5cdc539971a1a7c1e53b6e529edc5e7d1aad`, especially printed pages 15–16, Lemmas 5.2–5.3 and Corollary 5.4. Primary: S. O. Warnaar, *Summation and transformation formulas for elliptic hypergeometric series*, https://people.smp.uq.edu.au/OleWarnaar/pubs/Elliptic-HS.pdf . The finite p=0 specialization and auxiliary reciprocal-pair parameter zero are legitimate; the native class coefficient C is not that auxiliary parameter.

## Determinant, orientation and coefficient

The actual arguments are z_h=Vhat_h^-1. Therefore (z_h;q)_L has the original zero Vhat_h=q^i, with the stored signed original index i-e_h. The restored scalar product differs only by the acquired unit product of Vhat_h powers. The common phase inversions, mixed barpi^(-2m), enlarged L<4H and conductor-dependent r<=k^(1/3) are all retained.

For n retained points, multiply row i of R_(i,j)=(q^L z_i;q)_j/(z_i;q)_j by (z_i;q)_(n-1). Its column polynomial is exactly

    Q_j(z)=(q^L z;q)_j*(q^j z;q)_(n-1-j).

Its degree is n-1. Thus det(Q_j(z_i))=det(coefficients Q_j)*prod_(i<j)(z_j-z_i), with the source's Vandermonde orientation. Evaluation at z=q^(-i) gives the claimed triangular zero pattern, the cyclic-column sign and the n-1 negative factors in the remaining column cancel, and the coefficient determinant is

    K_n=q^(2*binom(n,3))
        *prod_(t=0)^(n-2)(1-q^(L-t))^(n-1-t).

This agrees with the reversed-column specialization of the primary corollary, including n=1 and the q power. All q-grid divisions in the independent coefficient check are guarded short unit differences. Consequently the displayed identity is lawful over the actual finite commutative algebra after the short denominators are screened; it does not require long Pochhammer values to be units.

The contiguous relation (z;q)_j P_L(q^j z)=(q^L z;q)_j P_L(z) is an exact polynomial identity. On the certified short-head branch it gives M=diag(P_L(z_i))R and detM=detR*prod_i P_L(z_i), including collisions. No covered product is divided out.

## Separation, heads and direction data

The optional exact global deduplication is explicitly only within each class. Original separation is not silently transferred to shifted roots. Product-tree/MPE derivative classification plus one localized distinct pair pays for actual shifted separation in soft k. A globally nonzero pair with saturated norm has both coordinates zero at the nonsplit side; some coordinate is globally nonzero, yielding a proper gcd. This establishes the claimed factor-or-unit branch without enumerating all pairs.

At the good smaller-nonsplit label the shifted unique-hit index exceeds B/2>r. Hence every first-(n-1) head factor is nonzero there. Any nonunit head norm therefore supplies a proper factor on that good branch; wrong labels may decline on a saturated auxiliary value. These are actual original short indices, not an unproved outside-horizon consumer.

Removing exact duplicate nonhit rows preserves the projective coarse readout by a nonzero LOCAL multiplier at the good zero. It is not asserted to preserve the literal full-r scalar product or the old uniform class-size formulas. For the full multiset, a zero Vandermonde is explicitly not called a unit.

The head preprocessing costs O(r^2) for all prefix polynomials and soft(J+r^2) for grouped MPE and derivatives, which is soft k. The K_n are acquired from actual short q differences. Ordered Vandermonde products are acquired by cross-product MPE in soft n per class. Their inverses, heads and K_n are all genuine global units on the continuing branch.

The log derivative of the ordered Vandermonde at z_i is F_c''(z_i)/(2F_c'(z_i)); subtraction of the head logarithmic derivative gives exactly formula (3). Division by 2 and all displayed inverses is certified. Directions 1 and the class label are legitimate weak coarse-label directions in the inverse points; their ratio at the unique zero is the desired coarse label. In particular this does not silently equate inverse-point directions with the old native-root motion. Unit normalization and deletion of nonhit duplicates multiply both useful outputs by the same nonzero local factor at the good zero.

## Cost and unresolved initialization

The rational-Newton action and transpose are for the short R only; fixed precomputed unit inverses make the action circuit linear in its supplied vector. Their cost and the total short normalizer/direction cost are soft k across the family. Dense r^2 matrices are not required.

Long M entries and their determinant/gradient remain unacquired. The known C=0 value is not an initial point on a native nonzero q orbit. The finite first-order equation in C does not initialize evaluation at the native unit, and its degree-nL coefficient execution and possible q-denominator resonances are explicitly charged rather than removed. No infinite theta tail, free Casoratian amplitude, generic lower bound or whole-query speedup is claimed. The old complete soft k^(3/2) query remains the valid continuation.

No source/shared files were edited, no numerical experiments were used, and repository preservation validation is outside this review.

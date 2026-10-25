# Original scalar application of the sheared-norm primitive

2026-10-22. Independent constructive attempt; scratch only. The near-linear known-support norm constructor is accepted as proved in `sheared-norm-constructor.md`. This report does not promote it to a collision evaluator.

## An exact computable block representation

Let Y be any supplied subset of the original acquired targets y_j=beta^(N+delta_j), J=|Y|<=m. Put q=beta^(m²). For a common seed interval [a,a+ell), write ell=mK+t, 0<=t<m, and define

 A_m(X)=product_(r=0)^(m−1)(X−q^r),
 R_Y(T)=product_(j in Y) product_(r=0)^(m−1)(y_j−Tq^r).

This is a scalar polynomial of degree Jm and unit constant coefficient C=product_j y_j^m. It is exactly a resultant, with a specified sign convention:

 R_Y(T)=Res_X(A_m(X), product_j(y_j−TX)).

The ORIGINAL query is exactly

 product_(b=0)^(K−1) R_Y(q^(a+mb))
 times product_j product_(r=0)^(t−1)(y_j−q^(a+mK+r)).          (1)

No root, hidden order or interpolation hypothesis is used here. Every factor in (1) is an original labeled scalar difference. Hence proper factors and saturated localization retain the existing bounded-leaf route. Row restriction changes only Y; interval restriction changes a,K,t. The final partial block is an actually paid degree-t product evaluated at J targets, in soft O(m+J) bit work.

A_m is acquired in soft O(m) by a product tree (or q-binomial coefficients), with no cross-factor inversions. All q powers have logarithmic exponent bitlength. This representation therefore pays its input and the incomplete block. The remaining operation is the K-term geometric product of R_Y, with K=Theta(m).

## What can genuinely be acquired in soft m

The first d=O(m) coefficients of the **normalized** R_Y/C are acquired in soft O(m+J) bit work, not merely specified formally. Its logarithm is

 log(R_Y(T)/C)=−sum_(s>=1) [T^s/s]
                   (sum_j y_j^(-s)) (sum_(r=0)^(m−1)q^(rs)).   (2)

Acquire the first d target reciprocal power sums from the already-paid degree-J target polynomial using its reversed logarithmic derivative and fast series arithmetic. The second factor in (2) is (1−q^(ms))/(1−q^s), with unit denominator for s<=d<16m². Integration/exponentiation uses only integers s<=d, also units because the retained primes exceed16m². This actually constructs R_Y mod T^(d+1), including all native beta scalars and carries. C is a paid shared scalar power. The truncated exponential is an algebraic formal-series computation over Z/N, not an analytic approximation.

This is a valid compact acquisition, but the same prefix principle was already audited in the Padé/long-product work; it is not presented as a newly solved query. Formula (2) is useful for comparing the NEW norm primitive with the actual original scalar source: the latter has a paid moment prefix as well, but its desired values are not the prefix.

## Why the new known-support multiplication does not yet complete (1)

The sheared cyclic norm succeeds because its coefficient z^j has at most three possible Y exponents, yielding O(m) KNOWN total support and interpolation nodes whose exponent span is below16m². Its fixed tangent preserves a similarly narrow Newton strip.

For R_Y(T), the formal candidate support is all 0,...,Jm. Over characteristic zero with independent y_j,q all coefficients are nonzero; specializing to the native values might create cancellations, but their existence, support and acquisition must be proved. The native stationary congruences do not by themselves assert any coefficient vanishing of R_Y. We have NOT proved that the actual support is large; we have simply not identified a small public support on which the new constructor can interpolate this polynomial.

Equivalently, directly encoding all original differences into one cyclic norm requires replacing the cyclic defining polynomial X^m−Y by A_m(X). This is a geometric grid, not a root-of-unity fibre. The conjugation X->−X used in Graeffe does not preserve its root multiset. The replacement has an acquired degree-m defining equation but loses the exact two-conjugate recursion on which the O(m) support proof depends. No theorem in the new primitive licenses that replacement.

Known-support interpolation at Jm+1 nodes would acquire R_Y fully, but costs soft O(Jm), hence soft O(m²) in the native regime. This is an upper bound for that explicit completion, not a lower bound on all scalar norm algorithms. Likewise first d coefficients plus the implicit resultant do not determine the K required values by a paid operation presently supplied.

## Concrete remaining constructive bridge

The exact representation (1) isolates a useful possible next theorem: acquire

 product_(b<K) Res_X(A_m(X), product_j(y_j−q^(a+mb)X))

in soft O(m+J), using the native y_j and all beta carries. A proof could exploit a new narrow-support invariant under geometric-grid norms, or a source-specific identity contracting the moments in (2) without expanding Jm coefficients. It must retain the original scalar factors; an auxiliary cyclic norm's zero support is not enough.

This pass supplies an actually acquired block polynomial, partial-block evaluation and O(m)-coefficient resultant prefix, with exact source-preserving factorization. It does not find the needed contraction, does not improve the known soft O(m^(3/2)) general query bound, and does not complete the sixth-rate factorizer. In particular no new representation has been silently counted as a paid resultant.

# Native antipodal geometry after colour normalization

This is an exact paid reduction for the current scalar gamma source. It does not reduce the dominant evaluator cost. Let d=m^2, q=gamma^d, Q=q^m, L=mK+t; assume the earlier translated-mask boundary stage has already reduced to H_e at y_j=gamma^(E_j-d*kappa_j). Here

    H_e(X)=prod_(r in R_e) prod_(0<=n<K)(X-q^r Q^n),
    R_e={0} union residues of quadratic sign e,
    kappa_j=-Delta_j/(4*a_j*j) mod m in [0,m),
    e_j=Legendre(N*j,m).

## Exact bounded antipodal carry

For j'=m-j, a_j'=a_j=a and

    b_j'=2a-b_j-ms,
    ell_j'=-ell_j-ds,
    Delta_j'=Delta_j+2 ell_j s+d s^2.

Since both b values are centered, s is one of 0,1,2. Consequently

    kappa_j'=-kappa_j-s mod m,
    u=(kappa_j+kappa_j'+s)/m is one of 0,1,2,
    y_j*y_j'=C_a Q^(-u), C_a=gamma^(2(N+a)).

Also e_j'=e_j*Legendre(-1,m). The (m-1)/2 antipodal pairs are indexed without repetition by a in N times the nonzero-square coset modulo m. Thus after bounded Q-shift removal their centers are exactly the explicit geometric subsequence C_a, with no remaining higher-input carry. Center parameters cost O(m) public arithmetic items.

## These bounded shifts are paid jointly

Write D0=(m+1)/2, D=K D0 and

    B_(e,n)(X)=prod_(r in R_e)(X-q^r Q^n).

For u=0,1,2,

    H_e(Q^(-u) z)
      =Q^(-uD) H_e(z)
         *prod_(n=K to K+u-1)B_(e,n)(z)
         /prod_(n=0 to u-1)B_(e,n)(z).

Only n in {0,1,K,K+1} is needed. The roots and coefficients of these constant-many degree-D0 block polynomials, and all their values at z_j=C_a/y_j, are acquired by product trees and batched MPE in soft O(m+J) work. Denominators are not silently discarded: localize a nonunit block value to its scalar gamma-power leaf and use gcd/annihilator recovery. In original row coordinates its index is kappa_j'+r+m(n-u), contained in [-2m,L+2m]; the explicit public bound min E_j>d(L+3m) suffices for every such exponent ledger to be nonzero. Otherwise preserve the inherited finite/ledger handling. For K<2, all H polynomials have O(m) degree and are acquired directly, avoiding overlapping-boundary 0/0. All these operations retain the original gamma source.

Hence the entire paired query is reduced, with paid boundaries, to

    H_e(y_j) * H_(e*Legendre(-1,m))(C_a/y_j)

for one representative j of each antipodal pair. This removes u exactly but only folds a constant number of rows.

## Exact reflection law and remaining coupled points

Set C0=Q^K and

    S_e=K*sum_(r in R_e)r + m*D0*K*(K-1)/2.

Negating nonzero residues changes e to e*Legendre(-1,m). Reflecting the n interval keeps all these roots; the residue-zero roots replace 1 by C0. Therefore, as a rational identity,

    H_(e*Legendre(-1,m))(C0/X)
      =(-1)^D q^(S_(e*Legendre(-1,m))) X^(-D)
         *H_e(X)*(X-C0)/(X-1).

For the actual w_j below, w_j-1 has annihilator ledger E_j' - d*(kappa_j'+m*(K-u)), while w_j-C0 has ledger E_j' - d*(kappa_j'-m*u), up to a nonzero sign. These lie in the already checked index range. Thus the X=1 denominator is handled by symbolic cancellation or localized scalar recovery, not interpreted as a harmless unit without checking.

For the actual pair set

    w_j=C0*y_j/C_a.

The two H evaluations thus become same-palette evaluations at y_j and w_j, up to the displayed elementary unit/boundary factors, with

    w_j/y_j=Q^K*gamma^(-2N)*gamma^(-2a_j).

This is a genuine common geometric dependence on the pair parameter a. It is stronger than treating the centers as arbitrary supplied units. It does NOT place all y_j on one known short gamma-grid: their full exponents E_j-d*kappa_j and their carried phases remain in the points. The reduction supplies O(m) known coupled nodes, not an evaluator for H at those nodes.

No identity or algorithm acquiring these same-palette paired values below the existing soft sqrt(JL) query cost was established in this pass. In particular the common quadratic-residue description of the center index a has not converted the multiplicative H query into an additive Gauss sum. The remaining constructive target is evaluation of H_e simultaneously at the coupled pairs (y_j, B gamma^(-2a_j)y_j), B=Q^K gamma^(-2N), with the actual native carried y_j. The paid boundary and reflection reductions above do not assume such an evaluator.

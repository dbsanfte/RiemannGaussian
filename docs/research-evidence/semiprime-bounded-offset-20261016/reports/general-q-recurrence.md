# No small positive-order, small-degree univariate q-recurrence for the chirped segment

2026-10-16. A source-specific recurrence-format obstruction. This does not bound arbitrary algorithms or every representation of the query.

## Statement on the retained actual family

Use the ORIGINAL qualified balanced source: N=P Q with P,Q=Theta(M³), current auxiliary primes m=Theta(M), d=m², and the literal g=gamma having distinct prime local orders R_P>P^.677 and R_Q>Q^.677. Put q=g^d, L=2d+2, and

 product_(i=0)^(L-1)(1-q^i t)=sum_(k=0)^L c_k t^k,
 A_k=c_k g^(-binom(k,2)).

In each hidden field all A_k are nonzero, since both local q-orders exceed16m²>L. Remove an additional soft O(M^5.969) ordered factor pairs from the SAME original Omega(M⁶/log²M) supply, as described below. On every survivor, simultaneously in either hidden field and at every current candidate, there is NO recurrence

 sum_(t=0)^r P_t(q^k) A_(k+t)=0, 0<=k<=L-r,                         (1)

where r>=1 is an integer, the field polynomials P_t are not all zero, their degrees are at most D>=0, and

 r(D+r)<=m.                                                       (2)

The coefficients may be fully advised and depend on the hidden field and full input. Positive order r>=1 is ESSENTIAL to this precise formulation: for r=0, (2) would not constrain D, and a polynomial vanishing on all required q-nodes would give a trivial relation. Zero endpoint coefficient polynomials are permitted; not all P_t may vanish.

## The simultaneous arithmetic nonalias condition

For every comparable m remove pairs for which either prime local order R divides ANY member of the signed hyperbolic catalog

 H_(s,t)=m²s-t,  s,t nonzero integers, |s t|<=m.                      (3)

This catalog has O(m log m) entries. Each integer is nonzero for m>=2: m²s=t would force |s t|=m²s²>m. Its absolute value is O(m³), so it has O(1) prime divisors exceeding c M^2.031. Each possible R gives only O(M^.969) qualified factors P=1+vR, and the opposite Q has O(M³) possible integer values in its bin. Sum over O(M) comparable m, O(M log M) catalog entries, both fields, and these cofactors. This gives soft O(M^5.969) exceptions, negligible against the ORIGINAL supply. All comparable m are an overcount; no fictitious global K_* menu is assumed. This is an application of the inherited short-exponent divisor-count mechanism, not a new prime-count theorem.

The surviving family can be intersected with previously retained majority families by unioning all exceptional sets against the same original supply. No new base is substituted for the literal source. In particular the prime-order hypotheses here are not asserted for the new arbitrary-odd-order preprocessing output.

## Clear denominators and expose the exponential bases

Fix one surviving hidden field, and write R for the prime order of g. The finite q-binomial ratios give, for every permitted k,t,

 A_(k+t)/A_k = g^(-tk-binom(t,2)) (-1)^t
              * product_(a=0)^(t-1)(q^a X-q^L)
              / product_(a=1)^t(1-q^a X),     X=q^k.                 (4)

All denominator factors are nonzero because their exponents range from1 throughL. Let

 D_r(X)=product_(a=1)^r(1-q^a X).

Divide (1) by nonzero A_k and multiply by D_r(q^k). This yields

 sum_(t=0)^r g^(-tk) B_t(q^k)=0,

where

 B_t(X)=(-1)^t g^(-binom(t,2)) P_t(X)
         * product_(a=0)^(t-1)(q^a X-q^L)
         * product_(a=t+1)^r(1-q^a X).

Every B_t has degree at most D+r. Its displayed multiplier is a nonzero polynomial, so B_t=0 if and only if P_t=0. Expanding B_t(X)=sum_u b_(t,u) X^u gives

 sum_(t=0)^r sum_(u=0)^(D+r) b_(t,u) (g^(du-t))^k=0.                (5)

## Distinctness and Vandermonde conclusion

The base array g^(du-t), 0<=t<=r and 0<=u<=D+r, is pairwise distinct. To see this, set s=u-u' and v=t-t'. A collision requires R|(ds-v).

If s=0 and v!=0, it is impossible because |v|<=r<=sqrt m<R. If v=0 and s!=0, it is impossible because gcd(R,d)=1 and |s|<=D+r<=m<R. If both are nonzero, |s v|<=r(D+r)<=m, and (3) excludes precisely this divisibility. The case s=v=0 is the same base.

There are n=(r+1)(D+r+1) bases. Since r>=1 and r(D+r)<=m,

 n<=(2r)(D+r+1)<=2m+2r<=4m.

For sufficiently large m, the available consecutive equations number L-r+1>=n (indeed L=2m²+2 and r<=sqrt m). Restrict (5) to its first n equations k=0,...,n-1. The square Vandermonde matrix on the distinct nonzero bases is invertible in the field. Hence all b_(t,u) vanish, all B_t vanish, and all P_t vanish, a contradiction. This proves the statement. Field characteristic and possible polynomial inseparability introduce no exception: the Vandermonde determinant is a product of nonzero pairwise differences.

## What is and is not excluded

This excludes fixed or polylogarithmic positive order AND degree for the standard univariate q^k-polynomial recurrence (1) on the actual chirped finite segment. It strengthens the separate first-order q-stream consequence. It is not a theorem that the original unchirped coefficients lack a short recurrence; they have their familiar first-order one.

The result does not exclude another base, multivariate coefficients, sparse high-degree coefficient polynomials, a different transform, selected-convolution sharing, or a direct scalar norm algorithm. It does not assert an operation lower bound or generic q-holonomic algorithm lower bound. The growing order/degree requirement is a rigorous failure of this specified fixed-parameter representation shortcut, not acquisition of the query. No native edit, Lean declaration or build is asserted.

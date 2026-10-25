# Tangent norm acquisition and transposition review

## Fixed-direction constructor: PASS

I independently checked the dual-number addendum in sheared-norm-constructor.md. Let F=(X+gamma)^2-z t^2 X^s(1+gamma X)^2 and supplied U(X) have degree L<=2m. In a tangent term of Norm(F+epsilon U), exactly one factor is U, so coefficient z^j has original X-exponent range [sj,sj+2(p-1)+L]. After norm invariance its Y-exponents have width at most 2+L/p. There are O(p+L) candidate slots. This remains a safe upper bound when some coefficients vanish or j=p is actually absent.

BEFORE parity filtering, V_p Q_p(-X)+Q_p V_p(-X) has strip width at most 4+L/p. Using the same floor shear as Q_p gives nonnegative stored exponents, bounded by j+4+ceil(L/p). The addendum's exponent-span estimate is safe for p<=m/2,L<=2m,m>=2; in particular it remains below 16m^2. Both cross-products are known-support sparse multiplications with the same proved unit-separated geometric nodes. Startup V_1=U is supplied explicitly and has O(L) coefficients. Summing O(p+L) over the logarithmic tower costs soft O(m+L), including repeated L, not O(mL). The actual-exponent conjugation sign and parity conventions from the denominator proof are still necessary.

At the final Y=1, differentiation of the norm in dual numbers gives EXACTLY

 V_m(1,z)/Q_m(1,z)=Tr_(A/base)[U(X)/F(X,z)].

This is an identity of formal power series, provided Q_m(1,0) is a unit. For the displayed squared denominator it equals Norm(X+gamma)^2, a unit since gamma^m-1 is a unit for dyadic m and the retained odd local orders. For R=W/X use F=g-zf with g=X(X+gamma), f=t(1+gamma X), U=B g. Here deg U<=m+1<=2m, Norm(g) is a signed unit multiple of gamma^m-1, and

 V/Q=Tr[B/(1-zR)]=sum_a Tr(B R^a)z^a.

The trace is m times cyclic CT, with m a unit modulo N. The supplied U=Bg is formed modulo no hidden characteristic. Monomial shifts X^s in f preserve the width-two support argument; g contains only fixed bounded-width nonnegative exponents, and any Laurent power is carried by exact shear metadata. Thus this is a genuine paid fixed-weight constructor also for shifted rational bases. It is not merely a formula for a derivative after an unacquired norm.

## What transposition supplies exactly

Fix R and precision m. The acquired map is the linear transformation

 T_R: B -> (CT[B R^a])_(0<=a<m).

Since every operation of the fixed-U algorithm is linear in the supplied direction, its transpose has the same soft O(m) arithmetic cost (with the same fixed denominators and normalizations). Under the coefficient pairing, the transpose computes the cyclic coefficient vector of sum_a v_a R^a, with the corresponding reversal convention if ordinary coefficient dot products replace CT. This is a real near-linear modular-composition interface for this rational R. Both directions accept ONE length-m vector and return ONE length-m vector.

For the requested diagonal, however,

 H_a=sum_k B_k CT[X^(u*a*k)R^a]
    =sum_k B_k CT[(X^(u*k)R)^a].

Hence H is a B-weighted sum of the power-projection columns of m DIFFERENT shifted bases X^(uk)R. Applying the paid shifted-base theorem separately costs soft O(m^2). Transposing one such map exchanges its input/output axes; it does not take this twisted diagonal of the entire family at the cost of one map. This statement identifies the precise linear operator still needed; it is not an assertion that the operator has a quadratic lower bound.

A multiplicative-group FFT diagonalizes the permutations k->a*k on each gcd stratum. It therefore provides a useful alternative shared basis for B. But after that transform the power-projection weight is an eigenvector indexed by the multiplicative character, and one fixed-weight call is still needed per eigenvector unless those calls have a simultaneous acquisition theorem. Writing the FFT does not remove that power-projection axis. An arbitrary acquired B=W^N is not proved to have polylogarithmic support in this eigenbasis. No such sparsity is assumed here.

## Concrete shared construction to target

The most direct simultaneous extension would compute

 S_B(z)=sum_k B_k Tr[1/(1-z X^(uk)R(X))]

through precision z^m in soft O(m), using the sparse shifted norm constructors jointly rather than separately. Its coefficient of z^a is exactly m H_a. This needs a weighted SUM of logarithmic derivatives of shifted norms, with weights the acquired B_k. A single dual-number norm only inserts ONE fixed spatial direction and does not currently implement this sum of varying rational denominators. Taking a product with coefficient exponents B_k would additionally require a justified ring-valued powering convention and would still leave its acquisition unproved; it is not a replacement algorithm.

Thus the fixed-U tangent extension and its transpose pass as actual acquired primitives. I did not obtain a simultaneous shifted-norm/logarithmic-derivative construction or a bounded-total-size direction family for the native diagonal. Such a construction would be a substantive next bridge, with an exact target series and output size m, rather than another validity check on the already-paid norms. Even that diagonal is only one native power piece: ell_j, the original seed index and scalar recovery must still be integrated before claiming the 1/6 factorizer.

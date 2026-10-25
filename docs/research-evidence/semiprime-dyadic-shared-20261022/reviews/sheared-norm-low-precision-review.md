# Low-precision sheared norm and fixed tangent: independent proof

2026-10-22. This strengthens the one-direction constructor's precision dependence. No all-branch construction or query acquisition is asserted.

## Contract

Let m>=2 be a power of two, 1<=h<=m, and R=Z/N. Supply units eta,gamma,t with eta's order modulo EACH prime divisor of N exceeding16m². Supply integer s and ONE polynomial U(X) of degree L<=2m. Exponent metadata has its native O(polylog N) bitlength. Set

 F(X,z)=(X+gamma)²−z t² X^s(1+gamma X)²,
 Norm_(X^m=Y)(F+epsilon U)=Q_m(Y,z)+epsilon V_m(Y,z), epsilon²=0.

Both Q_m and V_m modulo z^h are deterministically acquired in soft O(h+L) bit work and soft O(h+L) stored entries, including reading U. Here soft factors include log m, log N and the exponent metadata length. The bound is not independent of log|s| for arbitrary non-native huge integers.

## Truncation invariant

At level p, Q_p has z-degree<=p and V_p has z-degree<=p−1: a tangent term has exactly one U insertion and at most p−1 z factors. Neither contains negative z exponents. Therefore replacing both by their reductions modulo z^h before a Graeffe step preserves every output coefficient of z-degree<h. Laurent powers of X do not affect this assertion.

Write q=min(p,h−1). Each input has z-degree<=q (the tangent may have a smaller bound). Full products of these ALREADY TRUNCATED inputs have z-degree<=2q. All coefficients through this full product degree must be handled by the sparse multiplication, before dropping z-degree>=h.

## Candidate support and parity

Put A=floor(s/p), r=s−Ap, 0<=r<p. At level p use normalized X exponent e_actual−Aj. Denominator coefficient z^j has normalized exponent in [rj/p,rj/p+2]. Tangent coefficient z^j has normalized exponent in [rj/p,rj/p+2+(L−2)/p], safely enlarged to [rj/p,rj/p+2+L/p]. Every normalized exponent is nonnegative.

For the full products at a p->2p step, j ranges from0 to2q. Denominator support is contained in

 rj/p <=e<=rj/p+4,

and tangent cross-product support is contained in

 rj/p <=e<=rj/p+4+L/p.

Thus a public candidate support has respectively O(q+1) and

 T_p=O((q+1)(1+L/p))

integer slots. Floors/ceilings at endpoints only change constants. It can be enumerated directly in this many operations; no ambient dense exponent interval is scanned. Both tangent cross-products have the same safe support, and their sum is formed after acquisition.

Conjugation X->−X uses sign (−1)^(e+Aj), retaining the removed Laurent shear parity. After multiplying, restore e_actual=e+Aj; discard odd actual exponents; halve even actual exponents; then truncate z^j for j>=h. The resulting data are precisely the next level's truncated norm/tangent. Renormalize independently at the next level. This remains valid for negative s.

## Safe interpolation of the FULL product

Encode each candidate monomial z^j X^e as exponent E=j+(2q+1)e. This is injective because 0<=j<=2q. It also respects multiplication of the two truncated inputs. Since e<=j+4+ceil(L/p),

 E<=2q+(2q+1)(2q+4+ceil(L/p))
   <=2p+(2p+1)(2p+4+ceil(L/p))
   <=m²+13m+5<=10m²<16m²

for p<=m/2,m>=2,L<=2m; the intermediate coarse bound is the same bound proved in the full-precision constructor. The inputs themselves fit the product candidate range. Candidate exponents are nonnegative; the removed Laurent shear is metadata, not part of the interpolation span.

Consequently alpha_E=eta^E are units with unit pairwise differences. Known-support multiplication evaluates the two inputs' moment sequences at eta^i, multiplies these sequences, then inverts the transposed Vandermonde on the FULL candidate support. Product-tree rational moment summation, series inversion with constant1, MPE and derivative denominators cost soft O(T_p) bits. These operations use only proved unit interpolation denominators and monic polynomial arithmetic. The denominator-coordinate product and the two tangent cross-products require only a constant number of such operations.

IMPORTANT: setting the interpolation support to j<h while evaluating a full product would be wrong. The discarded high-j coefficients still contribute to every evaluation and can contaminate recovered low-j coefficients. The use of j<=2q and radix2q+1 above is essential. Only after exact recovery are j>=h discarded.

## Summed cost, including h=1

Sum over dyadic p=1,2,...,m/2. The cost excluding soft arithmetic factors is bounded by

 sum_p (min(p,h−1)+1)(1+L/p).

For p<h the first factor is p+1: its sum is O(h), while its L/p contribution is O(L(1+log h)). For p>=h it is h: the first contribution is O(h(1+log(m/h))), and the geometric sum of Lh/p is O(L). Hence total

 O(h(1+log(m/h))+L(1+log h))=soft O(h+L).

For h=1 specifically q=0 at EVERY level. No z-positive coefficient is constructed. The cost is sum_p O(1+L/p)=O(log m+L); radix1 is injective since j=0 only. Thus the bound includes h=1, rather than assuming a positive retained z-degree. Initial construction/reading costs O(L+1) and fits. A zero supplied U may simply omit tangent storage.

The final retained support is O(h(1+L/m))=O(h+L). Intermediate support has maximum O(h+L); product-tree working storage fits the same soft bound. All relevant integer exponents and encoded powers have logarithmic native bitlength, and modular exponentiation contributes only the stated soft factors.

## Scope

This is an actual low-precision constructor for ONE s and ONE supplied U. Different branches may have different s, modulated U, or precision h. A future all-branch bound must sum h and supplied direction sizes and account for their acquisition. This proof does not make varying numerator directions free and does not acquire the original scalar collision query.

# Executed quartic Laurent lattice attempt

24 October 2026. This initializes a rank-four Taylor lattice. Even granting the missing high-degree/high-order seed, its optimistic optimized execution costs soft k^(9/7), worse than the current signed two-weight k^(5/4). No new factoring algorithm or general obstruction to extension-field methods is claimed.

Credit the fixed-rank Taylor/centering construction in /tmp/semiprime-native-terminal-20261024/cubic-cover.md, SHA256 `9ca92557ef8b5229143e0ac2162e890d87b3b61d8bed18ce4bb1d0fd6844dec2`. The current complete comparator is /tmp/semiprime-arithmetic-query-reuse-20261024/signed-two-weight-query.md, SHA256 `b36e44e9d5e2c897caac87d6ad6339548fd9d438bd21352bd50971ff236efc93`.

## Exact congruence initialization

Let N=RS<=k^6, gcd(N,k)=1, j a public unit tag. Put

    G(X)=aX²+bX+cN/X+dN²/X²,
    f(X)=X²(G(X)+ell)=aX⁴+bX³+ell X²+cNX+dN².

For clock k⁴ acquire the lattice

    b=-4aj+ku,
    dN²=a j⁴-ku j³ mod k²,
    cNj=-2a j⁴+ku j³-2dN² mod k³.              (1)

Its determinant is EXACTLY k⁶: a,u are free, d is a known linear residue modulo k² plus a free k² multiple, and c is then a known linear residue modulo k³ plus a free k³ multiple. The triangular pivots in coordinate order(a,b,d,c) are1,k,k²,k³. This gives an explicit basis with polynomial-bit entries using only inverses of N,j; a failed gcd(k,N) factors first.

Set ell0=-aj²-bj-cN*j^-1-dN²*j^-2 modk⁴. Substitution proves

    f(j)=0 modk⁴, f'(j)=0 modk³,
    f''(j)/2=0 modk², f'''(j)/6=4aj+b=0 modk.

These are integer Taylor coefficients, with no inverse of2 or3. Therefore f(j+kx)=0 modk⁴ for every integerx. At own tag j=R modk, division by the unit R² proves (G(R)+ell0)/k⁴ is an integer.

## Derivative map and exact remainder

Fix public B>0, Delta=eta B, 0<eta<=1/2. Parameters are rational of polynomial height, Delta>=1. Define

    u=aB², v=bB, w=cN/B, z=dN²/B²,
    A1=2u+v-w-2z, A2=u+w+3z,
    A3=-w-4z, A4=w+5z,
    W_r=eta^r A_r, 1<=r<=4.

The A-map matrix is [2,1,-1,-2;1,0,1,3;0,0,-1,-4;0,0,1,5], determinant1. The monomial scaling has determinant N³. Thus the EXACT absolute determinant of this rational map is N³ eta^10, and the image lattice covolume is

    k⁶ N³ eta^10.                              (2)

Clear denominators, run fixed-rank LLL and rescale. The usual dimension-four first-vector bound supplies a nonzero(a,b,c,d) with max|W_r|<=T=2(k⁶N³eta^10)^(1/4); factor2 exceeds2^(3/4). Use exact upward integer-power/root rounding for an algorithmic T. The inverse map and cleared basis have polynomial height for B and eta of polynomial range; lattice work is polynomial(logN) per row.

For x=(X-B)/B there is the EXACT identity

    G(B(1+x))-G(B)=A1*x+A2*x²
        +A3*x³*(1+2x)/(1+x)²+A4*x⁴/(1+x)².      (3)

For |x|<=eta<=1/2, 0<=(1+2x)/(1+x)²<=1 and (1+x)^-2<=4. Hence the variation is at most7T. Center by the exact signed rational floor

    nu=floor((ell0+G(B))/k⁴+1/2), ell_c=ell0-k⁴nu.

Then |G(R)+ell_c|<=k⁴/2+7T in this interval. The signed horizon |i|<=U=ceil(1/2+7T/k⁴) covers the own index.

## Frobenius target and the unpaid seed

In a public small-conductor cyclotomic algebra, enumerate sigma_t. At a local factor R with R modulo conductor equal to t, actual Frobenius is sigma_t. Given an actual unit pi, the public expression

    pi^ell_c sigma_t²(pi)^a sigma_t(pi)^b
             sigma_t^-1(pi^N)^c sigma_t^-2(pi^(N²))^d    (4)

equals pi^(G(R)+ell_c) locally. Indeed sigma_t(pi^S)=pi^N and sigma_t²(pi^(S²))=pi^(N²). Only public automorphisms and signed polynomial-bit powers occur in(4); the unknown factor is not an exponent input. The clock would be pi^(k⁴).

If a group collision implies INTEGER G(R)+ell_c-k⁴i=0, then the nonzero integer quartic

    aX⁴+bX³+(ell_c-k⁴i)X²+cNX+dN²             (5)

has proper factor R as an integer root. Constant-degree exact roots/gcd validation handle all degenerate leading coefficients. Nonzero lattice vector prevents an identically zero polynomial.

But that implication requires a sufficiently large acquired order. Current quadratic pi certifies only order>256k⁴, versus quartic variation of scale k⁶eta^(5/2) at N~k⁶; its higher Frobenius powers also repeat with period2. A small cyclotomic prime with order_l(R)>2 does not supply a high-order unit. Nor is the full primitive algebra necessarily a field: norm zero can occur in any Frobenius orbit. Every possible supporting orbit needs an adequate order bound, or a new acquired support selector. No such supplier/selector is provided here. The primorial observation that some small l must have order_l(R)>2 does not close these gaps.

## Explicit optimistic cost and centre-localization qualification

Cover each dyadic factor bin[S,2S) by O(eta^-1) comparable centres with radius eta B. Acquire k tag rows per centre, so J=soft(k/eta), and

    h=O(1+T/k⁴)=O(1+N^(3/4)eta^(5/2)/k^(5/2)). (6)

All vectors, signed centres, targets, coefficients, giant arguments and residuals are charged. For an optimistic BATCHED-CENTRE norm query, grant a unit pi whose order at EVERY possible local cyclotomic support in the correct Frobenius label exceeds a strict public upper bound for

    max_rows[ |a|(2S)²+|b|2S+|c|N/S+|d|N²/S²
                                      +|ell_c|+k⁴U ].

This stronger grant validates every selected leaf in the bin, not only rows whose Taylor interval contains R. Without it, aggregating centres and decoding an arbitrary saturated leaf repeats the wrong-bin error repaired in the two-weight algorithm. Frobenius labels and dyadic factor bins themselves are attempted separately, with polylogarithmic enumeration.

Under this explicit free-seed grant, the old zero-safe monic q-product batch and norm localization cost soft(J+sqrt(Jh)). At N~k⁶ this becomes

    soft(k/eta+k^(3/2)eta^(3/4)),               (7)

optimized at eta comparable to k^(-2/7) to soft k^(9/7). Choose eta by exact rational rounding. Here both J and h are of this order, so dense coefficient/MPE execution also gives a literal completion at the same cost under the grant. The result is already worse than current k^(5/4), before paying a new seed supplier.

If only the CORRECT-CENTRE remainder-order guarantee is granted, run centres separately, permitting bounded failure on other centres. The cost is instead soft(k/eta+k^(3/2)eta^(1/4)), optimized at eta~k^(-2/5) to k^(7/5), worse still. These are costs of the specified executions, not lower bounds on different recurrences or representations.

This report supplies actual congruences, derivative determinant, remainder estimate and a conditional cost comparison, not a new acquired factoring route. Old cubic work and known fifth rate are credited. Current fixed-scale improvement and open sixth/Lean goal are unchanged. No shared/frozen source or numerical coverage campaign was used.

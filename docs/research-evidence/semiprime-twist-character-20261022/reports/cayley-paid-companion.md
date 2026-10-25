# Cayley transform: paid whole-product companion

22 October 2026. Independent exact audit; no acquisition evaluator or improved factoring bound is asserted.

Work in Z/N for odd N=PQ. Let gamma have odd order in both local fields. Assume x_j, u and q are gamma powers; in particular every y_i=u q^i lies in the same prepared odd-order subgroup. Merely assuming q is such a power does not suffice for an arbitrary u. Every subgroup element t has t+1 a unit, since -1 has order two at each prime. Thus

    T(t)=(t-1)/(t+1)
    T(x)-T(y)=2(x-y)/((x+1)(y+1))

is defined and preserves the exact local zero mask, not just its aggregate parity. For J targets and L seeds,

    R_T = product_(j,i)(T(x_j)-T(y_i))
        = 2^(JL) R / (A^L B^J),
    A=product_j(x_j+1), B=product_(0≤i<L)(1+u q^i).

A, B and 2 are units. The companion C=2^(JL)/(A^L B^J) is a publicly computable unit; hence R_T=C R even when R is a nonunit. No division by R is used. Proper gcd extraction is unchanged; at a selected saturated leaf the original exponent ledger can still be used for annihilator recovery.

## Full companion cost

A and all transformed targets cost soft O(J). B can be computed without enumerating L seeds: choose b≈sqrt L and write L=Kb+r. Form f(X)=product_(0≤h<b)(1+u q^h X), evaluate f at q^(bk), 0≤k<K, and multiply these values with the at most r remaining factors. Product construction, monic multipoint evaluation, generation of the points and final multiplication cost soft O(b+K)=soft O(sqrt L) ring operations. All remainder-tree divisors are monic; composite-ring point differences are never inverted. The leading coefficient of f is a unit if normalization is wanted, but normalization is unnecessary for evaluation.

Raising the three units to L, J and JL adds logarithmic costs. Consequently the ENTIRE companion is paid in soft O(J+sqrt L), with the usual modular multiplication bit cost, rather than JL. For an interval [a,a+L), replace u by u q^a; this stays in the subgroup. For an arbitrary supplied target subset, replace A and J accordingly. A union of separately supplied intervals pays the sum of their scalar square-root costs; no uncharged arbitrary seed subset claim is made. Empty products have value one.

## Transformed orbit and source-preserving identities

Put v=T(q), s=T(t). Direct calculation gives

    T(qt)=(s+v)/(1+vs),
    1+vs=2(1+qt)/((q+1)(t+1)),
    1-v²=4q/(q+1)².

Both displayed denominators and 1-v² are units. This proves that every transformed orbit step is valid over Z/N, including q=1. More generally T(xy)=T(x)⊕T(y), where s⊕t=(s+t)/(1+st); the denominator is a unit on the subgroup image. The transformed kernel obeys

    (s⊕v)-(t⊕v)
      = (1-v²)(s-t)/((1+vs)(1+vt)).

This supplies an exact paid projective form of the original q-shift. It is not ordinary additive translation by v; dropping its denominator would change the kernel. Since T has public inverse (1+s)/(1-s), and 1-s is a unit on its image, the one-step orbit recurrence alone is precisely a conjugate of the original one.

There is nevertheless a genuine additive simplification of reciprocal labels:

    T(t^(-1))=-T(t).

Its possible use must retain the zero ledger. In particular

    T(x)+T(y)=2(xy-1)/((x+1)(y+1)).

Thus replacing T(x)-T(y) by T(x)²-T(y)² introduces the reciprocal collision xy=1 as well as the original collision x=y. The new plus factor is not automatically a unit. Such a transform can preserve all original events, but extra events must be localized and discharged using a nonzero exponent certificate; it is not a free cancellation of the original product.

The strongest paid conclusion is therefore the exact whole-norm identity R_T=C R with C acquired in soft O(J+sqrt L), valid on every prepared input and every supplied target restriction/seed interval. No additional additive recurrence or cancellation was found that computes R_T, or a factor-producing observable of it, at that cost. Unlike a leafwise unit-factor observation, the full companion itself is already acquired.

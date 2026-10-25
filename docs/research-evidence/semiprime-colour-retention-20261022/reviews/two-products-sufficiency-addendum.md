# Sufficiency addendum: simultaneous H values need no extra H-localization oracle

22 October2026. New addendum; the archived independent review is not modified. Verdict: PASS. Supplied simultaneous values of H_+ and H_- at their assigned y_j are sufficient, together with the already paid boundary work, to factor in the native soft-m budget. No further evaluations, interval restrictions, or localization oracle for H_± are required.

Retain the exact scalar setup and checked identity from two-common-products.md:

    C_j(y_j) V_j(x_j)
      =q^(kappa_j D_j) H_(sign_j)(y_j) A_j(y_j) B_j(y_j),
    x_j=gamma^E_j, q=gamma^(m²),
    V_j(x_j)=product_(selected native i)(gamma^E_j−q^i).

First perform the paid boundary acquisition/screens. A nonunit boundary value already gives a proper factor or a useful saturated scalar leaf by the reviewed procedure. On the remaining branch all A_j,B_j,C_j values and scale factors are units. Consequently H_(sign_j)(y_j) and V_j(x_j) have EXACTLY the same local nonunit support. In particular a nonunit supplied H value certifies a nonunit native masked product without any numerical division by that product.

## Selecting a row and recovering the original unmasked interval

Take gcd with N of each of the J supplied H values. A proper gcd directly factors. If one is saturated, select that row. Its masked product V_j is nonunit. Since V_j is a literal factor of

    U_j[0,L)=product_(0<=i<L)(gamma^E_j−q^i),

the original UNMASKED scalar row product is nonunit too. This implication does not ask which mask residue caused the nonunit. It only selects one public target x_j for subsequent ordinary interval localization.

If every H value were a unit, all masked products would be units. That contradicts the retained true own-tag collision, which is inside one of those masks. Therefore the coverage promise supplies a selected row unless the boundary work has already terminated successfully. For K=0 the common products equal1, so the same argument says any retained collision must already be found by the fully paid boundary products.

## Paid scalar interval product: the inherited degree-one block primitive

For any supplied scalar x, integer a>=0 and length n, acquire

    P(x;a,n)=product_(0<=h<n)(x−q^(a+h))

in soft O(sqrt n+1) modular work. For completeness, choose b=max(1,ceil sqrt n), form the explicit degree-b polynomial

    F(T)=product_(0<=r<b)(x−q^(a+r) T),

and evaluate it at T=q^(bs) for the floor(n/b) complete blocks. A monic product/remainder-tree multipoint evaluator costs soft O(b+n/b), including construction of F and the block points. Multiply all block values and fewer than b tail factors. Computing q^a,q^b adds only logarithmic work. The n=0 case is the empty product1.

No point-difference inverse, hidden field, unknown local order, or H coefficient is used. All multipoint-tree divisors are monic over Z/N. A zero block product causes no division. This is the same inherited scalar geometric-product construction already stated in /tmp/semiprime-character-acquisition-20261022/character_counts/cayley-paid-companion.md, paragraphs describing B and interval shifts; it is also the degree-one q-factorial block construction used throughout the paid query reports.

## One-path localization and every saturation case

Maintain an interval [a,a+n) whose original unmasked row product is known nonunit. Initially this is [0,L), certified by the selected H value; an initial scalar product evaluation is optional and still fits the same bound. If n>1, split it into two nearly equal intervals and acquire the left interval product with the scalar primitive.

- If its gcd with N is proper, return that factor.
- If its gcd is N, the left interval is nonunit; continue there.
- If its gcd is1, the left product is a unit. Since the parent product is nonunit and equals left times right, the right interval is nonunit; continue there without evaluating a right sibling merely to re-establish the invariant.

At n=1 acquire the scalar difference and its gcd. It cannot be a unit by the invariant. A proper gcd factors; a saturated gcd gives

    gamma^(E_j−m² i)=1 mod N.

All gaps are positive: the prior review proves E_j>m²(L+m) from the retained bounds P,Q>16m², E_j>=N−3m² and L<=4m². Thus E_j−m²i>0 for every0<=i<L, and its bit length is O(log N). Apply the inherited prepared-gamma annihilator decoder once. This supplies the required useful original leaf even if the localized leaf happens to be outside the quadratic mask. The mask was needed to select a nonunit row, not to certify usefulness of each unmasked leaf.

The path lengths shrink geometrically. Hence total scalar-product work is bounded by

    soft O(sum_(0<=h<=ceil(log_2(max(1,L))))sqrt(ceil(L/2^h))+log(L+1))
       =soft O(sqrt L+1).

There is one path, not both children at every depth. Modular gcds, shifts/powers, and the final decoder cost only logarithmic overhead plus soft O(N^(1/12)), which fits soft m. Since L<=4m², localization is soft O(m).

## Exact final interface and cost

The remaining constructive theorem needs ONLY the J assigned scalar values

    H_(sign_j)(y_j),  1<=j<=J,

acquired simultaneously in soft O(m+J). The values need not come with H coefficients, per-row root catalogs, or a restriction-stable H oracle. Once those values are supplied, the boundary acquisition, J gcds, one-row scalar localization, and the original decoder cost soft O(m+J+sqrt L+N^(1/12))=soft O(m+J) in the retained regime.

This closes the sufficiency/localization interface. It does NOT supply the simultaneous H evaluator or improve the currently known dominant long-query cost. Only this new addendum was written; no archived review, source report, repository file, backend, or numerical campaign was changed.

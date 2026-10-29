# Arbitrary acquired label roots: paid permission and query audit

26 October2026. The proposed factor-or-exact-roots construction is valid with two qualifications: first-drop recovery uses the previous projected clock q_prev, and the remaining root exponents need the stated valuation margin. It extends an already-paid small-coindex construction to arbitrary acquired nonzero short labels. A further factor-or-unit-separation consequence is paid below. No whole-query contraction is proved.

Prior credit: read `semiprime-query-continuation-20261022/reports/shared-coindex-roots.md`. It already acquires roots for every t<=k by factorial cleaning and outside-product exponent propagation. The October16 frontier had already paid smooth projection/shared roots. The present adaptation changes the supported public labels and supplies factor-returning early-drop handling; it is not a new root-extraction oracle.

## 1. Projection, signs, and exact acquisition

Let e_j be nonzero O(logN)-bit signed integers, L=soft O(k). Remove exact duplicate labels if desired, retaining original metadata. Put a_j=|e_j|, M=product_j a_j, T=ceil log2N and R=M^T. Factors a_j=1 cause no problem; if M=1 then R=1 and every root is b or b^-1.

The retained base beta has odd coprime local orders, and q=beta^H has both orders>16H. Before constructing roots, test q^R by the existing arbitrary-unit small-order separator at cap16H. If both projected orders remain large, continue. Otherwise use the monotone prefix search in Section2 to return a factor.

Acquire w=beta^(M^(T−1)). A balanced integer product tree on a_j propagates complement powers from w: a node receives w^(M/product_of_its_labels), and its children are obtained by raising to the sibling's product. At leaf j this gives beta^(R/a_j); invert it for e_j<0. Thus

    b=beta^R, beta_j=beta^(R/e_j), beta_j^e_j=b.       (1)

All signed exponent operations use known units. The integer R has O(L log²N) bits; w's exponent has the same scale. Each complement-tree depth has total exponent bitwidth O(logM+L), so acquisition of every residue costs soft O(L) bits, including integer products, modular exponentiation, signs and storage. It does not perform L separate full-length exponentiations. No factorization of M, its labels or any local order is needed.

## 2. Factor on the first projected order drop

Expand the exponent schedule conceptually as the list a_1,...,a_L repeated T times. Its length is LT, and its product is R. For prefix product D, the clock is q_D=(beta^D)^H. Both local orders decrease monotonically along this schedule and remain coprime and odd. Each requested D and q_D is acquired via the product tree in soft O(L) bits; do not store all large prefix products separately.

Binary search for the first prefix with a local q_D order<=16H, using the existing separator. A proper gcd immediately factors. Any exact common local order returned there is1, because the projected local orders are coprime. After O(log(LT)) calls one obtains adjacent prefixes D and D a_j, with the previous q_D having both odd local orders>16H and

    (q_D)^a_j=1 modN.

The single nonzero short integer a_j is a GLOBAL annihilator of q_D and is passed to the licensed soft N^(31/192) extractor. It need not annihilate beta^D itself: remaining H-primary order can distinguish those two bases. This is the important projected-base qualification. The wide D or R is never submitted as the short annihilator. Values a_j=1 cannot be first-drop steps. Total separator/search/extractor work is soft O(k), including all prefix acquisitions.

## 3. Matching orders and the T−1 valuation margin

Let r be either original beta order. It divides p−1<N/A, A=16H+1, so v_ell(r)<log2N−log2A for every prime ell. Since T=ceil log2N and A>16, T−1 exceeds every possible such valuation by ample margin.

For ell|M,

    v_ell(R/e_j)=T v_ell(M)−v_ell(a_j)
                   >=(T−1)v_ell(M)>=T−1.

Hence R/e_j kills every M-primary part of r, even at a leaf containing all of a prime's M-valuation. For ell not dividing M, neither R nor any e_j changes its valuation. Consequently all beta_j and b have exactly the same local orders r*, generate the same local cyclic subgroup, and gcd(e_j,r*)=1. Equation(1) therefore supplies the unique signed e_jth root of b inside that retained subgroup. The same statements apply to q_j=beta_j^H and q_b=b^H; their local orders agree and exceed16H by the retained q^R screen. Including H as one additional public label is an optional paid way to kill all H-primary order as well; it is not required for (1).

## 4. Additional paid consequence: factor or unit-separated root nodes

For distinct integer labels, acquire F(X)=product_j(X−beta_j), F', and all F'(beta_j) in soft O(L) by monic product/remainder trees. If every derivative value is a unit, all pair differences beta_j−beta_l are certified units at both primes.

Otherwise a proper derivative gcd factors immediately. For a saturated derivative choose that row and scan its O(L) actual differences, yielding a proper gcd or a globally equal pair beta_j=beta_l. In the latter case (1) implies

    beta_j^(e_j−e_l)=1 modN.

The signed difference is a known NONZERO O(logN)-bit integer; beta_j has both large odd local orders. The licensed extractor factors in soft k. Exact duplicate labels were removed to prevent a zero annihilator. Thus the continued branch has an acquired degree-L root polynomial with certified unit-separated nodes, at soft-k total cost. This is a factor-or-separation proof, not an invalid inference from small exponent differences. The same operation on q_j uses q_j^e_j=q_b and the large q_j orders, and can certify separated row-clock bases too.

For the old t<=k family separation followed from |t−s|<order. Here labels can be much larger, so this explicit factor-returning derivative test is the meaningful extra acquired interface.

## 5. Native collision transport and knot/cyclic product test

Take e_j=E_j=a+bN+lambda from retained original scalar rows. E_j=0 has already been removed. An original local collision beta^E_j=beta^(Hi) survives raising to R/e_j and becomes

    b=beta_j^(Hi)=q_j^i.                             (2)

Cleaning is not injective on the original subgroup, so it can introduce extra collisions. They are safe: a nonunit difference in (2) yields a proper gcd, or a saturated equality gives

    beta_j^(E_j−Hi)=1 modN.

The old public whole-row deletion certifies E_j−Hi!=0 throughout the actual searched signed interval; its bitwidth remains O(logN). The large-order beta_j is therefore a legal extractor base. No wide R(E_j−Hi)/E_j label or knowledge of the physical witness is needed. Signs and inverse orientations retain their stored original labels.

The full transformed query is now a COMMON target b against DIFFERENT row bases q_j, not the earlier common-base geometric query. For positive indices its scalar is

    product_j product_(i=1)^m (b−q_j^i).

At a fixed i this equals, up to the conventional resultant sign, Res(F_q(X),X^i−b), F_q=product_j(X−q_j). Its value is genuinely acquired in soft O(L log i) by powering the supplied q_j. But the product over all i remains unacquired. The finite clock polynomial after swapping the two products is product_(i=1)^m(X^i−b), of degree m(m+1)/2; treating that short product descriptor as a paid resultant would lose the target bound. A single cyclic norm supplies one exponent i, not every shorter exponent.

Likewise lawful cabling uses beta_j^e_j=b to collapse a companion evaluation at that particular winding. That equality is a tautology already supplied by (1); it does not identify which unknown i makes (2) hold. To encode all physical i one must retain their different windings or prove a new finite composition law. The ordinary exterior/satellite product identities in the preceding packets do not supply such an initialization. In particular the previous common-base baby polynomial cannot silently be reused across the different q_j.

## Outcome

Arbitrary acquired signed labels admit paid common exact roots or a factor, with rigorous first-drop extraction and optional unit-separated nodes. Native collisions survive and every accidental transformed collision has a valid short-label consumer. These are stronger usable preparation interfaces than a formal root permission. Their tested cyclic-resultant/cabling contraction still leaves the physical-index product unpaid; no soft(L+sqrt m) full-family algorithm or exponent gain is established. Scratch only; no numerical campaign or repository edits.

## Addendum: native coverage forces H and the actual index to be invertible

For the full retained native label list e_j=E_j, the preceding cleaning gives gcd(E_j,r'_P r'_Q)=1 for every j, where r'_p=ord_p(b). At the surviving original P-witness, powering its Fermat identity gives

    E_j=HI mod r'_P.

Hence gcd(HI,r'_P)=1, and therefore BOTH gcd(H,r'_P)=1 and gcd(I,r'_P)=1. The swapped row gives the same conclusions at Q for the SAME integer I. Thus H and the actual witness index are units modulo both cleaned orders. In particular I!=0 on the continuing branch.

Public integer-zero row deletion does not invalidate this argument. The original witness and its swap already survive by the authoritative strict order/window and nonzero Fermat-integer proof. The construction retains that same surviving row metadata and merely powers its local equality. No new deletion based on an unknown residue of I is performed. One may also rerun the original survival proof using b and q_b=b^H, whose projected orders remain>16H, if preparing the cleaned catalogue afresh. Complete-swap pruning and any old unit-certified diagonal pruning still leave the original witnessed pair; extra collisions introduced by cleaning need not be witnesses.

This proves that the retained b group is automatically H-rough in the sense gcd(H,order)=1, without adding H to the cleaning-label list. Killing H-supported order and acquiring inverse-H roots were already paid preparation operations in the prior roughening/root packets. The automatic deduction is therefore a useful consistency/streamlining fact, not a new roughening power or complexity saving.

The index conclusion gives a precise inverse-root interpretation of the transformed witness: since q_j^I=b and I is invertible modulo r'_p, its row clock q_j is the unique I-th root of b in that local retained subgroup. It does not acquire I, its inverse exponent, or the list of all physical-index roots. Acquiring roots for every1<=i<=M by the same complement-tree method would cost soft M, above the target budget; using an implicit list restores the uninitialized physical-index product. No public restriction thinning the index range has been acquired here from gcd(I,r'_P r'_Q)=1. Thus the full query and any useful collective inversion/aggregation remain open.


## Integration addendum: exact common-base fallback

The follow-up cyclic-resultant audit supplies a paid fallback for the raw different-base representation. At each hidden prime p, beta_j and b have the same local order r*_p. Thus, for every signed physical index i,

    q_j^i=b iff beta_j^(Hi-E_j)=1
              iff r*_p divides Hi-E_j
              iff (b^H)^i=b^E_j.

Acquire the common base b^H and all row values b^E_j in soft L. This restores the existing common-base geometric product query at soft(L+sqrt(Lm)), including original negative intervals. It is exact local zero/nonunit equivalence; the numerical scalars need not be equal. A saturated rebased leaf has the same nonzero short gap on the large odd-order base b and is licensed by the existing extractor. The original common-base baby polynomial cannot be used on the raw q_j form without this change, but the change itself is paid. The faster target-scale whole-family query remains open. See cyclic-resultant-followup.md and integration-review.md.

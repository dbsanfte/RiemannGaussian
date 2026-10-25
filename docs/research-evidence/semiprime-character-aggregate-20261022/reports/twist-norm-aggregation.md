# Aggregated twist norms on the actual native target polynomial

22 October2026. Exact norm identities DO collapse the2^d explicit twist branches to a degree-J target polynomial, whose coefficients are paid. They leave a common-H resultant with the SAME long index set and degree. No soft O(J+sqrt L) aggregate-resultant evaluator is obtained. The precise unpaid operation after branch collapse is given below; no actual values of twist-unit factors are assumed.

## Input, extension safety and global support

Retain the original prepared odd scalar subgroup, step q=gamma^(m²), common root index set S_e={r+mn:r∈R_e,0<=n<K}, D=|S_e|, and assigned targets x_j of palette e. Treat the constant two palettes separately. Let h=2^d with d=O(logm), and

    F_e(T)=product_(j assigned e)(T−x_j).

All x_j and q are units. Coherent roots of the ORIGINAL targets and q can be publicly prepared by the earlier initial rebase; this report does not assume a hidden-order root oracle.

Proof-side roots of unity are treated COMPONENTWISE, since N is odd and the root polynomial is separable at both hidden characteristics. Choose a primitive hth root in each algebraic-closure component and label its powers by a∈{0,...,h−1}. Every labeled a!=0 has nontrivial2-power order in EVERY component and cannot equal a ratio of odd-subgroup elements. Thus x−zeta_h^a*s is a unit in the split algebra for every such fixed label. An arbitrary globally nonidentity element of a product etale algebra could specialize to1 in some components and is NOT sufficient for this claim. Equivalently, no extension is needed to prove support: on each original odd subgroup the map x→x^h is injective, hence x^h=s^h iff x=s. This also proves support preservation on collision components. Primitive cyclotomic strata can be used instead of a split algebra, with the same componentwise interpretation.

The monic identity

    product_(zeta^h=1)(T−zeta*s)=T^h−s^h

therefore preserves EXACT local nonunit support when one original odd-subgroup factor T−s is completed by all nontrivial twists. It does not compute the companion unit product's value.

## Paid branch collapse across ALL targets

The polynomial

    F_(e,h)(U)=product_(j assigned e)(U−x_j^h)

is acquired in soft O(J_e) native bit work: acquire the J_e public powers by repeated squaring and build one monic product tree. Repeated targets cause no difficulty. Its degree is J_e, not J_e*h. Equivalently,

    F_(e,h)(U)=Res_T(F_e(T), U−T^h),

with the resultant orientation chosen as displayed. The explicit-root construction pays this special norm without invoking a generic degree-J*h resultant algorithm. Thus it is NOT necessary to materialize all J*h twisted targets to acquire the coefficients of this particular norm polynomial.

The original scalar aggregate is

    R_e=product_j H_e(x_j;q)=Res_T(F_e(T),H_e(T;q)).

Completing all twists produces, up to a known global sign depending on twist convention,

    R_(e,h)=product_j H_e(x_j^h;q^h)
           =Res_U(F_(e,h)(U),H_e(U;q^h)).          (1)

For example product_(zeta^h=1)H_e(zeta*x;q) equals(-1)^((h−1)D)H_e(x^h;q^h). This follows from product_zeta(zeta*x−s)=(-1)^(h−1)(x^h−s^h) at each root s. Off-twist factors are certified units, so R_(e,h) and R_e have exactly the same prime-divisibility support. Local orders of q^h equal those of q; powering by h does not shorten the source orbit.

This is a genuinely paid target-polynomial collapse. The remaining H_e in(1) still has degree D~L, root descriptors r+mn unchanged, and still needs an evaluator in the new step q^h. A cheap transformation of the TARGET polynomial does not acquire the long resultant.

## The exact quotient/norm operation still unpaid

In the public quotient algebra A_e=(Z/N)[T]/F_e(T), define the monic outer seed polynomial

    B_e(Z)=product_(r∈R_e)(Z−q^r), a=|R_e|~m.

The desired quotient-ring element is

    U_e=product_(0<=n<K) q^(mn*a) B_e(T q^(−mn)) in A_e,

whose norm to Z/N is R_e. All identities are division-safe: q is a known unit and F_e is monic. U_e is a length-K product of a degree-a transition polynomial, evaluated at the quotient element T and a geometric scalar clock. Computing its NORM alone would suffice for a proper gcd or, with a uniform restricted-target evaluation routine, row localization.

An equivalent scalar-clock formulation takes

    A_e(Z)=product_(j,r)(x_j−q^r Z),
    R_e=product_(0<=n<K) A_e(q^(mn)).              (2)

The exact degree of A_e is J_e*a, generally Theta(m²). Its full coefficient construction or its implicit product application has NOT been acquired in softm. A standard polynomial block construction of (2) of block length b costs soft O(J_e*a*b+K/b), in addition to constructing the transition polynomial. Treating degree J_e*a as a constant is invalid. Nor can ring arithmetic in the degree-J_e quotient be counted as one constant-cost operation: a dense multiplication costs soft J_e native residue operations.

Using the original flattened geometric-root simultaneous evaluator instead gives the known soft O(J+sqrt(JL)) bound, not the requested soft O(J+sqrt L). This report asserts no lower bound: a direct norm-only algorithm could in principle avoid acquiring U_e or A_e, but such an algorithm is exactly the still-unpaid operation here.

## Relation to the ALREADY paid binomial quotient primitive

The repository semiprime-block-query-20261016/reports/block-transform.md, Section3, already acquires a full ordinary q-factorial remainder modulo ONE supplied binomial T^b−X in soft O(b+L/b+sqrt L). Its divide-and-conquer cofactor recursion explicitly uses monic binomial moduli; no root-of-unity branches or scalar inversions are needed. This known positive construction is not rediscovered as a new norm method here.

It does not directly compute (1): the native F_e is an arbitrary split target polynomial, not one binomial. Putting its coefficients in the coefficient ring of the binomial algorithm multiplies the dense arithmetic charge by the degree-J_e carrier unless a new contraction algorithm is supplied. Likewise covering the native targets by binomial twist orbits would need a paid orbit cover; arbitrary independent native x_j do not share a supplied value x_j^h. The paid special polynomial F_(e,h) only records their DIFFERENT powered values, rather than turning them into a single binomial fiber.

The older semiprime-multistream-query-20261015/reports/selected-determinant.md already explains why a small resultant determinant does not acquire its long remainder/filtered coefficients. No generic determinant, norm, or quotient-carrier theorem is claimed to supply those entries here. The present calculation specifically removes the J*h explicit-twist representation cost, while retaining that unresolved arithmetic task.

## Global detection and localization contract

A global aggregate need not output all row values. A uniform algorithm accepting the public target polynomial or its explicit roots, and evaluating its common-H aggregate at soft O(J+sqrt L), could be reused along ONE balanced target-subset path. At each node, compute a child aggregate. A proper gcd ends factoring; a saturated child is selected; a unit child forces the other child nonunit. O(log J) calls cost soft O(J+sqrt L) up to logarithms, because subset sizes shrink geometrically. Once one row is selected, the inherited original UNMASKED scalar interval descent costs soft sqrt L and uses the original positive gamma exponent ledger/decoder.

However an isolated supplied scalar R_e with gcd(R_e,N)=N does not itself provide target-subset products. A successful norm-only THEOREM must support the same algorithm on public target restrictions, or explicitly supply another paid localization method. It may not assume the full twist-unit correction values for those restrictions. Equation(1) and odd-order unit safety remain valid under every target restriction, so a future uniform evaluator would automatically have the right algebraic interface.

For the TWO palettes, compute their root aggregates or simply test each supplied aggregate; true native coverage ensures a nonunit in at least one unless the earlier boundary screens already factor. The target restrictions used here do not require restricted H-root products or an H localization oracle.

## Outcome

The exact paid result is branch collapse to F_(e,h), together with local-support preservation in(1). It neither materializes J*h arguments nor assumes the twist companions have known values. The remaining long norm/resultant(1), equivalently(2), is unacquired at softm. Coherent root supply, extension unit safety and target-polynomial construction are therefore NOT the blockers in this formulation; the unresolved operation is direct simultaneous long-product norm acquisition over the arbitrary native split target algebra.

Only this new scratch report was written. No repository edits, new agents, backend, finite example or broad literature obstruction campaign.


## Clarification: this fibre norm does not compress the actual dyadic states

The degree-J construction F_(e,h) above completes, for EACH original target, the full uniform root-of-unity fibre and pushes it through T→T^h. The multiplier recursion instead creates shifted-origin targets gamma^(e_j−m³t),0<=t<2^d, at a successively squared scalar base. These targets are generally in the same ODD subgroup, not the nontrivial2-power twists of one point. Taking their2^d powers does not identify them: power2^d is injective on that subgroup. Therefore the paid fibre norm does NOT establish a degree-J compression of those J*2^d shifted-origin states. Their norm polynomial, or a direct norm-only action on their implicit descriptors, remains unacquired. This distinction is essential; the earlier branch-collapse result applies only to the uniform twist fibre it explicitly constructs.

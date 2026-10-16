# One coarse channel suffices for the restriction-stable gcd query

2026-10-15. Conditional positive acquisition interface. This report does not construct the missing channel and does not establish the desired soft O(m) query bound. It makes the required input and all subsequent costs explicit; the smaller end state is not counted as acquisition progress by itself.

## Promised input and the missing operation

Work in R=Z/N with N an odd squarefree semiprime. Supply J>=1 units x_1,...,x_J and a unit q, and a length ell>=1. In both hidden fields the x_j and q belong to a common odd-order subgroup, and differences between distinct supplied nodes are units modulo N. Neither the factors nor the subgroup orders are input. This promise holds on the retained actual prime-order counterfamily after public deduplication of integer source offsets. A full all-input factorization theorem must establish its own promised branches; that work is not replaced here.

Set

    F(t)=P_ell(t;q),
    D(t)=prod_j(1-t/x_j),
    B=least power of two >=max(1,ell/J),
    D_B(t)=prod_j(1-t/x_j^B),
    E_B(t)=D_B(t^B)/D(t),
    K(t)=C_(B,0)(F(t)E_B(t)).

Here C_(B,0) extracts coefficients at multiples of B and divides their indices by B. Its numerator degree satisfies

    deg K<=floor((ell+J(B-1))/B)<=2J-1.

Indeed ell/B<=J, and the extra -J/B makes the displayed upper bound strict below 2J. When ell<J, B=1 and deg K=ell< J; the same bound holds. No roots of unity are needed to specify or supply K.

The missing operation is to acquire this ONE polynomial K, or a polynomial of degree<J agreeing with it modulo D_B, in soft O(J+sqrt ell) bit work including supplied-data construction, up to the usual log N factor. Requiring the full degree<2J polynomial is sufficient but not necessary. Any actual oracle must charge its constants, inversions, state acquisition, memory and failure/factor branches. The formula for K alone supplies none of those.

## Proof that its values preserve exactly the desired gcd

The reviewed decimation identity proves, at every original node,

    K(x_j^B)=F(x_j) E_B(x_j)/B.                    (1)

Because each local subgroup has odd order, raising to dyadic B is injective on it. Each geometric factor in E_B(x_j) is therefore nonzero in both fields: it is B when two nodes coincide, and otherwise (1-(x_j/x_l)^B)/(1-x_j/x_l). Thus E_B(x_j)/B is a unit modulo N. Identity (1) preserves the zero support in each hidden field, and consequently

    gcd(N,prod_j K(x_j^B))
       =gcd(N,prod_j P_ell(x_j;q)).                (2)

The same holds with public multiplicity weights for deduplicated original rows. No coefficient is interpreted as a characteristic-zero number, and no unknown local order is used operationally. The splitting-extension Fourier proof of (1) is a proof method; an implementation evaluating K needs no extension.

After K is supplied, compute the J powered nodes, monic multipoint-evaluate K, multiply the J outputs and take one integer gcd. All steps are ring-safe without dividing by node differences, derivatives, row values, collision values or B. The paid post-acquisition bit cost is soft O(J log N), including O(J log B) modular powering operations, for polynomial-size ell and hence log B=O(log N). Storage is soft O(J) residues. Extended gcd is needed only for the final integer gcd; this postprocessing neither assumes nor constructs a unit inverse.

If exact numerical row values are wanted as well, the reviewed derivative ratio provides them in the same soft scale on the unit-difference promise. That optional recovery uses batch unit inversions. It is not required by (2).

## Native restrictions remain in the same promised family

For a chosen row subset S and a COMMON contiguous seed interval [a,a+ell), replace each target z_j by

    x_j=z_j q^a,  j in S.

Then the original restricted row product is exactly P_ell(x_j;q). The common scaling preserves odd-subgroup membership and unit pairwise differences. A chosen dyadic B preserves them again. Equal source offsets may be deduplicated publicly; their multiplicities are retained. Metadata construction costs soft O(J_S) operations plus modular powering at bit length O(log N), and building the degree-J_S denominator costs soft O(J_S). These costs fit the desired acquisition scale. The case ell=0 is the known empty product; a subset with no rows also returns the empty product.

Thus an oracle satisfying the stated cost and promises for all such inputs would supply the needed row-subset/common-interval gcd query. The same formula can be replayed along a recovery controller with the controller's already required calls and overhead. This statement does not prove that controller's total bit/memory bound, add arbitrary independently shifted row origins to the contract, or assume that every semiprime input lies on the historical counterfamily. Those are separate obligations for the full guaranteed sixth-rate theorem.

## What the result changes, and what remains

Only the r=0 channel is needed for this gcd acquisition interface; there is no need to construct all B channels, nor one channel per original row. The all-phase and Fourier-pruning obstructions do not imply that those unrequested outputs must be paid. Conversely the known nearlinear algorithm for selected coefficients of F does not acquire coefficients of F E_B, and the cheap denominator updates do not acquire K.

This is now a concrete matrix-free target: one degree<2J polynomial (or its degree<J remainder) whose evaluations preserve the entire restricted gcd payload. A fast direct single-channel convolution, additive formula, or other sufficient observable remains possible. No such acquisition algorithm is established here. The general soft O(m^(3/2)) query and the unproved all-semiprime sixth-rate Lean goal are unchanged.

## Prerequisite

The exact mask, transport identity and source promises are proved in the independently reviewed decimation report, SHA256 65a5c827a64b5c035d3d0a7bed445c6970910f9f92749309878d1e1520e5c4fd. This report adds the specific r=0 degree choice, inversion-free gcd interface, and restriction replay with explicit limits. It imports no external theorem to claim an acquisition speedup.

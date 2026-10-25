# Shared exact roots for every possible small coindex

2026-10-22. Revalidation of the inherited outside-product root construction. The October 16 constructive-frontier index already records smooth projection and shared roots for small j^2 as paid. This report checks the full coindex-root family against the current prepared contract; it is not a new whole-family acquisition advance and does not give a factor on its retained branch. See order-cleaning-independent-review.md.

## Modified public cleaning exponent

Start with the prepared unit beta_0, with coprime odd local orders>B=16m². Optionally first apply the proved (N−1)-cleaning. Let L=m!, T=ceil(log2 N), and M=L^T. Public factorial/product trees and exact exponentiation acquire M and its prime-power factorization in soft O(m) bit work: log M=O(m log m log N).

Every prime ell<=m occurs in M to exponent at least T, hence every possible ell-adic part of either beta_0 order is removed by b=beta_0^M. Primes>m are unchanged. The previous quotient-prime-power tree handles b=1 in soft m using the original coprime local orders; the final small-order and q-order detectors restore the complete prepared contract. Thus the only retained branch has m-rough local orders r'_P,r'_Q>B.

This factorial exponent can replace the smaller prime-power product without changing the soft-m asymptotic bound. It is chosen because it also supplies many exact public roots cheaply.

## Actual acquisition of all t-th roots, 1<=t<=m

Let w=beta_0^(L^(T−1)). Build a balanced product tree whose leaves are the PUBLIC integers1,2,...,m and whose root product is L. Propagate complementary exponent powers down the tree: from w^(L/A), children with subtree products A_left,A_right receive powers A_right and A_left. At leaf t the output is

 b_t=w^(L/t)=beta_0^(M/t),        b_t^t=b.

The sum of exponent bitlengths at each depth is O(log L+m), so every b_t is acquired in soft O(m) TOTAL bit work. This is not m separate full-length exponentiations. Input acquisition, factorial tree, intermediate modular powers and all output residues are included. No hidden coindex, order or factor is used.

## These are the unique roots inside the retained subgroup

The original field orders divide P−1,Q−1, and the retained setup implies P,Q>16m². Therefore each original local order is <N/(16m²), and its ell-adic valuation is <log2 N−4. For ell<=m,

 v_ell(M/t)>= (T−1)v_ell(L)>=T−1,

since t divides L. Thus M/t still removes every small-prime primary component. For ell>m, t and M are coprime to ell. Consequently b_t has exactly the same local orders r'_P,r'_Q as b. It lies in the same local cyclic subgroup, since a cyclic group has a unique subgroup of each order.

Because gcd(t,r'_P r'_Q)=1, exponent t is an automorphism of that subgroup. Hence b_t is its unique t-th root of b. The family is a genuine paid simultaneous exact-root construction, including the UNKNOWN true coindex t_P=(P−1)/r'_P<m/16. It avoids a root-extraction oracle.

## Why it has not selected the true coindex

Every t<=m has the unique root just constructed on BOTH local components. The property “b has a t-th root” therefore does not distinguish t_P. This remains true even though the full field has exactly t_P roots for the t_P-th-power equation: the constructor selects the one root inside the common retained rough subgroup and does not acquire the other field-torsion branches.

There is a stronger exact check on potential collision use. For distinct s,t<=m,

 b_s=b_t modulo a hidden prime
 iff r' divides (s−t),

because inside the rough subgroup b_t=b^(t^(-1) mod r'). Equality is equivalent to s^(-1)=t^(-1) modulo r', hence to r'|(s−t). Since 0<|s−t|<m<r', this NEVER occurs. All pairwise differences of these acquired root nodes are units modulo N. They are legal interpolation nodes, but their pairwise comparison does not factor N.

Likewise, for k,t<=m, b_t=b^k would require r'|(kt−1). Since |kt−1|<m²<r', the only possible case is the integer-trivial kt=1. Thus a short power grid against these roots has no nontrivial local collision. This conclusion concerns this specific constructed family, not arbitrary exact-root algorithms or all character tests.

The obvious compatibility relations b_t^t=b_s^s supply exponent M−M=0 of beta_0. They do not produce a NONZERO annihilator. Encoding their product into a shared polynomial preserves those tautologies rather than acquiring the missing order.

## Where a useful next input could enter

At the true coindex t_P, X^t_P−b has t_P roots in F_P, while the acquired b_t_P is only one. Finding or tracing the OTHER t_P-th roots of unity would supply information about P−1 that the retained rough subgroup erases. The public M factorization bounds all these small torsion orders, but it does not itself acquire their field elements modulo a composite N. A deterministic, factor-returning construction of these torsion branches or a paid scalar invariant distinguishing their local multiplicities could be an actionable continuation.

The existing sparse norm constructs a public formal cyclic carrier for supplied roots of unity; it does not automatically instantiate hidden-field torsion, and a formal norm alone does not reveal the unknown t_P. No such multiplicity contraction was proved here. No extra literature theorem is used for these elementary constructions.

## Outcome

This pass revalidates acquisition, in one shared soft-m computation, of ALL exact roots associated with candidate small coindices. It clarifies exactly what information those roots retain and lose. Root acquisition was already paid in the inherited work; the remaining input is a paid way to distinguish full-field torsion/multiplicity from the common unique rough-subgroup root. No near-linear all-input factor algorithm or new acquisition advance is claimed.

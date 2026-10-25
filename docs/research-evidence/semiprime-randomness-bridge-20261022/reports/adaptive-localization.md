# Original support query: adaptive gcd and certificate-first localization

2026-10-22. Scratch only. This pass does not prove a new soft-m acquisition algorithm. It checks one concrete adaptive construction through its actual first expensive operation, rather than treating the known root nonunit promise as a useful decision oracle. No order preprocessing, auxiliary norm or finite coverage experiment is used.

## Input retained literally

N=PQ, the prepared beta has coprime odd local orders>16m^2, and q=beta^(m^2) has both local orders>16m^2. After public integer-offset deduplication, the acquired targets Y_j=beta^(N+delta_j), J<=m, have pairwise unit differences. Seeds q^i for 0<=i<L=O(m^2) have pairwise unit differences. Native arithmetic guarantees at least one hidden-prime cross collision. Offset acquisition, F(X)=product_j(X-Y_j), endpoint powers and interval-origin rescaling cost soft O(m) bits. All constructions below keep the original scalar beta and integer offsets, including carries.

At either hidden prime the collision graph is a partial matching. Hence G_p=gcd(F,H_L) is squarefree of degree at most J, where H_L=product_(i<L)(X-q^i). This sparsity of support does not imply that H_L is supplied sparsely or that its remainder has sparse coefficients.

## A complete locator-to-factor controller (the exact benefit of gcd output)

Suppose a guarded gcd routine either returns a proper scalar factor or acquires a monic G in (Z/N)[X] whose reductions are G_P,G_Q. It need not acquire H_L itself or its full remainder. Then a factor is recoverable in soft O(J+sqrt L) additional bits:

1. Evaluate G at every acquired Y_j by ordinary monic product/remainder trees. This costs soft O(J) and never inverts a cross difference.
2. Check gcd(G(Y_j),N) for all j. A proper value is already a factor. If no such factor exists, every value is either a unit or zero modulo N. The true collision ensures that at least one is nonunit, hence at least one is globally zero; choose that row.
3. In that one row, acquire scalar geometric interval products and descend a binary interval tree, keeping a nonunit child. The sum of square-root interval lengths along the path is O(sqrt L). A proper leaf gives a factor; a globally saturated leaf is an original scalar equality beta^(N+delta_j)=q^i and admits the existing bounded-global-leaf factor-sum recovery. Thus the entire recovery is paid.

This handles unequal local collision sets and repeated seed-index coincidences across fields; it never promotes a single algebra component hit into a whole-local hit. If local gcd degrees differ, guarded Euclid itself necessarily returns a proper pivot/degree-decision factor. If they agree, the explicit G supplies the row selector even when the local root subsets differ. Coprimality of local orders is used in inherited preparation/recovery, not to assert the two gcd degrees differ.

This controller clarifies the sufficient OUTPUT: an original-target gcd locator, rather than a long product, is enough. It does not acquire that output. It is consistent with the older locator audit and is not claimed as a fresh general circuit-gcd theorem.

## Tested adaptive strategy and its complete charge

A tempting way to avoid computing G or H_L mod F is to begin with the already-known nonunit rectangle and test only one child at each split. This is correct: if the tested child has unit product, the sibling inherits nonunit status without evaluation. A proper gcd finishes; a saturated child is retained. Thus an adaptive controller really can avoid acquiring the root product and all rejected siblings.

Using the existing restricted exact product evaluator, first bisect rows until one row remains. The tested children have sizes at most J/2,J/4,... and common length L. Their total evaluator work is

  soft O(sum_h (J/2^h + sqrt(J L/2^h)))
       = soft O(J+sqrt(JL)).

One-row interval localization adds soft O(sqrt L). Target restrictions reuse their explicit values and do not rebuild the original source. This is a valid full factor controller, but its first tested half already costs soft O(sqrt(JL)); at J~m,L~m^2 the whole cost remains soft O(m^(3/2)). Substituting a common-root/degree test for the child product only helps if that test has a separately acquired cheaper implementation. Its semantic yes/no output alone has no such cost consequence. Testing singleton rows instead gives m tests of cost sqrt L in the worst case, not a soft-m guarantee.

## Where guarded subresultants actually start

Given the explicit remainder R=H_L mod F, guarded fast half-gcd has soft O(J) BIT cost: guard every degree decision and attempted scalar inverse, return a proper gcd with N on a nonunit, and otherwise specialize identically to both fields. Since F is monic, the initial reduction requires no unsafe division, but its computation is still required. The geometric recurrence

 H_(2s)(X)=H_s(X) q^(s^2) H_s(X/q^s)

is exact. Reduction modulo F does not close using just H_s mod F: substitution X->X/q^s does not preserve the ideal (F) unless F(X/q^s) belongs to that ideal. If H_s=A F+R_s, the omitted term is A(X/q^s)F(X/q^s), and it can affect both the next remainder and its gcd. Native integer-offset deduplication does not give the missing ideal invariance. The q-Newton audit records the corresponding acquired rank-one boundary, not a paid elimination of its propagated quotient.

Dynamic splitting by invertibility tests therefore has its first useful branch only after it has computed some relevant remainder, pivot or Bezout certificate. Producing all row-idempotents or accepting a collision graph as input would simply supply the desired localization. A proof exploiting only the number of surviving factors must bound the cost of the first certificate before it can charge work to surviving factors.

## Primary-source applicability and concrete conclusion

The previously inspected van der Hoeven--Lecerf directed-evaluation theorem charges algebra dimension multiplicatively in circuit work, not additively; it does not turn the above implicit-factorial reduction into a soft-J routine. The public primary source is https://www.texmacs.org/joris/direval/direval.pdf (Theorem 4.2). Its splitting-overhead guarantee is useful once the computation and separable algebra are supplied, but it does not supply a geometric-factorial gcd seed. No general output-sensitive gcd result is imported with an unpaid evaluation or hidden-field oracle.

Read first: the frozen locator audit, packed-coefficient guarded-half-gcd specification, current query-continuation README, and q-Newton contraction. No checked theorem in those sources supplies the first restricted support certificate in soft O(J+sqrt L). The concrete attempted adaptive algorithm above is complete at the existing soft O(J+sqrt(JL)) rate; its hoped-for improvement fails at the first child-certificate acquisition, not at the subsequent localization. No lower bound or impossibility claim is inferred. A nearlinear original-gcd constructor, or a cheaper acquired child-support certificate with a proved total adaptive charge, remains the substantive missing operation.

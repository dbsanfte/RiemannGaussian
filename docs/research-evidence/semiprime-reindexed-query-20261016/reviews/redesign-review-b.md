# Second independent final-byte review: two actual denominator redesigns

2026-10-16. Reviewer q_product_literature_615. Verdict: PASS for both reports; no corrections requested. Read-only mathematics/source review; no examples or builds.

Reviewed exact files:

* `redesign/constant-leading-sidon.md`: 6115 bytes, SHA256 35753a778eab8f913d619c9f5e4aa70c97f13afb9c4a9dedeed611d0195731bf.
* `redesign/sidon-source-pins.json`: 1184 bytes, SHA256 7e2858e1548667148a9d34dfc9166e6f25b23747c456ce65ce373062329f1961.
* `redesign/denominator-m-redesign.md`: 6873 bytes, SHA256 2193b7985de153dd440276c431c9998ec53473b95929de7f8f902631ae3c9a24.
* `redesign/source-pins.json`: 1173 bytes, SHA256 a919d177aaabf1067fa0e0e35fac316e81012d143c98dffb0f56409a4b83e90a.

All ten listed source entries (five in each pin file, with overlaps) independently match their recorded lengths and SHA256 hashes. Checked native denseRow/representative/denseRows and liftRow definitions directly. Historical supply and scalar-baseline inputs are inherited, not new compiled results or newly reproved prime-distribution statements.

## Constant-leading-coefficient family

The public t_j=(N^-1 j² mod m) is nonzero, and denseRow's positive canonical representative is exactly one. Both lift divisions are integral. The quotient relation yields the stated i_P: multiplying its numerator by P gives m² times the quadratic at (P-j)/m. Therefore its numerator is divisible by m² since P is a unit modulo m². The exact exponent difference is (P-1)(t_jQ-1). Positivity is eventual from balanced Theta(m³) factors, and P+(m-1)Q+mb-2j <=m max(P,Q)+m²/2 gives i_P<2m²+2. Both hidden-factor own witnesses are covered; no hidden factor enters setup.

Euler gives N-(P+Q-1)=phi(N), so D|phi(N) implies the global phase replacement N≡S=P+Q-1 modulo D. The centered delta interval has exact width m²+m-4. Thus the effective phase span is at most (m-2)S+m²+m and a pair-sum difference has magnitude <8m⁴<D under the stated bounds. Global equality of products becomes exact integer equality. Because |signed delta sum|<2(m²+m)<S, the denominator sums agree as integers. Modulo m, the delta equality gives equal j sums and the denominator equality gives equal j-square sums. Odd characteristic forces equal unordered tag pairs. This proves the Sidon criterion and distinctness, and the energy is exactly 2J²-J with J=m-1.

The global-only qualification is necessary and correctly stated: neither the Euler reduction nor the large global no-wrap bound implies that local field targets have the same energy. Ambient embeddings preserve it, local quotients need not. The AP/GP partition argument gives k²T>=J⁴/(4J²-2J)>=J²/4; Cauchy--Schwarz gives |CC|>=J²/2; progression boxes satisfy |CC|<=2^rT even with duplicates/cyclic relations. The report only bounds these representations, not scalar norm algorithms.

## Denominator-m family

At t=m the positive canonical representative is zero, and liftRow gives b=centered(-N j^-1), c=(N+jb)/m with exact divisibility. The native generator list only emits t<m, so using the constructor at t=m really is a redesigned family, as explicitly acknowledged. Nonzero centered b values are permuted by tags. Own coverage i_P=(Q+b)/m is integral, positive eventually, and at most sqrt(3/2)m²+1/2<L; exponent difference mQ(P-1) proves the P-field hit. Swap factors for Q.

Adding b=0 enlarges the query. The index n=mi-b covers exactly [-h,mL-h-1] once: consecutive m-element blocks are adjacent and disjoint. Equation (2) is therefore exact with K=mL and base g=gamma^m. There is no mistaken division by the missing class; its separate length-L product can only be canceled when unit. The enlarged interval still preserves valid collision coverage, and any added globally zero leaf is recoverable on the retained branch.

Specifically D=R_PR_Q, gcd(D,m)=1, and global zero implies D|(N-n). Subtracting phi(N) gives D|(P+Q-1-n). Both n and factor sum are O(m³), whereas D>256m⁴, so exact equality yields factor sum n+1. Integer discriminant recovery is consequently valid even for an added b=0 leaf. Scalar interval restrictions remain geometric interval products, so logarithmic splitting handles saturation without pretending gcd=N is itself a factor. This recovery is scoped to the retained order-qualified branch.

The standard explicit small-block/monic-multipoint evaluator has soft sqrt(K)=m^(3/2) ring work and soft m^(3/2)log N bit cost. Its monic formulation avoids potentially nonunit 1-g^k denominators. Setup is softly linear, but neither the geometric cover nor the tiling identity supplies a nearlinear scalar evaluator. Both reports preserve that distinction and make no universal controller, operation lower bound, or new native proof claim.

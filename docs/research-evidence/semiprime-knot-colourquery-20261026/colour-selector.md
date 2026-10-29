# A paid shifted-gcd colour test, including hidden modular chains

26 October2026. Read the latest trace packet and the old collective integer-orbit bound. Selected ONE mechanism: gcd/resultant overlap between an acquired native root polynomial and its q-shift, including p-local aliases. The continuing certificate computation below is fully initialized in soft J per chosen shift. The general factor-or-certificate bound is soft O(J+T_ext), where the inherited saturated-annihilator extraction cost is T_ext=soft O(N^(31/192)); it either factors N or identifies precisely the literal integer-label overlap. It provides no guaranteed full-prefix zero predicate; its failure as that selector is scoped explicitly. No numerical campaign or repository edits.

## 1. Actual input and safe node preparation

Use original retained native roots y_j=beta^E_j, q=beta^H, H=k², with their original labels and colour-incidence metadata. A uniform recentering of every exponent gives the same proof. First remove exact INTEGER duplicate E labels, retaining all original source/colour metadata; this preserves zero/nonunit predicates over squarefree N.

Acquire F(X)=product_j(X−y_j), its derivative, and F'(y_j) by monic product/remainder trees in soft J. A proper derivative-value gcd factors N. If a derivative value is saturated, scan the O(J) differences y_j−y_l at that one node: some is nonunit. A proper difference gcd factors; a saturated difference gives beta^(E_j−E_l)=1 with a NONZERO O(logN)-bit label, so the licensed large-odd-order extractor factors. At most one such scan is needed before termination.

Thus the continuing branch has the ACTUAL certificate that all known node differences are units at both primes. This does not assume local order exceeds their exponent differences. The derivative operation is the previously established factor-aware separation primitive; no new preparation is claimed as the query result.

## 2. Execute the shifted-gcd test without a field gcd oracle

Fix a supplied integer h,0<|h|<=O(m), and acquire every x_j=q^h y_j. Monically evaluate F(x_j) at all j in soft J, including q^h and input powers. Scan their gcds with N.

* A proper gcd factors immediately.
* A unit value proves there is no p-local shifted match at either prime for that j.
* A saturated value F(x_j)=0 is handled as follows. Use a sorted table of the acquired global residues y_l to look for x_j. If a matching node exists and E_l−E_j−Hh is NONZERO, that short integer is a global beta-annihilator, and the licensed extractor factors. If the gap is0, retain this known literal edge.
* If F(x_j)=0 but no global node matches x_j, scan y_l−x_j for this ONE j. There must be a nonunit difference. Every such difference is proper: a saturated one would be a matching global node, contrary to the exact table lookup. Hence this scan returns a factor in O(J) further work.

The scan can equivalently descend the existing subproduct tree. It is not repeated J times on the continuing branch: the first unmatched saturated point ends the algorithm. Every exponent label used is O(logN) bits, although the difference may be much larger than the local order. No wide exponent or additive polynomial zero is passed to the extractor.

Consequently, with soft O(J) continuing certificate work and general factor-or-certificate cost soft O(J+T_ext), the procedure returns a factor OR certifies the following exact statement at BOTH primes:

    q^h y_j=y_l locally  iff E_l−E_j=Hh as integers. (1)

Unit node separation guarantees uniqueness of the local matching node. Mixed CRT matches cannot hide behind a saturated polynomial value: the unmatched-global-node case above exposes them. A global nonliteral match cannot hide either: it has an explicit nonzero short annihilator.

The actual monic gcd of F(X) and q^(-hJ)F(q^hX) is then acquired without an unqualified ring-Euclidean algorithm: it is the product over the nodes y_j having the literal successor E_j+Hh in the list. This product is a common divisor at both primes, and the local certificates show it is their complete gcd. Multiplicities were removed only for the zero-only task; an exact multiplicity-aware gcd would use the original multiplicities separately.

## 3. Specialize to native h=1: no hidden long chain remains

The collective packet proved the literal native bound. If b changes between rows, |E_l−E_j|>=N−H−2k exceeds H. Hence an integer shift+/-H stays at fixed b. At fixed b, all E span H+2k−1<2H, so after exact-label deduplication every residue moduloH has at most TWO values.

Applying(1) at h=1 therefore gives a stronger, operational conclusion than the previous integer-only observation: either factor N, OR every p-local q-adjacency graph on the acquired nodes has exactly those known literal components, of size at most2. Hidden p-local longer chains are eliminated by a paid test, not assumed absent from a large-order lower bound.

The gcd's potentially large degree, up to about J/2, merely records those two-node overlaps. Unioning their physical windows gives the old constant-factor saving. The known exact integer support already has Omega(k) distinct nodes in the complete family; this shifted-gcd test does not supply a growing compression in its factor-free branch. This is a statement about the executed overlap mechanism, not an algorithmic lower bound for the original query.

One may run the same operation at O(logm) selected shifts, e.g. powers of2, within soft J total continuing certificate work; the complete factor-or-certificate bound is soft O(J+T_ext), since at most one saturated-annihilator extraction occurs before termination across all tests. It certifies all those overlaps or factors, but there is no theorem that these chosen gaps include a guaranteed native collision difference. Such selected-shift unit certificates are not a full-prefix zero oracle.

## 4. Colour use and why the actual mixed witness does not trigger this test

The same construction works for subsets: evaluate F_C'(q^h y_j) for nodes in colour subset C, retaining their incidence metadata. For the public involution j->N/j, all paired-colour tests at ONE h have continuing certificate cost soft(sum of their actual incidence counts)=soft k, using separate small product trees, rather than a k-by-k colour table. If metadata overlaps, remove the expected literal shared nodes/edges in this auxiliary test exactly as above. A nontrivial comparison still uses its explicit exponent gap.

This is a paid colour-sensitive short-shift predicate. Its coverage obligation, however, is different from the native clock witness. The latter says that one unknown q^I equals a node of colour j at P and a node of its involute colour at Q. It does NOT say those two known nodes equal each other in the SAME field, or differ by the chosen q^h there. Known pair differences are already unit-screened. Thus no proper resultant or shifted gcd at a supplied short h is forced by the actual two-prime mixed-root promise.

In particular the zero-shift resultant between disjoint known-node subsets is a unit after the separation certificate, even while the original mixed clock witness remains guaranteed. This follows directly from that ACTUAL continuing input contract, not from an independent fake-root example. Adding a chosen h changes the tested incidence but supplies no all-semiprime theorem that a witness-related edge occurs.

A large p-local gcd not explained by literal edges WOULD be useful: the algorithm above factors immediately rather than exploiting it as an implicit long-chain evaluator. In the continuing branch its only reuse is the acquired literal short-chain union. This precisely resolves the proposed modular-alias escape for this mechanism; it does not exclude other colour contractions.

## 5. Whole-query accounting and next sufficient input

No call here evaluates the product over i=1..m. Each fixed shift has soft J continuing certificate cost; its factor-or-certificate cost is soft O(J+T_ext). Scanning every shift naively costs soft O(Jm+T_ext), with at most one extractor call before termination, not one per shift. Compiling all shifts into product_h F(q^hX) has growing degree J times the number of shifts and restores the old block-product cost when completed. Returning a vector of short-shift gcds does not automatically provide the desired prefix scalar or a witness-containing child colour.

A sufficient genuinely new arithmetic input would be a PUBLIC soft-size shift/colour test family, with a proof that the native stationary pair forces at least one nonliteral local edge in it, or a jointly acquired aggregate deciding that incidence over the long interval without materializing its degree. This test family must distinguish the same-field shifted overlap used here from the actual cross-prime common-index promise. No such coverage theorem is proved in this pass.

The completed result for the whole family J=soft O(k) is therefore factor-or-exact-literal-overlap in soft k, including all modular and saturation branches, since T_ext=soft O(N^(31/192))=soft O(k). For an arbitrary smaller subset the general bound remains soft O(J_subset+T_ext), not soft O(J_subset). It is a concrete attempted zero-selector whose regular initialization is paid, but whose required native coverage implication is absent. No helper/preparation result is presented as a full-goal advance, no generic lower bound is asserted, and the guaranteed query stays soft(J+sqrt(Jm)).


## Cost clarification: inherited saturated-annihilator extraction

The O(log N)-bit size of a nonzero annihilator is not a polylogarithmic extraction algorithm. The inherited scalar-catalogue consumer costs T_ext=soft O(N^(31/192)). Proper gcds cost only polylogarithmic work, while a saturated difference can invoke this consumer once before the entire procedure terminates. Thus all continuing certificates and fixed-shift polynomial work cost soft J; general factor-or-certificate work costs soft O(J+T_ext), including for small colour subsets. For the complete J=soft O(k), k asymptotic N^(1/6), the additional exponent 31/192<1/6 keeps the whole-family result soft k. Multiple selected shifts share the same at-most-one terminating extractor budget. This correction does not change the unproved long-query coverage implication.

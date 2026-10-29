# Joint multiple windings: an executed safe twisted-cover contraction

26 October 2026. Scratch only; no numerical campaign or repository edits. **No complete target-rate query is proved.** There is an exact zero-safe finite identity combining any supplied set of divisor windings into one acquired boundary polynomial. Its full input cost is charged below. The untwisted cover/Möbius shortcut fails specifically because the native target is b, not1. A native-specific sparse witness cover or a genuinely compressed boundary-polynomial readout remains possible and unproved.

Read the current Adams packet, including shared-label roots, exact common-base rebasing and original signed decoder. Those results are retained; no new rank-one eliminant or formal-periodicity argument is counted here.

## 1. Actual data and ordinary multiple-cover correction

Use beta_j^E_j=b, q_j=beta_j^H, hence q_j^E_j=b^H (not b). All these bases generate the same large local subgroup after the paid cleaning; each E_j is coprime to its order. The target leaves are q_j^i−b on the original signed interval. Positive indices below are notation; negative-only queries use the actual signed labels unchanged, or replace q_j by q_j^(-1) and i by |i|.

For every positive multiplier d the exact polynomial identity is

    X^(di)−b = (X^i−b) D_d(X^i,b)+(b^d−b),
    D_d(U,V)=Σ_(r=0)^(d−1)U^(d−1−r)V^r.             (1)

At a local target hit X^i=b, an **untwisted** larger cover gives b(b^(d−1)−1). For 2≤d≤m+1 this is a certified unit: b is a unit and its local order exceeds16H>m. Thus the common-target sequence does not have the ordinary winding divisibility property. This is an exact native conditional statement at a hit, not a sampled counterexample.

The correct multiple cover changes the boundary target:

    X^(di)−b^d=(X^i−b)D_d(X^i,b).                    (2)

If d is coprime to the actual local subgroup orders, (2)'s left factor has exactly the same local zero bit as X^i−b. No numerical D_d value is needed for that predicate equivalence. If d is also a unit in the residue field, D_d is a unit even at a collision (there its value is d*b^(d−1)); otherwise do not claim a multiplicative unit correction, only the injective-power zero equivalence. No unknown period is assumed.

## 2. Exact finite multi-winding identity

Let S be an **actually supplied** finite set of nonzero signed physical indices. Put a_i=|i| and D=product_(i in S)a_i; split positive/negative signs into two queries when needed. Include these a_i in the existing shared-label cleaning, if they are not already coprime to the retained orders. The factor-or-interface cleaning costs softly O(k+|S|) for short labels: a first order-drop uses the previous large-order base and a nonzero short label. It preserves every original hit; accidental cleaned hits retain the original E_j−Hi decoder. This is already licensed cleaning, not a new order oracle.

For one sign and positive S, define the **actual coefficient polynomial**

    T_(D,S)(Y)=∏_(i in S)(Y−b^(D/i)).                 (3)

On the continuing cleaned branch gcd(D,r)=1 for both local orders. Then

    T_(D,S)(q_j^D)=0 locally
       iff q_j^i=b for some i in S.                  (4)

Indeed a factor on the left is q_j^D−b^(D/i)=(q_j^i)^(D/i)−b^(D/i), and D/i is an invertible exponent on the subgroup. Thus

    ∏_j T_(D,S)(q_j^D)

has exactly the original complete local zero predicate on S. It therefore preserves global zero and nonunit status over the squarefree composite ring. This is a finite identity of zero predicates, not asserted numerical equality of products. It never divides by a collision factor.

The boundary twists in (3) are unit-separated at each hidden prime. For distinct i,l in S⊂[1,m],

    D/i−D/l = D(l−i)/(il) mod r,

and D,i,l are units mod r, while 0<|i−l|<m<r. Therefore b^(D/i)−b^(D/l) is a unit. This proves that, under this safe completion, its distinct boundary states cannot be collapsed merely by identifying repeated twist values. It is not a lower bound on a different compressed polynomial evaluator.

## 3. Actual acquisition cost, including long D

Let t=|S| and ell_D=bitlength(D). Directly powering each acquired q_j by D costs O(L*ell_D) ring multiplications; this must be charged if q_j are passed as a bare unrelated list.

With the **actual shared-root acquisition provenance**, there is a better shared construction. All q_j are produced from the same beta by the known complement-power tree from `shared-label-roots.md`. Start that entire construction with beta^D instead of beta: computing beta^D costs O(ell_D) ring multiplications; the existing product/valuation/complement exponents then cost softly O(L) with their original short-label bit budget. Its output is exactly every q_j^D and b^D. This avoids L separate long-D powers. It is available only because that provenance is retained, not from a formal common-target equality alone.

Likewise choose D to be the product of S as above. Then every b^(D/i) is an outside-product power: a product tree on the integer a_i propagates b^(D/product_node) to its children by sibling powers. Total exponent bitwidth per depth is O(sum_i log a_i+t), so all t boundary values cost softly O(t) bit work, with the usual log N factors. No inverse exponent is used. Construct T_(D,S) by a product tree in softly O(t); evaluate it at the L powered nodes by monic multipoint remainders in softly O(L+t). Repeats would also be legal. The integer D has ell_D=O(t log m) and is acquired by the same tree.

Thus for a supplied t-element short-index set the whole scalar in (4), including shared powered inputs and boundary coefficients, is acquired in softly O(L+t+k) with any new cleaning; if the relevant cleaning is already paid, softly O(L+t). This is an executable finite contraction algorithm, not a short unexpanded norm descriptor. But direct common-base multipoint evaluation at a supplied S has essentially the same bound. No novel rate is claimed for this identity alone.

For S=[1,m], the boundary polynomial has m acquired roots/coefficients and ell_D=Theta(m log m) with D=m!. Even replacing it by lcm(1,...,m) leaves ell_D=Theta(m), and acquiring its m boundary twists is not free: the outside-product construction just used no longer follows automatically because the product of the labels need not divide that lcm. One may use direct O(m*ell_D) powering or prove another shared procedure; either way an unexpanded divisor descriptor is not an acquired coefficient list. The full product version already costs softly O(L+m), worse than the retained softly O(L+sqrt(Lm)) bound in the native scale.

For several literal winding covers D_1,...,D_s and divisor-index sets S_l, charge the powered-root acquisition separately per cover unless a shared exponent construction is explicitly supplied, and charge every acquired boundary alphabet/coefficient list. Duplicate physical indices can be removed. Covering all m indices by such **expanded** boundary lists has total size at least m. This concerns only this explicit implementation; a new succinct boundary polynomial/norm theorem could bypass that output.

## 4. Could existing label products supply the winding?

The existing M=product_j |E_j| has softly O(L log N) bits and is already coprime to both retained local orders. It is therefore a lawful D for (4), without a fresh order promise. Shared complement powering acquires q_j^M in softly O(L), even though log M need not be O(log N).

However, neither the native equation r | Hi−E_j nor gcd(i,r)=1 proves the **integer** divisibility i|M. No such all-semiprime coverage theorem is supplied. Moreover, even if a witness i divides M, its twist b^(M/i) must occur in an acquired boundary set or be handled by a proved compressed divisor-polynomial evaluator. The presence of a divisor in a short integer descriptor does not acquire its factor in (3).

If one uses only existing labels E_l as boundary windings, their twists can indeed be reused via beta_l^M. This tests cross incidences q_j=beta_l after injective M-powering, hence the index i=E_l, rather than every physical i. A mixed polynomial product/remainder tree evaluates that particular cross-incidence screen in softly O(L). First hash-check literal relations E_j=H*E_l: uniqueness of the acquired E_l-th root shows q_j=beta_l globally on that branch; all its other beta-node differences are units by the paid separation, so omit that entire j from this auxiliary screen. For each remaining j, every gap E_j−H*E_l is a nonzero short integer. A nonunit mixed product is localized to j and then scanned over l in O(L), giving a proper gcd or a saturated equality whose gap annihilates the large-order beta_j. Thus no out-of-window physical-index decoder is invoked on a tautological zero. But almost all native nonaxis |E_l| exceed the physical horizon; no coverage implication follows. This is a routine resultant/separation screen on the new acquired alphabet, not a new complete witness theorem or factoring improvement.

The precise potential arithmetic input is a native-specific family of index sets S_l, total softly O(k), that still contains a guaranteed original common-index witness for every semiprime, **or** a compressed readout of (3) for a larger succinct divisor family at that cost. Neither follows just from the unit witness index. This leaves native sparse-cover possibilities open.

## 5. Möbius/dynatomic source test, with boundary hypotheses retained

Primary cyclic-cover context: Silver–Williams, *Torsion numbers of augmented groups*, https://arxiv.org/pdf/math/0202197 . Ordinary cyclic-cover norms have complete character cycles and their periodic/Betti corrections; they do not convert the marked target b into1. At a singular value one cannot replace the desired zero by a nonzero torsion cardinality.

Primary finite incidence source: Doyle–Fili–Hyde, *Dynatomic polynomials, necklace operators, and universal relations for dynamical units*, NYJM28 (2022),534–556, https://nyjm.albany.edu/j/2022/28-21p.pdf , Definition 2.15, Lemma 2.16, Theorem 3.1/Corollary 1.3. Their polynomial Möbius factorization concerns iterates f^d(X)−X and complete periodic/preperiodic dynatomic factors; under their stated index/necklace hypotheses it gives exact resultant-one/unit relations. That is a genuine unit-completion mechanism, not merely an asymptotic statement.

The direct native dynamics f_j(Z)=q_j Z instead has f_j^i(1)=b, a **marked hitting relation**. Its periodic relation is f_j^i(Z)=Z, which on nonzero Z detects q_j^i=1 instead. The source degree-at-least-two polynomial and dynatomic-index hypotheses are not met by silently calling X^i−b an iterate-minus-variable. A coordinate conjugation cannot make the nonfixed marked point b fixed: f_j(b)=q_j b≠b under the native short-order guard. No complete dynatomic orbit/factor alphabet satisfying those hypotheses has been acquired.

Equation (1) executes the missing compatibility: untwisted multiple windings lose a hit, while (2) restores it only with the changing boundary twist. The safe finite remedy is exactly (3)–(4). Numerical Möbius ratios may have vanishing denominators at genuine hits; only the corresponding polynomial identity with all factors retained could be specialized. No unproved unit denominator or undeclared period is used here.

## Outcome

This pass supplies a lawful multi-winding contraction for an **acquired** index set and pays its integer exponent, shared-node, boundary-polynomial and scalar-readout costs. For the full interval it costs softly O(L+m), so the old common-base evaluator remains preferable. The actual missing step is a native sparse witness-cover theorem or a new compressed divisor-boundary norm algorithm, not ordinary Möbius inversion of untwisted covers. The complete guaranteed native query remains softly O(L+sqrt(Lm)); the softly O(L+sqrt m) target is open.

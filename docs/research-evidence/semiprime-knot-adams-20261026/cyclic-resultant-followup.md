# Shared-label cyclic resultants: exact rebasing and the rank-one recurrence test

26 October 2026. Scratch only; no numerical campaign or repository edits. **No softly O(L+sqrt m) contraction found.** The different-base query retains a complete softly O(L+sqrt(Lm)) zero/nonunit implementation by the exact componentwise rebasing below. A short algebraic recurrence exists in a characteristic-zero rank-one lift, but the inspected literature does not initialize an efficient unique step or a collision-safe fast prefix from it.

## 1. Keep the actual common targets distinct

Read `shared-label-roots.md` and the current lift/Adams interfaces. The acquired data are

    beta_j^E_j=b, q_j=beta_j^H,
    q_j^E_j=b^H, H=k².                              (1)

Thus the target in Res(F_q(X),X^i−b) is b, while the common label power is b^H. They are not the same input. Alternatively use Res(F_beta(X),X^(Hi)−b). Every E_j is a retained original nonzero signed O(log N)-bit label; E_j−Hi is nonzero on the actual searched signed interval by whole-row deletion.

After the paid projection/order screen, beta_j and b have the same local orders, these orders exceed the needed margin after H-powering, and gcd(E_j,ord(beta_j))=1 at both hidden primes. The supplied root and node separation guarantees are kept. No inverse label modulo an unknown order is acquired.

## 2. Exact componentwise common-base recovery

For either residue prime, with local order r_j=ord(beta_j),

    q_j^i=b
    iff beta_j^(Hi−E_j)=1
    iff b^(Hi−E_j)=1.                              (2)

The last equivalence uses b=beta_j^E_j and gcd(E_j,r_j)=1. Therefore the factor q_j^i−b has exactly the same local zero bit as

    (b^H)^i−b^E_j.                                 (3)

This holds for signed i and E_j as well; all bases are units. It is **not a numerical equality of factors or scalar products**. No numerical unit correction is required for a zero/nonunit oracle.

Taking products preserves the componentwise zero equivalence, hence global zero and nonunit equivalence over the actual squarefree R=Z/NZ. Acquire x_j=b^E_j and q_b=b^H in softly O(L), then use the already licensed common-base product evaluator on F_b(X)=∏(X−x_j) and q_b. Its local q_b orders are large by the projection screen. For an actual negative-only interval, retain exactly its original i labels (or its previously proved centering/opposite transport); do not replace it by positive indices just because the displayed resultant notation uses i≥1.

The known complete cost remains softly O(L+sqrt(Lm)), not L independent square-root queries. Original coverage survives because raising an original equality beta^E_j=beta^(Hi) to the projection exponent gives (3). An accidental saturated equality in (3) supplies the nonzero short annihilator E_j−Hi of the prepared base b; proper gcds factor directly. Thus this rebasing keeps the existing signed/original-label decoder. A result acquired at a newly extended index outside the deletion interval would require its own gap check.

Unit separation can also be transported if wanted: since E_j,E_l are invertible modulo the common local order, beta_j=beta_l iff E_j=E_l modulo that order, which is equivalent to b^E_j=b^E_l. Hence the paid separation test is compatible with this common-base coefficient input. It does not shorten the clock.

## 3. Execute the strongest rank-one cyclic-resultant recurrence lead

Primary source: Hillar–Levine, *Polynomial recurrences and cyclic resultants*, Proc. AMS135 (2007),1607–1618, Theorem 1.5, its proof in §2, and cyclic-resultant applications in §4, https://lionellevine.github.io/hillarlevineAMSrevised.pdf . Their general theorem concerns exponential-polynomial sequences over a characteristic-zero algebraically closed field. For a simple exponential sequence, a multiplicative base group of free rank r gives a polynomial relation among r+1 successive values. This is an algebraic dependence statement, not an efficiently evaluable or uniquely solvable recurrence.

The present common-root structure has rank at most one in its formal characteristic-zero lift. Indeed let A=lcm_j |E_j|, R the known projection exponent (a multiple of A), and tau=beta^(R*H/A). Then exactly

    q_j=tau^(A/E_j),
    r_i:=Res(F_q,X^i−b)=prod_j(q_j^i−b)
       =sum_(S subset {1,...,L})(−b)^(L−|S|) (prod_(j in S)q_j)^i.

Thus Theorem 1.5's simple-exponential case gives a length-two polynomial relation in that lift. This low rank already holds for the original common-base catalogue; it is not by itself a new preparation gain.

Here is the explicit eliminant candidate, including its actual input size. Define the Laurent polynomial

    A_0(Z)=prod_j(Z^(A/E_j)−b), r_i=A_0(tau^i).

After monomial clearing, eliminate Z from A_0(Z)−U and A_0(tau Z)−V. The resultant is an exact relation R_0(r_i,r_(i+1))=0. However the span of A_0 is sum_j A/|E_j|, potentially enormous even though A has only softly O(L log N) bits. Expanding that eliminant is not softly O(L) acquisition. The alternative subset exponential expansion has up to 2^L bases, also not acquired cheaply. Neither descriptor supplies the needed scalar step.

Even an already acquired small relation R_0(U,V)=0 would require a proved rule selecting the correct next V among its algebraic branches, at U=0 and zero divisors as well as units. Dividing by a derivative/leading coefficient needs an explicit unit certificate or a terminating factor/recovery branch. The theorem provides no such rule, no finite-ring specialization with guaranteed pivots, and no algorithm to advance the prefix product. Knowing the auxiliary clock tau^i allows direct evaluation from the supplied q_j in softly O(L) per i, but restores the Lm loop rather than accelerating it.

For native nonaxis rows, |E_j|≥N−H−k, since the original b-coefficient of N is a nonzero integer. This exceeds the m=Theta(k^(3/2)) physical index range on the prepared branch. Thus the literal relation (1) is not a short periodic reduction in i; reducing i modulo the large known label E_j does nothing on that range. The axis labels and any exceptional small labels retain their separate already-audited handling. No unknown order or discrete logarithm is substituted for E_j.

## 4. Cyclic-cover torsion scope and initialized fallback

Primary context: Silver–Williams, *Torsion numbers of augmented groups: with applications to knots and links*, L'Enseignement Math.48 (2002),317–343, https://arxiv.org/pdf/math/0202197 , especially its resultant/torsion recurrence discussion. These theorems concern full finite cyclic-cover invariants, with periodic Betti corrections when roots of unity intervene. They do not compute a product of all cover degrees up to m from a short binary m input, and they do not state the common-target b≠1 finite-ring algorithm needed here. Replacing homology torsion by a nonzero cardinality at a collision would in particular lose the zero predicate.

At one supplied index i, r_i is genuinely acquired in softly O(L log i) by powering the known nodes and multiplying. This is the initialized one-resultant bound, not the long product bound. Swapping products gives Res(F_q,prod_(i≤m)(X^i−b)); that second polynomial has degree m(m+1)/2. Its formal product descriptor or an expanded cyclic cover matrix is not a paid nearlinear scalar contraction. This standard observation is retained only to identify the exact missing readout, not as a general algorithmic lower bound.

The constructive complete fallback is (2)–(3), with the previous common-base evaluator and decoder. The genuinely new theorem still needed is a uniformly initialized unique-step/algebraic-orbit contraction that uses the known shared labels without constructing their enormous lcm exponent support, preserves every local zero, and contracts all i in softly O(L+sqrt m). The inspected cyclic-resultant and cover-torsion sources do not supply it. No new factoring exponent or whole-family query improvement is claimed.

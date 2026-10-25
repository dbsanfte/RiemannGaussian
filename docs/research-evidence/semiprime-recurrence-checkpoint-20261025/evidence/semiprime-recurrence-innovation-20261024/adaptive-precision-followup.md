# Initialized adaptive precision follow-up

2026-10-24. This implements a possibility already mentioned in the pinned direct-residue parent; it is not a new worst-case bound or a fast specialized unit-argument evaluator.

Let cP,cQ<=J be the true local hit counts. Keep fixed integer representatives of acquired q1,Z_j modulo N^2. At precisions t=2,4,8,... capped at J+1, acquire W(N) modulo N^t by the scalar geometric block algorithm: construct F_t=product_j(X-Z_j), construct D_s(X)=product_(r<s)F_t(q1^r X-N) by doubling, evaluate it at the h/s geometric block starts by monic MPE, multiply, and include the final short block. Choose s near sqrt(h/J), handling empty dimensions directly. The construction costs soft t*(J+sqrt(Jh))*log N bits. No long coefficient list is supplied.

If the acquired residue w_t is zero, increase precision. Otherwise set e to the largest integer with N^e dividing w_t, and compute u=w_t/N^e modulo N. A proper gcd(u,N) factors; gcd=1 proves cP=cQ=e and returns that exact count. gcd=N is excluded by maximality of e. Stop no later than precision J+1.

Proof: each factor has exact valuation zero or one locally, preserved by the fixed lifts because only residues modulo p^2 matter. Hence vP(W)=cP and vQ(W)=cQ. Once t>min(cP,cQ), w_t is nonzero, e=min(cP,cQ), and division leaves a proper gcd precisely if the counts differ. Increasing t geometrically charges a total precision O(min(cP,cQ)+1).

Thus the initialized output-sensitive cost is soft (min(cP,cQ)+1)*(J+sqrt(Jh))*log N, improving the literal precision-J engine on sparse instances. For equal counts Theta(J), there is no worst-case improvement; the existing direct-list soft(J+h) alternative is better then. This does not meet the required native soft m whole-query goal, does not change the formal-prefix failure, and is not presented as new rate progress.

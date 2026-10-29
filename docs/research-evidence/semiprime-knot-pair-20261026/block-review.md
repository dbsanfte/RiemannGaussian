# Independent review: initialized geometric Alexander block

26 October 2026. Read-only algebra/cost review, except for the explicitly authorized scratch wording correction to the start z and short block range. No experiments or repository edits.

**PASS after the native-start correction.** Section 2 now permits any supplied unit z and states the actual odd-weight start z=eta^3*q^s, 0<=s, s+b<=m. A bare z=q^s is not the native parametrization with known short integer s. The identity itself never needed that stronger restriction. I also made 1<=b<=m explicit, with the empty b=0 product handled directly.

The native factor normalization in equation (1) is exact:

    (v-t)(v-t^-1)/(v-1)^2
      =1-v*(t+t^-1-2)/(v-1)^2.

No missing power of v or t is present. In the block product, the first factor supplies v^b Q_b(z/v); the second supplies (-z^-1)^b q^(-b(b-1)/2)Q_b(zv). This gives precisely equation (2) and, on multiplying over L rows, the stated

    U=(-1)^(Lb)z^(-Lb)q^(-Lb(b-1)/2)
        *(product v_j)^b/(product(v_j-1))^(2b).

All ingredients of U are known units after the native screens. The exponent b(b-1)/2 is an integer; no inverse of 2 in the ring is needed. U preserves exact zero and nonunit predicates over R, and every collision factor remains in the two Q_b evaluations. Repeated roots are harmless and retain multiplicity.

For 1<=b<=m strictly below both local q orders, every denominator 1-q^(r+1) in recurrence (4), 0<=r<b, is a certified unit. The recurrence is the correct q-binomial ratio, including the sign and q^r factor. Powers and all b denominator inverses can be acquired in soft b; alternatively the direct polynomial product tree is division-free. The leading coefficient is a unit, so the degree is exactly b. Evaluating this arbitrary polynomial with monic SUBPRODUCT divisors does not require distinct evaluation points or a monic Q_b.

The soft(L+b) single-block cost includes the full Q_b coefficient list, all 2L actual points, their monic multipoint evaluations and U. It is correct at collisions. The nonoverlapping-block bound soft(b+ML/b+M) honestly retains the cost of each shifted evaluation list and does not improve the existing soft(L+sqrt(LM)) whole-prefix bound. A shorter final block can be acquired at the same aggregate scale. The native z starts and endpoint powers each have binary descriptors and paid powering; no discrete logarithm is assumed.

The binary shift identities Q_(a+b)=Q_a(Y)Q_b(q^aY) and Q_2a=Q_a(Y)Q_a(q^aY) are exact. The claimed b-leaf accounting applies to that particular recursively evaluated descriptor, not every algorithm. For D=diag(1,q,...,q^(b-1)), the Krylov/Vandermonde determinant is a unit since each difference q^j-q^i has 0<j-i<b within the unit range. Thus that proposed one-particle companion realization has rank b; this is appropriately not presented as a lower bound for a zero-only native contraction.

The conclusions correctly distinguish an acquired lawful block scalar from the unacquired shared full-prefix interaction. No new whole-query exponent is claimed. The topological input discussion also avoids identifying an arbitrary integer Seifert realization with a specified twist knot merely from its Alexander polynomial.

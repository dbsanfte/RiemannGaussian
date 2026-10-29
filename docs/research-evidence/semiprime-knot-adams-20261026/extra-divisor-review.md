# Independent review: complete-family extra-divisor elimination

26 October 2026. Verdict: the coefficient identities, full-family scalar correction, unit margin, and softly O(L+sqrt m) correction acquisition are correct. The original-prefix decoder is valid using the **actual opposite-row transport** spelled out below; do not implement it using an unlicensed positive endpoint m+1. No full-query speedup is established. Read-only review; no source/repository edits or numerical campaign.

## Algebra and normalization

The supplied local three-state matrix has determinant 2(u+1)/u², a unit. Its inversion gives the stated B,B² expressions. Thus H_v=B(B−w_v), w_v=1+u−v−u/v, is a lawful finite scalar skein combination with no target-value inverse. The sign convention s=v/(v−1)² is consistent with the chosen negative twist lift: the ordinary factor is 1−s(T+T^(-1)−2), since c=−s.

For one reciprocal root pair, direct expansion gives

    P_s(B)=(s²/u)(B−w_v)(B−w_(v^(-1))).

Its constant term is

    (s²/u) w_v w_(v^(-1))
      =(v−u)(uv−1)/(u(v−1)²)
      =1−s(u−1)²/u.

The linear and quadratic coefficients are likewise s(1+u^(-1)) and s²/u. Therefore D=u^(−L)*product_j s_j² and P_native=D*M are correct, with every factor of D a known unit. Multiplying both orientations for every j proves exactly

    H_native(B)=B^(2L) D^(-1) P_native(B).

There is no missing sign, eta power, or multiplicity. M and P_native have degree exactly 2L and unit leading coefficients; H_native in fact has degree exactly 4L for L>0, with leading coefficient1 (the report's “at most 4L” is harmless). L=0 is the empty product case.

Over n pair positions, the complete scalar correction is exactly D^(−n)*U_clock^(2L). Unit multiplication preserves both zero and nonunit predicates over any commutative ring; no squarefree-root inference is used in this step.

## Clock starts, tails and order margin

For h=0,...,n−1, a_h=eta³ q^(2h)=eta^(4h+3), b_h=eta^(−5)q^(−2h)=eta^(−4h−5). These are the disjoint original odd-argument pairs (3,5),(7,9),..., with the second argument inverted using ordinary reciprocity. They begin at 3, not 1.

The largest absolute exponent in a pair is 4n+1. For m=2n this equals 2m+1, precisely the original last argument; for m=2n+1 it is 2m−1. The unpaired factor is then **K(eta^(2m+1))**, with exponent 4n+3. Thus the supplied guard 2m+1 below both local eta-orders certifies all a_h−1,b_h−1 and hence all B_h units, including initial h=0. On the actual packet, eta and q have the same odd local orders >16k² and the legal horizon satisfies this short-exponent condition. Do not extrapolate the proof to arbitrary m beyond that horizon.

For m=0, n=0, U_clock=1 and the full product is1. For m=1 there are no pairs and the sole leftover is K(eta³), evaluated directly. These cases require no q-factorial algorithm or division. For odd m≥3, multiply both sides of the paired identity by that same leftover factor; the correction stays unchanged.

The exact scalar formula

    U_clock=(eta³;q²)_n (eta^(−5);q^(−2))_n

has no extra sign or monomial: B_h=(a_h−1)(b_h−1)=(1−a_h)(1−b_h). Starts and steps are known units, including inverse steps. Monic remainder-tree scalar q-Pochhammer evaluation works over the composite ring with repeated points and without point-difference inverses. Two such products cost softly O(sqrt n); acquiring D and the optional odd tail costs softly O(L), and binary powering handles the 2L,n exponents. Hence the entire numerical correction really is acquired in softly O(L+sqrt m) ring work and the corresponding polylog-N bit overhead. This does not compute the left-hand norm.

## Original-label decoder: explicit negative-index transport

Let i=2h+1, so a_h=t_i=eta^(2i+1) and b_h=t_(i+1)^(-1). Write an acquired representative v=x/eta, where x=beta^E is an original surviving row, and its actual opposite is x'=q/x=beta^(H−E). The complete catalogue/paid half-center preparation supplies that opposite label. Then:

* v=t_i implies x=q^(i+1); use **opposite row x'=q^(−i)**, at legal negative index −i.
* v=t_i^(-1) implies **original row x=q^(−i)**.
* v=t_(i+1) implies x=q^(i+2); use **opposite row x'=q^(−i−1)**.
* v=t_(i+1)^(-1) implies **original row x=q^(−i−1)**.

At a localized H_v(B_h), the factor B_h is a unit, so only B_h−w_v can contribute a nonunit. The exact factorization

    B(a)−B(v)=−(a−v)(a−u/v)/a

maps its two factors to v=t_i or v=t_(i+1)^(-1), respectively. The v^(-1) orientation gives the other two cases above. If the two factors hit different primes, localize their product: a proper gcd factors directly; otherwise a saturated factor is taken with the stated original label and negative integer index. That original difference has its public-deletion guarantee of a nonzero polynomial-bit exponent gap, so the licensed saturated-leaf extractor applies. No new positive-index leaf is required.

In particular at the final even pair, the formal x=q^(m+1) branch must be transported to its opposite x'=q^(−m). Merely passing m+1 to the original negative-window consumer would be invalid. For the odd leftover t_m, its v=t_m or v=t_m^(-1) branches use the same opposite/original rule at index −m. Unit masks and actual retained labels must remain attached during any restricted row/index query. The report's decoder claim is sound with this bookkeeping made explicit.

## Scope and Adams clarification

The complete-family identity removes all extra scalar zeros: a localized zero/nonunit is a genuine original factor, after the above transport. The complete numerical correction is cheap; the remaining norm has the same original interaction and still costs softly O(L+sqrt(Lm)) with the current evaluator. No factorization exponent or new full-prefix oracle follows.

Separately, a zero/nonunit-only Adams oracle does **not** need the numerical unit U(T) or a computed Frobenius-deflation correction. Proving its unit existence already proves the predicate equivalence. Those values would matter for exact numerical scalar recovery, or for a particular transfer algorithm that explicitly divides by them, not as mandatory prerequisites for every zero-only method. The actual missing Adams target is a shorter acquired joint clock contraction. This clarification is coordinated with the ongoing Adams report review.

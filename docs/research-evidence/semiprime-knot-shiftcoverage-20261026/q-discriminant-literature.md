# q-discriminant: prior credit and one actual-alphabet deflation interface

26 October 2026. Bounded primary-source check; no new evaluation algorithm or query-rate gain. Read the prior audit in `/home/dbsanfte/riemann/formal/docs/semiprime-factorisation-investigation.md`, lines 34673–34715 and 34818–34850. The q-Dyson and staircase-Macdonald identification, normalization telescope, and unpaid long numerator are OLD credit.

[Boussicault–Luque, arXiv:0801.2443](https://arxiv.org/pdf/0801.2443), Eq. (7), Theorem 3.2, printed p.4, identifies

    D_d(X;p)=prod_(l=1)^d prod_(i!=j)(p^(2l-1)*x_i-x_j)
       =(-p)^[d²*n*(n-1)/2] P_(2d*rho)(X;q_src,p^(2d-1)),
    q_src=p^-2, rho=(n-1,...,0).

The scalar prefactor is a monomial unit. The physical shift parameter is p=q_physical; confusing it with q_src changes every shift. The theorem is a symmetric-polynomial specialization, not a fast scalar evaluation at native reciprocal/opposite-closed alphabets. No principal-specialization hypothesis is supplied merely by opposite closure. Generic eigenvector uniqueness and rational coefficient formulas do not automatically specialize as finite-ring algorithms. No new cheap specialization was found here.

Put W_m(X)=prod_(l=2)^(m+1) prod_(i!=j)(q^(2l-1)*x_i-x_j). Then

    D_(m+1)(X;q)=D_1(X;q)*W_m(X)

is an exact polynomial factorization. Writing W_m=D_(m+1)/D_1 is FORMAL only. D_1 can have literal native q-adjacencies and vanish; no numerical division is licensed.

There is a fresh finite bridge using the new fixed-shift certificate. On its factor-free branch for h=1, after exact node deduplication, all local q-adjacencies are the known literal ones; each component has at most two nodes in the complete original family. Let r be the number of directed q-edges, so r<=n/2. Set c_i=0,1 on the two ordered endpoints of each edge, and c_i=0 on isolated nodes, and define

    x_i(eps)=x_i*(1+c_i*eps).

Every literal edge factor has a simple epsilon zero with coefficient q*x_i*(c_i-c_j); with source c_i=0 and target c_j=1 this is exactly -x_j, a unit. Every other D_1 factor is a unit at epsilon=0 by the certificate. Hence, division-free,

    D_1(X(eps);q)=eps^r U(eps), U(0) a certified unit,
    [eps^r]D_(m+1)(X(eps);q)=U(0)*W_m(X).           (1)

Thus the indicated regularized coefficient has EXACTLY the desired odd-shift product's local-zero/nonunit predicate, without inverting a vanishing D_1 or acquiring the optional numerical U(0). The orientation-reversed edge is not another zero: q²-1 is a short certified unit. Distinct native nodes already have unit differences. This is a finite ring identity, including collisions in W_m.

Equation (1) does not acquire its coefficient. The jet order is r=O(n), not bounded independently of the alphabet. A Macdonald/fusion algorithm would still have to compute this specific coefficient, with all seeds and any denominators certified, at soft O(n+sqrt(m)) or another adequate complete-query cost. Computing the defining product simply restores the long paired norm. Formal opposite closure does not supply that readout. The general h=1 certificate costs soft O(n+T_ext), T_ext=soft N^(31/192), at most one terminating extractor; for n=soft k it is soft k. This prior certificate cost is separate from the still-unpaid regularized Macdonald value.

This note records the exact fresh normalization/zero interface, not the rediscovered literature as progress and not a new fast algorithm. The known complete query bound is unchanged.


## Actual odd-shift resultant and cleared normalization ledger

Read the current `joint-shifts.md`. Its full resultant also has diagonal factors (q^(2l-1)-1)*x_i. For 3<=2l-1<=2m+1<16H these are certified units, so removing ALL diagonal factors changes no local-zero/nonunit predicate and needs no numerical unit-product acquisition. The remaining odd shifts are exactly W_m above. The native opposite closure is x_bar=q/x; uniform recentering by eta makes it reciprocal, changes all ratios by no amount, and scales these homogeneous products only by a monomial unit. It does not make the alphabet a principal specialization.

The derivative/separation prepass must first rule out numeric repeated nodes or return a factor; exact integer duplicates alone are insufficient. Then the h=1 certificate makes the directed literal zero edges disjoint two-node components. No vertex is assigned conflicting c-values. At epsilon=0, multiply the r exact edge coefficients (-x_target) and every other D_1 factor. This is U(0), a unit by the certificate; its numerical value is NOT needed. In D_(m+1)=D_1*W_m, coefficients below order r vanish, and the order-r coefficient is U(0)*W_m(X), even if W_m(X)=0. This proves (1) without cancelling any target factor or inverting an additive value. When r=0 it reduces to the ordinary unit-prefactor equality.

Keep the source's monomial normalization OUTSIDE the coefficient: if kappa_d=(-q)^[d²*n*(n-1)/2], then [eps^r]D_d(X(eps);q)=kappa_d*[eps^r]P_(2d*rho)(X(eps);q^-2,q^(2d-1)). Only kappa_d, a certified unit, is moved across. No rational Macdonald expansion denominator is assumed invertible. This identifies the sufficient specialized Hasse coefficient, not an algorithm acquiring it. The prior audit remains the literature credit; the new statement is only this exact certified deflation interface on the actual alphabet.

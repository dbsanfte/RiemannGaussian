# Integrable closure experiment for the two selected cofactors

26 October 2026. Scratch, paper-only. No repository edits or experiments. This continues the authoritative [selected-subresultant report](../semiprime-unique-pole-20261026/selected-subresultant.md), especially its exact E_n recurrence. All complexity below includes acquisition of the entries, rather than merely specifying a determinant.

**Outcome.** There is an initialized Christoffel moving-frontier algorithm and an exact Hankel/Toda realization of E_n. The frontier costs soft(Jh); the Hankel realization does not acquire its final moments or eliminate its structurally singular initial pivots. A separate, paid native test resolves the proposed cancellation of D(X)/D(qX): on continuation those two polynomials have unit resultant. None supplies a soft-K acquisition of the final two E values. These are conclusions about these executed constructions, not an exclusion of other integrable algorithms.

## 1. Actual input and two-value target

Use the supplied monic D(X)=product_j(X-T_j), degree J<=K/3, a_t=q^t and h=O(K^(3/2))<16H. Work over the prepared quadratic etale algebra B. Every q^i-q^j used below with 0<|i-j|<=J is a unit. In the correct bin, at the good nonsplit field there is exactly one common row-clock root theta, simple in D and W_h; D can repeat elsewhere.

Put C=multiplication by X modulo D, v_t=adj(W_t(C))1, sigma=(-1)^(J+1), eta_t=v_t(a_t). The frozen report proves

    v_(t+1)=sigma Q_(a_t)(C)v_t,
    Q_a=(D(X)-D(a))/(X-a),
    E_t=(-1)^(Jt) eta_t.

It also proves E_0=1, paid soft-J initialization of the first J scalar E values, and the exact final locator

    theta=a_(h-1)+D(a_(h-1))*E_(h-2)/E_(h-1).

Only the final denominator is promised nonzero at the good field. Norm/coordinate gates and the bounded native tag validator remain necessary over B and on wrong bins. J=1 and h<=J use the already supplied short cases.

## 2. Christoffel/Lax execution, including the frontier

Before normalization the universal polynomial identity is

    (X-a_t)v_(t+1)(X)
      =sigma*(eta_t D(X)-D(a_t)v_t(X)).              (1)

If the leading coefficients are actual units, normalizing v_t to the monic degree-(J-1) polynomial p_t yields

    p_(t+1)(X)=(D(X)-gamma_t p_t(X))/(X-a_t),
    gamma_t=D(a_t)/p_t(a_t).                       (2)

This is a Christoffel-type update with the degree-J polynomial D fixed. It is a legitimate finite analogue of the standard Christoffel formula; it is not a licensed normalization through all native prefixes. Prefix leading coefficients can vanish additively, with no promised multiplicative-annihilator decoder.

There is an entirely initialized, unit-safe frontier version of (1). Set Z_(t,k)=v_t(a_(t+k)), 0<=k<J. Then

    Z_(t+1,k)=sigma*(Z_(t,0)D(a_(t+k+1))
                   -D(a_t)Z_(t,k+1))
                  /(a_(t+k+1)-a_t).               (3)

For k=J-1, extrapolate Z_(t,J) from the J stored values: v_t has degree<J, and all interpolation node gaps are units. The geometric extrapolation functional is acquired once in soft J. Its denominators contain only 1-q^r with 1<=r<=J. Initially every Z_(0,k)=1. Store a rolling list of D(a_t),...,D(a_(t+J)); new D evaluations cost soft J per step, or can be batched. The J updates, interpolation dot product, and rolling evaluations cost soft J per step, hence soft(Jh) in total.

Thus a weighted-shift-plus-rank-one frontier is actually available, not just a formal Lax matrix. Its next injection requires the frontier component Z_(t,0); advancing that component requires the next frontier entry. A two-coordinate Riccati rule has not resulted from (3). Uniqueness is a final rank statement and supplies neither the earlier frontier entries nor their normalization. This calculation does not rule out a different native closure.

Primary comparison: [Pearson equations for discrete orthogonal polynomials: III—Christoffel and Geronimus transformations, Theorem 3](https://link.springer.com/article/10.1007/s13398-022-01296-4) gives the standard Christoffel polynomial transformation under its nonsingularity assumptions. We use the cleared identity (1), not its unverified pivot assumptions.

## 3. A genuine Hankel/Toda tau, and the exact seed it needs

Define a functional without separating the roots:

    ell(f)=[X^(J-1)](f mod D).

Let p_n(X)=product_(i=0..n)(a_i-X), and mu_k(n)=ell(X^k p_n(X)). Its initialized evolution is

    mu_k(n)=a_n mu_k(n-1)-mu_(k+1)(n-1).            (4)

Initially ell(X^k)=0 for k<J-1, equals 1 for k=J-1, and its remaining values follow the supplied D recurrence. Any O(J) initial moment interval is acquired in soft J.

Write H_m^(r)(n)=det[mu_(r+i+j)(n)]_(0<=i,j<m). For J>=2, the exact identities are

    H_(J-1)^(0)(n)=(-1)^(J(J-1)/2+n) E_n,
    H_J^(0)(n)=(-1)^(J(J-1)/2) product_(i=0..n)D(a_i). (5)

For verification on the separated universal locus, ell(f)=sum_j f(T_j)/D'(T_j); Cauchy–Binet gives the full determinant and its one-hole minor, and ordinary partial fractions identify E_n. Both sides are polynomial identities in the supplied coefficients and a_i, so the cleared identities specialize to repeated roots and composite B without numerical D'(T_j) inversions.

The exact condensation relation is

    H_m^(r) H_(m-2)^(r+2)
      =H_(m-1)^(r) H_(m-1)^(r+2)-(H_(m-1)^(r+1))^2. (6)

All terms in (6) have the same n. This makes E_n a genuine Toda/Plucker minor; it does not make its neighbors supplied. The obstruction to the standard ratio implementation is especially concrete here: at n=-1 the moments with k<J-1 are zero. Whenever 2m-2<J-1, the entire leading m-by-m Hankel matrix is zero. Therefore ordinary no-zero-pivot Toda/qd initialization is not available for this very coefficient functional. Fraction-free (6) remains valid, but cannot recover an unknown numerator from 0=0 or divide these prescribed zero pivots.

At the desired final n, acquiring the O(J) moments required in (5) amounts to applying the long polynomial p_n to the companion algebra. Once p_n mod D is supplied, transposed multiplication/power projection extracts the moments in soft J; supplying that remainder is precisely a long-clock operation still absent. Executing (4) through time with the required moving moment frontier costs soft(Jh). Thus the missing input is explicit: a final moment frontier, or enough neighboring minors to bypass it, acquired without the long companion product. The correct-bin vanishing of the full determinant in (5) does not supply its nonzero one-hole minor or the other components' data.

For an integrable-source check, [Nagao–Yamada, Study of q-Garnier system by Pade method, §2.1 and §2.5](https://arxiv.org/html/1601.01099) uses a two-by-two scalar-Lax formulation with polynomial data of growing degree N and special reductions to low-dimensional equations. Its complex-|q|<1 setup does not initialize a finite-ring reduction here. We have not identified native constraints supplying those special reductions; matrix size two alone would not supply its polynomial coefficients.

## 4. An actual native cancellation gate for the Pearson datum

A concrete way to shorten an integrable spectral datum would be to cancel common factors from

    (1/D(qX))/(1/D(X))=D(X)/D(qX).                 (7)

This candidate can be tested on the ACTUAL row family in soft K, rather than left as a hypothetical gcd oracle. Form D(qX) from its supplied coefficients and evaluate it at all supplied T_j by monic multipoint evaluation. Repeated target values cause no difficulty. Norm gcds and a product tree localize a nonunit evaluation to a row, and then to a factor qT_j-T_k; proper gcds already factor N. Coordinate gcds distinguish a saturated norm from an actual global zero. One must not infer a single global edge merely from a saturated aggregate product: localization is essential.

For a global edge, write the native roots using centered ell_j and coefficients a_j,b_j. Their common clock normalization cancels. The relation qT_j=T_k is

    pi^(ell_j-ell_k+H)
       *barpi^((a_j-a_k)+N(b_j-b_k))=1.            (8)

Both short integer labels in (8) cannot be zero. The second being zero forces b_j=b_k and a_j=a_k since |a_j-a_k|<=2K<N. The first would then require ell_k-ell_j=H, impossible for centered phases with |ell_k-ell_j|<H. Duplicate numerical roots do not affect this integer-label argument.

The prepared mixed-relation decoder now factors from every actual global nonzero label pair: norm gives a short scalar-beta annihilator when the sum of the labels is nonzero; otherwise the nonzero torus label uses the newly proved torus-to-scalar transfer. Proper local gcd branches factor directly. These are existing shifted-root screen and annihilator consumers, not a newly claimed general algorithm. Each label has O(log N) bits, and the one licensed extraction costs below soft K.

Consequently this screen either factors, or certifies that every evaluated D(qT_j) is a unit. On continuation Res(D,D(qX)) is a unit in every component: (7) has no adjacent-q root cancellation. This resolves this specific proposed degree reduction on native input; it does not exclude a noncancelling Garnier specialization or another collective identity.

## 5. Charged conclusion

The available finite algorithms from these identities are: soft(Jh) for the division-free moving frontier; the inherited soft(J+sqrt(Jh)) long-clock engine; and soft K for the additional adjacent-q cancellation screen. At J=O(K), h=O(K^(3/2)), the inherited worst-case bound remains soft(K^(5/4)). No prefix-bit or selected-cofactor improvement follows from condensation alone. A successful next integrable handoff must acquire the final moment/frontier data or a closed replacement for its rank-one injections, with legal seeds and pivot gates; the exact object needing that acquisition is now specified by (3)–(5).

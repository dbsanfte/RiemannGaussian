# Simultaneous quadratic traces: exact norm state and the missing transport

2026-10-23. Scratch continuation only. The 222 entries across prior packets and all repository files are unchanged; the frozen curvature packet itself contains 14 entries.

## Outcome

No soft-O(r+h) algorithm for S_1,...,S_h with h of order r, and no polylogarithmic-query local nonunit locator, is proved here. The acquired upper bound remains soft O(rh (log N)^2). This is not a lower bound.

The useful exact formulation is a single split rank-r row algebra with all canonical-B carries included. It converts the desired contraction into a specific scalar norm of a quadratic-exponent product. The natural doubling law for that product changes a second clock. It cannot be implemented by an algebra endomorphism of the existing rank-r row algebra: the prepared local-order bound proves this narrowly and explicitly. Thus that doubling needs additional transported states or a different scalar identity. Merely applying power projection to the row algebra does not finish the contraction.

## 1. Data and conventions

Let N=PQ, P<Q distinct primes; squares have already been handled. Let r=Theta(N^(1/6)), H=r^2, M=r^4, and let beta be the prepared unit with local orders greater than 16r^2. Work over R=Z/NZ. Let

    C_u=C0+r u,  0<=u<r,
    B_u=canonical centered cubic lift modulo M,
    E_u,c=C_u N+c^2+B_u c,
    q=beta^M.

This is the positive-C / centered-B AP convention of phase-contraction.md. Its short sigma interval is I=[a,b] with |a|,|b|=O(r); the sibling centered-C / centered-b finite constants are not silently substituted. Row restrictions and common multiplier masks are allowed.

Define the raw full-interval product by

    F_raw(z)=product_(u,c,sigma in I) (1-z beta^(E_u,c) q^(-sigma)).   (1)

If the screened number of public integer K=0 leaves is h0, define separately

    F_clean(z)=F_raw(z)/(1-z)^h0.

The raw product has the original raw leaf support up to an explicit unit; F_clean(1) has the support after the legal public-zero deletion. Global nonzero exponents are handled by the existing annihilator decoder. These facts do not turn an additive trace into a zero detector. All norm identities below concern F_raw; cleanup is applied separately by the displayed factor and its trace correction.

## 2. Legal shared AP row algebra, including the carry mask

Put

    alpha=beta^(rN),    delta=beta^(C0 N),
    a_u=alpha^u,
    f(U)=product_(u<r)(U-a_u).

The points a_u are pairwise separated by units, or the separation test factors N. Indeed, if a_u-a_v vanishes modulo the smaller prime P, then

    ord_P(beta) divides r N (u-v).

Since gcd(P-1,N)=1 for P<Q, it follows that ord_P(beta) divides r(u-v), whose absolute value is less than r^2. This contradicts the prepared order bound. Thus no point difference vanishes modulo P. A nonunit product of differences has gcd exactly Q with N, never the saturated gcd N. A product-tree batch screen followed by ordinary fast interpolation is therefore legal and costs soft O(r (log N)^2) bits or returns a proper factor.

Let

    A=R[U]/(f(U)),
    W=delta U in A,
    V(a_u)=beta^(B_u),  deg(V)<r.

The interpolation data use the actual canonical B_u. If

    B_u=P3(u)-M h_u,

then V(a_u)=beta^(P3(u)) q^(-h_u), with h_u retained exactly. No substitution q=1 is used. Likewise, if a centered-C convention is used, the actual C_u values must enter W, or their corresponding extra interpolant; they cannot be replaced by the positive AP without their carry. The AP-linear W here belongs to the stated positive-C convention.

The Chinese remainder map identifies A with R^r. Trace and norm therefore give exact sums and products over the original rows, even over the composite base ring. All values V(a_u) are units, so V is a unit of A. A supplied row mask may be represented either by the corresponding factor of f or by the exact interpolated idempotent; the first option has rank equal to the number of included rows and retains W and V by reduction. This is row metadata, not an acquired factoring query.

## 3. The exact norm requiring contraction

For the full consecutive multiplier interval 0<=c<n, define the universal polynomial

    J_n(Z,T)=product_(c=0)^(n-1) (1-Z beta^(c^2) T^c).

The actual multiplier range 1<=c<r is obtained by deleting c=0 or shifting the origin with the exact same identities. Common masks retain only the selected factors; they do not generally preserve the interval recurrence below.

Let

    G(z)=Norm_(A/R) J_n(z W,V).

Then

    G(z)=product_(u,c)(1-z beta^(C_u N+c^2+B_u c)),
    F_raw(z)=product_(sigma=a)^b G(z q^(-sigma)).                  (2)

The endpoints a,b in (2) are the actual integer endpoints. Equivalently, if

    T_k=Tr_(A/R) [ W^k sum_c beta^(k c^2) V^(k c) ],
    A_k(I)=sum_(sigma=a)^b q^(-k sigma),

then S_k=A_k(I) T_k, with the already known public-zero correction S_k(clean)=S_k-h0. Thus the sigma direction is already separated; it is the c/k coupling inside T_k that remains.

Ordinary power projection applies to Tr(L X^k) for a fixed algebra element X and fixed linear functional L. Here both the multiplier sum and W^k change with k:

    T_k=sum_c beta^(k c^2) Tr(W^k V^(kc)).                         (3)

There are r fixed elements X_c=beta^(c^2)W V^c, and (3) is the sum of their power traces. Passing to the direct-product algebra A^n makes this a standard one-element power-projection problem, but its rank is rn=Theta(r^2). No rank-r replacement of this direct-product state preserving the required h moments has been constructed.

This statement identifies an unpaid representation step; it is not a claim that every algorithm must construct the direct product or its rn entries.

## 4. Exact doubling law and a narrow closure obstruction

The quadratic product has the exact identity

    J_(2n)(Z,T)
      = J_n(Z,T) J_n(Z beta^(n^2) T^n, beta^(2n) T).               (4)

It follows by writing c=n+d in the second half. A short odd tail has its explicit additional factor. Equation (4) includes the quadratic exponent beta^(n^2); omitting it changes the product.

After the specialization (Z,T)=(zW,V), the second block requires

    J_n(z W beta^(n^2) V^n, beta^(2n) V).                        (5)

A universal polynomial J_n in two independent variables permits this substitution. A previously reduced element of A[z] generally does not. Reducing modulo f has preserved only the r row evaluations, and (5) asks for shifted row-clock evaluations.

In fact no R-algebra endomorphism phi of this split rank-r A can satisfy

    phi(V)=beta^(2n) V,  1<=n<=r.                               (6)

Proof: reduce modulo the smaller P. Because the a_u are distinct, A modulo P is F_P^r. A unital F_P-algebra endomorphism induces a map on the r coordinate points. Every such finite map has a cycle of length ell<=r. Along that cycle (6), together with the nonzero coordinates of V, forces

    beta^(2n ell)=1 mod P.

But 2n ell<=2r^2, contradicting ord_P(beta)>16r^2. This proves the assertion. It does not depend on falsely treating the modular cubic B_u as an ordinary polynomial exponent; its actual canonical values are used.

This is an obstruction only to this specific closed-state reuse of (4). It does not exclude an identity for the scalar norm, an enlarged state with a proved soft-r ledger, a transposed algorithm, or another query construction. The exact additional state needed by the current doubling is the family of shifted clock pairs

    ( beta^(t^2) W V^t, beta^(2t) V ),

at the required block offsets t. The recurrence does not show that their norms or restricted evaluations can be acquired for free.

## 5. Recurrence and interpolation attempts, with their actual state

### Trace-index recurrence

For one fixed c, the sequence Tr(X_c^k) has the characteristic polynomial of X_c as a recurrence. For all c at once the immediate common recurrence is

    product_c det(T I-M_(X_c)),

of degree rn. Acquiring its first h coefficients or a smaller exact recurrence is precisely the missing scalar contraction, rather than a consequence of the rank-r row algebra. The AP parameterization of W does not make V degree <=2: V is a degree-<r interpolant carrying the canonical cubic centering mask.

### Bivariate moment generating function

One may keep the r clock pairs without expansion as

    R(X,Y)=sum_u 1/[(1-X W(a_u))(1-Y V(a_u))].

Its coefficient at X^a Y^b is Tr(W^a V^b). Equation (3) requests the weighted dilated diagonals (a,b)=(k,kc), with weight beta^(kc^2). This is not a single ordinary diagonal or a single fixed-element Krylov sequence. Producing the required contracted diagonals in soft O(r+h) is an explicit alternative formulation of the missing theorem. No dense bivariate coefficient table is counted as free input.

### Fast q-recurrences

[Bostan and Yurkevich, sections 3.3–3.4](https://arxiv.org/html/2012.08656) give algorithms whose cost depends on recurrence order and coefficient degree, and algorithms for selected indices of one supplied q-recurrence. They do not supply that recurrence here. Advancing the truncation endpoint c of a partial theta sum while holding beta^k fixed changes a different parameter from advancing k: the latter changes the base beta^k. Applying the cited algorithms would require a proved low-order recurrence for (3), with every coefficient and its base-ring unit condition paid. The immediate rn-order recurrence above does not meet the target.

### Sparse resultant / norm

Formula (2) is a valid resultant representation: Norm_(A/R) of an element represented modulo the degree-r polynomial f. However, a z-prefix of length h in A has rh scalar coefficients. Computing it by generic polynomial arithmetic over A and then taking its norm has not contracted that state. The paid degree-two carrier norm does not apply to the arbitrary degree-<r interpolant V or to the second-clock transport (5). A scalar identity avoiding these rh coefficient states would be new progress; merely writing this norm is not.

## 6. Unreduced Newton support and an acquired boundary family

The unreduced bivariate polynomial is explicit enough to audit rather than assuming low support. Its coefficient of Z^j is

    (-1)^j sum_(0<=c1<...<cj<n) beta^(c1^2+...+cj^2) T^(c1+...+cj).

The possible T exponents are every integer in

    j(j-1)/2 <= ell <= j(2n-j-1)/2.

For beta regarded as a formal indeterminate, all these coefficients are nonzero, because their coefficients in beta are positive integers. Thus the universal Newton-support count through Z degree h<=n is

    sum_(j=0)^h [j(n-j)+1]
      = n h(h+1)/2-h(h+1)(2h+1)/6+h+1.

It is Theta(n h^2) for h<=n/2 and Theta(n^3) for the full polynomial. A specialized modular beta can create cancellations; none is presumed. This count is the size of the explicit coefficient representation being considered, not a lower bound on a circuit or a scalar algorithm.

Taking the logarithm makes the support substantially smaller:

    -log J_n(Z,T)
      = sum_(k>=1) Z^k/k sum_(c<n) beta^(k c^2) T^(kc).             (7)

Through degree h, (7) has exactly nh monomial locations (k,ell=kc). The established fixed-k contraction traces each horizontal slice of these locations. The unreduced Newton polygon does not itself yield a soft-O(n+h) coefficient representation when n and h are both of order r.

There is, however, an exact simultaneously contracted **difference**. Define

    Theta_(n,k)(T)=sum_(c=0)^(n-1) beta^(k c^2) T^c.

Its elementary q-difference identity is

    Theta_(n,k)(T)-beta^k T Theta_(n,k)(beta^(2k)T)
      =1-beta^(k n^2) T^n.                                     (8)

With T=V^k, multiply by W^k and trace. If Phi(W,V)=(beta W V,beta^2 V), then

    T_k(W,V)-T_k(Phi(W,V))
      =Tr(W^k)-Tr((beta^(n^2) W V^n)^k).                         (9)

All k=1,...,h on the right of (9) can genuinely be acquired together in soft O((r+h)b^2) bit work. Form the two ordinary degree-r scalar polynomials

    Q0(z)=product_u (1-z W(a_u)),
    Qn(z)=product_u (1-z beta^(n^2) W(a_u)V(a_u)^n).

Their negative logarithmic derivatives supply their first h power sums using fast formal division; the constant denominators are 1, so no point separation or order inversion is required. The O(r) modular powers forming the second node list cost soft O(rb^2), and polynomial work costs soft O((r+h)b). Workspace is soft O((r+h)b) bits. This is a first-difference family, not the original T_k family.

The multiplicative identity underlying (9) is

    Norm J_n(zW,V) / Norm J_n(z beta W V,beta^2 V)
      = Q0(z)/Qn(z)                                             (10)

as a formal series at z=0. For the actual sigma interval, multiply the kth difference in (9) by the exact A_k(I). Its h-term formal ratio prefix is then acquired in the same soft O((r+h)b^2) bound, using legal division by k<=h. Any public-zero correction on the two windows differs only at their two boundary multipliers and can be screened in O(r) work.

Equation (10) is not a valid nonunit locator by evaluating and cancelling at z=1: numerator and denominator may both vanish at a local prime. It is a ratio of two overlapping multiplier windows and loses their common collision support. An anchor value for one shifted window, or a proved scalar solution of this difference equation, remains missing. Iterating (9) without such an anchor only telescopes known boundary terms.

The exact finite-difference description of the cubic row clock also stops short of a degree-two algebraic relation. Writing B_u=P3(u)-M h_u gives

    V(a_(u+1))/V(a_u)
      = beta^(P3(u+1)-P3(u)) q^(-(h_(u+1)-h_u)),

where the exponent before the carry is quadratic in u. This is a relation in successive row values and exponent clocks. It is not an ordinary degree-two polynomial relation in U,V; dropping the q carry changes the values. No such low-degree relation with a proved nearlinear acquisition ledger has emerged in this audit.

## 7. Base-ring bit ledger and exact frontier

Let b=ceil(log_2 N), r=Theta(N^(1/6)), h<=r. Canonical B,C and all exponents above have O(b) bits, including the endpoint and carry exponents.

* Row-algebra setup: O(r) modular powers of O(b)-bit exponents, one batch separation screen, product tree, and interpolation. Conservative bit cost soft O(r b^2), storage soft O(rb) bits. A failed separation screen returns a proper factor, as proved in section 2.
* A multiplication or monic reduction in A: soft O(rb) bit operations and soft O(rb) bits of storage. This cost cannot be replaced by one scalar modular multiplication.
* An arbitrary element of A[z]/z^(h+1): up to rh base-ring coefficients and soft O(rhb) bits. Generic arithmetic on this state pays its full size.
* Already acquired traces: compute each k by the scalar monic multipoint formula in phase-contraction.md, in soft O(r b^2) bits. Repeating h times costs soft O(rh b^2), with soft O((r+h)b) storage when the workspace is reused. This remains the actual acquired bound; it is not asserted to be optimal.
* Seed factor and cleanup: each A_k(I) is acquired division-free with the exact endpoints; the public K=0 screen is one O(r)-operation scan, and its h0 subtraction is paid once per k. No inverse of 1-q^k is used.

The boundary-difference family (9), including its sigma factor, is acquired in soft O((r+h)b^2) bits. It does not improve the acquisition bound for the original traces, because its shifted-window anchor is unacquired and its multiplicative ratio does not retain common zero support.

The remaining constructive target is therefore precise: evaluate the scalar norm in (2), contract the dilated-diagonal family (3), or supply a legal anchored solution to (9), in soft O(r+h) base-ring bit work after the stated setup, while retaining the actual V values and sigma endpoints. A locator using only polylogarithmically many such traces would instead need a proved identity linking those particular traces to local collision support. No such identity is established by the row algebra or by the recurrence attempts above. No universal lower-bound or generic low-moment counterexample is claimed.

Exact small checks: the boundary trace identity (9) was checked directly over Z/(101*103)Z with the canonical positive-C/centered-B rows for r=3,5,7 and k=1,...,5. The Newton-support count was checked by subset enumeration for n=1,...,8 and every h<=n. Both checks passed. The algebraic proofs above do not depend on those examples satisfying the large-order setup.

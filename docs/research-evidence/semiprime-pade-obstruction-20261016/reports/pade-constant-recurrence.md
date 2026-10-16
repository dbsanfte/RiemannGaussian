# A rational functional-equation certificate forces quadratic constant-recurrence order

2026-10-16. Classical finite-segment obstruction proposed by root and independently derived here. It strengthens the preceding order-at-most-m constant-recurrence result to order at most L/4, without frequency-distinctness, alias screening, or a prime-order hypothesis. It is a representation theorem, not an operation lower bound or a new acquisition algorithm.

## Theorem

Let K be a field and g,q nonzero elements. Let L>=1, and let C(X)=sum_(k=0)^L A_k X^k have exact degree L, A_0=1, and satisfy the coefficient identity (2) below. The general theorem needs no relation between g and q. Its canonical application is obtained as follows: for an integer d>=1 put q=g^d and define

 F(T)=product_(i=0)^(L−1)(1−q^i T)=sum_(k=0)^L c_k T^k,
 A_k=c_k g^(−binom(k,2)), C(X)=sum_(k=0)^L A_k X^k.

Let r>=1 satisfy4r<=L and ord(q)>L+r. Then there are NO constants a_0,...,a_r in K, with a_r!=0, such that

 sum_(t=0)^r a_t A_(k+t)=0 for every0<=k<=L−r.                        (1)

Equivalently no nontrivial constant-coefficient recurrence of maximal nonzero order at most floor(L/4) holds throughout its natural finite range. An order-zero nontrivial relation is also impossible since A_0=1. Coefficients may be fully advised and depend on the entire input or hidden field. There is no condition on the characteristic, no distinctness assumption on the g-powers, and no requirement that g or q have prime order.

## 1. Exact two-clock polynomial identity

For the canonical q-binomial/chirped construction, the finite coefficient relation is

 (1−q^(k+1))c_(k+1)=(q^L−q^k)c_k.

Substituting the chirp gives the identity assumed in the general theorem:

 g^k(1−q^(k+1))A_(k+1)=(q^L−q^k)A_k, 0<=k<L.                      (2)

In the canonical construction all c_k and A_k are nonzero because ord(q)>L; its leading A_L is visibly a product of units, verifying the general exact-degree premise. Summing (2), with the endpoint q^L−q^L=0, gives the exact polynomial identity

 C(gX)−C(gqX)=gX[q^L C(X)−C(qX)].                                  (3)

There is no omitted top-degree boundary term: the coefficient of X^(L+1) on the right is g(q^L−q^L)A_L=0; on the left the constant term is0.

## 2. A finite recurrence supplies a rational approximant

Assume (1). Set

 Q(X)=sum_(j=0)^r a_(r−j)X^j,       Q(0)=a_r!=0.

For every n=r,...,L the coefficient of X^n in Q(X)C(X) is zero by (1). Let P(X) be the truncation of Q C to degrees below r. Thus

 deg Q<=r, deg P<r,
 Q C−P=O(X^(L+1)),
 G=P/Q=C+O(X^(L+1)) in K[[X]].                                    (4)

The possibility deg Q<r is allowed; no nonzero a_0 is assumed. This is a direct coefficient identity over a field, not an acquisition claim about computing a Padé approximant.

## 3. Finite precision forces an exact rational equation

Substitute G into the left side minus right side of (3), and call the resulting rational function E_G(X). Since G−C has order at least L+1 at0 and every scaling argument is a nonzero scalar multiple of X,

 E_G(X)=O(X^(L+1)).

Clear the FOUR denominator factors

 Q(gX) Q(gqX) Q(X) Q(qX).

Their product has nonzero constant coefficient. The resulting numerator has degree at most4r: the first two terms have degree at most(r−1)+3r=4r−1, and the two terms multiplied by X have degree at most1+(r−1)+3r=4r. Zero terms or lower actual degrees only improve this bound.

That numerator vanishes to order at least L+1. Since4r<=L, it is the zero polynomial. Therefore

 G(gX)−G(gqX)=gX[q^L G(X)−G(qX)]                                   (5)

holds EXACTLY in K(X), not merely at finitely many evaluation points.

## 4. Uniqueness beyond the polynomial endpoint

Write G=sum_(n>=0)b_n X^n as its formal series at0. Its constant coefficient is b_0=A_0=1 by (4). Comparing X^(k+1) coefficients in (5) gives

 g^k(1−q^(k+1))b_(k+1)=(q^L−q^k)b_k.                              (6)

For k+1<=L+r all leading factors are nonzero because ord(q)>L+r. Consequently the recursion uniquely determines b_1,...,b_(L+r). Up through L it agrees with (2), hence b_k=A_k. At k=L the right side is zero, forcing b_(L+1)=0; continuing (6) forces b_(L+2),...,b_(L+r)=0.

Thus

 G−C=O(X^(L+r+1)).

Multiplying by Q, whose constant coefficient is nonzero, shows that P−Q C vanishes to order at least L+r+1. Its degree is at most L+r. It is therefore identically zero. But Q!=0 and C has exact degree L, so deg(Q C)>=L, while deg P<r<=L. This contradiction proves the theorem.

No differentiation, factorial division, separability, analytic identity theorem, or characteristic-zero premise occurs. Only formal power-series coefficient comparison and field polynomial degrees are used.

## Canonical actual-source and uniform-setup consequences

Set d=m² and L=2m²+2. Both the original qualified prime-order source and the new paid certified beta/q setup have each local q-order>16m². This exceeds L+floor(L/4) for m>=1. Applying the theorem separately in both hidden fields yields

 maximal nonzero constant-recurrence order >floor((2m²+2)/4).

In particular no orderO(m polylog m) constant-coefficient recurrence can describe the entire finite chirped segment eventually. Unlike the earlier frequency-count theorem, this closes the order2m and larger nearlinear constant-recurrence escape as well. It does not exclude general q-dependent coefficient recurrences, multivariate/two-clock state methods, sparse or nonlinear representations, selected convolution, rational transforms of another stream, or direct scalar norms.

The uniform application is conditional on the paid setup returning its certified base rather than a factor, with that setup's exact input hypotheses. It does not transfer the original collision controller automatically to a new base. No source exceptional set or new analytic prime theorem is required here.

## Provenance and remaining cost gap

The coefficient ratio and exact chirp are inherited from the earlier block-transform and bounded-offset reports. The old order-at-most-m proof used finite-frequency collinearity and a highest-shift pole. The new argument instead uses finite recurrence-to-rational approximation, the TWO-CLOCK functional equation, a four-denominator degree bound, and uniqueness through r zeros beyond the polynomial endpoint. The existing old Padé audits concerned different filtered rational functions and do not supply this finite-segment theorem.

The rational Padé approximation and denominator-clearing method are standard. A targeted journal/report search for this four-shift chirped application found no prior version of the present finite-segment argument; this is a limited repository novelty check, not a literature-priority claim. Root originated the strengthening; this report records its complete independent algebraic verification.

The theorem prevents invoking a low-order CONSTANT recurrence for this stream while omitting its growing order. It is not a lower bound for a q-holonomic algorithm or an arbitrary arithmetic circuit. No improved whole-query clock, factor acquisition, native code, Lean declaration, numerical example or broad build follows. Exact inherited prerequisite pins are recorded in source-pins.json.

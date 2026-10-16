# Exact first-order rational degree of the chirped q-binomial stream

2026-10-16. A route-specific finite-segment statement, not a lower bound for arbitrary query algorithms.

Let K be a field, g a nonzero element, d>=1 an integer, q=g^d, and L=2d+2. Assume the L elements g^k (0<=k<L) are distinct and ord(q)>L+1. Define

 F(t)=product_(i=0)^(L-1)(1-q^i t)=sum_(k=0)^L c_k t^k,
 A_k=c_k g^(-k(k-1)/2).

All c_k and A_k are nonzero. Indeed c_0=1, and the finite q-binomial identity, or direct coefficient comparison in (1-t)F(qt)=(1-q^L t)F(t), gives

 c_(k+1)/c_k=-(q^k-q^L)/(1-q^(k+1)), 0<=k<L.

All numerator and denominator factors here are nonzero under the order assumption. Consequently, at X=g^k,

 A_(k+1)/A_k=-(X^d-g^(dL))/[X(1-g^d X^d)].                         (1)

Claim: among rational descriptions U(X)/V(X) agreeing with these L consecutive ratios and satisfying V(g^k)!=0 for every 0<=k<L, the minimum of max(deg U,deg V) is EXACTLY d+1.

The displayed formula supplies degree d+1 and has nonzero denominator on every required node. For the converse suppose deg U,deg V<=d. Agreement implies that

 C(X)=U(X) X(1-g^d X^d)+V(X)(X^d-g^(dL))

vanishes at all L distinct nodes. Its degree is at most 2d+1<L, so C is identically zero.

The polynomials X^d-g^(dL) and X(1-g^d X^d) are coprime. The first is nonzero at X=0. A common divisor of X^d-g^(dL) and 1-g^d X^d would divide their linear combination 1-g^(d(L+1))=1-q^(L+1), a nonzero scalar. This works in every field characteristic and does not require separability of X^d. From C=0 and this coprimality, the degree-(d+1) denominator divides V. That is impossible for deg V<=d unless V=0, which is forbidden by its required nonzero evaluations. The claim follows.

## Actual source and algorithmic scope

For canonical d=m² and L=2m²+2, the original qualified source has g=gamma with prime local order R>16m² and R coprime to d. Thus both node distinctness and ord(q)=R>L+1 hold in each hidden field. The newly paid setup also supplies the needed conditions when g is its retained beta and q=beta^(m²): its global/local g-order bounds and certified local q-orders exceed16m². This theorem is fieldwise; it does not require computing either hidden factor or order.

Multiplying c_k by a fixed unit geometric factor (for example absorbing the common gamma^(-N) node origin) only rescales the rational numerator and leaves the same minimum degree.

The exact integer identity ek=binom(e+k,2)-binom(e,2)-binom(k,2) gives the usual ring-safe Bluestein expression

 F(g^e)=g^(-binom(e,2)) sum_(k=0)^L A_k g^(binom(e+k,2)).

A bounded e-window of size O(d) permits a full convolution of length O(L+d), but the requested J~sqrt L outputs are selected positions of that convolution. The result above proves that this particular chirped coefficient stream is NOT a fixed-degree univariate g-geometric rational-ratio stream on its actual finite segment: its exact minimum degree grows as d+1. Therefore a fixed-degree q-holonomic selected-coefficient theorem cannot be invoked on that representation while omitting d.

This does not prohibit another basis, multivariate recurrence, higher-order recurrence, a q-base rather than g-base representation, implicit selected convolution, scalar-only norm method, or any unrestricted algorithm. It is not an arithmetic-operation or black-box lower bound. No acquisition bound, collision coverage, native edit or Lean theorem is asserted.

A targeted journal novelty search found older Bluestein/phase identities and q-binomial convolutions, but no statement of this finite-segment minimum rational-ratio degree. This is a limited search, not an exhaustive priority claim.

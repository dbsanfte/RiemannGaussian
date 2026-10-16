# A degree tradeoff for rational compression of the full finite Taylor stream

2026-10-16. Short corollary of the four-shift argument in pade-constant-recurrence.md. This is a finite Taylor-stream representation theorem, not an operation lower bound, selected-value interpolation obstruction, or acquired query algorithm.

Let K be a field, g,q nonzero, and C(X)=sum_(k=0)^L A_k X^k of exact degree L>=1, with A_0=1, satisfying

 g^k(1−q^(k+1))A_(k+1)=(q^L−q^k)A_k for0<=k<L.

Equivalently it satisfies the exact polynomial identity

 C(gX)−C(gqX)=gX[q^L C(X)−C(qX)].                                    (1)

Suppose P,Q in K[X], Q(0)!=0, deg P=u<L, deg Q=v, and

 P/Q−C=O(X^(L+1)) in K[[X]],       ord(q)>L+v.                        (2)

P is nonzero because its quotient has constant coefficient1. Then

 u+3v>=L.                                                           (3)

To prove this, suppose conversely that u+3v+1<=L. Put G=P/Q. Substituting G into (1) leaves a rational residual vanishing to order at least L+1 at0. Clear the four factors Q(gX),Q(gqX),Q(X),Q(qX), whose product has nonzero constant coefficient. The first two residual terms have numerator degree at most u+3v; the X-multiplied terms have degree at most u+3v+1. The entire numerator has degree at most L but vanishes to order at least L+1, so it is identically zero. Hence G satisfies (1) exactly as a rational function.

Write its formal series G=sum b_k X^k. Comparing coefficients gives

 g^k(1−q^(k+1))b_(k+1)=(q^L−q^k)b_k.

The initial b_0=1 and ord(q)>L+v determine its coefficients through L+v. They equal A_k through L, then equal zero from L+1 through L+v: the step k=L has zero right side, and every leading factor through that precision is nonzero. Consequently P−QC vanishes to order at least L+v+1. Its degree is at most L+v, because u<L. Therefore P=QC as polynomials. This contradicts deg P=u<L<=deg(QC). This proves (3), including v=0. No separability, characteristic-zero, differentiation, or factorial-division premise is used.

For the canonical chirped q-binomial stream, d=m²,L=2m²+2, and the paid strong-order setup certifies local q-orders>16m². Thus for v<16m²−L, the order hypothesis in (2) holds in both hidden fields. In particular any attempted rational generating-function compressor of the FULL finite Taylor stream with u,v=O(m polylog m) eventually violates (3). The constant-recurrence theorem is its special shape degP<r,degQ<=r, recovering the exclusion4r<=L.

The required agreement in (2) is at every coefficient through L. This does NOT exclude a rational function agreeing only at m selected evaluation points, a sparse coefficient subset, a multivariate/two-clock state, another transformed stream, or another scalar acquisition method. A high-degree rational function may also have a succinct circuit, which is not priced by (3). The standard rational Padé/denominator-clearing method and coefficient identity are inherited; this supplement records the sharper weighted degree tradeoff, with no literature-priority claim or new algorithm.

The immutable main proof is pade-constant-recurrence.md,7291 bytes,SHA256 d749385717bca05f1cdb1bbe3e432b3571200b07e79902b64491a796739d6937. Its five exact prerequisite pins are in source-pins.json, including the latest paid all-semiprime setup; no further source or primary-paper premise is added here. No native edit, Lean declaration, example or broad build is used.

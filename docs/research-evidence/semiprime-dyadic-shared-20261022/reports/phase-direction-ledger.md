# Quantitative phase-direction folding and its exact nested operation

Let m=2^h, p|m, d=m/p, Y=X^p, zeta_p=X^d, and u=N^-1 mod m. Write B=sum_(k<d,r<p) B_(k+rd) X^(k+rd). For a=pn+sigma define

 C_(sigma,k)(X)=X^(u sigma k) sum_(r<p) B_(k+rd) zeta_p^(u sigma r).

Then, in the ORIGINAL cyclic algebra, exactly

 rho_(u a)B = sum_(k<d) C_(sigma,k)(X) Y^(u k n),
 H_(pn+sigma)=CT_X sum_(k<d) C_(sigma,k)(X) R(X)^sigma
                                      [R(X)^p Y^(uk)]^n.

Thus the stated generating kernel C_(sigma,k) R^sigma/(1-z R^p Y^(uk)) is correct. The omitted terms from r*n have exponent u*m*r*n and legitimately disappear. No carry or denominator is discarded. Restricting to odd a means odd sigma when p>=2.

## The proposed scalar support ledger is quantitatively sound under its input contract

Suppose a branch truly has ONE supplied fixed scalar polynomial direction of degree L=d, a shared norm-kernel prefix with O(min(p,d)) coefficient slots per bounded-width strip, and a constructor costing soft O(min(p,d)*(1+d/p)). Then p branches cost

 soft O(p min(p,d) + d min(p,d)) = soft O(m),

because p<=sqrt(m) gives p^2+m and p>=sqrt(m) gives m+d^2. This arithmetic is correct. The question is the representation and contraction of C_(sigma,k)R^sigma, not this summation.

## Exact phase-coordinate issue

The p Fourier coefficients for one k are Galois conjugates of the polynomial sum_r B_(k+rd) zeta_p^r, with the appropriate primitive-component/order decomposition. They can be STORED as one length-p coefficient list per k, hence O(pd)=O(m) source data. This is useful genuine sharing.

But Y and zeta_p are not independent coordinates. If p<=d, zeta_p=Y^(d/p) already belongs to the base cyclic algebra; if d<=p, Y=zeta_p^(p/d) belongs to the phase algebra. In general X cannot be recovered from these two coordinates: their exponents have gcd(p,d), which is nontrivial at interior dyadic levels. A tensor-product identification with two independent root coordinates would therefore change the source algebra. A correct tower representation must keep X^p=Y and zeta_p=X^d simultaneously, including their common lower-order components.

Moreover conjugating zeta_p by sigma is not a relative automorphism fixing Y in general. The ambient automorphism X->X^sigma sends Y->Y^sigma and R(X)->R(X^sigma), whereas the required numerator contains the POWER R(X)^sigma. These are distinct, and no equality between them is implied by the phase packing. Accordingly conjugating one already-contracted numerator does not automatically produce the other sigma branches.

## What a nested/transposed constructor must actually do

After using the O(m)-size phase storage, the unacquired operation is the simultaneous pairing

 (sigma,n) -> CT_X sum_k X^(u sigma k)
       [sum_r B_(k+rd) zeta_p^(u sigma r)]
       R^sigma (R^p Y^(uk))^n.

It couples Fourier automorphism in sigma, ordinary powers R^sigma, and the k-dependent next-level base. A fixed-direction tangent routine pays ordinary powers against ONE fixed coefficient vector. Its transpose pays polynomial composition into that one base. Neither interface evaluates this coupled phase-power diagonal solely because its INPUT direction has a packed Fourier description.

A particularly useful correctness test is p=m,d=1. The phase data then consists of just one polynomial B(zeta_m) of degree<m; the nominal scalar direction degree is d=1. But n=0 and the requested sigma outputs are

 CT_X B(X^(u sigma)) R(X)^sigma,

which is precisely the original varying diagonal. Thus applying the proposed small-L cost at this endpoint requires a new simultaneous phase-power contraction theorem; scalar degree1 alone has not instantiated its input contract. This is not a lower bound or a disproof of the potential theorem. It pinpoints the exact operation that must be paid instead of being hidden in the phase coefficient representation.

## Positive next algorithm contract

A successful nested primitive would accept the O(m) packed B_(k+rd), the actual cyclic extension relation, and the low-degree rational R; it would return the preceding (sigma,n) pairings with total soft O(m) arithmetic, or supply recursive calls whose TOTAL input/output coefficient size is O(m) per level. Its updates must act on R^sigma and the phase automorphism together. The sparse norm and fixed-direction tangent constructors provide genuine subroutines for its carrier arithmetic, but do not yet implement this phase-power pairing.

I verified the relation and the conditional O(m) ledger, and found the O(m) packed Fourier input representation. I did not derive the required nested pairing or a recursion with bounded total phase-extension rank. No claim that Galois packing is useless, no generic lower bound, and no all-input factoring-rate theorem is made. The remaining operation is explicit enough to test any proposed transposed/tower algorithm without expanding p arrays prematurely or treating a packed phase coefficient as scalar cost.

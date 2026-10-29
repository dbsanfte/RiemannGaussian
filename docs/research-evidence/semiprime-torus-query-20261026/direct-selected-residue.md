# Direct selected singleton residue: truncated Euclid and its zero gate

26 October 2026. Focused paper execution plus one tiny exact symbolic check. This concerns OUR ORIGINAL beta-coupled-bank selected block residue; no identification with another agent's unspecified scalar C is made. It neither proves a general obstruction nor improves the soft K^(5/4) acquisition bound.

## 1. We can choose a different unit amplitude

A correct bin has blocks with zero or one good-field leaf hit. Therefore an acquired pair (V_b,U_b) need only be (0,0) on an empty good block and (A_b,A_b*w_hit) with A_b nonzero on a singleton block. It need not reproduce the Lambert c_I, the full reciprocal product, or its normalization. This permits a direct local-duality/subresultant algorithm rather than evaluation of a full resolvent.

Use actual monic row polynomial D_b(X)=prod_(j in b)(X-T_j) and monic clock polynomial W(X)=prod_(i=0)^(h-1)(X-rho^-i). Form the weighted cofactor polynomial H_b(X)=sum_j w_j prod_(l!=j)(X-T_l), and D_b'(X) similarly. Product-tree differentiation acquires D_b,H_b,D_b' for ALL blocks in soft K, even with repeated roots. At a singleton good hit theta, D_b'(theta) is nonzero and H_b(theta)/D_b'(theta)=w_hit. This uses no tag interpolation or separated-root hypothesis away from the hit.

Thus a concrete alternative sufficient readout is an EMPTY-GATED projective first subresultant giving the common root theta, followed by this short cofactor ratio. This is prior gcd/subresultant locator machinery with the singleton promise applied; it is not new scalar-acquisition credit.

## 2. Execute the truncated-Euclid candidate

Let W=Q_b D_b+R_b, deg R_b<deg D_b. Guarded fast Euclid on (D_b,R_b) determines the intersection gate and its first subresultant together from only O(deg D_b) input coefficients. Once these remainders are supplied, the gate is not a second independent missing input. All blocks together then have soft-K polynomial input size. A degree-one common factor gives theta; evaluate H_b,D_b' there and norm-test the denominator. Any denominator nonzero at the good field is either globally invertible or gives a proper norm factor, so that inversion is legal on its certified branch.

The important missing initialization is the actual remainder R_b. Matching the leading h-d coefficients of W to a quotient does not determine its low-degree error for free. Ordinary remainder trees require W mod product_b D_b, or another procedure supplying these selected remainders/projective subresultants. The inherited implicit q-factorial engine acquires this input in soft(K+sqrt(Kh))=soft K^(5/4). A constant-rank jet does not alter that bill. Existing fast coefficient-Cauchy actions initialize linear q-binomial functionals; they do not yet supply these nonlinear subresultant gates.

Moreover a root locator is not enough on EMPTY blocks. One must either certify the intersection nonempty, or output a denominator that vanishes on an empty good block. Trying to use a nonzero Euclidean coefficient as the denominator fails that condition. In a composite ring, a cleared singular subresultant identity with a specialized zero denominator is not automatically a usable projective ratio. A regular pivot's nonunit branches may factor, but a saturated pivot cannot simply be inverted. These are branch conditions of this candidate, not claims that all direct residue algorithms need the whole remainder.

## 3. Small exact symbolic execution, including an empty-block gate

Take the clock W=(X-1)(X-r)(X-r²), and a two-row D=(X-t)(X-s). Put u=t+s,v=ts, E1=1+r+r²,E2=r+r²+r³,E3=r³. Direct reduction gives

 R(X)=A X+B,
 A=u²-v-E1*u+E2,   B=-u*v+E1*v-E3.                 (1)

At a hit t=1,

 A=(s-r)(s-r²),   B=-A,   R=A(X-1).                (2)

So one root locator coefficient really does suffice projectively when support is certified and the other row is not a clock root. The same A does NOT certify support. The exact resultant gate is

 Res(D,R)=B²+u*A*B+v*A².                           (3)

It vanishes in (2), but for the exact empty example r=2,t=6,s=7 one gets A=50,B=-260 and gate=3600. A is nonzero despite no clock hit. This is a symbolic-interface check, NOT an attained native bank counterexample and NOT a general no-go theorem.

The scratch checker [check_selected_euclid.py](check_selected_euclid.py) verifies (2) as a polynomial identity in Z[r,s] using sparse coefficient dictionaries, and verifies the empty diagnostic by integer arithmetic. Output: [selected-euclid-check.json](selected-euclid-check.json). It does not use a factoring backend or prepared-group oracle.

## 4. Direct conclusion and constructive handoff

The singleton promise genuinely reduces local pole precision and permits arbitrary nonzero amplitudes. It also lets a supplied first subresultant replace a full resolvent or all row products. What it does NOT initialize in this attempted algorithm is the short Euclidean ERROR R_b or an empty-gated selected subresultant directly from the implicit clock polynomial. Supplying just a regular Padé polynomial part omits that error; this specific mismatch is already documented, and is not elevated to a general bound here.

A useful next algorithm target is simultaneous projective first subresultants WITH the zero-intersection gate for the O(sqrt K) acquired D_b, total degree K, against the finite q-clock. It can output only the two short weighted cofactor functionals; emitting all R_b is optional. Such an algorithm would bolt directly onto the existing validator and HH consumer. The present execution gives no soft-K supplier for those gated outputs. The completed algorithm remains the joint q-factorial/first-jet baseline at K^(5/4), not an unjustified O(sqrt K) repetition of a per-block engine.

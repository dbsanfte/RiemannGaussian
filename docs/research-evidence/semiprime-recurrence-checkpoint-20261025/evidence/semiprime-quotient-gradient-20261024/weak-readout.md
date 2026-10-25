# A finite rank-one weak readout and its initialized reset state

24 October 2026. Scratch only. The concrete candidate tested here is a UNIT-regularized Bezout solve, rather than acquisition of exact gradients. Its finite rank-one determinant certificate admits errors equal to the scalar resultant. There is an actual three-state implementation with the supplied start (lambda0,1,1); it computes the weak pair without outputting the scalar product or either exact gradient. The implemented cost is still soft(J+sqrt(JL)), not soft k. The regularized structured-solve shortcut is examined below with its actual input generator and hypotheses; it does not yet reduce that cost.

## 1. Acquired labels and the precise weaker contract

Use the prepared canonical minus F(X)=prod_j(X-V_j), of degree J~k, with retained original integer tags j in [1,k), and q with all differences through 16H guarded, H=k², L=3H+2. The roots and their differences are units in the actual quadratic algebra B. On the good smaller-nonsplit orientation, exactly one row and one grid point x_I=q^I collide; no such promise is imported on wrong orientations.

Acquire the polynomial w of degree <J such that w(V_j)=j. This costs soft J: acquire F'(V_j), invert those ACTUAL unit values, and build

    w(X)=sum_j [j/F'(V_j)] prod_(a!=j)(X-V_a)

by the weighted product tree. This is actual coefficient acquisition, not hidden local interpolation. For J=1 use the original one-row locator; assume J>=2 below. The old tag directions H_1=-F' and H_j=-sum_j j prod_(a!=j)(X-V_a) are separately credited to native-orbit-blocks.md. Here w is the normalized interpolation polynomial, not either of those directions.

The required output is ANY pair (A,B0) with A nonzero at the good unknown field and B0/A=j* there, or a verified proper factor. It can differ from a particular cofactor by multiples of the scalar resultant or by a common unit scale. The tag consumer remains the previously proved one: classify A, form the ratio on a unit branch, use its tau-coordinate gcd to obtain a proper factor or a global base scalar, locate a tag in [1,k) by a soft sqrt k integer-block query, and query that ONE stored original interval in soft sqrt L. Wrong orientations have bounded verified failure, not a free recognized promise. No inverse-gradient-to-product identity is asserted for this weaker projective interface.

## 2. The finite rank-one certificate on the collision hypersurface

Write G(X)=prod_(i<L)(X-q^i), h=G mod F, and let K be the symmetric Bezout matrix

    K(X,Y)=[F(X)h(Y)-F(Y)h(X)]/(X-Y).

The variables h and K in this section define the certificate; they are NOT asserted acquired by definition. Put sigma=(-1)^[J(J-1)/2] and e0=(1,0,...). The already proved Vandermonde diagonalization gives detK=sigma prod_j G(V_j). At the good field its kernel is spanned by

    v*=(1,V_j*,...,V_j*^(J-1))^t,
    adjK=c v* v*^t,  c!=0.

Here corank is exactly one, since all other G(V_j) and the discriminants are nonzero. With w_coeff the actual coefficient column of w, define

    A_det=det(K+e0 e0^t),
    B_det=det(K+e0 w_coeff^t).                       (1)

Multilinearity of a determinant in a rank-one update proves the UNIVERSAL identities

    A_det=detK+e0^t adjK e0,
    B_det=detK+w_coeff^t adjK e0.                    (2)

No inverse, expansion in a finite nonzero deformation parameter, or analytic limit is used. At detK=0 in the good field, A_det=c!=0 and B_det=j*c. These are finite weak readouts differing from the corresponding adjugate statistics by detK. Their values are NOT exact gradients of the original resultant. The two updated matrices are not assumed to be Bezoutians of an arbitrary monic perturbation of G.

There is a useful equivalent UNIT-solve target. For M=K+e0 e0^t, we have Mv*=e0, so over the good field

    M^-1 e0=v*,  w_coeff^t M^-1 e0=j*.              (3)

The determinant is nonzero there. Thus, if its actual norm is acquired, it gives a proper factor or a global unit, never saturation on that promised field. On the unit branch a solve of Mz=e0 returns a weak scalar tag w_coeff^t z, with common denominator normalization removed. This is a fully specified candidate interface; neither the determinant nor a black-box solve is supplied free. A final unit determinant also does not certify every particular leading pivot in a fast elimination trace.

## 3. Execute (1) without acquiring h: three states, all starts paid

The root supplied the complementary-grid realization of the rank-one updates. Let lambda_i=1/G'(q^i), and define

    P_n=prod_(r<n)F(q^r),
    Z_n=lambda_n P_n,
    H_w,n=sum_(i<n) lambda_i w(q^i) prod_(r<n,r!=i)F(q^r),
    H_0,n=sum_(i<n) lambda_i prod_(r<n,r!=i)F(q^r).

The same residue-at-infinity identity as in cofactor-contraction.md holds for ANY polynomial w of degree <J, by linearity or by residues of w(X)/(F(X)G(X)). It yields, for the public common unit d=sigma(-1)^(JL),

    A_det=d(P_L-H_0,L),
    B_det=d(P_L-H_w,L).                             (4)

In particular the common sign can be omitted. This is an algebraic identity through hits; it authorizes no inverse of F(q^i).

Now set A_n=P_n-H_0,n and B_n=P_n-H_w,n. Their actual initialized state and step are

    (Z_0,A_0,B_0)=(lambda0,1,1),
    Z_next=rho(x)F(x) Z,
    A_next=F(x) A-Z,
    B_next=F(x) B-w(x) Z,  x=q^n,                   (5)

where

    lambda0=(q;q)_(L-1)^-1,
    rho(x)=q(1-q^(1-L)x)/(1-qx).

Acquire lambda0 and the total denominator (q;q)_L by the existing soft sqrt L prefix routine. All their factors are actual guarded units. Extend lambda_L=0; the final ratio has a zero numerator and unit denominator. The terminal first state is therefore known zero, while A_L,B_L remain the two requested weak values. Equation (5) directly computes them; it does not output P_L, h, K, or the exact adjugate statistics separately.

There is also a direct projective correctness proof. Before the unique hit I, Z_I is nonzero at the good field, because lambda_I and every prior F value are units there. The hit step F(q^I)=0 resets

    (A_(I+1),B_(I+1))=-Z_I (1,w(q^I))=-Z_I(1,j*).

It also sets Z_(I+1)=0. Every remaining nonhit step multiplies A and B by the same unit F(q^n), preserving that tag ratio and its nonzero denominator. This is an executable reset-and-rescale statement, not an instruction to recognize I or divide by an evolving zero. At wrong zero patterns the global polynomial recurrence still produces its actual defined outputs and the existing bounded validator may decline.

Clearing only b(x)=1-qx gives the polynomial transition

    [[a(x)F(x),0,0],
     [-b(x), b(x)F(x),0],
     [-b(x)w(x),0,b(x)F(x)]],
    a(x)=q-q^(2-L)x.

Its degree is J+1, including the known degree-<J w. Build the actual degree-(J+1)b baby product, acquire all L/b giant starts and entry values by monic MPE, process the clipped tail, and divide by the acquired global unit (q;q)_L. Complete work is

    soft(J+(J+1)b+L/b+sqrt L),
    hence soft(J+sqrt(JL)) for b near sqrt(L/J).     (6)

The final weak-pair validation costs soft k and preserves original row/index witnesses. Thus (5) is an actual complete weak-readout algorithm at the retained k^(3/2) clock. Its being a linear recombination of the old weighted states is explicitly acknowledged; it is not advertised as a new faster recurrence evaluator.

## 4. Test the regularized structured-solve shortcut on actual input

The hoped improvement was to exploit (3), since M is invertible at the good field even when the original resultant vanishes. Its actual compact input can be specified, rather than charging J² matrix entries. For the lower nilpotent shift S, the cyclic shift Z=S+e0 e_last^t, and f=(f0,...,f_(J-1))^t, coefficient comparison gives

    S K-K S^t=f h_coeff^t-h_coeff f^t,
    K e_last=h_coeff.

Therefore, including the rank-one regularization,

    S M-M Z^t
      =f h_coeff^t-h_coeff(f+e0)^t
                               +e1 e0^t-e0 e1^t.   (7)

This rank-at-most-four Sylvester generator is EXACT, including its cyclic boundary. Its operator is invertible: S is nilpotent and Z^t is invertible, so its inverse is a finite sum, not an unknown spectral-separation oracle. If h is actually acquired, (7) and its standard shift-generator conversions are softly linear-sized input. Their small displacement rank does not acquire h.

Primary contract checked: Bostan, Jeannerod and Schost, *Solving structured linear systems with large displacement rank*, TCS 407 (2008), 155–181, Theorem 1:
https://mathexp.eu/bostan/publications/BoJeSc08.pdf
https://doi.org/10.1016/j.tcs.2008.05.014

The theorem takes a SUPPLIED generator for a specific Toeplitz-like Stein operator over a field, and a supplied right-hand side. Its bound is O(alpha^(omega-1) M(J) log²J); its algorithm is probabilistic of type P(3J-2,J²+J). Equation (7) is a complete actual generator description for our related cyclic Sylvester operator once h is supplied; conversion and extra boundary data must still be acquired before invoking a theorem in its exact operator form. The paper is not a deterministic arbitrary-composite-ring theorem, and a locally unit final determinant does not automatically prove its randomized preconditioner or pivot conditions globally. These are retained contracts, not a claim that structured solving cannot be adapted.

The actual G modF input, or its full J native values followed by interpolation, currently costs soft(J+sqrt(JL)). Acquiring it and then solving a short regularized system is thus a lawful retained-cost route, not a soft-k construction. The direct state execution (5) avoids acquiring it entirely, so this observation is not being mistaken for an unavoidable input lower bound. What remains unacquired for this attempted shortcut is a deterministic zero-safe UNIT-regularized solve from F and the implicit geometric G, or another projective weak-pair evaluator faster than (6).

## Scope and exact source pins

This pass supplies a finite rank-one certificate modulo the scalar resultant, an equivalent normalized unit-solve target, and an initialized three-state weak readout with a complete reset proof and retained-cost execution. It does not turn an implicit generator into a paid one, divide through a collision, assume the unknown field, or infer a general lower bound. The original covered query remains the final fallback on unpromised labels, and the QRH orientation palette stays conditional. No improved whole-query or factoring exponent is claimed.

Inherited sources: unique-gcd.md 8eba0f3676ef0de414f4b48fa463a54058aed4fed97db3a0557be0189ec8c862; cofactor-contraction.md e4100f7c507a1f3a894b9c9285425b942f086f0080e3f2ef51bd2b0aa7838ee0; native-orbit-blocks.md a6ab972dd085669e3c322a5031597fd441821d43945b4fee62e97b3f2a818e15. These supply the previously proved corank-one, residue, unit-start and actual tag-consumer contracts. No frozen file was edited.

Cached primary sources/BoJeSc08.pdf SHA256 7a76e996fd9186c0d375ddf12c60eaf9b1f9ff43ba0915c7876ebb9754f2b5ee, copied unchanged from the earlier paired-contraction packet and reread for the exact theorem hypotheses above.

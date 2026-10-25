# Initialized geometric-moment Toda recurrence and its terminal norm

24 October 2026. Scratch only; no repository edits, numerical examples or backend work. The attempted scalar recurrence is executed through the next nontrivial condensation and an exact q-contiguous moment update. Two normalizations are tested. The resulting norm recurrence retains an explicit additive mixed-minor norm, and the full-support Toda boundary removes the unknown amplitude rather than computing it. No soft-m terminal evaluator is obtained.

## Prior material and preserved source

Read the actual current files:

| Source | SHA-256 |
|---|---|
| /tmp/semiprime-tensor-norm-20261024/sylvester-elimination.md | f3375df02a067a43230d1f4accddc476bbbe020a64c9145b90757ba5404720c2 |
| /tmp/semiprime-tensor-norm-20261024/geometric-generator.md | 8ff92a623b50d8698b34260ab01216f3d17ad89c26c5a88831561d3602aa581a |
| /tmp/semiprime-character-endpoint-20261024/character-resultant.md | 87c7b82b0bcc516f63d8ff4f1f81f2214f1e8c4e3e23083072470d7c2a672fb1 |

They already acquire compact first Schur data, all q-hook principal constants, first-two auxiliary support cleanup, and the transverse/within-grid transport distinction. None is counted again as a rate gain. The present trial uses the ORIGINAL acquired F and q and keeps original row/index labels for recovery. It does not change the covered family or invoke a hidden field.

For a concrete balanced block take n=J>=3, s=n, t=floor(L/n), L0=nt, and acquire

    A_n(X)=product_(a<n)(X-x_a), x_a=q^a,
    B_t(Y)=product_(b<t)(Y-q^(nb)), K=R[Y]/B_t,
    R=Z/N.

A final seed tail costs soft(J+n). All short q-differences needed below (up to 3n and the actual native horizon) are certified units. Degree-zero and bounded small dimensions can use their direct products. A K operation costs soft t base-ring operations.

## 1. Moment state that actually gives the scalar inner resultant

Let A*(u)=u^n A_n(1/u), and F*(u)=u^n F(1/u), both constant one. Put Z=Y^-1 and

    H(u,Z)=F*(Zu)/A*(u)=sum_(r>=0)c_r(Z)u^r,
    c_0=1.

The coefficient c_r is an acquired formula

    c_r(Z)=sum_(j=0)^min(r,n) f_(n-j)*Z^j*h_(r-j),
    1/A*(u)=sum h_r u^r.

For ONE supplied scalar Z=z, all c_1,...,c_(2n+1) are genuinely acquired in soft n by coefficient scaling and constant-one series division. For the first five moments as polynomials in Z, only the first five F/A coefficients are needed, so their bounded-degree coefficients are acquired with constant extra work after the short inputs. Simultaneously expanding the whole moment vector over rank-t K, however, costs soft nt; its short formula is not free expanded input.

Define actual Hankel minors

    tau_k^(r)(Z)=det(c_(r+i+j)(Z))_(0<=i,j<k), r>=1,
    tau_0^(r)=1.

The partial fractions of the proper part of B_Z(X)/A_n(X), with B_Z(X)=Z^n F(X/Z), give

    c_r(Z)=sum_(a<n) w_a(Z)*x_a^(r-1),
    w_a(Z)=B_Z(x_a)/A_n'(x_a).

All A_n'(x_a) are certified units; weights may vanish. This is a ring identity, not an inversion of any target value. Consequently, with c_x=product_a x_a,

    tau_n^(r)(Y^-1)
      =(-1)^[n(n-1)/2] * c_x^(r-1) *Y^(-n²)
          *product_(a<n)F(q^aY).                    (1)

Indeed the Hankel determinant is the grid Vandermonde square times product w_a, while product A_n'(x_a)=(-1)^[n(n-1)/2] times that square. Thus the desired full scalar block norm is a KNOWN UNIT times N_(K/R)(tau_n^(1)). This establishes the target, sign and normalization exactly, including zeros.

These Hankel minors are the usual signed principal/adjacent subresultant minors. The proof of (1) and the condensation identities below is direct, so no quasi-definite infinite orthogonality theorem is imported.

## 2. An executed Toda step with its additive cross term

Desnanot-Jacobi on the actual Hankel block gives the polynomial identity

    tau_(k+1)^(r)*tau_(k-1)^(r+2)
      =tau_k^(r)*tau_k^(r+2)-(tau_k^(r+1))².         (2)

The two shifted minors on the right are essential. Keeping only principal r=1 pivots does not initialize them.

The first genuinely new step beyond the already-read quadratic/quartic pivot test is k=2,r=1. Acquire c_1,...,c_5 from the exact rational series above. Then

    tau_2^1=c1*c3-c2²,
    tau_2^2=c2*c4-c3²,
    tau_2^3=c3*c5-c4²,
    tau_3^1=c1*c3*c5+2*c2*c3*c4-c1*c4²-c2²*c5-c3³.

All these are actually computed by the displayed bounded-degree polynomial operations, with deg_Z tau_3^1<=9. Direct substitution/expansion proves

    c3*tau_3^1=tau_2^1*tau_2^3-(tau_2^2)².         (3)

In particular a recurrence that omits the square cross term is incorrect. There is NO need to invert c3 to acquire this stage: the explicit determinant polynomial supplies the quotient even if c3 is nonunit. Conversely numerical division by c3 in (3) is not licensed merely by the integral identity.

This executed degree-nine stage is an initialization check, not a new covered early-pivot claim. Its scalar norm over the geometric t-node grid can be acquired by fixed-degree blocking in soft sqrt t, and its values/support can be acquired in soft t. Since its reversed leading coefficient is a q-hook unit, its exceptional global nodes can be handled by at most nine original short slices, just as in the prior first-two cleanup. This is still only a FIXED number of stages; it does not pay all n stages or imply that one of these auxiliary supports contains an original hit.

## 3. First normalization: q-hook units and the exact remaining norm term

At Z=0, c_r=h_r(x_0,...,x_(n-1)). Reversing the k rows in the Hankel determinant gives

    u_k^r=tau_k^r(0)
       =(-1)^[k(k-1)/2] s_((r+k-1)^k)(1,q,...,q^(n-1)).

For k<=n and the finite moment window r+2k-2<=2n+1, every numerator/denominator exponent in the rectangular hook specialization is <=3n. Thus these constants are units. The shared short q-factorial and factorial-prefix arrays acquire an INDIVIDUAL requested rectangle value in soft 1 after soft-n preparation. This does not materialize all O(n²) adjacent constants or minor arrays for free. The principal r=1 all-k boundary is the earlier paid square-Schur sequence.

Let theta_k^r=tau_k^r/u_k^r. For k<n equation (2) becomes exactly

    theta_(k+1)^r*theta_(k-1)^(r+2)
      =alpha_k^r*theta_k^r*theta_k^(r+2)
         -beta_k^r*(theta_k^(r+1))²,                (4)

where alpha=u_k^r*u_k^(r+2)/(u_(k+1)^r*u_(k-1)^(r+2)) and beta=(u_k^(r+1))²/(u_(k+1)^r*u_(k-1)^(r+2)). All these scalar coefficients are paid units, and alpha-beta=1 follows by setting Z=0 in (2). This is the correct q-hook-normalized Toda equation, including its coefficient and additive square.

Now try to propagate ONLY scalar norms over K. Even on a component where all needed denominator minors are certified units, (4) requires the NEW scalar

    W_k^r=N_(K/R)(1-eta_k^r),
    eta_k^r=(beta/alpha)*(theta_k^(r+1))²/
                          (theta_k^r*theta_k^(r+2)). (5)

The other norm factors are multiplicative combinations of already supplied norm data. But norm(1-eta) is NOT 1-norm(eta), and no value of (5) is supplied by knowing the separate minor norms. It is a norm of an actual additive mixed-minor expression at the SAME outer nodes. The newly acquired relation (3) verifies this point at the first nontrivial stage; it does not delete it.

If denominator minors are nonunit, (5) must not be evaluated by inversion. Their actual endpoint zero sets have to be acquired and removed/handled as original slices, or the division-free determinant identity retained. The prior first-two cleanup handles its explicit supports; higher stages have growing mixed polynomials. Constant formal terms and the relation alpha-beta=1 do not certify those endpoint units or acquire their support. No new pivot-to-native-hit decoder is assumed.

## 4. Alternate normalization at the FULL-support boundary loses the amplitude

It might still be hoped that the outer K-norm of (4) telescopes at k=n. The finite measure above has n nodes, so tau_(n+1)^r=0 identically. Moreover (1) gives

    tau_n^r=c_x^(r-1)*tau_n^1,
    theta_n^r=theta_n^1 for every r.

Therefore the full-support Toda boundary is just

    tau_n^r*tau_n^(r+2)-(tau_n^(r+1))²=0.

It is identically zero for EVERY F, whether or not the target has a hit. Where ratios are units, its cross-ratio is identically one; at hits the numerical ratio may be undefined. Either way the unknown amplitude tau_n^1, whose K-norm is the desired scalar, has canceled. This boundary equation cannot be used as a zero/nonzero selector or a normalization that computes that amplitude. For k=n, the would-be constant u_(n+1)^r is zero, so dividing it away to extend (4) would additionally be illegal.

This is a precise failure of the tested boundary-normalized Toda recurrence, not a statement that every scalar determinant algorithm must acquire all minors.

## 5. Actual q-contiguous moment recurrence, paid startup and norm transport

A different normalization uses the geometric A rather than the k direction. Its exact relation is

    A*(q u)=A*(u)*(1-q^n u)/(1-u).

Thus

    (1-q^n u)*H(q u,Z/q)=(1-u)*H(u,Z).

Comparing coefficients gives an ACTUAL initialized short recurrence

    q^r*c_r(Z/q)-q^(n+r-1)*c_(r-1)(Z/q)
       =c_r(Z)-c_(r-1)(Z), c_0=1.                 (6)

Every division needed to transport a supplied moment vector is only by a power of the certified unit q. After the initial soft-n moment acquisition at one scalar Z, the whole length-(2n+O(1)) vector at Z/q is acquired in soft n by the triangular recurrence. A jump Z->Z/q^s can also be done by scaling and a constant-one rational convolution with A*, in soft n per vector. This is not a claim that q-scaling is an algebra homomorphism modulo B_t; it is an identity of the ACTUAL generating family with both variables transformed.

The first q-contiguous determinant update can be executed too, rather than leaving a formal q-Toda suggestion. Put g=q^n, a=g-1. Formula (6) gives

    q*c1'=c1+a,
    q²*c2'=c2+a*c1+a*g,
    q³*c3'=c3+a*c2+a*g*c1+a*g²,

where prime means Z->Z/q. Expanding the ACTUAL quadratic determinant yields

    q^4*tau_2^1(Z/q)=tau_2^1(Z)+a*Omega(Z),
    Omega=c3-c1*c2+c1²+g*c1-(g+1)*c2.              (6a)

All terms are acquired bounded-degree polynomials from the supplied moment startup. In particular Omega has degree at most three, with Z³ coefficient f_(n-3)-f_(n-1)*f_(n-2); no vanishing of that mixed coefficient is assumed. This explicitly retains the additive cross terms caused by the degree-one rational moment filter, including the known c0=1 boundary. The q-hook normalization fixes Omega(0), but does not remove its nonconstant part.

On a certified unit tau_2^1 component, the norm update in (6a) asks for

    q^(-4t)*N_K(1+a*Omega/tau_2^1).

This is again a newly acquired mixed expression, not a product of previously known scalar norms. At this fixed stage its degree is constant, so it IS affordable by the ordinary small-degree norm routine; this does not provide the corresponding all-k scalar contraction. Carrying the compatible moment vector makes every subsequent shift well defined, but its growing determinant/minor observables still have to be computed and normed. Thus the proposed rank-one/degree-one q-boundary is actually tested through a nontrivial scalar determinant step; the unresolved term is Omega and its higher-minor analogues, not a missing first vector or an omitted formal tail.

There is nevertheless no identification of the r shifts in Toda with the Z/q shift in (6): r shifts the moment weight x_a^r; Z changes the actual F input. Equation (6), rather than a guessed equality of adjacent minors, is the compatible transport data. Evaluating it on all t outer points separately costs soft nt, and an expanded K-valued vector has exactly that charge.

At the full inner resultant, (1) yields the simpler division-free relation

    q^(n²)*tau_n^1(qY)*F(Y)
       =tau_n^1(Y)*F(q^nY),                        (7)

where tau_n^1(Y) here abbreviates tau_n^1(Y^-1) in the Y coordinate. This notation is used only in (7) and the norm relation below. Its first scalar startup at Y=1 is genuinely acquired: evaluate F on the n short q nodes and multiply, costing soft n, with no target inversion.

Taking the K-norm in (7) and canceling identical factors as a UNIVERSAL product identity gives

    q^(n²t)*T(1)*F(1)=T(0)*F(q^(nt)),
    T(a)=product_(b<t)tau_n^1(q^(a+nb)).            (8)

This identity is division free even when intermediate factors vanish. Guard F(1),F(q^(nt)) before forming their numerical endpoint quotient: they are actual bounded original-source boundary values, so a nonunit permits original recovery within the retained decoder horizon. Here nt<=L<=2H+2<4H on the native branch; for a shifted restriction the actual endpoint index a0+nt is explicitly retained and checked to satisfy a0+nt<4H. Repeated shifts outside that retained decoder horizon have only the algebraic identity, with no original-leaf recovery promised. If both endpoint values are units, acquire the UNIT multiplier c=q^(-n²t)*F(q^(nt))/F(1), and retain the lawful identity T(1)=c*T(0). A numerical quotient T(1)/T(0) additionally requires T(0) to be a unit; it is not formed in the covered zero/nonunit case.

But T(0), not the SINGLE scalar tau_n^1(1), is the desired outer norm. The cheap unit-multiplier transport (8) does not initialize T(0). Applying it repeatedly preserves the same unknown initial amplitude. Taking outer length zero gives one as a real startup, but extending that length inserts the new inner norm at each outer node; computing those t inner norms separately costs soft nt. Thus the alternate q-contiguous normalization is fully executed and its remaining initialization is exact: the product across the t different moment-vector amplitudes has not been acquired by their cheap transport.

## 6. Paid completion, restrictions and stopping point

A fully initialized inversion-free completion is to acquire each inner slice F(q^(nb+a)), a=0,...,n-1, by monic MPE and multiply. Formula (1) gives its moment determinant if wanted; a direct target-matrix determinant is unnecessary. There are t slices, total soft nt=soft m². Moment transport/fast compatible Hankel evaluation gives no better bound here. The existing global scalar blocked constructor is BETTER and actually acquires the original target in soft(J+sqrt(JL)), with every coefficient and giant start paid.

All original row subsets and seed subintervals are supported by that same constructor. Proper gcds factor; saturated products descend to retained original row/index leaves and use the original bounded beta decoder. Auxiliary Toda/minor zeros do not themselves invoke that decoder. The fixed-degree early support cleanup and the explicitly computed cubic determinant stage may return additional valid adaptive factors, but are not a proved covered substitute for the terminal query.

| Operation | Paid work | Actual output |
|---|---:|---|
| One full moment vector at scalar Z | soft n | 2n+O(1) compatible coefficients |
| Next Toda step (3) | bounded-degree polynomial work | actual tau_3 polynomial, degree<=9 |
| Shared q-hook boundary arrays | soft n | individual adjacent unit constants available |
| All adjacent-minor array, if expanded | not free | O(n²) minor slots, with their data costs |
| q-contiguous vector update/jump (6) | soft n per supplied scalar vector | next compatible moments |
| Norm-only normalized Toda (4) | missing term (5) | fresh additive mixed-minor norm |
| Full-support cross-ratio | identically one on units | terminal amplitude eliminated |
| Outer norm transport (8) | cheap endpoint multiplier | unknown T(0) remains |
| Inversion-free tensor completion | soft nt | original scalar norm |
| Better original blocked completion | soft(J+sqrt(JL)) | covered norm and recovery |

The tested q-Toda route has valid acquired starts, correct additive cross terms and a lawful q-contiguous update. Neither q-hook normalization nor the full-support/q-shift boundary turns its norm into a product of O(m) already acquired scalars. The precise missing quantity is (5), or equivalently the unknown outer amplitude in (8). This is a scoped failure of this executed recurrence and its alternate normalization, not a general scalar-algorithm lower bound. No new whole-query exponent or sixth-rate claim is made.

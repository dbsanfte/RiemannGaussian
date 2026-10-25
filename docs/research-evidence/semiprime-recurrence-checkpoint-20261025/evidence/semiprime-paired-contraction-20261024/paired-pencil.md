# The paired Vandermonde pencil: acquired forcing, diagonal cancellation, and a transverse test

24 October 2026. Scratch only. This executes the source pencil after BOTH native Vandermonde maps. Its two forcing generators are acquired in the desired soft(H+D+K) budget, but they cancel exactly on the requested diagonal. A first transverse derivative and an acquired Cauchy factorization are then tested; neither yet supplies the diagonal amplitudes or their product. The completed safe algorithm retained below costs soft(sqrt(Kb)+K), the existing query clock, not soft(H+D+K). These conclusions concern the executed representations, not all scalar algorithms.

## Actual input and source pin

Use `/tmp/semiprime-implicit-thin-encoding-20261024/all-mask-sharing.md`, SHA256 `5f79d577ff7fddf72a6e3670d5bca3b7ff2ef72557f137553d388b9fea9c0f31`, independently reviewed at SHA256 `131aa98fb6f09ce933d20dddb35045ab5ac3b555e233fabcb15f43413d6eaa02`. Its acquired q-binomial matrix, boundary and linear actions are inputs; this report does not count their reproof as a terminal gain.

Work over R=Z/N or its fixed-rank quadratic algebra B. The actual native q is a unit, and 1-q^r for1<=r<=C=16k² are certified units. Set b=L=2k²+2, choose1<=D<=b and H=ceil((b+1)/D), with H,D of order sqrt b in the substantive branch. Bounded dimensions use direct arithmetic. In particular b+D<=2L<C. There are K=Theta(k) actual unit target arguments y_j, with their original row labels; for the full source one may take y_j=V_j^(-1). Existing factor-or-target separation can be used, but no new separation of y_j^D, no q-orbit labels for y_j, and no unit assumptions on1-y_j are imported.

Put

    P(Y)=product_(i=0)^(b-1)(1-q^iY)=sum_(n=0)^b c_nY^n,
    C[rho,r]=c_(D*rho+r), with coefficients beyond b set to zero,
    U=diag(q^(D*rho)), V=diag(q^r),
    A0=S-q^bI, B0=(qS-I)V.

S is the D-by-D lower shift. The independently verified pencil is

    C A0-U C B0=g e_(D-1)^t,
    g_rho=c_(D*rho+D-1)*(q^(D*rho+D-1)-q^b).       (1)

The acquired prefix lemma supplies all needed c_(D*rho), and every actual coefficient in a last partial row, in soft(sqrt b+H+D). All integer exponents have O(log N) bits. q-inverse is a certified unit inverse; no terminal value is inverted below.

## 1. Transform the pencil and acquire its actual generators

Define

    a(X)=sum_(rho=0)^(H-1) gamma_rho X^rho,
    gamma_rho=c_(D*rho), gamma_H=0.

The adjacent coefficient recurrence gives the EXACT boundary identity

    g_rho=(q^[D(rho+1)]-1)*gamma_(rho+1),
    a(X)-a(q^D X)=-X g(X), g(X)=sum_rho g_rho X^rho.      (2)

This includes the final row: its source boundary is zero, whether its last column is padded or its last coefficient is c_b. Thus g has degree at most H-2. It is acquired from the same actual gamma vector in soft H, not from a length-b coefficient expansion.

Let

    G(X,Y)=sum_(rho,r) c_(D*rho+r) X^rho Y^r,
    M_ij=G(y_i^D,y_j),
    Mplus_ij=G((qy_i)^D,qy_j),
    d_i=a(y_i^D)-a(q^D y_i^D).

The requested values are M_jj=P(y_j). The two native Vandermonde matrices are implicit evaluation maps; their full K*H or K*D arrays are NOT constructed. Acquire y_i^D by actual binary powers, then a at all y_i^D and q^D y_i^D by monic MPE. This acquires every d_i in soft(H+K), after the paid gamma constants. Repetitions or nonunits among the native-node DIFFERENCES cause no exception for that monic evaluation. Right vectors1,y_j^D are acquired in soft K.

Directly applying (1) gives the complete transformed displacement

    (1-q^b y_j) M_ij-(1-y_j) Mplus_ij
       =d_i*[1-y_j^D/y_i^D].                     (3)

The division here is only by the supplied unit y_i^D. Hence the right side is a sum of TWO acquired outer products, with all coefficients and starts paid in soft(sqrt b+H+D+K). This is an actual transformed-generator acquisition, not a dimension count.

For an independent sign check, polynomial coefficient comparison in (1) gives

    (1-q^bY)G(X,Y)-(1-Y)G(q^D X,qY)
       =(Y^D-X)g(X).                             (4)

Substitute X=y_i^D,Y=y_j and use (2) to get (3). Thus there is no unaccounted companion-row boundary or dropped last coefficient in (3).

## 2. What happens on the desired diagonal

Set i=j in (3). Its right side is identically zero, BEFORE any reduction modulo a hidden prime. The acquired relation is exactly

    (1-q^b y_j)P(y_j)=(1-y_j)P(qy_j).             (5)

It is the true shifted-window identity and remains valid at zero values or nonunit endpoints. It does not acquire either amplitude. If the actual endpoint factors are units, they acquire a unit multiplier between the two amplitudes; they do not license calling an undefined quotient P(qy)/P(y) a value when P(y) is nonunit.

No new point is made free by (5). In particular the input does not provide an index h with qy_j=y_h, or a known endpoint value on the q-orbit of y_j. Finding that y_j is q^(-i) in the original interval is itself the native collision problem. The formal coefficient start P(0)=1 is known, but zero is not reached by q-shifting a unit argument. The scalar merge is mathematically closed without giving the algorithm a cheap native starting value.

Endpoint tests may be performed only at actual retained indices with their own valid consumer. This report simply keeps (3)--(5) division-free. It does not screen an unbounded orbit, divide after a hit, or discard a zero endpoint to invent an amplitude.

## 3. Execute a transverse derivative rather than stop at zero forcing

Move normally to the diagonal X=Y^D by X=Y^D+delta. Define the ACTUAL coefficient polynomials

    G(Y^D+delta,Y)=sum_(n>=0) delta^n J_n(Y),
    J_0(Y)=P(Y).

The q-shift in (4) sends delta to q^D delta. Its first transverse equation is therefore

    (1-q^bY)J_1(Y)-q^D(1-Y)J_1(qY)=-g(Y^D).       (6)

Its forcing polynomial is acquired compactly from g, and its value at every supplied y_j costs soft(H+K) by one monic MPE at y_j^D. The initial constant J_1(0)=c_D is also actually acquired. This is a genuine initialized inhomogeneous equation, not a merely formal normal derivative.

Its coefficients expose what it computes. For m>=0,

    [Y^m]J_1(Y)=(floor(m/D)+1)*c_(D+m),             (7)

with the ordinary coefficient zero convention beyond b. Writing j_m=[Y^m]J_1, equation (6) becomes

    (1-q^(D+m))*j_m+(q^(D+m-1)-q^b)*j_(m-1)
       =-[Y^m]g(Y^D), j_(-1)=0.                  (8)

All denominators for forward use of (8), D+m<=b, are certified units. Thus it really can acquire the entire polynomial in O(b) coefficient steps; its start and forcing are not missing. However J_1 has EXACT degree b-D: its leading coefficient is floor(b/D)*c_b, a unit since floor(b/D)<C<P,Q and c_b is a known unit. The equation does not already evaluate J_1 at all native y_j in soft(H+D+K), and even those derivative values would need an additional relation to recover P(y_j).

In terms of the source matrix, J_1 is the paired evaluation of the SAME C with its row rho multiplied by rho and with an explicit unit monomial shift. A fast C action for one vector still does not acquire those paired moving-vector values. We have not found an algebraic step eliminating J_1 into known g-values and P(0). No claim is made that its high degree rules out another scalar algorithm; (7)--(8) are the exact retained state of this tested derivative route.

Higher normal coefficients similarly satisfy

    (1-q^bY)J_n(Y)-q^(Dn)(1-Y)J_n(qY)
       =-g^[n-1](Y^D), n>=1,

where g^[n-1] is the Hasse derivative. Only the first actual equation (6) was needed for this attempt; a whole normal-jet array is not treated as a free constant-size state.

## 4. Acquire the Cauchy factorization with the CORRECT basis order

Root supplied a sharper factorization, independently checked here as an alternative paired-input representation. Let W0 be lower triangular Toeplitz with coefficient sequence

    h_0=1,
    h_t=q^(-bt)*(q^(b+1);q)_t/(q;q)_t,
    h_t/h_(t-1)=q^(-b)*(1-q^(b+t))/(1-q^t).       (9)

All h through D-1 are acquired with actual O(D) short ratios. Their denominators are certified units; the broader native b+D<=2L<C also certifies the displayed numerator differences, though these are never inverted. These are constants, not native target values.

With Lambda=diag(q^(b-s)), the generalized eigenvector identity is

    A0 W0=B0 W0 Lambda.

Indeed in column s and row s+t the recurrence is exactly (9). Consequently it is

    E=B0 W0,

not W0 alone, that gives

    (C E)Lambda-U(C E)=g*(e_(D-1)^t W0).          (10)

The order of B0 and W0 matters: W0 diagonalizes B0^(-1)A0, not A0 B0^(-1). B0 is invertible lower bidiagonal and W0 has diagonal one. Their actions/inverses have acquired fixed descriptions of O(D) size, with no arbitrary matrix inversion.

There is one possible row/pole overlap q^(D*rho)=q^(b-s), exactly at D*rho+s=b. Remove the LAST coefficient row explicitly, partial or full. Its at-most-D actual coefficients are acquired by the prefix lemma; its contribution to ALL K diagonals is y_j^[D(H-1)] times its degree<D row polynomial at y_j. Monic MPE and actual powers acquire this in soft(sqrt b+D+K).

For the remaining rows rho<=H-2, every cross difference is

    lambda_s-U_rho=q^(D*rho)*(q^[b-s-D*rho]-1),

with1<=b-s-D*rho<=b, hence a certified unit. The row/pole arrays and their pair differences need no hidden-field choices. Equation (10) therefore gives the exact acquired factorization

    Cminus*E=diag(gminus)*Kc*diag(nu),
    Kc[rho,s]=1/(lambda_s-U_rho),
    nu_s=h_(D-1-s).                               (11)

All generators, nodes, unit inverses and basis constants are paid in soft(sqrt b+H+D). The Cauchy matrix is supplied by these actual nodes/generators, not by an expanded H*D table. No target-node separation beyond the original contract is needed for the generator statements.

### The transformed right native vector, with no hidden endpoint denominator

One can make E^(-1)*v(y) completely explicit without expanding D² basis coefficients. B0^(-1) acts on the geometric v(y)=(1,y,...,y^(D-1)) by

    (B0^(-1)v(y))_r=-sum_(ell=0)^r(y/q)^ell.

There is NO division by1-y/q, which may be nonunit. The actually acquired coefficients satisfy the formal TRUNCATED identity

    sum_(0<=t<D)h_t Z^t
       =1/product_(i=-b)^0(1-q^i Z) mod Z^D.

No coefficient h_t with t>=D is acquired by a long q-difference denominator. If a further formal extension is desired, define it by the constant-one reciprocal product, not by an inverse of1-q^t beyond the guards. Thus for the first D coefficients alpha_t of W0^(-1)/(1-Z),

    sum_(0<=t<D)alpha_t Z^t=P_b(q^(-b)Z) mod Z^D,
    alpha_t=q^(-bt)*c_t for0<=t<D.               (12)

Only these first D coefficients are needed and acquired in O(D) guarded q-binomial ratios. Constant-one formal inversion/cancellation in (12) is valid independently of any native endpoint y/q; the full degree-b polynomial on the right is not being expanded.

The actual s-th right coordinate after E^(-1) is

    R_s(y)=-sum_(ell=0)^s alpha_(s-ell)*(y/q)^ell. (13)

This is a shared, acquired nested-polynomial description. It is not the incorrect formula using coefficients of W0^(-1) without the prefix1/(1-Z). All K full transformed vectors could be acquired by K fixed-basis actions, costing soft(KD). Retaining the nested description avoids that expansion, but does not itself contract it with each target's different left powers.

Combining (11)--(13), the unknown portion of a requested diagonal is exactly

    sum_(rho<H-1) sum_(s<D)
       y_j^(D*rho)*g_rho
        *nu_s*R_s(y_j)/(lambda_s-U_rho),           (14)

plus the already acquired last-row contribution. Every coefficient/generator in (14) is now actual short data. It is a precise paired Cauchy--Vandermonde/nested-polynomial contraction, not an unknown matrix input. We have not acquired ALL its K values in soft(H+D+K). Applying the Cauchy operator separately to each acquired right vector still costs soft(K(H+D)).

Taking an ordinary determinant of a square transformed matrix is a different scalar objective: even for two targets, the product of its diagonal equals its determinant PLUS M_12*M_21. The off-diagonal cycle term has not been removed by (10). No Cauchy determinant formula is used as if it were the product of the paired diagonal values.

## 5. A completed zero-safe continuation and its actual cost

For comparison keep the ORIGINAL unit native y_j and choose an actual seed-block length a. Acquire

    P_a(Y)=product_(i<a)(1-q^iY)

by a monic/product-tree implementation, cost soft a. Write b=ra+d,0<=d<a. Acquire EVERY labelled argument y_j*q^(ag),0<=g<r, by actual power walks, and evaluate the ONE P_a by monic MPE at these K*r points. Its literal shorter tail is treated at q^(ar)y_j. Every output is then multiplied only within its actual target j, giving P_b(y_j) exactly. Total cost is

    soft(K+a+Kb/a),

optimized at a~sqrt(Kb), clipped to[1,b], yielding soft(K+sqrt(Kb)). At b~k²,K~k this is the existing soft k^1.5 clock. The short polynomial and mixed point list, not just their root/index descriptions, are charged.

The product-only variant is also safe at this clock. Scan the actual scalar norms of block values. A proper gcd factors. A saturated block retains j,g and is descended in the acquired short seed product tree, returning a proper factor or the ORIGINAL index ag+i. The sum of degrees on one descent is O(a). A saturated ORIGINAL NORM leaf does not assert whole split-side equality: invoke the predecessor's nonsplit-field/G_beta consumer, which yields a factor or a saturated original scalar beta leaf with the bounded decoder. Original row restrictions and interval offsets retain their actual labels; the tail has no overhang. No scalar endpoint or nonunit determinant is divided out.

## Ledger and scoped outcome

| Acquired object/operation | Paid work, fixed-rank arithmetic and bit logs included | What it supplies |
|---|---:|---|
| gamma row starts, g, q-grid pencil data | soft(sqrt b+H+D) | actual short source generators |
| Paired transformed forcing vectors in (3) | soft(sqrt b+H+D+K) | every needed rank-two RHS constant |
| Desired diagonal recurrence | soft K after above | EXACT zero forcing; no acquired amplitude |
| First transverse forcing and constant c_D | soft(sqrt b+H+K) | actual inhomogeneous equation, degree-b-D state not evaluated for free |
| Cauchy basis, nodes, generators and removed final row | soft(sqrt b+H+D+K) | exact short-data factorization and known row contribution |
| ALL K explicit right vectors or separate paired actions | soft(K(H+D)) | a valid but overbudget continuation |
| Completed original block evaluation/product and recovery | soft(K+sqrt(Kb)) | every original value or factor/witness controller |
| Simultaneous contraction (14) below that clock | NOT acquired here | precise next terminal operation |

The transformed pencil is genuinely useful short-data structure, and the correct Cauchy basis is actually initialized. Its forcing disappears on the diagonal, while the first nontrivial normal equation retains the stated weighted coefficient polynomial. No completed whole-query improvement has followed from these representations. A new simultaneous paired contraction, using the actual native arguments and original restriction consumer, is still required; this is not a generic impossibility claim.

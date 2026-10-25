# Actual native mixed traces: centered Dickson sharing and an executed Jacobi update

24 October 2026. Scratch only. The original covered scalar source and decoder are retained. This attempt obtains an exact two-stream sharing identity for the actual mixed traces, with acquired square-root seed and division-free endpoint handling. It executes a normalized Jacobi/Adams update, including its next mixed term. Neither construction acquires the whole long query in soft k. The remaining term below is specific to this attempted recurrence, not a lower bound for other scalar algorithms.

## Inputs, pins, and credit

Read `/tmp/semiprime-native-character-20261024/character-acquisition.md`, SHA256 `83bd40ae27d975320566827bba50ae73d63464218d2993bfc5b226e60e7749a7`, and its companion `character-literature.md`, SHA256 `24ec2dd1529a9c36070df12e880347c21c8841e7367eaa711c0bd7cfcf601c02`. Read the integrated journal heading beginning line 40097 in `/home/dbsanfte/riemann/formal/docs/semiprime-factorisation-investigation.md`, read-version SHA256 `86292c9871ff0c4e2242b830d7cb7bfbb046f66635a4cd9f9254c652edcafb53`.

The public prime ell is chosen first, k=ell-1 is even, H=k², and all tags are units modulo k. Native a_j,b_j,ell_j,E_j and all original scalar beta guards are as in those sources. Let A=(Z/N)[X]/(X^k-1); one expanded A operation costs soft k base-ring work. A bar means rho_-1. The full corrected Gauss product is D=e0+ell*X^(k/2)*(1-e0), a certified unit fixed by every unit automorphism. With u=g_1, U=u^k, the acquired rows satisfy

    R_j=D^(-E_j/2)*T_j, q=D^(-H/2)*u^H,
    R_j*bar(R_j)=q*bar(q)=1,
    R_j*R_-j=q^tau_j, tau_j in {-2,-1,0}.

One actual R_j costs soft k; all explicit rows currently cost soft(k*|G|). Pair products, the globally zero augmentation, one-vector primitive norm, and the original-beta paired-hit bridge are prior results. In particular a raw primitive-norm saturation is not an original beta leaf. The old complete scalar query costs soft(J+sqrt(JL)), J<=|G|<=k and L=2k²+2. None of the following replaces that guaranteed interface.

## 1. An acquired center gives an exact TWO-stream query

Set

    W=D^(-k/2)*U, v=W^(k/2).

Then W, v are acquired in soft k, have bar-norm one, and v²=q. This is an integer-power construction, not extraction of a square root in A. Choose one representative per antipodal pair (k>2; the bounded k=2 case is direct), and define

    X_j=v^(-tau_j)*R_j,
    x_j=X_j+X_j^(-1), theta=v+v^(-1).

The antipodal partner is exactly X_-j=X_j^(-1). Therefore x_j is the actual centered pair trace and the old uncentered S_j equals v^tau_j*x_j. All inverses here are supplied by bar, or by explicit certified Gauss units. The descriptors v^(-tau) cost soft k for the three tau values; applying them to all expanded rows still costs soft(k*J).

Let D_n(T) denote the Dickson trace polynomial, D_0=2, D_1=T, D_(n+1)=T*D_n-D_(n-1). For the supplied v,

    d_n=D_n(theta)=v^n+v^(-n).

At the ORIGINAL index i, z=q^i=v^(2i), the actual pair difference is exactly

    (R_j-z)*(R_-j-z)
      =z*v^tau_j * [d_(2i-tau_j)-x_j].             (1)

The prefactor is a certified unit. This equality is valid at zeros and over the composite ring without cancellation. It retains the original bounded i label; the Dickson degree is an auxiliary label, not a new collision index or order certificate.

The three tau values thus give only an even stream and an odd stream:

    tau=0:  d_0,d_2,...,d_(2L-2),
    tau=-2: d_2,d_4,...,d_(2L),
    tau=-1: d_1,d_3,...,d_(2L-1).

The actual initial values and recurrence for these streams are acquired:

    c=theta²-2=q+q^(-1),
    d_(2i+2)=c*d_(2i)-d_(2i-2),
    d_(2i+3)=c*d_(2i+1)-d_(2i-1),
    (d_0,d_2)=(2,c), (d_1,d_3)=(theta,theta³-3theta).

No inverse of a stream value is used. Every subsequent expanded value costs an A operation; a short recurrence is not free evaluation of its L terms.

For clarity, suppose the actual trace polynomials have been acquired:

    F_tau(T)=product_(pairs of type tau)(T-x_j).

Write M_tau=degree(F_tau), M=sum M_tau=|G|/2 before any legitimate deduplication. Formula (1), over all rows and indices, has a known unit prefactor

    q^[M*L*(L-1)/2] * v^[L*sum_tau(tau*M_tau)]

and the remaining product admits the exact division-free sharing identity

    product_(i<L) F_0(d_(2i))*F_-2(d_(2i+2))
      =F_0(d_0)*F_-2(d_(2L))
       *product_(1<=i<L) (F_0*F_-2)(d_(2i)).        (2)

The tau=-1 product remains on the odd stream. Empty groups mean polynomial 1. Equation (2) merges the two even queries with their ACTUAL endpoints; it never divides out an endpoint that may be a collision. Restrictions to arbitrary original row/index subsets need their actual clipped streams; (2) applies to full common intervals or their correctly clipped intersections, not to arbitrary holes without retaining their boundary factors.

This is genuine shared recurrence/endpoint bookkeeping rather than just a pair constant: all three original trace streams reduce to two, with the same total target degree and explicit endpoint factors. It supplies no asymptotic gain. The F_tau coefficients, including their first mixed sum, have not been acquired by knowing the three centers. Building them from the acquired rows costs soft(k*M). If their endpoints have zeros, those nodes are retained and tested; they are not declared units.

## 2. Execute a normalized Jacobi closure, including native carries

For every odd integer e coprime to k define the grade-zero norm-one quotient

    Z_e=D^(-(e-1)/2)*C_e, u^e=C_e*g_e.

Then bar(Z_e)=Z_e^(-1). The integer normalizing exponent is essential. From the corrected cocycle one gets exact identities

    Z_(ab)=Z_a^b *rho_a(Z_b),
    Z_(e+k)=W*Z_e,
    Z_j^k=W^j/rho_j(W).                           (3)

These are identities of actual units, including exceptional characters. For the last identity use C_j^k=U^j/rho_j(U); D is fixed by rho_j. No unknown order or division by j is used.

With s=[j^(-1)]_k, define the known integer

    n_j=(ell_j+a_j*j+N*s)/k,
    h_j=n_j-k*tau_j/2.

The actual centered row is now

    X_j=W^h_j *Z_j^(-a_j)*Z_s^(-N).               (4)

The D exponents cancel exactly against E_j/2. Equation (4) uses all changing native a_j, inverse s, and centered carries rather than replacing them by constant weights.

Try one public multiplicative step j'=[g*j]_k, with g a public unit and t=[g^(-1)]_k. Put s'=[t*s]_k and a'=[t²*a_j]_k. Let

    e=(g*j-j')/k, f=(t*s-s')/k,
    d=(g*a'-t*a_j)/k.

All three are exact integers; the last is integral since g*t=1 modulo k. Equation (3) yields

    Z_j'=W^(-e)*Z_j^g*rho_j(Z_g),
    Z_s'=W^(-f)*Z_s^t*rho_s(Z_t).

Substitution in (4), followed by the last identity in (3), EXECUTES the next-row update:

    X_j'=X_j^t *L_j,
    L_j=W^A_j *rho_j(W)^d
         *rho_j(Z_g)^(-a')*rho_s(Z_t)^(-N),
    A_j=h_j'+e*a'+f*N-t*h_j-j*d.                (5)

Thus just three shared packed vectors W,Z_g,Z_t and actual native metadata describe each multiplier for this fixed public g. Direct-product generators cover all tags with the corresponding generator tuples. All metadata and those O(log k) fixed generator vectors cost soft k. This removes a need to enumerate k separate Jacobi histograms merely to DESCRIBE these unit multipliers. To apply (5), each coefficient permutation/power/multiplication still costs soft k. This is not an all-row scalar trace acquisition.

The trace version has an explicit next mixed term. For a norm-one y put tr(y)=y+y^(-1), delta(y)=y-y^(-1), and define polynomial V_n by V_0=0,V_1=1,V_(n+1)=T*V_n-V_(n-1); extend D_-n=D_n and V_-n=-V_n. The polynomial identities

    y^n=(D_n(tr(y))+delta(y)*V_n(tr(y)))/2

are division-free in delta(y), including delta(y)=0. Because 2 is a certified scalar unit, (5) gives

    x_j'=[D_t(x_j)*tr(L_j)
           +V_t(x_j)*delta(X_j)*delta(L_j)]/2.     (6)

The extra term is an actual product of two anti-invariant vectors; it is not supplied by x_j and tr(L_j). If the following multiplier is L_next, updating that extra term requires

    delta(X_j')*delta(L_next)
      =[D_t(x_j)*delta(L_j)*delta(L_next)
        +V_t(x_j)*tr(L_j)*delta(X_j)*delta(L_next)]/2. (7)

The second mixed product in (7), delta(X_j)*delta(L_next), is the exact unacquired boundary for the proposed two-trace state. Unlike a constant-multiplier Adams progression, (5) changes rho_j to rho_j', rho_s to rho_s', a', d and A_j. Formula (7) does not close from the previous mixed product by a stated Jacobi identity. It CAN be acquired from actual vectors at soft k per step; doing so over all tags pays soft(k*|G|). This is a concrete execution/cost of this representation, not an assertion that other scalar representations cannot do better.

There is no pole or nonunit pivot hidden in this failure to close. All formulas use unit words, polynomial recurrences and division by 2. If a trace discriminant x_j²-4 vanishes, the same formulas still hold. Trying to diagonalize by its square root or invert delta(X_j) would be an extra unsupported operation and is unnecessary here.

## 3. An alternate bounded trace basis is fully initialized, but per row

To check that (7) is not merely an avoidable sign or missing initial value, implement (4) directly as a three-generator trace recurrence. For norm-one generators y_1=W,y_2=Z_j,y_3=Z_s, acquire t_r=tr(y_r), b_rs=delta(y_r)*delta(y_s), and actual exponents (h_j,-a_j,-N). Then

    tr(y_1^a*y_2^b*y_3^c)
      =[D_a(t_1)D_b(t_2)D_c(t_3)
       +b_12 V_a(t_1)V_b(t_2)D_c(t_3)
       +b_13 V_a(t_1)D_b(t_2)V_c(t_3)
       +b_23 D_a(t_1)V_b(t_2)V_c(t_3)]/4.          (8)

Expand each power as above and sum its simultaneous inverse: odd numbers of delta factors cancel, proving (8) over the ring itself. Compute D,V by binary powering in the quadratic algebra Y²-t_r*Y+1; this takes O(log N) A operations for polynomial-bit exponents, including negative ones via inversion of norm-one y. This algorithm acquires the ACTUAL x_j in soft k with all starts and all mixed coefficients supplied. It is uniform at repeated roots and at zeros of its answer. Across all rows its supplied b_rs and t_2,t_3 still cost soft(k*|G|); the common W data alone do not initialize them. It improves neither the already available per-row bound nor the whole-family exponent.

## 4. Execute seed decimation and price its state

The seed stream itself has exact binary identities

    d_(2n)=d_n²-2,
    d_(2n+1)=d_n*d_(n+1)-theta.

Thus an attempted binary-length contraction can use the actual consecutive state (d_n,d_(n+1)). Its two branches are

    (x,y) -> (x²-2, x*y-theta),
    (x,y) -> (x*y-theta, y²-2).                   (9)

The invariant is x²+y²-theta*x*y=4-theta². Initial state (2,theta) is acquired, and (9) has no inverses or genericity assumptions. This genuinely initializes all seed values as a compact circuit; it does not initialize the product of their evaluations.

For the even stream, already one literal pullback sends an actual monic target polynomial F(T) of degree M to F(T²-2), of EXACT degree 2M with leading coefficient one, and converts F(d_(2i)) to that polynomial at d_i. This is an actual degree increase, not a maximum-degree heuristic over a ring. The odd pullback is F(x*y-theta) on the consecutive state. Continuing (9) requires the corresponding higher-degree pullbacks; the conic relation can reduce a variable but does not turn the specified nonlinear pullback into a proved fixed-degree update. The current algorithm either expands them and pays their degrees or returns to geometric blocking. No terminal norm is supplied just by the small transition circuit.

A fully paid completion after the actual rows are supplied is straightforward and safe as a VALUE computation. Rewrite a trace target factor as the Laurent polynomial in z in (1), or use directly its two supplied roots R_j,R_-j. Construct the baby product product_(a<b)(Z-q^a) by a monic product tree, acquire every giant start, and evaluate it at the supplied unit-scaled row roots by monic multipoint evaluation. Repeated points or zero values cause no division by collision values. Choosing b near sqrt(JL) yields soft(J+sqrt(JL)) A operations, hence soft k*(J+sqrt(JL)) base-ring work, plus the paid row acquisition. At J~k,L~k² this is soft k^(5/2). One final acquired primitive norm adds soft k. This explicitly computes the trace query value; its possible unpaired character zeros still require separate recovery. The primitive norm routine is not a free row constructor.

## 5. Support, recovery, restrictions, and ledger

Equations (1),(2),(5)--(9) are identities in A, so they remain valid modulo either hidden prime and on restrictions. Monic product trees retain all zero support. There is no step dividing a terminal value, an endpoint, a trace discriminant, or an auxiliary pivot. The endpoints in (2) correspond to actual i=0 or i=L-1 in their original tau group; the degree label 2L is not an extra original collision index.

Coverage says at least one original row/index has R_j=q^I at its own prime. It does not assert that a saturated primitive norm identifies that row/index, that Q0 has prepared beta orders, or that a componentwise Gauss zero is a scalar beta witness. The centered normalization preserves exactly the same issue. A proper gcd of an acquired scalar norm is valid. For any selected conjugate-paired beta-coupled hit, the already proved identity (f,bar f)=(f,beta0^(2E_j)-beta0^(2Hi)) recovers the original scalar condition; a saturated bounded original beta leaf then has its original decoder. Otherwise retain the guaranteed original scalar query and its complete recovery at soft(J+sqrt(JL)); do not call the raw trace query a replacement. No new index outside its retained bounded horizon is fed to that decoder.

| Actually acquired operation | Cost in base-ring work | Scope |
|---|---:|---|
| Native metadata, W,v,theta and initial stream values | soft k | entire family descriptors / actual shared vectors |
| Centering and two-stream identity (1),(2) | soft k descriptors | exact factors and endpoints, no trace coefficients supplied |
| Public generator W,Z_g,Z_t data and all carries in (5) | soft k | fixed generator input vectors and metadata |
| One actual trace by (5)--(8) | soft k | paid vector operations and all mixed starts |
| All actual traces / F_tau | soft(k*J) | no expanded row is priced as a scalar |
| Streamed next mixed products (7) over tags | soft(k*|G|) | actual initialized update, no two-trace closure claimed |
| Seed circuit (9) | O(log L) descriptor depth | terminal product absent until pullbacks/evaluations paid |
| Supplied-row full mixed query and primitive scalar norm | soft k*(J+sqrt(JL)) | value computation, not automatic saturation recovery |
| Retained original scalar covered query | soft(J+sqrt(JL)) | complete original witness/decoder interface |

The constructive sharing gain is the acquired center and exact two-stream merge, and the concrete recurrence gain is a generator-based normalized unit update with every carry displayed. The trace update was tested through its next mixed coefficient; the seed update was tested through its first polynomial pullback. Neither has produced a bounded, acquired scalar terminal state at soft k, nor an asymptotic improvement on the original covered query. This scoped conclusion does not rule out a different fused recurrence or original-source selection algorithm.

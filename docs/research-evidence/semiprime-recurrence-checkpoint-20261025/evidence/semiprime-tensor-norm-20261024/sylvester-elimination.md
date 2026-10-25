# Tensor norm: executed fraction-free Sylvester step and scalar closure audit

24 October 2026. Scratch only, no repository edits, examples or backend work. The preceding endpoint validator was rerun WITHOUT --append and passed: 270 frozen entries, report/review pins, shared-document prefixes and diff check, timestamp 2026-10-24T12:20:38.234492+00:00 in /tmp/semiprime-recurrence-endpoint-20261024/continuation-validation.json.

This attempts actual elimination in X over the short Y algebra. The first nontrivial Schur complement is acquired compactly and denominator free, exploiting the diagonal support of F(XY). Its scalar norm does not yet close through the subsequent elimination: norms of additive Schur updates are the specified missing operation. A fully expanded unit-pivot completion is paid below; no soft-m final norm or exponent gain results.

## 1. Paid tensor input and chosen balanced trial

Let R=Z/NZ, F(Z)=sum_(i=0)^J f_i Z^i monic, and

    A_s(X)=product_(a<s)(X-q^a),
    B_t(Y)=product_(b<t)(Y-q^(sb)).

The original prepared q is a unit and short q differences through the rectangle horizon are units. All three polynomials have acquired coefficients in soft(s+t+J); B_t's constant coefficient is a unit, so Y is a unit in K=R[Y]/B_t. Monic quotient operations are legal. A multiplication in K costs soft t BASE-RING operations, not one.

The requested norm is exactly

    N_(K/R)( Res_X(A_s(X),F(XY)) )
       =product_(b<t)product_(a<s)F(q^(a+sb)).        (1)

The two seed sets are unit-separated, but mixed target hits are allowed. The norm identity is valid at zero divisors. A final short block handles L not divisible by s; selected original intervals retain their actual seed indices. No large polynomial product has been acquired by (1).

Choose the concrete balanced case s=J=n, with t~n~m. This is already an admissible s choice for the full-block native algorithm. Unequal degrees can use the same ordinary Sylvester/pseudodivision rules; they are not granted a stronger bound from this balanced calculation.

Normalize only by a KNOWN unit:

    B(X)=Y^-n F(XY)=X^n+sum_(i<n)b_i X^i,
    b_i=f_i Y^(i-n).

Thus Res_X(A_n,F(XY))=Y^(n²) Res_X(A_n,B). The first scalar norm factor N_K(Y)^(n²) is a paid known unit. Every b_i starts as one Laurent monomial in Y. Store that compact description rather than n expanded K vectors.

The q-binomial coefficients are actually acquired:

    a_(n-r)=(-1)^r q^(r(r-1)/2) [n choose r]_q.

They are units under the short guard. In particular alpha=a_(n-1) is a unit. This does NOT say differences a_i-b_i or future Schur pivots are units.

## 2. First degree cancellation and the actual 2-by-2 Schur complement

Subtract the two monic degree-n polynomials:

    C=A_n-B, c_i=a_i-b_i, deg_X C<=n-1.

All c_i are acquired as TWO Laurent monomials in soft n base work. For the branch deg C=n-1 set

    c=c_(n-1), d=c_(n-2), h=c*b_(n-1)-d.

These are explicit short Laurent polynomials. Computing the degree-one quotient of B by C amounts to the leading coefficient system

    [ c  0 ] [u] = [1        ]
    [ d  c ] [v]   [b_(n-1) ].

If c is a unit, its solution is u=c^-1, v=h/c². The low coefficient Schur complement is therefore

    R_i=b_i-[c_(i-1),c_i] T^-1 [1,b_(n-1)]^t,
    T=[[c,0],[d,c]].

Instead of assuming that inverse, acquire its fraction-free numerator:

    D_i=c²*b_i-c*c_(i-1)-h*c_i, 0<=i<=n-2, c_(-1)=0,
    D(X)=c² B(X)-(c X+h) C(X), deg_X D<=n-2.         (2)

This is a POLYNOMIAL identity even when c is a zero divisor or zero. It is the adjugate Schur formula det(T)*B_low-lowblock*adj(T)*leadvector. When c is a unit, R=D/c² is exactly the ordinary next remainder. Thus the first nontrivial Schur update is executed, not asserted through a rank description.

Crucially it still has short diagonal support. Since c=alpha-f_(n-1)Y^-1 and d=a_(n-2)-f_(n-2)Y^-2, expansion of each D_i uses only the exponents

    {0,-1,-2, i-n, i-n-1, i-n-2}.                  (3)

Coincident exponents combine. The shared short factors c,h and the input coefficient arrays acquire all D_i in O(n) base-ring work/storage as sparse descriptors. No n-by-t table is needed for THIS first step. This is a real positive initialized simplification from the tensor's diagonal coefficient support.

## 3. Pivot guard is paid and cannot be silently strengthened

The first c is linear Laurent, so its K-unit status can be tested in soft t, not treated as generic. Write z=f_(n-1)/alpha, using the certified unit alpha. Then

    c=alpha*Y^-1*(Y-z),
    N_K(c)=alpha^t*N_K(Y)^-1*(-1)^t B_t(z).

Evaluate the acquired degree-t B_t at z and take gcd with N. A proper gcd factors N. If it is a unit, acquire c inverse explicitly: write B_t(Y)-B_t(z)=(Y-z)Q(Y); modulo B_t,

    (Y-z)^-1=-Q(Y)/B_t(z),
    c^-1=-Y Q(Y)/(alpha B_t(z)).

All scalar divisions are guarded and the quotient is an ordinary monic exact division. This costs soft t and yields an explicit K vector or its common rational description. Formula (2) can meanwhile remain fraction free.

If gcd(B_t(z),N)=N, c is NOT licensed for inversion. This is a leading-coefficient collision, not necessarily F(q^(a+sb))=0; no original-beta leaf decoder follows from it. One may inspect the t explicit c-values to find proper local gcds, but a globally zero leading coefficient at a component is a degree-drop branch, not a factor certificate. No uniform compact continuation for all such branches is supplied here. A complete algorithm can stop this experiment and run the original scalar product constructor, whose proper/saturated-leaf recovery is already paid.

Later pivots have the same issue: unit-separated seed grids license CRT coordinates, not arbitrary Sylvester principal minors. Fraction-free identities avoid INVALID divisions, but do not turn a saturated pivot into a factor or permit dividing by it modulo B_t.

## 4. Exact general closure and what must actually be carried

For ordinary unit-pivot Euclidean elimination, write R_(-1)=A_n, R_0=B and successively

    R_(k+1)=R_(k-1)-Q_k R_k,
    R_k=U_k A_n+V_k B,
    U_(k+1)=U_(k-1)-Q_k U_k,
    V_(k+1)=V_(k-1)-Q_k V_k.                         (4)

For generic degree drops of one, Q_k has degree one in X. In the fully fraction-free version replace the first line by

    R_(k+1)=lc(R_k)^(deg R_(k-1)-deg R_k+1)*R_(k-1)-Qtilde_k R_k,

and make the identical scaled cofactor updates. This is exact pseudodivision over K, with no inverse. Retaining previous-pivot divisions to normalize subresultants requires a separately lawful exact-division implementation; it is not division by a nonunit in K merely because an identity holds over a field. The q-hook extension below supplies such exact divisions BEFORE reducing in K, with their polynomial degrees explicitly charged; it still does not make the specialized pivot a K-unit.

The cofactor representation is a genuine closure: there are acquired polynomial circuits for every remainder, starting from A_n and the diagonal B, and each new leading coefficient is the corresponding coefficient of U_k A_n+V_k B. But (4) needs that coefficient, not only the norm of the previous pivot. At depth k, explicitly retaining U_k,V_k has O(k) K coefficients, and each new leading coefficient is a mixed convolution against a_i and f_iY^(i-n). Keeping these K coefficients expanded costs O(kt) residue words; near the end it is n*t~m². The first sparse six-exponent identity (3) does not by itself provide a compact scalar rule for all these mixed coefficients.

A straight-line expression for (4) is allowed as a descriptor. Evaluating a leading coefficient or its scalar norm from that growing expression must still be executed. Repeated products create mixed Y powers and sums; no fixed finite list of acquired scalar norms or q-binomial entries closes those updates in this attempted implementation. No independence/rank lower bound is asserted about another representation.

## 5. Testing the determinant-only objective directly

If P,Q are acquired polynomials of degrees p,q and R=P mod Q has degree r, the valid unit-pivot resultant update is

    Res(P,Q)=(-1)^(pq)*lc(Q)^(p-r)*Res(Q,R).

Applying N_K to this identity would retain only scalar norms of the pivots and the final constant. Thus the determinant-only objective genuinely asks for less output than every remainder vector.

But the next pivot in the first executed step is already

    lc(D)=c²*b_(n-2)-c*c_(n-3)-h*c_(n-2).             (5)

Its norm is not determined by norms of the three summands: norm is multiplicative, not additive. Here (5) is still an acquired Laurent polynomial with exponents among 0,-1,-2,-3,-4, so THIS next pivot norm is genuinely computable in soft t by evaluation or a short resultant against B_t. After that, obtaining the next Schur numerator requires its mixed cofactor coefficients in (4); knowing only the scalar norm from (5) does not initialize them.

One can carry all needed mixed data and compute each pivot norm by a separate t-point evaluation. That pays soft t per acquired pivot, or soft nt for n pivots even before an improved shared circuit contraction. Replacing those evaluations by the phrase scalar resultant against B_t simply names the same unacquired mixed-input norm operation. This is the exact failure point of the tested scalar-only elimination recurrence: multiplicative determinant transport is cheap, but additive Schur updates require new mixed pivot data.

The q-binomial A coefficients are fully known and structured. They make alpha and all original a_i units and keep the initial descriptors short. They do not supply the f-dependent mixed pivot norms in (5) or the subsequent cofactor updates by a paid simultaneous computation. No claim is made that they cannot support such a new computation.

## 6. Fully expanded completion and comparison with the old query

On a branch where needed pivots are units, ordinary fast polynomial resultant/half-GCD over K takes soft n K operations for degrees O(n). Each K operation costs soft t, so this is soft nt=soft m² base-ring work, including acquisition of compatible coefficients. Acquire the final scalar K-norm by monic MPE at the t explicit Y-grid points and multiply; a supplied degree-<t residue costs soft t to norm. Target zeros are allowed; no final norm inverse is used.

A naive coefficientwise Euclidean implementation is worse; it is not priced as soft n base operations. Unnormalized fraction-free pseudo-remainders can increase expression/degree sizes and are not assigned the fast unit-pivot bound for free. If a pivot guard saturates without giving a factor, revert to the existing zero-safe original scalar blocking routine. This gives a defined full computation, but the expanded unit branch is slower than the available soft(J+sqrt(Jst))=soft m^(3/2) routine, so a practical controller should retain that old routine rather than execute the expensive expansion.

All ordinary row/seed restrictions remain available through the original scalar constructor. The present compact Sylvester experiment has not supplied its own new restriction-stable nearlinear norm oracle. A saturated final ORIGINAL scalar leaf retains original index a+sb and beta/offset metadata for the existing bounded decoder; a saturated intermediate Sylvester pivot does not.

## 7. Explicit ledger and outcome

| Operation | Acquired state | Paid cost |
|---|---|---:|
| A_s,B_t,F | three short coefficient lists | soft(s+t+J) |
| K and Y inverse | monic quotient, unit constant | soft t |
| Balanced B(X)=Y^-n F(XY) | n diagonal Laurent monomials | soft n descriptor |
| C=A-B | two monomials/coefficient | soft n descriptor |
| First adjugate Schur D | <=6 monomials/coefficient, shared c,h | soft n descriptor |
| First pivot guard/inverse, next mixed norm | explicit scalar test / short Laurent norm | soft t each |
| Depth-k cofactor closure, if expanded | O(k) K coefficients | O(kt) residue storage; operations charged in K |
| Full fast resultant on unit branch | acquired K-valued compatible data | soft nt |
| Final supplied K element norm | t-coordinate or polynomial input | soft t |
| Existing complete original query | actual scalar norm and recovery | soft(J+sqrt(Jst)) |

The experiment supplies an actual compact first Schur complement and a paid guard for its pivot, with an explicit determinant-only continuation test. The retained bottleneck is acquiring norms of the additive, f-dependent mixed pivots through the cofactor recurrence, without expanding rank-t coefficient data or independently evaluating n different pivots. The final scalar norm has not been acquired in soft m. This is a failure of this concrete closure/completion, not a lower bound on scalar tensor norms or implicit Sylvester algorithms. The original fast-recurrence endpoint objective remains open.


## 8. Positive q-hook extension: ALL formal principal pivot boundaries are paid units

This extension was reached independently with root after the first Schur calculation. It removes pivot genericity at a formal origin, while keeping the unit-Y endpoint acquisition explicit.

Put Z=Y^-1 and regard

    B_Z(X)=X^n+sum_(i<n)f_i Z^(n-i) X^i

as a polynomial over R[Z], BEFORE reduction modulo B_t(Y). Let p_k(Z) be the principal coefficient of the degree-(n-k) subresultant of A_n and B_Z, with the signed Sylvester-minor convention chosen consistently. At Z=0 the second polynomial is X^n. Eliminating its trivial monomial-shift block leaves the k-by-k Toeplitz determinant

    Delta_k=det(a_(n-k+i-j))_(1<=i,j<=k),

up to the harmless overall sign of the chosen subresultant convention; a_i=0 outside 0,...,n. For k=1 this is a_(n-1), and for k=2 it is a_(n-2)^2-a_(n-1)a_(n-3), precisely the constant boundary of the first quartic Schur numerator. Thus p_k(0) is a known signed Delta_k.

Writing a_(n-r)=(-1)^r e_r(1,q,...,q^(n-1)), dual Jacobi-Trudi gives

    Delta_k=(-1)^k s_(k^k)(1,q,...,q^(n-1)).

This is an integral polynomial identity, hence valid after composite-ring specialization. The principal specialization may be derived by substituting the geometric variables into the bialternant and dividing the two Vandermonde products; every denominator difference is a unit because all relevant exponent differences are <=2n-1. Equivalently its explicit hook-content product is

    s_(k^k)=q^[k²(k-1)/2]
             * product_(1<=i,j<=k) (1-q^(n+j-i))/(1-q^(2k-i-j+1)).

Each numerator/denominator exponent is between 1 and 2n-1. The original short order guard therefore certifies every Delta_k is a UNIT, for ALL k=1,...,n; this conclusion does not involve f_i or any hidden local field.

All these scalar boundaries are acquired in soft n, not by listing n² hook cells for each k. Define Q_r=product_(v=1)^r(1-q^v), Q_0=1, and T_r=product_(u=0)^(r-1)Q_u. Acquire Q through 2n-1, their prefix products T, and unit inverses by batch inversion. Then

    s_(k^k)=q^[k²(k-1)/2]
              *T_(n+k)*T_(n-k)*T_k²/(T_n²*T_(2k)).    (6)

Each k uses O(1) acquired array entries and a logarithmic-bit unit power. Thus (6) pays every normalization scalar within soft n base-ring work.

### Public degree bounds, reversal, and exact division over R[Y]

The SAME principal Sylvester minor gives the public bound deg_Z p_k<=k², even if its actual highest coefficient vanishes. Indeed its 2k-by-2k leading-coefficient block has k B_Z rows shifted by 0,...,k-1 and k A rows. In a determinant term the exponent supplied by B rows is k*n minus the sum of their selected coefficient-column degrees plus the sum 0+...+(k-1). Selecting the k lowest possible column degrees n-k,...,n-1 bounds this by k²; selecting the highest gives the nonnegative lower bound. This also identifies the Z=0 monomial-block elimination above.

Use the PROVED PUBLIC bound, not an assumption of a nonzero Z^k² coefficient, to reverse:

    phat_k(Y)=Y^(k²)*p_k(Y^-1).

Its coefficient of Y^k² is the signed Delta_k, a unit, so phat_k has a certified unit LEADING coefficient. A vanishing highest Z coefficient merely produces trailing Y factors; no nonzero top-Z assertion is made. Thus phat_k can be normalized to monic over R[Y].

Bareiss/subresultant exact-division identities are universal determinant identities. If an identity before specialization is N(Z)=p_k(Z)^e Q(Z), choose compatible public reversal bounds D_N=e*k²+D_Q. Reversal gives the literal polynomial identity

    Y^D_N N(Y^-1)=phat_k(Y)^e * Y^D_Q Q(Y^-1).

Extra known powers of Y can be included if a larger public bound is used. Division by the monic-normalized phat_k is ordinary polynomial long/fast division over R, lawful even with zero divisors; exactness is the specialized universal determinant identity, not an assumption that phat_k is invertible modulo B_t. A unit-leading polynomial is not a zero divisor in R[Y], so the exact quotient is unique. This supplies a genuine denominator-safe normalization method before quotient reduction.

It does not make such divisions free. The pivot bounds grow to n², and explicitly acquiring/reversing their full coefficient data or executing large exact divisions must be charged. Products of normalization factors retain unit leading coefficients but can have still larger public degrees in an unoptimized implementation.

### Initialized formal precision and the remaining endpoint

Since p_k(0) is a unit for EVERY k, all these pivots are units in R[[Z]] and in R[Z]/Z^M. Consequently the formal subresultant chain has the predictable degree profile n-k, and a half-GCD/resultant computation at supplied precision M can be executed with certified unit pivots. An ordinary expanded implementation costs soft(n*M) base-ring work and O(n*M) compatible coefficient storage; it does not count each truncated series operation as one R operation. At M=1 the all-pivot data reduce to the already acquired soft-n q-hook values.

However Z=Y^-1 is a UNIT in the actual endpoint algebra K. Reducing a formal prefix modulo Z^M does not acquire its value there: the omitted Z^M tail is not zero in K. Even a pivot with unit constant coefficient can become nonunit after this specialization. The reversed monic exact-division route avoids illegal division, but still needs the actual polynomial data or a new compact contraction of it before taking the final K-norm. A degree bound and a unit boundary are not that acquisition.

Thus this q-hook extension proves a positive, fully initialized all-pivot normalization result and removes formal-origin genericity. It neither pays the growing mixed polynomial data in the Schur chain nor acquires the final scalar tensor norm in soft m. Scalar-only contraction through those additive updates remains the exact open operation in this attempted algorithm.

# Independent Sylvester elimination and q-hook review

2026-10-24. **PASS. No required fixes.** Scratch review only; no source or repository edits, examples or backend work.

Reviewed source: `/tmp/semiprime-tensor-norm-20261024/sylvester-elimination.md`

Exact SHA256: `f3375df02a067a43230d1f4accddc476bbbe020a64c9145b90757ba5404720c2`

The report was frozen by its author after the all-pivot q-hook extension. This review checks that extension together with the actual first elimination, collision guards and claimed cost/scope. Preservation-validation statements are separate from this mathematical audit.

## First elimination is genuinely acquired

Normalizing F(XY) by Y^-n uses a known unit in K, since B_t has a unit constant coefficient. Res(A_n,F(XY))=Y^(n^2)Res(A_n,B) has the correct exponent: scaling the degree-n second operand by Y^n scales its resultant with degree-n A by Y^(n^2).

The q-binomial coefficients of A_n are acquired short scalar data, and their factors are certified units. In particular alpha=a_(n-1)=-(1-q^n)/(1-q) is a unit. This does not certify alpha-f_(n-1)Y^-1.

For C=A_n-B, the triangular leading system [[c,0],[d,c]] has determinant c^2. Its adjugate gives h=c*b_(n-1)-d and

    D=c^2 B-(cX+h)C,
    D_i=c^2 b_i-c c_(i-1)-h c_i.

Both degree-n and degree-(n-1) terms cancel identically, so deg_X D<=n-2 even without c invertible. The first Schur identity is thus valid at zero divisors.

Expanding c=alpha-f_(n-1)Y^-1 and h shows exactly the claimed six-exponent containment {0,-1,-2,i-n,i-n-1,i-n-2}. Shared factors and O(1) monomials per coefficient acquire this first update in O(n) base-ring operations, without an n-by-t coefficient table. The next leading coefficient has exponents contained in 0,-1,-2,-3,-4 and can indeed be normed separately at soft t.

## Actual pivot guard and singularity handling

For z=f_(n-1)/alpha,

    c=alpha Y^-1(Y-z),
    Norm_K(c)=alpha^t Norm_K(Y)^-1 (-1)^t B_t(z).

The sign is correct. The exact quotient Q=(B_t(Y)-B_t(z))/(Y-z) gives the stated inverse -YQ/(alpha B_t(z)) only after the scalar value is certified unit. Evaluating B_t(z), guarding it and constructing Q cost soft t.

A saturated leading-coefficient norm is not an original target collision. The report correctly refuses to invert it or invoke the original leaf decoder. It permits a fallback to the existing original scalar query. This makes the overall experiment well defined without claiming compact continuation through every intermediate singular pivot.

The unit-pivot resultant formula Res(P,Q)=(-1)^(degP*degQ)lc(Q)^(degP-degR)Res(Q,R) is correct. Norms of additive Schur sums are not determined by norms of their summands, and the report identifies the missing mixed coefficients rather than supplying them as an oracle.

## Principal pivot boundary and rectangular Schur sign

For the principal coefficient associated with degree n-k, the standard signed 2k-by-2k Sylvester coefficient block uses k rows of each polynomial and coefficient degrees n-k,...,n+k-1. At Z=0 the B_Z rows are monomial shifts. Eliminating their fixed columns leaves

    Delta_k=det(a_(n-k+i-j))_(1<=i,j<=k),

up to the consistently chosen subresultant sign. The low-k boundary agrees with the displayed first Schur numerator: Delta_1=a_(n-1), Delta_2=a_(n-2)^2-a_(n-1)a_(n-3).

Each a_(n-r)=(-1)^r e_r(1,q,...,q^(n-1)). In any determinant term the total sign exponent is k^2, so the sign is (-1)^k. Dual Jacobi-Trudi gives EXACTLY

    Delta_k=(-1)^k s_(k^k)(1,q,...,q^(n-1)).

The square partition and sign are correct; the unit proof is independent of the harmless standard subresultant sign convention.

The principal-specialization q-power is k^2(k-1)/2. Every content exponent n+j-i and every hook exponent 2k-i-j+1 lies between 1 and 2n-1 for k<=n. Thus every factor in the specialization is a certified unit under the short q-order guard. This establishes every principal boundary unit without a hidden field or an f-dependent unit assumption.

## All boundaries really cost soft n

For Q_r=product_(v=1)^r(1-q^v) and T_r=product_(u=0)^(r-1)Q_u, the numerator hook-content product is T_(n+k)T_(n-k)/T_n^2, and the hook denominator is T_(2k)/T_k^2. Hence the report's formula

    s_(k^k)=q^[k^2(k-1)/2]
              T_(n+k)T_(n-k)T_k^2/(T_n^2 T_(2k))

is exact. Acquiring Q through 2n-1 supplies T through 2n. All are units. Prefix products, unit inverses and O(n) bounded-bit powers therefore acquire ALL Delta_k in soft n, without a separate k-by-k or hook-cell computation for every k. This is a genuine paid positive normalization result.

## Public degree, reversal and exact division over zero divisors

In a determinant term of the actual principal minor, the exponent of Z from the k B_Z rows is kn minus the sum of their selected coefficient-column degrees plus 0+...+(k-1). Choosing the k lowest available columns n-k,...,n-1 bounds this by k^2. Thus deg_Z p_k<=k^2 is a proved PUBLIC bound, not an assumption about a nonzero highest coefficient.

Consequently phat_k(Y)=Y^(k^2)p_k(Y^-1) has leading coefficient p_k(0), a signed unit Delta_k. It can be normalized to monic over R[Y]. A vanished highest-Z coefficient produces trailing powers of Y only, exactly as stated.

Reversing a universal exact identity N=p_k^e Q with compatible public degree bounds gives an exact polynomial identity before reducing modulo B_t. Division by the monic-normalized phat_k is ordinary polynomial division over R and is valid despite zero divisors. Its quotient is unique because a unit-leading polynomial is not a zero divisor. No inverse of its specialized residue in K is implied or required. The report explicitly charges the growing polynomial degrees, which can reach n^2 for individual public pivot bounds.

The formal-series conclusion is also correctly scoped: all p_k(0) units give lawful formal/truncated-series pivots and the predictable principal degree profile. Expanded arithmetic at precision M costs soft(nM), not soft n independently of M. A truncated Z-prefix cannot be evaluated at the unit Z=Y^-1 by dropping its tail. The report does not confuse formal-origin units with endpoint units.

## Cost, recovery and scope

The six-monomial first step and all q-hook boundaries are paid in soft n descriptors/scalars. Expanded later cofactors or quotient-algebra arithmetic retain the factor t. The fast unit-pivot resultant completion costs soft nt, while singular auxiliary pivots revert to the old zero-safe scalar query. Neither this implementation nor the q-hook extension acquires the final scalar tensor norm in soft m.

Only saturated ORIGINAL scalar leaves retain the original bounded beta decoder. Intermediate Sylvester pivots are expressly excluded. The source states no general lower bound, no generic independence premise, no uncharged explicit pivot family, and no new whole-query exponent. All positive claims are actual initialization/normalization results, not merely determinant identities.

The exact reviewed report is mathematically consistent and its costs and unacquired endpoint are properly qualified.

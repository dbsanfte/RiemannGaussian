# Projective gradient normalization, explicit errors, and cyclic boundary carries

24 October 2026. Scratch only. The exact ratio-only target is weaker than two uniform gradient values. This note tests whether the acquired Cauchy quotient eliminates its missing correction modulo the original collision product. It proves one legitimate unit normalization, computes the finite-prefix/commutator error without deleting it, and acquires ALL scalar boundary carries of a short cyclic recurrence in soft k. Those carries do not acquire its native paired projection. No whole-query improvement is obtained; the covered completion remains soft k^(3/2).

## 1. Actual inputs and projective target

Use cauchy-contraction.md SHA256 `cc91bc1edc9534368081749933e980daa1ec04b6aea2b750366481741bc8bc70`, native-orbit-blocks.md SHA256 `a6ab972dd085669e3c322a5031597fd441821d43945b4fee62e97b3f2a818e15`, and this packet's unit-filter.md SHA256 `fae30a63a9693ba9e38a2653c7feefa4dcbbc31ebb112a1a42b21d2958ddb18c`. The companion owns the shared unit-filter lemma and its actual screening; it is not claimed as a separate acquisition breakthrough here.

Take canonical repaired MINUS rows, their actual unit y_j=V_j^(-1), original tags j, and the smaller-nonsplit promise. There is exactly one original hit at P, with tag j* and index I. The actual native bounds give I<33H/16+1. Set

    L=3H+2, m=k, R=3k, ell=mR-1=3H-1,
    A(T)=P_ell(T)=prod_(n<ell)(1-q^n T),
    alpha=q^(1-ell),
    Psi(Z)=prod_(r<R)(1-q^[m(r+ell-1)]Z).

The THREE original tail factors at ell,ell+1,ell+2 are acquired separately in soft k, with actual original-index consumers. On the good promise the unique hit lies in the prefix. All 1-q^n through16H are guarded and the ACTUAL q component orders are odd and k-rough. No native or coefficient deformation is assigned a hidden local-field oracle.

For root-label directions define partial_w=sum_j w_j partial/partial y_j, with q fixed. Let E=prod_j A(y_j). At its P-side unique simple zero,

    partial_tag E = j* partial_1 E,
    partial_1 E !=0.                               (1)

These y-direction outputs are sufficient for the same small-tag validation consumer: classify the first scalar, recover a base-field tag by coordinate/interval gcds, and verify its ORIGINAL row by the paid one-row locator. They are not asserted to be the original V-direction gradients with an omitted inverse-root chain factor. A different common unit base direction would also give (1). Wrong labels have bounded failure and the original full-family fallback.

The desired shortcut may return A0,B0 satisfying B0=j*A0 modulo P and A0 nonzero there, without acquiring two exact gradients. It need not support the exact-output/one-shift contract. No consequence of that stronger contract is used as a lower bound here.

## 2. A genuine allowed error: acquired unit normalization

Put psi_j=Psi(y_j^m), U=prod_j psi_j. The companion unit-filter proof applies to this ACTUAL native minus family: the possible q-grid indices of a Psi zero are ell-1,...,ell+R-2, all near3H, while the smaller-nonsplit minus hit is the own tag with I<33H/16+1. Extending the same short integer congruence argument over that <4H range excludes such a zero at P. Consequently the actual soft-k norm screens of all psi_j return a proper factor or globally certified units on the good branch; no saturated auxiliary endpoint decoder is needed. Wrong orientations may decline on an unverified/global-zero denominator.

All values psi_j, their actual inverses on the unit branch, U and both label logarithmic derivatives are acquired in soft k. Explicitly

    c_w=partial_w U/U
       =sum_j w_j*m*y_j^(m-1)*Psi'(y_j^m)/psi_j.

Degree-R MPE, public powers and the known labels pay every entry. For the TRUE normalized product Ebar=E/U,

    partial_w Ebar=U^(-1) partial_w E-Ebar*c_w.      (2)

Thus the second term really is a multiple of the ORIGINAL product, and at P both directions retain the SAME nonzero unit factor. This is a valid projective normalization. It does not acquire either gradient in (2). The allowed error statement is proved before using it, rather than calling an arbitrary tail an E multiple.

## 3. Compute the actual finite-prefix error

The Cauchy report supplies the coefficient transforms of W and E_tail with

    Psi(T^m)W(T)=A(T)+T^(ell+1)E_tail(T),
    deg W,deg E_tail<=ell.

Both transforms have soft-k actions/transposes. They are not full native evaluation arrays. With r_j=y_j^(ell+1)/psi_j, the TRUE normalized factors are

    A(y_j)/psi_j=W(y_j)-r_j E_tail(y_j).             (3)

All r_j and their derivatives in the two root-label directions are acquired in soft k, but the paired W and E_tail values are still missing. At the actual own root y*=q^(-I), equation (3) says

    W(y*)=r_* E_tail(y*),                           (4)

not that either side vanishes or is proportional to A(y*) by a proved unit.

For clarity the exact projective error of replacing the true factors by W is already explicit. If D_w^W=partial_w prod_j W(y_j), then at P

    D_tag^W-j*D_1^W
       =sum_j(j-j*) W'(y_j) prod_(h!=j)W(y_h).      (5)

The own summand is zero, but the NONHIT summands remain. Equation (4) is the only supplied pointwise cancellation at the own row and does not erase (5). Native tags are not replaced by arbitrary interpolation values, and no proof that (5) is zero on this family was found. Thus this replacement is not a proved ratio algorithm. Nor does the fast ordinary action of the W transform acquire the derivatives/product in (5).

An analogous fully explicit low-degree test is available, but is NOT credited as a covered algorithm. A cyclic remainder B_1 below gives f_1(y)=B_1(y/t_1), t_1=alpha/q=q^(-ell), degree<m. Its two root-label derivatives are actually acquired in soft k by MPE of f_1,f_1', plus prefix/suffix products at the supplied roots. The exact division identity is

    A(y)=f_1(y)+(y^m-t_1^m)Q_1(y).

At the own root y*, the multiplier y*^m-t_1^m is a P-side unit, so f_1(y*)=-(unit)Q_1(y*), not a forced zero. Its tag-gradient error has the same explicit nonhit sum as (5), with f_1 in place of W. The usual tag validation can reject a wrong answer, but no proof of success/coverage follows from this truncation. It is not counted as an acquisition win or a replacement for the guaranteed query.

## 4. Compute the restored commutator error, including its non-E terms

This section tests another proposed common-factor cancellation directly. Use the acquired q-grid U_r=q^(mr), its symmetric Vandermonde V, and D=C E_col from the Cauchy report. Let u(X)=(1,X,...,X^(R-1))^t, v(y)=(1,y,...,y^(m-1))^t and Gamma(X)=prod_r(X-U_r). The native scalar is u(y^m)^t C v(y)=A(y). Let l_X^t=u(X)^t V^(-1), the acquired Lagrange transfer.

The paired part of the restored ordinary commutator has the exact form

    Rcal(y)=l_X^t [U,V] C v(y), X=y^m.

Lagrange interpolation gives l_X^t U=X l_X^t-Gamma(X)b^t, where b_r=1/Gamma'(U_r), and b^t V=e_(R-1)^t. Therefore

    Rcal(y)=X A(y)-Gamma(X)T_last(y)-A_biv(QX,y),
    Q=q^m,
    T_last(y)=sum_(s<m)c_(m(R-1)+s)y^s.             (6)

Every T_last coefficient is actually acquired by the selected-q-coefficient primitive; its full native value array and Gamma(y_j^m) cost soft k. The first term in (6) vanishes at the own collision, but the short term and the ONE shifted paired term remain. The latter has an acquired ordinary coefficient action (row-scaled C), not acquired native paired values. Skew symmetry of [U,V] does not kill it: the actual two vectors are l_X and C v(y), not a vector paired with itself. The collision imposes u(X)^t C v(y)=0, not that missing eigenvector/proportionality relation.

Thus (6) computes exactly which part of this error is an A(y) multiple and which parts are not justified as such. It does not prove that the remaining terms are nonzero on every input; it refuses an unproved native congruence. The old middle-transform correction has not become a shared unit in two tag directions merely because the full coefficient actions are cheap.

## 5. Positive acquisition: ALL cyclic boundary carry scalars in soft k

Root proposed probing the short poles of Psi. Define, for r>=0,

    t_r=alpha q^(-r), z_r=t_r^m,
    B_r(T)=A(t_r T) mod(T^m-1), deg B_r<m.

Its ACTUAL coefficients are folded q coefficients. ONE B_1 array is acquired by the paid C^t action on the geometric row vector t_1^(m rho), followed by column factors t_1^s. B_0 is obtained by the same operation when needed; neither whole R-by-m array is acquired.

The q-Pochhammer identity implies the exact ORDINARY polynomial recurrence

    (1-q^(-r)T)B_(r+1)(T)
       -(1-alpha q^(-r-1)T)B_r(T)
                         =gamma_r(T^m-1).          (7)

Only a scalar carry occurs because both representatives have degree<m. Its sign and value follow from constant coefficients:

    gamma_r=B_r(0)-B_(r+1)(0),
    B_r(0)=G0(z_r),
    G0(Z)=sum_(rho<R)c_(m rho)Z^rho.                (8)

Acquire the ENTIRE short G0 coefficient vector by R selected coefficient requests, soft(sqrt ell+R)=soft k. Then monic MPE at all R+1 actual z_r gives ALL required gamma_r in soft k. This is actual boundary initialization, not a promise that those carries will later be supplied. For r>=1 the cyclic denominator 1-q^(-r)T has norm 1-q^(-mr), a guarded unit for r<=R. At r=0 it is not a cyclic unit; retain the directly acquired B_0/B_1 and (7), never invert 1-T in that quotient.

The fixed-state description is equally initialized. Put D_r(t)=B_r(q^r t). Then

    (1-qt)D_(r+1)(t)-(1-alpha t)D_r(qt)
                   =gamma_r[q^(m(r+1))t^m-1].      (9)

Modulo t^m the operator is M[f]=[(1-alpha t)/(1-qt) f(qt)]_<m with forcing -gamma_r/(1-qt). A concrete fast eigenbasis is the unit-diagonal lower Toeplitz matrix with coefficients w_0=1 and

    w_n=(alpha q^(n-1)-q)/(q^n-1)*w_(n-1), n<m.

All denominators and the numerator q-difference ranges are guarded; only this finite precision is used. The identity (1-alpha t)w(qt)=(1-qt)w(t) proves M=T_w diag(q^s)T_w^(-1). All basis/inverse data cost soft m.

Consequently ONE endpoint D_R is acquired in soft(R+m). With the directly acquired D_0=B_0, its exact formula is D_R=M^R D_0-g(M)v, where v=(1-qt)^(-1) mod t^m and g(Z)=sum_(h=0)^(R-1)gamma_h Z^(R-1-h). Diagonalize M, evaluate the acquired g at q^s by MPE, apply the two Toeplitz transforms and the supplied start. This uses the ordinary truncated identity (9), not an inverse of 1-T in the cyclic quotient at r=0. Equivalently start from D_1=B_1(qt), use M^(R-1)D_1 and the forcing indices h=1,...,R-1. This is a valid short fixed-core execution. It agrees with an independently cheap C^t geometric action and is not counted twice as a new terminal solution.

## 6. The partial-fraction projection still requested after that acquisition

All poles z_r are separated by guarded q differences. Acquire

    d_r=prod_(s!=r)(1-z_r/z_s), r=0,...,R-1,

and their inverses by short product/derivative trees, cost soft R. Exact block CRT, with no mth roots of unity, proves

    A(y)/Psi(y^m)
       =sum_(r<R) B_r(y/t_r)
                         /[d_r(1-y^m/z_r)]
       =sum_(r<R) D_r(y/alpha)
                         /[d_r(1-y^m/z_r)].         (10)

This is a proper rational partial-fraction identity since deg A=mR-1<deg Psi(T^m)=mR. On the actual unit-filter branch every denominator at a native y_j is a certified unit; its Cauchy weight matrix has paid soft-k actions. The coefficients D_r are not fictitious missing inputs: (7)--(9) supply their starts and all carries, and equivalently

    [t^s]D_r(t)=alpha^s sum_(rho<R)c_(m rho+s)z_r^rho.

Thus their whole implicit map is V_z C diag(alpha^s), with the acquired fast actions. A single fixed y's contraction (10), or one fixed linear functional applied at all r, is acquired in soft k by those actions. But the J native points change BOTH the Cauchy weights and the evaluation vector. Eigenvalues q^s of M versus nodes z_r=alpha^m q^(-mr) retain the mixed-step Vandermonde pairing. Neither gamma acquisition nor one fixed-core endpoint is that paired operation.

This is the exact old terminal-projection gate in an initialized short-pole presentation, not an unpaid numerator disguised as a new solver. Direct acquisition of all D_r coefficients/evaluations costs soft Rm=soft k². The original blocked query/gradient constructor remains better at soft k^(3/2). No proof that the unreduced part of (10) is an E multiple or one common unit in two tag directions was obtained. Formula (2) states the common-unit correction that IS proved; (3)--(6) retain the actual terms for which it is not proved.

All claimed soft-k data in this note are explicit starts, boundaries, short polynomials, unit screens or fixed-vector actions. A failed optional tag replacement is not a covered algorithm; the original both-colour query remains the guaranteed fallback. Proper factors are checked, and only actual original row/index leaves use the authoritative consumer. No change to frozen packets/shared documents, numerical example campaign, generic no-go theorem or improved factoring exponent is claimed.

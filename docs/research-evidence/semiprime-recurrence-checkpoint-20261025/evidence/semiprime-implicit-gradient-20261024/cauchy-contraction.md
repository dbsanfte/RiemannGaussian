# Exact Cauchy/symmetrizer transfer and a paid two-transform remainder identity

24 October 2026. Scratch only. This executes the proposed symmetrizer test with the ACTUAL coefficient matrix. It acquires a modified rank-two Cauchy diagonal and, separately, an exact representation of the TRUE query as the difference of two acquired fast coefficient transforms. It does not acquire those transforms' paired diagonals. The reciprocal twist and the polynomial tail are retained explicitly; the best complete query remains soft k^(3/2).

## 1. Read the old gate and fix an exact rectangular instance

Read the preserved journal at 38636--39020 before this attempt: the q-Pascal/companion core, initialized feedback, causal inverse and short rational numerator are ALREADY acquired. The unpaid operation is its static terminal projection, not a missing feedback numerator. The dyadic hierarchy already telescopes to two ordinary commutator terms; fast actions do not acquire their Hadamard contraction. This report does not repackage that inverse as a new solver.

Pinned inputs are all-mask-sharing.md SHA256 `5f79d577ff7fddf72a6e3670d5bca3b7ff2ef72557f137553d388b9fea9c0f31`, kernel-cauchy.md SHA256 `0153202f0e05e06437085ec6c8050725be1603993d83383a8949b8acaf209181`, and cofactor-contraction.md SHA256 `e4100f7c507a1f3a894b9c9285425b942f086f0080e3f2ef51bd2b0aa7838ee0`. The older joint-hadamard-recurrence.md, SHA256 `9e93a8b82e4728a37a01b14a55357d7d496cc85dcfe493a9d8ed3f98e2966ba3`, retains the relevant middle-matrix correction. All these operations keep their actual input and zero-safe scopes.

Use the canonical acquired native family V_j, its inverses y_j, actual row labels and target-separation preparation, J<=k. Both colours can be retained; a minus-only restriction also fits. The repaired full horizon is L=3H+2, H=k². Choose

    m=k, R=3k, ell=mR-1=3H-1,
    P_ell(T)=prod_(n<ell)(1-q^n T)=sum_(n=0)^ell c_n T^n.

The THREE remaining original factors n=ell,ell+1,ell+2 are acquired at all native rows in soft J: evaluate their common degree-three polynomial at the actual shifted starts, retaining original indices and unit V phases. A nonunit tail is localized to an ORIGINAL bounded leaf. Otherwise the desired covered query reduces to this prefix. No overquery, new decoder or balanced divisor of 3H+2 is assumed.

The acquired coefficient rectangle is FULL:

    C_(rho,s)=c_(m rho+s), 0<=rho<R, 0<=s<m.

All C/C^t actions and selected O(k) coefficient requests cost soft k, including their q-factorial starts. We never acquire its Rm=Theta(k²) entries. Every 1-q^r through Ccap=16H is guarded, q's component orders are odd and k-rough, and the small q ranges below satisfy ell+m<Ccap.

Write V_X for monomial evaluation at X_j=y_j^m and V_Y for evaluation at y_j. The true paired matrix and remainder values are

    S=V_X C V_Y^t,
    S_(j,j)=P_ell(y_j), h=P_ell mod F_y,
    F_y(T)=prod_j(T-y_j).                            (1)

All ordinary actions by S and S^t cost soft k; acquiring its diagonal is the unresolved operation. Acquiring that diagonal would interpolate the actual h in soft k extra work. A true Bezout action K*e0 would likewise recover h by the previously proved explicit first-column formula. No such image is introduced as a free generator here.

## 2. Acquire the complete Cauchy core, including its resonant corner

Let U_rho=q^(m rho), Lambda_s=q^(ell-s), U=diag(U_rho), Lambda=diag(Lambda_s). The known column eigenbasis E is lower triangular bidiagonal times lower triangular Toeplitz, acquired in soft m as in the pinned Cauchy report. It has actual soft-m actions/inverses using known unit diagonals and constant-one series inversion. Put D=C E. Its exact displacement is

    D Lambda-U D=g eta^t,
    g_rho=c_(m rho+m-1)(q^(m rho+m-1)-q^ell).       (2)

Every g,eta coefficient is paid in soft k. At the FULL last row g_(R-1)=0. All cross differences Lambda_s-U_rho are guarded units except the SINGLE equality rho=R-1,s=m-1. The actual corresponding entry is

    d_star=D_(R-1,m-1)=-q^(m-1)c_ell,

an explicitly acquired unit. Every other last-row entry is zero by (2). Thus D consists of its ordinary regular Cauchy core plus the one known rank-one corner. No division by the zero cross difference is made. Its actions/transposes and all boundary data remain soft k.

## 3. Test the actual companion symmetrizer, not a dropped inverse

Acquire the q-grid polynomial and its monomial evaluation map

    Gamma(Z)=prod_(rho<R)(Z-U_rho),
    V_(i,rho)=U_i^rho=q^(m i rho), V=V^t.

Gamma and all grid derivative inverses cost soft R. The q-grid differences are guarded (their exponents are below mR<Ccap). V,V^t,V^-1 actions are actual monic MPE/interpolation maps, costing soft R; their R² entries are not supplied. Let M be the lower companion multiplication matrix of Gamma. Then

    V M=U V, M^t V=V U.

The ACTUAL Hankel/Bezout symmetrizer is

    H=Bez(Gamma,1), H_(r,s)=gamma_(r+s+1),
    H M^t=M H,
    H=V^-1 diag(Gamma'(U_i)) V^-1.                  (3)

Indices outside Gamma's degree are zero and gamma_R=1. H and H^-1 have actual soft-R Hankel/Toeplitz actions. None is the identity or a cost-free replacement for V^-1.

There IS a genuinely short modified diagonal. Put Z=V D and W=H Z. Equation (2) gives M W-W Lambda=-H V g eta^t. Since monomial evaluation satisfies

    diag(X_j) V_X-V_X M=a_X e_(R-1)^t,
    a_X,j=Gamma(X_j),

we obtain the initialized rank-two equation

    diag(X_j) S_corr-S_corr Lambda
      =a_X r^t-p_X eta^t,
    S_corr=V_X H V D,
    r^t=e_(R-1)^t H V D=1^t D,
    p_X=V_X H V g.                                 (4)

Every displayed generator is ACTUALLY acquired in soft(R+m+J): D^t*1 uses the paid C^t circuit, H Vg uses one q-grid MPE and Hankel action, and Gamma,p are evaluated at the actual native X_j. All degrees and representations are short. Thus any matching J entries S_corr(j,j) are acquired in soft k from (4), with lawful scalar classification. If X_j-Lambda_j is a unit divide by it; a proper coefficient gcd factors. A globally zero difference uses the derivative of the polynomial numerator Gamma(X)r_j-p(X)eta_j at Lambda_j, since that numerator is identically divisible by X-Lambda_j. These derivative arrays are acquired by short MPE. No auxiliary equality is assigned an original decoder.

This really executes a fast diagonal for the MODIFIED object, but S_corr is not S. Restoring the required inverse gives

    V_X D=V_X H V D_new,
    D_new=V^-1 H^-1 D=diag(Gamma'(U_i)^(-1)) V D.

Its displacement retains the explicit correction

    U D_new-D_new Lambda
      =diag(Gamma'(U)^(-1)) [U,V]D
                  -diag(Gamma'(U)^(-1)) Vg eta^t.   (5)

The ordinary actions of [U,V]D are paid in soft k; its compatible short diagonal/entrywise contraction is not supplied by those actions. This is precisely the kind of middle commutator retained by the old journal gate. Dropping H^-1 or V in this equation changes the observable. No new fast true Bezout action follows from (4).

## 4. Execute the q-binomial/symmetrizer cancellation on actual symbols

The possible further cancellation is tested without guessing a q-Vandermonde identity. Write Gamma*(z)=z^R Gamma(1/z), J_R for row reversal, and T_Gamma* for its lower triangular Toeplitz multiplication matrix truncated to R rows. Direct coefficient inspection of (3) gives

    H^-1=T_Gamma*^(-1) J_R.

Set a=q^(1-ell) and c_top=c_ell. Actual q-Pochhammer reciprocity gives

    J_R C=c_top D_R C J_m D_m,
    (D_R)_(rho,rho)=a^(m rho),
    (D_m)_(s,s)=a^(m-1-s).

Therefore the EXACT result, including the reciprocal twist, is

    H^-1 C=c_top D_R T_Psi^(-1) C J_m D_m,
    Psi(z)=Gamma*(a^(-m)z)
           =prod_(rho<R)(1-q^[m(rho+ell-1)]z).      (6)

All factors and actions in (6) are acquired in soft k. For example, with Qmat=T_Psi^(-1)C, its first two actual rows are

    Qmat_(0,s)=c_s,
    Qmat_(1,s)=c_(m+s)-psi_1 c_s.

The selected c band through 2m-1 and psi_1 are actually acquired in soft k; no full coefficient array is hidden. Fast Qmat and Qmat^t actions follow from a constant-one Toeplitz inverse combined with the paid C actions, not from a descriptor alone.

The polynomial responsible for (6) is

    Psi(T^m)=prod_(rho<R)[1-(q^(rho+ell-1)T)^m].

Its common factor with P_ell(T) is EXACTLY 1-q^(ell-1)T, over every local component. Indeed at a P_ell root T=q^(-n), the factors have exponent m(rho+ell-1-n). For a nonzero integer d=rho+ell-1-n, |d|<ell+R<Ccap; k-roughness makes m-powering injective on the q component subgroup, so 1-q^(md) is a unit. The sole zero is rho=0,n=ell-1, with a simple common factor (m is an integer unit). This is a source-specific calculation; it removes one endpoint factor, not a length-R or length-ell q-product. It does not assume a primitive mth root of unity or an additive character.

## 5. A TRUE difference of two acquired coefficient transforms, with tail retained

Equation (6) nevertheless supplies a concrete two-transform representation. Let W(T) be the degree-at-most-ell truncation

    W(T)=P_ell(T)/Psi(T^m) mod T^(ell+1).

Its reshape is Qmat. Form the tail polynomial E_tail by the EXACT identity

    Psi(T^m) W(T)=P_ell(T)+T^(ell+1)E_tail(T).       (7)

The tail has degree at most ell; it is not set to zero. Both W and E_tail have acquired soft-k coefficient-matrix actions and transposes WITHOUT emitting their ell+1 coefficients. In detail the upper Toeplitz convolution tail, with entries psi_(R+rho-sigma), maps Qmat to the R-by-m reshape of E_tail. That short Toeplitz operator is actually constructed from Psi and costs soft R per action. It is upper triangular with unit diagonal psi_R. All fixed transforms are independent of the supplied action vector.

In bivariate notation this becomes

    A(X,Y)=Psi(X) W_biv(X,Y)-X^R E_biv(X,Y),
    P_ell(y_j)=Psi(y_j^m) W_biv(y_j^m,y_j)
                   -y_j^(ell+1) E_biv(y_j^m,y_j).  (8)

The weights Psi(y_j^m) and y_j^(ell+1) are ACTUALLY acquired in soft k: evaluate the acquired degree-R Psi at the supplied powers and use binary powering. They need not be units and are never inverted. This is an exact difference of two acquired structured transforms giving the TRUE native values, not a false replacement by S_corr.

What has not been acquired are the two matched diagonals on the right of (8). Their fast ordinary actions, transposes and all weights are paid, but this does not give the paired values. Replacing W(y) by the untruncated rational quotient would delete T^(ell+1)E_tail(y); y is a unit, so that deletion is unlawful. The one common factor found in Section 4 does not eliminate this actual tail. Keeping the whole tail implicit avoids a false missing-generator claim, but does not execute its paired contraction.

The transformed row pencil is short as well. With S the lower R-shift, Q0=q^m, c=q^[m(ell-1)], and U=diag(Q0^rho), the geometric ratio Psi(Q0 z)/Psi(z)=(1-c Q0^R z)/(1-cz) gives

    (I-cS) Qmat A0-(I-c Q0^R S)U Qmat B0
                      =(I-cS)T_Psi^(-1)g e_(m-1)^t,
    A0=S_col-q^ell I, B0=(q S_col-I)diag(q^s).     (9)

This follows by multiplying the existing coefficient pencil, with the actual transformed generator on the right. It has soft-k actions and input acquisition. It is not an initialized pointwise solver for (8): its q-scaled arguments and row boundaries still have to be contracted. Treating (9) as the previously solved causal-feedback inverse would reintroduce the old terminal projection gate.

## Complete cost and recovery ledger

| Actually executed object | Paid cost | Scope |
|---|---:|---|
| Exact rectangle, actual three-factor tail, C/C^t | soft k | original full horizon retained |
| Cauchy eigenbasis/core and known resonant corner | soft k | no zero cross-difference inverse |
| Gamma,V,H and their actions/inverses | soft k | all constants actually supplied |
| Rank-two modified core and its matched diagonal | soft k | S_corr, not the original Pochhammer |
| True two transforms W,E_tail and all native weights | soft k actions/preprocessing | matched diagonals NOT acquired |
| Full dense diagonal/column expansion of these transforms | soft k² upper cost | not the desired shortcut |
| Original blocked full query/derivative product | soft k^(3/2) | retained best completion |

The original blocked constructor acquires the native P_ell values or scalar norm at soft(J+sqrt(Jell)); combine the actual three-factor tail and retained unit phases, and localize any nonunit to its original row/index before the nonsplit/G_beta consumer. The derivative product in the cofactor report has the same acquired clock and its precise unique-branch validation scope. None of S_corr, a commutator entry, a formal denominator or a coefficient tail is itself decoded as an original collision.

This pass supplies actual generators for a fast modified Cauchy diagonal and an exact fast-action DIFFERENCE representation of the true query, including the symmetry twist and its tail. It establishes neither their paired-diagonal contraction nor a faster all-input norm/gradient. A successful next algorithm must evaluate (8), or its scalar/gradient norm, from those acquired transforms without the dense expansion; the present identities do not perform that operation. No generic impossibility, new backend, numerical experiment or factoring-exponent gain is claimed.

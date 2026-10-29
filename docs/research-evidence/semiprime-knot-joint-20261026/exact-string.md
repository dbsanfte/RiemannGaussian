# Exact Bethe string: finite Jacobian contraction and retained native norm

26 October 2026. Scratch only. New exact-string test, distinct from the prior free-fermion TQ packet whose Q was the acquired native root polynomial. Here Q is the LONG physical geometric clock itself. No numerical campaign or repository edits.

**Executed result.** Endpoint factors make the entire native q-string formally on-shell with a degree-O(J) acquired transfer polynomial. For the favorable coupled choice d(z)=(z-z_1)F(qz), its cleared finite Bethe Jacobian is tridiagonal and contracts EXACTLY to

    (known clock unit) * product_(i=2)^m F(z_i) * S_m(F),

where S_m(F) is genuinely acquired in soft(J+sqrt m) by a finite q-binomial summation. The almost-entire original norm remains as an explicit multiplicative factor. A “reduced norm” that retains only S_m(F) would divide out the target's zeros. No faster whole-query bound is obtained, and no physical singular Gaudin norm is identified without its additional normalization theorem.

## 1. Actual native polynomial and clock

Let F(z)=sum_(j=0)^J f_j z^j be the acquired monic polynomial on the RECENTERED reciprocal native roots, J=2L. Thus

    K(z)=c*z^-L*F(z),

with c a known unit. Put z_0=eta, z_i=z_0*q^i=eta^(2i+1), 1<=i<=m. The original odd-weight prefix is the product of F(z_i), up to the known unit c^m*eta^(-L m(m+2)). This retains the earlier actual opposite-row map to the legal negative-only original indices, including the apparent positive endpoint and odd tails. No newly extended endpoint comparison is assigned an original decoder.

Assume first J<m and 2m below both local q orders. These hold eventually at J=soft O(k), m=Theta(k^(3/2)), local q orders>16k². For short requested prefixes m<=J, the OLD evaluator already costs soft(J+sqrt(Jm))=soft J, so no new string argument is needed. Exceptional finite guard ranges retain that original evaluator. m=0 is the empty product and m=1 is one direct F evaluation.

Define the long string polynomial only symbolically:

    Q(z)=product_(i=1)^m(z-z_i).

There is no claim to acquire its m+1 coefficients in soft J.

## 2. TQ identity with acquired endpoints and polynomial regularization

Its finite ratios, interpreted after clearing, are

    Q(qz)/Q(z)=q^m*(z-z_0)/(z-z_m),
    Q(z/q)/Q(z)=q^-m*(z-z_(m+1))/(z-z_1).

Take a formal regularization parameter epsilon and choose

    a(z)=(z-z_m)F(z),
    d_epsilon(z)=epsilon*(z-z_1)F(qz).

Then EXACTLY

    T_epsilon(z)Q(z)=a(z)Q(qz)+d_epsilon(z)Q(z/q),
    T_epsilon(z)=q^m(z-z_0)F(z)
                 +epsilon*q^-m(z-z_(m+1))F(qz).      (1)

All coefficients of T_epsilon are acquired in soft J using powers and coefficient scaling. No Q coefficients or full physical clock list are required. Every internal root sees both shifted Q factors vanish, while endpoint factors remove the other two residues. This is a polynomial TQ identity, including native collisions. It is a FORMAL on-shell condition, not proof that this is a regular nonzero physical spin-chain Bethe vector.

## 3. Exact cleared finite Bethe Jacobian

Keep a,d_epsilon and the external endpoint parameters fixed. For independent root variables u_1,...,u_m define the polynomial residue equations

    B_i(u)=a(u_i)product_j(q*u_i-u_j)
           +d_epsilon(u_i)product_j(u_i/q-u_j).

They vanish at u_i=z_i. Use logarithmic tangent coordinates delta u_i=z_i*delta e_i. Because each shifted product has exactly one neighboring zero (except at the endpoint whose coefficient vanishes), the derivative is tridiagonal; this calculation does not divide by a zero Bethe equation or take a logarithm of a vanishing factor.

For i<m put

    C_i=z_(i+1)*(z_i-z_m)*Q'(z_(i+1)),

and put C_m=z_m*Q(z_(m+1)). For m=1 use that endpoint definition directly. These are ALL clock units: every factor is a unit times 1-q^r with 0<|r|<=m. Denote Omega_m=product_i C_i. Dividing row i by C_i is therefore valid as an algebraic normalization and never divides a native F value.

Write F_i=F(z_i). The resulting normalized tridiagonal matrix M_epsilon has

    diagonal: F_i+epsilon*kappa_i*F_(i+1),
    upper:   -F_i,
    lower:   -epsilon*kappa_i*F_(i+1),

with the upper/lower term omitted beyond the endpoints, and

    kappa_i=-q^(i-2m)*(1-q^(m-i+1))/(1-q^i), 1<=i<=m. (2)

For the lower entry in row i use the same i as its diagonal. The endpoint D_1 contribution before row division is epsilon*z_1*F_2*Q(z_0); the endpoint A_m contribution is z_m*F_m*Q(z_(m+1)). These give (2) at i=1,m too. For interior i the derivative before normalization is

    z_(i+1)*a(z_i)*Q'(z_(i+1))*(delta e_i-delta e_(i+1))
    +z_(i-1)*d_epsilon(z_i)*Q'(z_(i-1))
                               *(delta e_i-delta e_(i-1)).

One way to verify the ratio in (2) is the exact clock cofactor formula

    Q'(z_j)=(-1)^(j-1) z_0^(m-1)
       q^[jm-j(j+1)/2] (q;q)_(j-1)(q;q)_(m-j).

No F-related inverse enters this normalization. Omega_m is explicitly given above and is a known mathematical unit from the original guard. Numerically acquiring all its factors by a direct clock/cofactor loop would cost soft m; no soft-sqrt-m algorithm for this optional weighted clock product is claimed. Its numerical value is NOT needed for the original zero/nonunit task, since row multiplication by units preserves that predicate. Likewise the m-by-m matrix entries are an exact formula, not an acquired target-scale matrix.

## 4. Execute the determinant and its finite q-binomial reduction

For a Dirichlet tridiagonal path matrix with diagonal A_i+D_i, upper -A_i and lower -D_i, direct continuant expansion gives

    det=sum_(r=0)^m [product_(i=1)^r D_i]
                         [product_(i=r+1)^m A_i].

Substitute A_i=F_i and D_i=epsilon*kappa_i*F_(i+1). Every summand has the COMMON native factor product_(i=2)^m F_i, without division:

    det M_epsilon
      =[product_(i=2)^m F_i]
        *sum_(r=0)^m epsilon^r*w_r*F_(r+1),
    w_r=product_(i=1)^r kappa_i
       =(-1)^r q^[r(r+1)/2-2mr] [m choose r]_q.       (3)

This is a polynomial identity even where the common factor vanishes. It is not inferred by canceling zeros in a generic determinant. At epsilon=0 it becomes exactly product_(i=1)^m F_i, so the triangular regularization coefficient is the target itself.

The favorable epsilon=1 sum really DOES collapse. The finite q-binomial theorem gives

    S_m(F):=sum_(r=0)^m w_r F(z_1*q^r)
       =sum_(j=0)^J f_j*z_1^j*(q^(j+1-2m);q)_m.     (4)

Indeed the r-dependent exponent is r(r-1)/2+(j+1-2m)r, exactly the finite theorem. This executes the sum rather than leaving m+1 endpoint values unacquired. For the full polynomial regularization one similarly obtains (epsilon*q^(j+1-2m);q)_m on the right.

## 5. Pay for S_m(F), and identify the norm that remains

Let B_j=(q^(j+1-2m);q)_m. Acquire B_0 with the standard scalar q-factorial BSGS in soft sqrt m, with known unit start q^(1-2m). Then

    B_(j+1)/B_j=(1-q^(j+1-m))/(1-q^(j+1-2m)).         (5)

For 0<=j<J<m all exponents are nonzero, of absolute value<2m. All factors and denominators are certified units. Consecutive powers, batch inversions and (5) acquire B_0,...,B_J in soft J further work. Evaluate the coefficient sum in (4), with z_1=eta³, in soft J. Thus the entire auxiliary scalar S_m(F) is acquired in soft(J+sqrt m). This is a genuine initialized finite contraction, not a generic holonomicity claim.

Combining (3),(4), the exact finite cleared Jacobian is

    det [d B_i/d e_j]_(u=z)
      =Omega_m * [product_(i=2)^m F(z_i)] * S_m(F).   (6)

Only the OPTIONAL numerical Omega_m is unacquired at the desired scale; its unit status is proved and sufficient for predicates. The SUBSTANTIVE retained factor is product_(i=2)^m F(z_i), almost the whole original prefix. F(z_1) is paid in soft J; a nonunit there is a genuine original leaf and handled by the existing decoder. If it is a unit, removing it does not help with the remaining product in (6).

A proper gcd of the cheaply acquired S_m(F) itself would factor N. A saturated S_m(F)=0, however, is an ADDITIVE coefficient relation, not a beta^K=1 original leaf; it cannot be sent to the short-annihilator extractor or taken as proof of an original collision. When S_m(F) is a unit, (6) has exactly the target's remaining zero pattern. Computing its determinant from the compact TQ data still requires the explicit retained norm. Taking only the contracted scalar S_m(F) as a “fused norm” would omit the factor that carries all interior collision zeros.

For arbitrary epsilon, extracting the constant coefficient of (3) simply requests the target product directly. The long auxiliary epsilon polynomial has a large UNIVERSAL factor and a degree-at-most-J core, both described and fully charged in the extension below. Its determinant coefficients still include the same unknown native norm. No interpolation or singular limit is used to count that readout as free.

## 6. Relation to the exact/singular-string literature

Primary search found the relevant warnings and normalization framework:

* Korepin, *Calculation of norms of Bethe wave functions*, CMP86(1982),391–418, DOI https://doi.org/10.1007/BF01212176 , establishes norm determinants for specified integrable models. It does not identify every polynomial residue Jacobian with a physical norm with unit prefactor at arbitrary singular roots.
* Nepomechie–Wang, *Twisting singular solutions of Bethe's equations*, inspected arXiv:1409.7382v3,7 November2014, https://arxiv.org/pdf/1409.7382 . They use twist regularization and derive additional conditions for singular XXX/XXZ solutions to correspond to physical eigenvectors. Thus polynomial on-shell equations alone are insufficient.
* Fabricius–McCoy, *Completing Bethe's equations at roots of unity*, arXiv:cond-mat/0012501, https://arxiv.org/abs/cond-mat/0012501 , concerns exact complete strings and missing eigenvector data at root-of-unity degeneracy. Our native q has order greater than the entire short string, so it is not an m-periodic auxiliary complete string. That source cannot justify closing the native open string or deleting its endpoint/prefactor data.
* The finite q-binomial theorem used in (4) is a polynomial identity; a primary display is Warnaar, *q-Trinomial identities*, JMP40(1999),2514–2530, equation(1), https://people.smp.uq.edu.au/OleWarnaar/pubs/qTrinomials.pdf . All inverses used for its arithmetic coefficient acquisition have been checked separately above.

This report claims only the explicitly defined polynomial Jacobian and its finite normalized determinant identity. No physical spin-chain vacuum factorization, nonzero Bethe vector, Slavnov prefactor or singular Gaudin regularization is assumed without proof. In particular an actual physical fused-norm theorem would need to match (6), including every native F-dependent zero, rather than normalize them away. The prior free-fermion TQ calculation used Q=the acquired source polynomial; here Q=the long physical clock and the new coupled choice d=epsilon*(z-z_1)F(qz) was executed directly.

## 7. Focused result and next constructive possibility

Endpoint TQ closure and even the weighted string-center sum are cheap: (1) costs soft J and (4),(5) cost soft(J+sqrt m). The exact remaining scalar in their finite Jacobian is the actual native product, with a completely explicit original-leaf meaning and no arbitrary-annihilator claims. This identifies precisely what a useful singular/fused norm formula must additionally compute or preserve.

The calculation scopes the failure to dropping the retained factor in this favorable exact-string determinant; it is not a no-go theorem for all endpoint algorithms, alternate d, native arithmetic specializations or zero-only methods. A native-specific theorem making S_m(F) factor-revealing or giving an initialized way to obtain the whole determinant without its explicit interior norm could still help. Neither is inferred here. The guaranteed query remains soft(J+sqrt(Jm)); no sixth-exponent improvement is claimed.

## 8. Paid epsilon core: universal factor and division-free basis conversion

The full auxiliary polynomial S_epsilon(F) has a positive small-core refinement. Put

    B_j(epsilon)=(epsilon*q^(j+1-2m);q)_m,
    C(epsilon)=(epsilon*q^(J+1-2m);q)_(m-J).

For every 0<=j<=J<m the exponent intervals intersect exactly in C, and

    B_j=C*U_j,
    U_j=(epsilon*q^(j+1-2m);q)_(J-j)
          *(epsilon*q^(1-m);q)_j.

Therefore the polynomial identity is

    S_epsilon(F)=C(epsilon)*T_J(epsilon),
    T_J(epsilon)=sum_(j=0)^J f_j*z_1^j*U_j(epsilon).  (7)

The degree of T_J is AT MOST J. Even native unit leading f_J does not preclude cancellation among the leading coefficients of U_j. No regularity/nonzero-leading assumption is made. The explicit universal zeros are epsilon=q^m,...,q^(2m-J-1), with distinct values in the guarded short range. These zeros do not signify an original native collision. They follow from C alone.

Here the coefficient list of T_J really is acquired in soft J, without an m-term expansion or matrix. Write

    A_r=1-epsilon*q^(r-2m),
    B_r=1-epsilon*q^(r-m), 1<=r<=J,
    c_j=f_j*z_1^j.

For any 0<=lo<=hi<=J define

    P_[lo,hi]=sum_(j=lo)^hi c_j
       *product_(r=j+1)^hi A_r
       *product_(r=lo+1)^j B_r.

Then P_[0,J]=T_J. With mid=floor((lo+hi)/2), the exact divide-and-conquer rule is

    P_[lo,hi]
      =P_[lo,mid]*product_(r=mid+1)^hi A_r
       +P_[mid+1,hi]*product_(r=lo+1)^(mid+1) B_r.    (8)

Leaves are P_[j,j]=c_j. Balanced product trees acquire the two needed interval products and combine them using polynomial multiplication. At each depth the total degrees are O(J), so standard fast polynomial arithmetic gives soft J total ring work and coefficient storage. There is NO division, interpolation pivot or assumption about the leading coefficient of T_J. All q-powers in the linear factors are acquired in soft J from supplied q. Formula (8) thus supplies a paid finite q-Bernstein/Newton-like basis conversion rather than an unevaluated basis descriptor.

C remains a long polynomial of degree m-J, so its full coefficient list is not acquired in soft J. Its short Pochhammer descriptor and universal zeros are explicit; at a SINGLE supplied epsilon its value is acquired by the scalar q-factorial algorithm in soft sqrt m without divisions by its potentially zero values. At epsilon=1 all C factors are units in the short range, so C(1) is a unit; its value can be acquired in soft sqrt m. Together with (8), S_1(F)=C(1)T_J(1) has the earlier soft(J+sqrt m) scalar bound. At a universal zero of C one may evaluate the formally deflated core T_J, but this is polynomial factor removal, not numerical division by C=0.

The complete determinant remains

    det[d B_i/d e_j]=Omega_m * product_(i=2)^m F(z_i)
                                  *C(epsilon)*T_J(epsilon).

Thus the normalized small-core input is paid and may be coupled to an independently acquired moment construction. It does not remove the native norm factor. Treating roots of T_J as generalized eigenvalues of a fixed pencil would require a separately proved REGULAR pencil; no such claim is made for possibly singular/canceling native inputs. The degree-at-most-J core by itself supplies neither the full determinant scalar nor an original-leaf decoder for its additive zeros.

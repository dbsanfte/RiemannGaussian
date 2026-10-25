# Actual stripe pencil and a separate shared-resolvent candidate

24 October 2026. Scratch only. The exact native identity below contains a q-SUBSTITUTION. The later shared-resolvent calculation is a fully supplied algebraic candidate, not a proved elimination of that substitution. It corrects the earlier suggestion that every class denominator F_c(U_rho) must be output: global F(U_rho) suffices. Neither calculation acquires the paired native query faster.

## Frozen inputs and exact source locations

- /tmp/semiprime-implicit-thin-encoding-20261024/all-mask-sharing.md SHA256 `5f79d577ff7fddf72a6e3670d5bca3b7ff2ef72557f137553d388b9fea9c0f31`: lines13–21 give the cleared coefficient recurrence; lines25–33 define the stripe matrix and paid actions; lines84–93 give the EXACT pencil/boundary; lines156–164 state the actual paired native contraction and its scope.
- /tmp/semiprime-nested-alignment-20261024/nested-alignment.md SHA256 `fc96885e2ec89b08b939012777df8f542563a46bfea51667ed56a1eabd554216`: acquired levels, all canonical carries, actual boundary-unit alignment and unit-scaled elementary directions. Its long amplitudes remain unacquired.

Rename the old polynomial degree as ell to avoid collision with the composite integer N. Use b=k,T=3k, ell=bT-1=3H-1, H=k^2. Put

    P_ell(Y)=prod_(i<ell)(1-q^i Y)=sum_n c_n Y^n,
    C[rho,s]=c_(b*rho+s), U_rho=q^(b*rho),
    gamma_rho=c_(b*rho),
    g_rho=c_(b*rho+b-1)*(q^(b*rho+b-1)-q^ell).

All gamma and g arrays are acquired by the selected-coefficient/prefix primitive in soft(sqrt ell+T)=soft k; all U_rho are acquired by a power walk. P_ell differs from the original L0=3H+2 product by three explicit original factors. The nested source supplies the further canonical boundary alignments. These corrections are retained, not deleted from a long product.

## 1. Verify the actual native row identity

Let S be the b-by-b lower shift, V=diag(q^s), U=diag(U_rho), and v(Y)=(1,Y,...,Y^(b-1))^t. The actual source pencil is

    C(S-q^ell I)-U C((qS-I)V)=g e_last^t.          (1)

The interior columns are exactly
(1-q^(n+1))*c_(n+1)=(q^ell-q^n)*c_n; the last column gives the displayed g, including its sign.

Define f_rho(Y)=sum_(s<b)c_(b*rho+s)Y^s. Multiplying(1) by v(Y) and clearing Y gives the EXACT polynomial identity

    (1-q^ell Y) f_rho(Y)
       -(1-Y)U_rho f_rho(qY)
       =(1-U_rho)gamma_rho+g_rho Y^b.             (2)

For example, Sv(Y)=Y^-1(v(Y)-e0), whereas Vv(Y)=v(qY). The inverse Y in that derivation is absent from the final cleared identity; direct coefficient comparison also verifies it at Y=0. Thus it is f_rho(qY), not Y*f_rho(Y) or an algebraic resolvent, on the left.

Multiplying(2) by Y^(b*rho) and summing gives the usual homogeneous equation for P_ell: adjacent row forcing cancels by the same coefficient recurrence, and the final boundary g_(T-1) is zero. This is consistent with the actual paired native contraction, not an acquisition of its values.

A fixed native quotient does not authorize replacing q-substitution by an endomorphism. For a class modulus F_c, substitution Y->qY descends only if F_c(Y) divides F_c(qY). At the good field a nonempty unit-root set of size <=R cannot be invariant under multiplication by q, whose order exceeds16H>R. Even without a field argument, F_c(A)=0 does not imply F_c(qA)=0 for its companion A. Varying quotients can transport the substitution correctly, but no such transport endpoint is acquired by the following algebraic identity.

## 2. A separate, fully supplied resolvent candidate

Consider the proposed expression

    R(A)=sum_(rho<T) g_rho A^(b*rho)*(U_rho I-A)^-1.       (3)

It is NOT asserted that(1) or(2) yields(3) for the native kernel. Its g,U inputs are actual acquired arrays, and it is useful to state exactly what an algebraic contraction of(3) would require.

Let y_j be supplied inverse native points, possibly their actual canonical q-shifted versions; retain all original labels. Acquire their global monic polynomial

    F(Y)=prod_j(Y-y_j)=sum_(n=0)^J f_n Y^n.

It costs soft J; aliases do not invalidate the polynomial arithmetic. For any class quotient with modulus dividing F, let A be its multiplication matrix. Then F(A)=0. Only the SHARED values F(U_rho) are needed, acquired by one monic MPE in soft(J+T). There is no need to acquire every F_c(U_rho), or to write T times the number-of-classes entries.

The inverse in(3) is lawful only after actual norm/coordinate classification of these shared F(U_rho). A proper gcd returns a verified factor. On a unit branch acquire their inverses explicitly; a saturated wrong-orientation auxiliary value gives bounded failure, not an arbitrary original-leaf claim.

Here a stronger good-side check is available. For unshifted y_j=V_j^-1, equality y_j=U_rho means original index i=-b*rho. For a canonical point y_j=q^-e_j V_j^-1 with 0<=e_j<H, it means i=-b*rho-e_j, hence -4H<i<=0 because b*rho<3H. At the smaller nonsplit minus field the same congruences make the odd coprime order product>256H^2 divide

    K=A_j P+Q+ell_j-H*i.

Using A_j<2k, P<=k^3, Q<H^2/16 and |ell_j|<4.5H gives |K|<7H^2 on this range. Therefore K=0 as an integer; the prime-valuation argument forces the own tag and its STRICTLY POSITIVE original index, a contradiction. Thus all F(U_rho) are nonzero at good P. Actual classification returns a proper factor or GLOBAL units there, in soft k, even though their negative indices extend below the earlier (-H,4H) envelope. This is a fresh bound for these particular denominators, not an inherited outside-index decoder. The nested source's check on maximum canonical shifts ensures e_j<H.

## 3. Execute the global-denominator identity

On that certified unit branch define acquired shared weights

    w_rho=g_rho/F(U_rho), W(Z)=sum_(rho<T)w_rho Z^rho.

Because F(A)=0, polynomial division of F(U)-F(A) gives the exact inverse

    (U I-A)^-1 = 1/F(U) *
       sum_(n=1)^J f_n sum_(j=0)^(n-1) U^(n-1-j) A^j.

Consequently(3) is exactly

    R(A)=sum_(j=0)^(J-1) A^j
           sum_(n=j+1)^J f_n
             W(q^(b*(n-1-j))*A^b).               (4)

All coefficients, exponents and W data on the right are genuinely supplied in soft k. The identity holds over the actual composite algebra and over nonreduced class quotients; no target separation is required for it. Only certified F(U) values are inverted.

ONE entire batch W(y_j^b) costs soft(J+T): acquire the J powers and evaluate the supplied degree-(T-1) W by monic MPE. More generally any one FIXED q-shift of those arguments has the same paid cost. Formula(4), however, requests the correlated sum of differently shifted W values multiplied by powers of the SAME native A. Its acquisition is not a bounded number of those ordinary actions. No output-count lower bound is inferred; an implicit contraction could still avoid writing all shifted values.

## Exact conclusion

The global-denominator observation prevents a false explicit-array obstruction: the proposed resolvent has actual shared denominators and short initialized coefficients. Its remaining paired q-shift sum is stated exactly. More fundamentally, the ACTUAL stripe equation(2) retains q-substitution; it has not been converted to(3). Dropping that distinction would assert a false native elimination.

Neither the proposed resolvent nor its identity(4) is claimed as a faster native remainder, scalar product or weak selector. The old complete soft sqrt(JL) query and its verified consumers remain the available completion. No generic recurrence lower bound, free corrected kernel, missing coefficient window or hidden local factor is assumed. Only this new scratch file was written; no frozen/shared source or numerical experiment was used.

# An executed rank-one Casoratian selector and its finite boundary system

24 October 2026. Scratch only. This constructs an exact sufficient coarse-label gradient and executes its two-state endpoint transport. Its coefficients and all short rank-one perturbations are paid. The initial long product/gradient is not acquired; the old whole-query continuation remains soft k^(3/2). No fast determinant oracle is inferred.

## Supplied finite identities

Authoritative sources are /tmp/semiprime-quadratic-class-query-20261024/literature.md SHA256 `5aa07471d0d2c514b62eff39c1b5f77eb247632cc15c0907eef82dff32f6bea4`, independent review `4defa1e82a139a7cfa5f68ad79c94d45d63077c3490ce6e4d7d0d0aef62787d3`, and class-transport.md SHA256 `f813dc08c143a108758bd4a286bc601ded2a854b3a5c5bdb4693fc2695fca360` in the same packet.

Use the actual inverse points z_h=Vhat_h^-1=C D^h E^(h^2), with all original q carries and labels retained, L<4H, E^(r^2)=q^a, and the independent barpi^(-2m) factor in D. P_L(z)=prod_(i<L)(1-q^i z). Thus P_L(z_h)=0 is an original bounded native collision after undoing its stored shift. A unit scalar prefactor restores products of Vhat_h-q^i if required.

Within a class retain n<=r distinct points after the actual factor-or-separation step, as permitted by the finite normalizer report. On its short-head unit branch the known invertible short matrix R and unknown long Casoratian M satisfy

    M=diag(a_0,...,a_(n-1)) R, a_i=P_L(z_i),
    U=det R is an acquired global unit.

All R actions/transposes and U are paid soft n. The first r heads cannot contain the good hit, whose shifted index is >r. A wrong label can decline at an unconsumed saturated auxiliary head. Do not replace M by R.

## 1. Actually acquire a sufficient rank-one perturbation

Acquire u=1 and v^T=1^T R by the short transpose action. Then

    D_c(epsilon)=det(M+epsilon*u*v^T)
       = U [Z_c+epsilon*S_c],                    (1)
    Z_c=prod_i a_i,
    S_c=sum_i prod_(j!=i) a_j.

This holds as a polynomial identity over the actual composite algebra, with no a_i inversion. Indeed factor the RIGHT R:

    M+epsilon*1*(1^T R)=(diag(a)+epsilon*1*1^T)R.

The coefficient of epsilon in the remaining determinant is the sum of its diagonal cofactors, and rank-one multilinearity kills every higher coefficient. Thus the long determinant is only affine in epsilon, but its TWO coefficients are not acquired by the short circuit.

For the full block family, use one global rank-one perturbation with u concatenated ones and v^T formed by concatenating 1^T R_c. Its epsilon coefficient is

    (prod_c U_c) * A,
    A=sum_c S_c prod_(d!=c) Z_d.

Weight the corresponding segment of v by the known coarse class label c to get coefficient (prod_c U_c)*B, with

    B=sum_c c*S_c prod_(d!=c) Z_d.                 (2)

At the unique smaller-nonsplit hit exactly one a_i is zero and every other a_j is nonzero. Consequently A is nonzero at that field and B/A equals the coarse tag of the hit. Deleting nonhit duplicates changes this by the common nonzero local factor already proved in the source. The consumer is the independently proved partial-tag validation/completion, not an assumption that a matrix kernel is supplied.

All perturbing vectors, unit prefactors and labels in (1)--(2) cost soft k across classes. The long diagonal a is not supplied, so evaluating either coefficient remains a substantive task. The rank-one identity alone is not an algorithm for them.

## 2. Execute a finite endpoint transport for both coefficients

For this calculation retain the literal full-r class, including nonhit aliases, so that the exact quadratic order remains available. It needs no separation. Extend its acquired formula z_h=C D^h E^(h^2) to integer h, and set a_h=P_L(z_h). Define windows

    Z_t=prod_(h=t)^(t+r-1) a_h,
    S_t=sum_(h=t)^(t+r-1) prod_(j=t,j!=h)^(t+r-1) a_j.

The exact cross-multiplied identities are

    a_t Z_(t+1)=a_(t+r) Z_t,
    a_t S_(t+1)+Z_(t+1)=a_(t+r) S_t+Z_t.          (3)

To verify them without divisions, put b_h=a_h+epsilon. The first identity with b_h holds identically for products of the two windows; its epsilon coefficient is the second line. This gives the ACTUAL initialized transfer once its state (Z_t,S_t) is supplied.

If the two endpoint values are units, acquire c_t=a_(t+r)/a_t and the numerical triangular matrix

    [ Z_(t+1) ]   [ c_t          0 ] [ Z_t ]
    [ S_(t+1) ] = [ (1-c_t)/a_t c_t ] [ S_t ].    (4)

No covered Z is inverted. At t=0 the two endpoints across M=J/r classes cost soft(sqrt(M L)+M) to evaluate, by the explicit baby-product/monic-MPE algorithm in class-transport.md. All matrix coefficients are then acquired, or a proper factor/nonunit auxiliary branch is explicitly identified. This is below the old full query for growing r. A saturated artificial endpoint is not silently treated as an original bounded leaf.

At an interior hit, Z_t=0 but S_t is nonzero. Equation (4) reduces to S_(t+1)=c_t S_t: it transports the unknown nonzero gradient by a KNOWN unit. Subtracting c_t times one window from the other removes its useful interior signal as well as its amplitude. This tests the rank-one derivative, not just the old scalar product.

## 3. Boundary closure and actual continuation

The known finite parameter orbit after t shifts is

    C_t=C D^t E^(t^2), D_t=D E^(2t).

At t=r^2 it gives C_t=C D^(r^2)q^(a r^2), D_t=D q^(2a), with the actual mixed factor barpi^(-2m r^2) still in D^(r^2). It is not a supplied periodic boundary. At C=0 the state is (Z,S)=(1,r), but multiplicative shifts keep zero at zero and do not initialize the native unit orbit. No zero-to-unit analytic continuation is used.

Thus the tested boundary system has paid transfer coefficients, but no supplied initial long state or verified terminal periodic condition. The formal affine determinant (1) does not fix those coefficients by its epsilon degree. Both the known short R and the paid endpoint transfer are consistent with the actual unknown interior common factor in (3).

A complete fallback remains available: compute the global native class-gradient reset from the supplied roots and directions with the standard baby/giant polynomial-matrix algorithm, cost soft sqrt(JL)=soft k^(3/2). On the correct unique orientation it yields a valid coarse ratio; on other labels use bounded validation and the original verified fallback. This completion is zero safe and retains original norm-leaf consumers and stored index corrections. Alternatively, evaluating all long a_i first has the same soft sqrt(JL) batch cost and then (1)--(2) are trivial. Neither route improves the query clock.

The concrete new attempted contraction is (1)--(4): an acquired short rank-one direction reduces the required determinant output to two coefficients; an explicit finite two-state recurrence transports them with acquired endpoint coefficients. Its uninitialized interior state is precisely exhibited. No generic lower bound, free long matrix action, deleted theta tail, or all-input exponent gain is claimed. No frozen/shared source or numerical experiment was used.

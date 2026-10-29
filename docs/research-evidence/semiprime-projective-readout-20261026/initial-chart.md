# Paid initial projective chart from the first 5J clock steps

26 October 2026. Root construction, independently checked here. Paper only; no tests, repository edits or changes to frozen reports.

**Positive correction to the earlier chart discussion:** the undefined initial ratio U_0/V_0 is not a fundamental acquisition obstacle. The first proof acquires adjacent globally unit V states; the stronger upgrade at the end acquires two adjacent ratios with a certified GLOBAL UNIT increment in one of three fixed charts. Continuing work is soft J; a legal factor-return branch costs at most soft K with the once-only extractor. Future projective pivots and fast long advancement remain open.

## Actual input and acquired prefix

Use either uniform two-monic family, J<=K, H=K², h=2H+1, K>16, P,Q>16H and N>256H². The algebra has one nonsplit prime R. Acquire the polynomials

    f(X)=product_j(1-y_j X),
    v(X)=sum_j product_(l!=j)(1-y_l X),
    u(X)=sum_j w_j product_(l!=j)(1-y_l X).

All cost soft J by product trees. Put rho=q^-1, X_i=rho^i and L=5J. Since L<=5K<h and L<16H, these are original clock indices and their distinctness follows from the actual coupled short-order screen. Monic multipoint evaluation acquires ALL f(X_i),v(X_i),u(X_i), 0<=i<L, in soft J. No point-difference inverse or collision value is inverted.

First classify the f values. A proper norm gcd factors. At a saturated norm, scan the J original row leaves at that supplied index. Norm multiplicativity ensures some leaf norm is nonunit; a proper leaf norm gcd factors. If a leaf norm is saturated, the leaf is zero in the nonsplit field. If its coordinate vector is not globally zero, a coordinate/common-coordinate gcd gives a proper factor. Otherwise it is a genuine whole-algebra equality y_j=q^i globally.

For that global equality define the source integer

    E=ell_j+a_j+b_j*N-H*i.

The monic families have a_j,b_j>=1 and |ell_j|<=H/2. Since i<5J<=5K,

    E>N-5K³-H/2>0.

Its bit length is O(log N). Taking norms gives beta^(2E)=1 globally; this nonzero short label is licensed for the inherited extractor T_ext=soft N^(31/192). Odd beta orders also imply beta^E=1 if that label convention is preferred. Thus every prefix f-nonunit has a verified proper-factor or licensed saturated-leaf route, including the wrong-family attempt. The source need not be the good family for this small-index label proof.

If no factor is returned, every f_i is a global algebra unit. Now advance the raw state for L steps:

    (P_0,V_0,U_0)=(1,0,0),
    P_(i+1)=f_i P_i,
    V_(i+1)=f_i V_i+v_i P_i,
    U_(i+1)=f_i U_i+u_i P_i.

This costs O(J). All P_i are units. Actual inversion of every P_i is unnecessary for the state computation, but is valid if normalized values are wanted.

## Counting proof of adjacent nonzero V states

Work at the nonsplit field and set z_i=V_i/P_i. Then

    z_0=0, z_(i+1)=z_i+b_i,
    b_i=v(X_i)/f(X_i).

Assume for contradiction that none of the L edges between states 0,...,L has two nonzero endpoints.

A zero-zero edge satisfies b_i=0, so v(X_i)=0. The polynomial v has degree at most J-1 and constant coefficient J, which is nonzero because J<=K<R. Hence there are at most J-1 such edges.

Every nonzero INTERNAL state z_i, 1<=i<L, is isolated. Its two neighbors are zero, so b_(i-1)+b_i=0. Consequently X_(i-1) is a root of

    B(X)=v(X)f(rho X)+v(rho X)f(X).

This polynomial has degree at most 2J-1 and constant coefficient 2J, nonzero since R>16K². The evaluation points are distinct, so at most 2J-1 internal states are nonzero. Each such isolated state accounts for exactly two edges. The last state, if nonzero, accounts for one extra edge; the initial state is zero.

All edges are covered by these categories. Therefore

    L <= (J-1)+2(2J-1)+1 = 5J-2,

contradicting L=5J. Thus some adjacent V_s,V_(s+1) are nonzero at the nonsplit field.

## Global certification and exact cost

Classify all acquired V_i by norm/coordinate gcds. If V_i is nonzero at R, its norm is nonzero there, so its norm gcd is proper or 1. If V_i is zero at R but not globally zero, both coordinates are divisible by R and at least one is not divisible by the other prime, giving a proper coordinate gcd. Consequently, on a no-factor continuation, each V_i is either a global algebra unit or the globally zero vector. The counting proof therefore guarantees an ADJACENT pair of globally certified units, found by scanning the classification results.

The raw states give the actual ratios r_s=U_s/V_s and r_(s+1)=U_(s+1)/V_(s+1), and also P_s/V_s if the two-variable Riccati chart is retained. Unit inversion is certified by norms. Total continuing work is soft J in the fixed-rank algebra. A terminating original-leaf branch costs soft(J+T_ext)=soft K, with T_ext paid once. No additive V-zero is sent to the annihilator routine.

## Scope relative to projective-closure.md

The earlier observation V_0=0 remains true, but it does NOT justify calling initial-chart acquisition a fundamental obstacle: the short prefix above resolves it. This corrects that acquisition assessment without changing the older frozen formulas.

The stronger construction below additionally certifies a unit initial increment in a selected fixed chart. Future chart denominators and nonlinear stepping pivots may still vanish; an acquired nonlinear recurrence does not automatically admit fast long advancement. Those issues and the existing soft(J+sqrt(Jh)) execution cost remain separate. The positive result is paid projective initialization, not a faster whole-query evaluator.

## Stronger upgrade: a certified nonzero initial increment in one of three charts

The parent supplied the following strengthening; independently checked here. It applies to the actual COMPLETE unit-tag monic lists and n>2 from the current handoff. It strengthens the preceding adjacent-state construction by certifying the INITIAL increment as well. Future pivots and fast advancement remain unproved.

### A nonzero polynomial controlling changes of direction

For the good family define

    E(X)=v(X)u(rho X)-u(X)v(rho X).

Its degree is at most 2J-2. It is NONZERO at the good field. Indeed if it were zero, the rational function u/v would be rho-invariant. Since v(0)=J!=0, put c=u(0)/J and consider g=u-cv. If g is nonzero, its lowest nonzero degree m satisfies 1<=m<=J-1<ord_R(q). The invariance identity at degree m then forces rho^m=1, a contradiction. Hence u/v is constant c.

For the full unit-tag lists, reduction modulo n has equal-size unit fibers, so c=(sum_j w_j)/J=n/2. At the unique hit, however, v(X_I)!=0 and u(X_I)/v(X_I)=w_*=R mod n. These cannot agree: for odd n the equality 2w_*=n is impossible even modulo R since 2n<R; for even n>2, n/2 is not a unit modulo n. Thus E cannot vanish identically. This uses the actual full unit-tag lists and promised unique hit; it is not asserted for arbitrary pruned or reweighted families.

### Vector counting in the acquired short prefix

On the no-factor/unit-f branch retain the previously acquired raw states and put

    z_i=(V_i/P_i,U_i/P_i),
    b_i=(v(X_i)/f(X_i),u(X_i)/f(X_i)),
    z_(i+1)=z_i+b_i, z_0=(0,0).

Suppose det(z_i,z_(i+1))=0 on every edge of 0,...,L. For any NONZERO internal vector z_t, its neighbors are parallel to it (the zero vector is allowed). Hence b_(t-1) and b_t are collinear, so E(X_(t-1))=0. Distinctness of the clock points bounds the number of nonzero internal vectors by 2J-2.

A zero-zero edge has b_i=(0,0), in particular v(X_i)=0, so there are at most J-1 such edges. Every other edge touches a nonzero internal vector or the final endpoint. Counting at most two edges per such internal vector and at most one for the last endpoint gives

    L<=2(2J-2)+1+(J-1)=5J-4,

again contradicting L=5J. This counting does not assume nonzero vectors are isolated; any duplicated edge count only strengthens its upper bound.

Therefore at least one ACTUAL raw determinant

    D_i=U_(i+1)*V_i-U_i*V_(i+1)

is nonzero at the good field, since its normalized version is det(z_i,z_(i+1)) times the known unit P_i*P_(i+1). Scan all D_i by norm/coordinate classification as before. On a no-factor continuation a good nonzero determinant has certified globally unit norm, and so gives a globally unit D_i. This selection costs O(J).

### Three fixed charts and the actual initial ratios

For c in {0,1,2} put L_t(c)=V_t+cU_t. At either endpoint i,i+1, a nonzero good-field vector excludes at most one value of c. Thus at most two of the three choices make either endpoint zero. Test the actual forms by norms/coordinates. A proper gcd factors. For a choice nonzero at both good-field endpoints, failure of a norm-unit test can only give a proper factor; hence on no-factor continuation some choice has BOTH forms globally certified units.

Set

    r_c(t)=U_t/(V_t+cU_t).

The acquired adjacent initial ratios obey

    r_c(i+1)-r_c(i)=D_i/[L_i(c)*L_(i+1)(c)],

which is a certified GLOBAL UNIT. Both actual ratios and P_i/L_i(c) are acquired in O(1) extra unit inversions. The homogeneous recurrence uses exactly the same acquired f,u, with v replaced by v+c*u. No new long state or coefficient list is hidden in this chart choice.

At the good unique hit and thereafter the chart is ALSO valid locally: V+cU=V*(1+c*w_*), and 1<=1+c*w_*<=2n-1<R. Thus the eventual ratio is w_*/(1+c*w_*). Its conversion back is w_*=r_c/(1-c*r_c), whose denominator is nonzero at the good field and can be norm-classified, or one can undo the homogeneous linear chart before the old validator. A modified integer-label scan likewise keeps actual factor provenance. No numerical nonunit is inverted without certification.

The complete stronger initialization costs soft J continuing work, or soft(J+T_ext)=soft K on a legal factor-return branch. It supplies two adjacent ratios AND a nonzero unit increment on one unrecognized good family. Initial-chart acquisition is therefore resolved at the desired budget. It supplies neither all future chart/pivot certificates nor a faster algorithm for advancing the nonlinear law through the long clock; those remain separate acquisition tasks.

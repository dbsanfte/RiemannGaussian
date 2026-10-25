# Geometric tensor norm: acquired Cauchy transport and its multiplication carry

2026-10-24. Scratch only; no source/repository edits, numerical examples or Lean work. This is a concrete geometric evaluation/transport attempt, separate from fraction-free Sylvester elimination. The first Cauchy elimination and first inverse transport are actually initialized with collision-safe guards. The completed scalar norm still costs soft s(J+t) in this implementation; the existing soft(J+sqrt(Jst)) blocking is better. No soft(J+s+t) tensor norm or new factoring exponent is obtained.

## Prior guards and actual inputs

Read the final endpoint reports/reviews under /tmp/semiprime-recurrence-endpoint-20261024, especially literature-endpoint.md (SHA256 762a054cb539cc633f3d8295184a3feb9a8339348bd115396f2e4d340cbad85b) and christoffel-terminal.md (c523fc8a1a7a23d667f32714e1671c6eb782b52d423984681402eb8deea01008). They already distinguish a paid sparse tensor input from its unpaid scalar norm, and compact actions/generators from determinant acquisition. The earlier scalar-Schur/Christoffel far-boundary and q-scaling-chart failures are not counted as new obstacles here.

Let R=Z/N, F(X)=sum_(k=0)^J f_k X^k the acquired original scalar native target polynomial, q a certified unit, and s,t>=2 with L0=st<=2m^2+2 in the native horizon. All 1-q^k for 1<=k<=st+1 are certified units; the original order margin supplies this. Put Q=q^s,

    A_s(X)=product_(a=0)^(s-1)(X-q^a),
    P(Y)=B_t(Y)=product_(b=0)^(t-1)(Y-Q^b),
    K=R[Y]/P(Y),  y_b=Q^b.

The input polynomials, short scalar power lists and sparse coefficients F(XY) are acquired in soft(J+s+t), as in the endpoint report. This report does not construct a dense rank-st tensor table. A final seed tail outside st is handled separately at soft(J+s).

All y_b differences are units. Thus evaluation ev:K->R^t is a genuine acquired CRT isomorphism, implemented by monic MPE and unit-safe interpolation. Its dimension is t, so a call costs soft t, not O(1). No hidden-field roots or characteristic oracle are supplied.

## 1. An actual geometric Cauchy connection in soft t

On degree-<t representatives define the R-linear scaling operator

    S_q(g)=g(qY) mod P.

This is invertible as a LINEAR map: in coefficient coordinates it is diag(1,q,...,q^(t-1)). It need not preserve multiplication in K.

In value coordinates its matrix is

    (S_q)_(b,c)=P(q y_b)/((q y_b-y_c)P'(y_c)).       (1)

This follows by evaluating the Lagrange basis at q y_b. Every scalar denominator is a certified unit. Indeed 1+s(b-c) cannot be zero for s>=2, and its absolute value is <=st+1; hence each q y_b-y_c is a known unit. Likewise all P'(y_c) are products of certified short differences. The two shifted geometric grids are DISJOINT locally.

Acquire P(q y_b) and P'(y_c) by two ordinary MPEs, and batch-invert the derivative values. All t coordinates and inverses cost soft t. The matrix is represented by these diagonal factors and the Cauchy kernel C_(b,c)=1/(x_b-y_c), x_b=q y_b; no t-by-t table is materialized. Its actions are also initialized: interpolate, scale coefficients, evaluate, at soft t.

For the requested FIRST elimination update, C_00=1/(q-1) is a certified-unit pivot. For b,c>0 its exact Schur complement is

    C'_(b,c)=C_(b,c)-C_(b,0)C_00^-1 C_(0,c)
      = [(x_b-x_0)/(x_b-y_0)]
        *[(y_0-y_c)/(x_0-y_c)] /(x_b-y_c).          (2)

All four new differences are short q-differences and units. Thus this Cauchy elimination really closes after one step by updating two actual length-t diagonal vectors, in O(t) work, without a singular target pivot. The same geometric Cauchy class persists. In coefficient coordinates det(S_q)=q^(t(t-1)/2), so its scalar determinant is known/acquired by binary powering as well.

This is a positive initialized change-of-grid operation. It is NOT the determinant of multiplication by F in the tensor quotient.

## 2. The exact multiplication carry is not a one-boundary correction

Set

    d_q(Y)=P(qY) mod P.

It is acquired from explicit P by scaling/reduction in soft t. It is a UNIT in K, because d_q(y_b)=P(q y_b) is a product of the certified cross-grid units above. Its inverse, if needed, is acquired by CRT evaluation, batch inversion and interpolation in soft t.

For degree-<t representatives f,g, acquire the actual Euclidean quotient h and remainder r from

    f g=r+P h.

Then the exact identity is

    S_q(r)=S_q(f) S_q(g)-d_q S_q(h) mod P.          (3)

The quotient h is part of the computation, not determined by r alone. Discarding it would turn a linear interpolation/scaling operator into an unlicensed algebra endomorphism. Crucially, multiplication by d_q is invertible: the lost quotient is NOT supported at one scalar boundary coordinate. S_q is invertible linearly too, so no h-information disappears in the correction d_q S_q(h).

The defect has genuinely large ambient module rank in this tested representation. For products of degree-<t polynomials, h has degree <=t-2. Holding the known unit f=Y^(t-1) fixed, the map from the coefficients of g in span(Y,...,Y^(t-1)) to this quotient is triangular with diagonal 1 by monic division; it ranges over every polynomial of degree <=t-2. Thus the multiplication defect contains a free rank-(t-1) image submodule. This is a formal operator fact, not an actual-native counterfamily or a lower bound for another tensor-norm algorithm. It proves that treating this particular connection as a homomorphism with a single seam is false.

At the actual multiplication operator M_Y on K there is a useful SMALL first commutator:

    S_q M_Y-q M_Y S_q=-d_q e_top^T,               (4)

where e_top selects the coefficient of Y^(t-1). Equation (4) follows because reducing Yg removes exactly e_top(g)P. Hence for the ACTUAL degree-J polynomial,

    S_q F(M_Y)-F(qM_Y)S_q
      =-sum_(k=1)^J f_k sum_(r=0)^(k-1)
           (qM_Y)^r d_q e_top^T M_Y^(k-1-r).       (5)

The rank is at most J, with column space generated by d_q,Yd_q,...,Y^(J-1)d_q. The formula is division free and its actions cost soft(J+t) using polynomial arithmetic. Explicit generator vectors contain O(Jt) entries; at J~t the correction has no proved constant-rank closure. Neither the upper rank bound nor the ambient defect statement proves that every native instance has maximal rank. A faster scalar contraction accepting the compact action is still possible, but it has not been constructed here.

## 3. FIRST actual inverse/pivot transport, with all guards paid

The following is a legitimate first step for an engine attempting to reuse one slice inverse across q-shifted slices.

Acquire F(y_b) for all b by monic MPE, at soft(J+t). Multiply and gcd their product with N. If nonunit, inspect the acquired values and localize the original target rows at that seed. A proper gcd factors. A saturated original scalar leaf uses the retained original-beta bounded decoder; seed indices a+sb stay inside the original horizon. These are ACTUAL query leaves, so no extra decoder is assumed.

On the unit branch, batch-invert every F(y_b) and interpolate the degree-<t inverse v=F^-1 in K. Acquire the exact Bezout quotient h from

    F(Y)v(Y)+P(Y)h(Y)=1,  deg h<=J-1.

All objects have O(J+t) coefficients and are acquired in soft(J+t). Scaling and reducing gives

    F(qY)S_q(v)=1-d_q*(h(qY) mod P)=G_q mod P.           (6)

Here h(qY) means scaling the ACTUAL acquired Bezout polynomial BEFORE reducing modulo P. Since deg h can be J-1>=t, it must not be replaced by S_q(h mod P); that would discard another quotient carry. Raw scaling/reduction still costs soft(J+t). Thus if G_q is a certified unit, an actual next inverse is

    F(qY)^-1=S_q(v)G_q^-1.

Acquire G_q by explicit polynomial operations and guard its unit status through its t CRT values, including any inverse/interpolation; this costs soft(J+t), not constant scalar time.

A nonunit G_q must NOT be declared an original F-hit automatically. Equation (6) shows that a zero can also come from S_q(v), since S_q is not multiplicative. A proper scalar gcd still legitimately factors N, but a globally nonunit G_q may be an auxiliary pivot failure. On that branch recompute/guard F(q y_b) directly; it gives the actual slice classification and, on its unit branch, a fresh legal inverse by the same CRT constructor. No division by an unverified pivot or spurious support inference is used.

The first slice and the first attempted update are therefore initialized, including every collision and pivot branch. Their cost is soft(J+t). Repeating this at s actual slice parameters costs soft s(J+t), not soft(J+s+t). The recurrence for the connection matrix alone does not acquire those varying multipliers or their determinants.

## 4. A genuine one-boundary transport exists at Q=q^s, but has no cheap initial norm

For contrast, S_Q(g)=g(QY) has shared interpolation nodes: P(Q y_b)=0 for b<t-1 and is a unit at b=t-1. Its product carry is therefore supported in ONE value coordinate. This is a real distinction between the within-grid Q shift and the needed transverse q shift.

For a fixed slice parameter a, put

    N_a(r)=product_(b=0)^(t-1) F(q^a Q^(r+b)).

The exact division-free boundary update is

    N_a(r+1) F(q^a Q^r)=N_a(r) F(q^a Q^(r+t)).     (7)

For the FIRST update r=0, both boundary lists over a=0,...,s-1 can be acquired together in soft(J+s), because each is F on a short contiguous geometric list. If a boundary product is a unit, ordinary division is legal; nonunit ACTUAL boundaries can be localized and decoded through the original scalar native channel. Here t>=2 and st<=2m^2+2 imply every first-update index is <st+s<=3m^2+3<4m^2, within the retained bounded native decoder. Equation (7) is algebraically valid for arbitrary r, but no original native recovery is claimed for shifts outside its bounded decoder horizon.

But N_a(0) is precisely the unacquired slice norm, and product_a N_a(0) is the tensor target. Equation (7) does not initialize it. The known empty-product state at length zero is a different length variable, whose extension inserts the whole set of actual F-values and restores the original degree-times-horizon interaction. This records an executed transport and its missing initial datum, not a proposed endpoint oracle.

## 5. Completed scalar norm from the short inputs, with its real ledger

A completely initialized inversion-free fallback within K is

    G_0(Y)=1,
    G_(a+1)(Y)=G_a(Y)F(q^aY) mod P,  0<=a<s.

Acquire each scaled F, reduce it monically, and multiply/reduce the actual degree-<t state. Each stage costs soft(J+t); store O(J+t) coefficients. Finally evaluate G_s at all y_b by monic MPE and multiply. Exactly

    product_b G_s(y_b)=product_(a<s,b<t)F(q^(a+sb))=E_(st).

No target or intermediate state is inverted, so this completion remains valid at every hit, including global saturation. Its full cost is soft s(J+t), equal to soft m^2 at J,s,t~m. Its determinant inputs and every state update are acquired; no rank-t quotient operation is priced as O(1).

The already initialized global scalar blocking is BETTER: choose a seed block length B, acquire product_(r<B)F(q^rX) of degree JB, evaluate it at st/B actual giant starts, pay the tail, and optimize to

    soft(J+sqrt(Jst))=soft m^1.5.

It supplies native row/interval restrictions and the original-beta saturated decoder at that same clock. Nothing in the geometric connection changes this available whole-query bound.

| Operation | Actual paid data/work |
|---|---|
| A_s,B_t,F and tensor sparse input | soft(J+s+t) |
| q-shift Cauchy connection/action | soft t; compact length-t diagonals |
| First Cauchy Schur update | O(t), certified-unit pivots |
| d_q and its CRT inverse | soft t; degree-<t polynomials |
| Rank-J commutator action | soft(J+t); explicit vectors O(Jt) |
| First actual slice inverse/guard | soft(J+t), all t values paid |
| First inverse transport/correction | soft(J+t), auxiliary failures guarded |
| K-valued sequential product norm | soft s(J+t), inversion free |
| Better inherited whole-query fallback | soft(J+sqrt(Jst)) |

## Scope

The positive structural result is an acquired geometric Cauchy connection with a lawful first Schur update and exact compact commutator. The tested compression fails because transverse q transport does not preserve multiplication: its carry is multiplied by a UNIT, and degree-J weights create a rank-J correction whose compact action has not been converted into a determinant algorithm. The within-grid rank-one boundary transport retains the unacquired initial norm.

This is a precise closure/initialization failure of this implementation, not a claim that small geometric generators cannot be eliminated by another method. No all-input support selector, free coefficient list, singular-target inverse or new factoring exponent is asserted. A successful continuation must acquire the scalar norm or a restriction-stable witness from these short inputs with the complete compact-generator and nonunit ledger paid.

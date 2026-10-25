
## Unit-normalized collision ratios and initialized weak readouts, 2026-10-24

This pass tests whether acquiring only a collision label can be easier than
acquiring the exact product or its gradients. There is a precise finite
readout, and the proposed normalizing filter is genuinely acquired and
invertible on every continuing good label. The finite truncation correction
still contributes to that readout. No faster whole-family query is proved:
the completed execution remains soft O(k^(3/2)), with J=O(k), L=O(k²).
The all-semiprime sixth-rate and full executable Lean bit proof remain open.
Sources, independent reviews, and the append validator are in
`/tmp/semiprime-quotient-gradient-20261024/`.

### A weaker, fully initialized output target

Use the acquired separated native minus roots V_j and their stored original
tags j. Acquire the polynomial w of degree <J with w(V_j)=j using the actual
unit values F'(V_j), where F(X)=prod_j(X-V_j). Its weighted product-tree
construction costs soft J. On the smaller-nonsplit good orientation exactly
one grid value F(q^I) vanishes. That promise is not recognized publicly and
is not extended to wrong orientations or the full both-colour family.

The required output can be ANY A,B with A nonzero at that good field and
B/A equal to the original tag. Exact adjugate entries are unnecessary. In
particular, the following unweighted recurrence is sufficient:

    (Z_0,A_0,B_0)=(1,1,1), x_n=q^n,
    Z_(n+1)=F(x_n) Z_n,
    A_(n+1)=F(x_n) A_n-Z_n,
    B_(n+1)=F(x_n) B_n-w(x_n) Z_n.                 (QG1)

Indeed, before the unique hit Z_I is nonzero at the good field. The hit sets
(A_(I+1),B_(I+1))=-Z_I(1,j*) and Z_(I+1)=0. Every subsequent nonhit step
multiplies A and B by the same nonzero value. Thus A_L is nonzero and
B_L/A_L=j*. No evolving F value is inverted, and all starts are supplied.
Equivalently, with U_w,n=sum_(i<n)w(q^i)prod_(r<n,r!=i)F(q^r), the states
are (P_n,P_n-U_1,n,P_n-U_w,n). This is an output recombination of the old
unweighted square-zero product, not a new complexity result or the weighted
Bezout identity below. Its degree-J polynomial transition and actual baby
blocks, all giant evaluations and clipped tail still cost soft sqrt(JL).
The existing bounded norm/coordinate-gcd, integer-tag, and ONE original-row
consumer costs soft k after acquisition. Wrong labels may decline.

The concrete target for an innovation is a zero-safe evaluator of (QG1)'s
projective output in soft(J+sqrt L), or another output satisfying the same
tag contract. This is a weaker target than the exact-gradient contract in
the preceding section. Its unique-hit orientation still retains the stated
QRH condition. The preceding stronger uniform product contract continues
to cover the original full family without that orientation condition.

### A finite regularized Bezout solve represents the same local tag

Let G(X)=prod_(i<L)(X-q^i), h=G mod F, and K=Bez(F,h). These objects define
the certificate; h and K are NOT supplied free. At the good collision,
adj(K)=c v v^t, c!=0, v=(1,V_*,...,V_*^(J-1))^t. Consequently the finite
rank-one updates

    A_det=det(K+e0 e0^t)=det K+adj(K)_(0,0),
    B_det=det(K+e0 w_coeff^t)=det K+w_coeff^t adj(K)e0

satisfy B_det/A_det=j*. For M=K+e0 e0^t, Mv=e0, so a unit-regularized
solve M z=e0 would return w_coeff^t z=j* at that field. Its actual
determinant norm is a unit or a proper factor on a good label; this does
not certify each pivot of an arbitrary elimination algorithm.

There is also a fully supplied weighted execution. Set
lambda_i=1/G'(q^i), lambda_0=(q;q)_(L-1)^-1, and
rho(x)=q(1-q^(1-L)x)/(1-qx). From the same residue identity as the prior
cofactor pass, with d=(-1)^[J(J-1)/2+JL],

    (Z,A,B)_0=(lambda_0,1,1),
    (Z,A,B)_next=(rho F Z, F A-Z, F B-w Z),
    (A_det,B_det)=d(A_L,B_L).                       (QG2)

The last lambda_L is zero. Actual unit prefix products acquire lambda_0
and the clearing denominator in soft sqrt L. The cleared transition has
degree J+1, and the complete cost is still soft(J+sqrt(JL)). Equation
(QG1) removes these extra weights when only the local tag is requested.

The short structured-solve description is exact but not yet acquired.
For the nilpotent shift S, cyclic shift C=S+e0 e_last^t, and f the first
J coefficients of F,

    S M-M C^t=f h^t-h(f+e0)^t+e1 e0^t-e0 e1^t.

This has rank at most four and an invertible displacement operator. Its
generator still contains h. The checked Bostan--Jeannerod--Schost 2008
Theorem 1 takes a SUPPLIED generator over a field and uses a probabilistic
algorithm; it is not an acquisition theorem for this implicit h or a
deterministic composite-ring pivot theorem. The direct recurrences above
do not need h, so its current acquisition cost is not asserted to be a
general lower bound for a weak readout.

### The reciprocal filter is a paid unit normalization

Write m=k, R=3k, ell=mR-1, y_j=V_j^-1,

    P(T)=prod_(n<ell)(1-q^n T),
    Psi(Z)=prod_(rho<R)(1-q^[m(rho+ell-1)] Z).

The THREE original tail factors n=ell,ell+1,ell+2, and optionally the
shared endpoint ell-1, are evaluated at every row in soft k and retain
their original consumers. The actual degree-R Psi is acquired. Every
u_j=Psi(y_j^m) is nonzero at the smaller nonsplit prime on a good label.
For if one factor vanished, actual k-roughness would give V_j=q^n for
ell-1<=n<=ell+R-2<4H. The native congruences then force the coprime local
order product, greater than 256H², to divide

    K_n=a'_j P+Q+ell_j-Hn,
    -5H²<K_n<-15H²/16+5H/2<0.

The promised P>16k² and P<=k³ already force k>16, so these inequalities
hold throughout the continuing range. This is a contradiction proof for
the filter; it does not extend the original outside-index witness decoder.
MPE acquires all u_j in soft k. Their norm screens return a proper factor
or certified global units on a good label; wrong labels can decline on
actual saturation. Psi' evaluations acquire all requested directional
derivatives of U=prod_j u_j at the same clock.

For E=prod_j P(y_j), exact square-zero differentiation gives

    partial_w(E/U)=U^-1 partial_w E-E U^-2 partial_w U.   (QG3)

At the covered zero, the second term vanishes and the two label gradients
share the same nonzero multiplier U^-1. Thus this normalization preserves
their ratio. It acquires the normalizer and its derivatives, not the
unknown numerator gradients. A routine valid only at native points is
not automatically a valid circuit under independent root deformation.

The actual finite correction from the preceding Cauchy pass remains:

    Psi(T^m) W(T)=P(T)+T^(ell+1) E_tail(T),
    P(y)/Psi(y^m)=W(y)-[y^(ell+1)/Psi(y^m)] E_tail(y).   (QG4)

Both reshaped coefficient actions and all scalar weights are acquired;
the matched values are not. At the own root, W(y*) equals the weighted
E_tail(y*), rather than forcing E_tail(y*)=0. Its derivative also retains
both correction terms. The tail is not the product E in (QG3). A uniform
polynomial check proves it cannot vanish at every nonendpoint q-grid
root: such vanishing would force W=P, contradicting
[T^m]W=[T^m]P-psi_1 with psi_1 a certified unit. This is not a claimed
counterexample at every native own hit.

The restored commutator also has an explicit retained error. For the old
q-grid Vandermonde V, U=diag(q^(m r)), Gamma(X)=prod_r(X-q^(m r)),
l_X^t=(1,X,...,X^(R-1))V^-1, and coefficient reshape C, let
A_biv(X,y)=sum_(r,s)c_(mr+s)X^r y^s. Lagrange interpolation gives

    l_X^t[U,V]C(1,y,...,y^(m-1))^t
      =X P(y)-Gamma(X)T_last(y)-A_biv(q^m X,y), X=y^m,

where T_last(y)=sum_(s<m)c_(m(R-1)+s)y^s. Its short coefficients and
all native values are acquired in soft k. The own hit kills X P(y);
it does not yet cancel the other two terms. The shifted paired term
retains a cheap ordinary action but an unpaid matched evaluation. Skew
symmetry alone does not help: the two vectors in this contraction differ.

### Short residue-row data are acquired; their coupled evaluation is open

Put alpha=q^(1-ell), t_r=alpha q^-r, and
B_r(T)=P(t_r T) mod(T^m-1). A C^t geometric-vector action supplies each
required initial polynomial, including B_0 and B_1, in soft k. The exact
recurrence is

    (1-q^-r T) B_(r+1)(T)
       -(1-alpha q^(-r-1) T) B_r(T)
      =gamma_r(T^m-1),
    gamma_r=B_r(0)-B_(r+1)(0).                         (QG5)

Acquire G0(Z)=sum_(rho<R)c_(m rho) Z^rho by the selected-coefficient
primitive. Since B_r(0)=G0(t_r^m), MPE acquires every required gamma_r
in soft k. This is actual boundary acquisition, not a hidden mR array.
The r=0 pole is retained; no inverse of 1-T modulo T^m-1 is presumed.

For D_r(t)=B_r(q^r t), the exact relation becomes

    (1-qt)D_(r+1)(t)-(1-alpha t)D_r(qt)
      =gamma_r(q^[m(r+1)]t^m-1).                       (QG6)

Modulo t^m this is the old fixed q-Pascal operator with supplied forcing.
The desired partial fractions need the paired values D_r(y/alpha) with
denominators y^m-t_r^m. They retain the mixed-step Vandermonde coupling
between q^s and q^(-mr). A fast action producing one row or all boundary
values does not evaluate that coupled sum. Thus the newly paid boundary
data do not supply a new terminal algorithm.

The pass closes a unit-normalization proof and supplies exact weaker
output specifications, while retaining the unpaid finite correction and
the present sqrt(JL) execution. Next work must reduce the computation
of the weak output itself, or meet the stronger uniform product contract;
another descriptor or successful finite sample is not that advance.

Exact source pins: unit-filter.md
`fae30a63a9693ba9e38a2653c7feefa4dcbbc31ebb112a1a42b21d2958ddb18c`;
weak-readout.md
`6d324cd99fa32427de877666e82fb67cc60c857c49e2eecbaa9ad2526e1d9bd1`;
quotient-cauchy.md
`1814877cd7cae711a15623e0aa189a8d6ae6d194cb29106ce8e1385276ba1444`.
The corresponding independent reviews and inherited source hashes are
retained in the packet. No broad build or numerical campaign was used.

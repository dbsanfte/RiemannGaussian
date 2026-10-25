# Acquired Cauchy factors and the characteristic diagonal

24 October 2026. Root derivation; independent review is recorded separately. The aim is
simultaneous original Pochhammer evaluations or their restricted product,
not another uninitialized matrix action. This note acquires the exact
Cauchy factors and derives a kernel equation. It does not yet supply the
paired diagonal contraction at the desired whole-family cost.

## Input and actual coefficients

Use the independently reviewed source
`/tmp/semiprime-implicit-thin-encoding-20261024/all-mask-sharing.md`, SHA256
`5f79d577ff7fddf72a6e3670d5bca3b7ff2ef72557f137553d388b9fea9c0f31`.
Let A be the actual constant-rank quadratic algebra over Z/N. The native
q is a unit; 1-q^s is certified unit for 1<=s<=C=16k^2. Choose
1<=b<=L=2k^2+2 and a balanced width 1<=d<=b+1 of order sqrt(b+1).
Bounded b is handled directly. In particular b+d<=2L+1<C in the
prepared native range. All integer metadata have O(log N) bits.

Write

    P_b(Y)=prod_(i=0)^(b-1)(1-q^i Y)=sum_(n=0)^b c_n Y^n.

Set c_n=0 for n>b. The cleared coefficient recurrence is

    (1-q^(n+1))*c_(n+1)=(q^b-q^n)*c_n.                 (1)

It holds at n=b and beyond with that zero padding. The earlier acquired
prefix algorithm supplies any t coefficients through b in
soft(sqrt b+t), including phases and certified unit divisions.

## 1. Full kernel identity, including the last row

Let H=ceil((b+1)/d) and define

    G(X,Y)=sum_(rho<H) sum_(r<d) c_(d*rho+r) X^rho Y^r,
    G0(X)=sum_(rho<H) c_(d*rho) X^rho,
    g(X)=sum_(rho<H) c_(d*rho+d-1)
                         *(q^(d*rho+d-1)-q^b) X^rho.   (2)

The degree-<H polynomials G0 and g are actually acquired in soft sqrt b
at balanced d,H, by requesting their existing coefficient indices;
out-of-range entries are explicit zeros.

Applying (1) across row boundaries yields the polynomial identity

    G0(X)-G0(q^d X)=-X*g(X).                           (3)

For coefficient X^rho with rho>=1, this is exactly (1) at n=d*rho-1.
At the final boundary, a nonzero term beyond the last G0 coefficient
cannot occur: either the corresponding c is padded zero, or its index
equals b and q^b-q^b=0. The constant coefficient cancels.

The column-pencil identity from the cited source, multiplied by the
geometric row and column vectors, gives

    (1-q^b Y)G(X,Y)-(1-Y)G(q^d X,qY)
       =G0(X)-G0(q^d X)+Y^d*g(X)
       =(Y^d-X)*g(X).                                (4)

This can also be checked coefficientwise using (1); it does not invert
Y, X, an output, or any q-difference beyond the native screen.

On the ORIGINAL diagonal X=Y^d we have G(Y^d,Y)=P_b(Y), and (4) becomes

    (1-q^b Y)P_b(Y)=(1-Y)P_b(qY).                     (5)

Thus the acquired rank-one boundary forcing vanishes EXACTLY on this
diagonal. Equation (5) is the original first-order product recurrence;
it is not a new endpoint supplier. At a collision, its coefficients can
be nonunits, so dividing by 1-Y is not a legitimate universal shortcut.
Even when that division is legal at a chosen point, an endpoint value
on that point's q-orbit is still required.

The transverse derivative is also exact. Put
T(Y)=(partial G/partial X)(Y^d,Y). Differentiating (4) in X gives

    (1-q^bY)T(Y)-q^d(1-Y)T(qY)=-g(Y^d).              (6)

No inverse is used in deriving this equation. Its degree may be b-d;
the sparse acquired forcing alone does not acquire its values at all
native targets. A use of (6) must supply actual initialization and pay
the simultaneous endpoint operation. This note does not count (6) as
such an algorithm.

## 2. Explicit Cauchy factorization with unit cross differences

To avoid every spectral overlap, use only R=floor(b/d) REGULAR rows
with n=d*rho and n+d<=b. Let C_reg be their R-by-d coefficient matrix.
The remaining coefficients c_(Rd),...,c_b number at most d and are
acquired explicitly by the prefix lemma.

Let S be the d-by-d lower shift, V=diag(q^r), and put

    A0=S-q^b I, B0=(qS-I)V,
    U=diag(q^(d*rho)), Lambda=diag(q^(b-s)).

All these sparse entries are explicit. B0 has unit diagonal -q^r;
its inverse on a vector is the paid prefix-sum formula

    (B0^(-1)v)_r=-sum_(a=0)^r q^(-a)*v_a.            (7)

The actual rank-one pencil relation is

    C_reg*A0-U*C_reg*B0=g_reg*e_(d-1)^t,
    (g_reg)_rho=c_(n+d-1)*(q^(n+d-1)-q^b).            (8)

Define h_0=1 and, for 1<=t<d,

    h_t=q^(-b*t)*prod_(a=1)^t(1-q^(b+a))
                         /prod_(a=1)^t(1-q^a).        (9)

All h_t cost soft d via their first-order ratio. The denominator
indices are <=d-1; numerator factors through b+d-1 are also units
under the existing BROADER native screen. The construction does not
assume a characteristic-zero generic parameter.

Let W be the lower triangular Toeplitz matrix W_(r,s)=h_(r-s) for r>=s.
It has diagonal 1 and a softly linear inverse/action from truncated
series multiplication and constant-one inversion. The exact identity

    A0*W=B0*W*Lambda                                (10)

follows by substituting r=s+t in (9):

    (q^b-q^(b+t))*h_t=(1-q^(b+t))*h_(t-1).

For t=0, the diagonal terms agree directly; for r<s both sides vanish.
Notice the order: W diagonalizes the generalized pair (A0,B0).
For A0*B0^(-1), its ordinary right eigenbasis is E=B0*W, not W.

Multiply (8) by W and use (10). With eta_s=h_(d-1-s),

    (C_reg*E)*Lambda-U*(C_reg*E)=g_reg*eta^t,
    (C_reg*E)_(rho,s)
         =(g_reg)_rho*eta_s/(q^(b-s)-q^(d*rho)).     (11)

Every cross difference is a certified unit: b-s-d*rho ranges from
1 through b on the regular rows. This includes split components of
the quadratic ring because it uses the actual q-difference screen.
The last <=d coefficients were removed precisely to avoid possible
zero cross differences, then retained as a separately acquired tail.

Thus, with the actual Cauchy matrix

    K_(rho,s)=1/(q^(b-s)-q^(d*rho)),

we have the exact initialized representation

    C_reg=diag(g_reg)*K*diag(eta)*E^(-1),
    E^(-1)=W^(-1)*B0^(-1).                          (12)

The nodes, generators, first d Toeplitz coefficients, inverse series,
and all tail coefficients cost soft(sqrt b+R+d). Formula (12) is a
compressed representation; it does not materialize the R*d cross
differences. Standard rational numerator trees give actual K and K^t
actions in soft(R+d), with these pre-certified denominators. This is
consistent with the previous initialized matrix action, not a new
whole-family bound by itself.

## 3. What the original target now requires

Let T_tail(Y)=sum_(r=0)^(b-Rd) c_(Rd+r)Y^r. For ANY native target y,
including a zero of the original product, exactly

    P_b(y)=u_R(y)^t diag(g_reg) K diag(eta) E^(-1)v_d(y)
                       +y^(Rd)*T_tail(y),            (13)
    u_R(y)=(1,y^d,...,y^((R-1)d)),
    v_d(y)=(1,y,...,y^(d-1)).

For K_targets actual target arguments, all tail values and powers cost
soft(d+K_targets) by MPE and binary powering. The hard part is the
PAIRED bilinear term in (13). The Cauchy generators and basis are now
fully acquired; one must still compute the diagonal at the same y on
both sides, or its zero-safe original product, without paying one
R+d action per target. Separate summation of the two vectors changes
the output. Computing determinant(C_reg) when square also changes the
output and does not solve this product problem.

Equations (4), (12), and (13) sharpen the candidate route but do not
prove the requested soft k contraction for b=Theta(k^2), K_targets=Theta(k).
The original native block arguments remain q^(ab)/V_j, with known unit
factors, tails and original row/interval labels. A completed algorithm
must retain the existing original-leaf localization and saturated-norm
consumer. No encoded sum or Cauchy pivot is itself substituted for an
original collision witness.

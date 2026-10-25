# Exact dual moment pencil and companion q-boundary

24 October 2026. Scratch calculation; no faster fused contraction is claimed.

Use the genuine diagonalizer and partial-stripe formula in `/tmp/semiprime-genuine-stripe-diagonalizer-20261024/diagonalizer.md`. Thus lambda_j=a q^-j, U_rho=q^(b rho), and w_j(X)=sum_(r<=j)u_r X^(j-r), with u_r=q^r(a^-1;q)_r/(q;q)_r. Put w_-1=0.

For a supplied R-linear functional L on R[X]/F, extend it to every polynomial by monic reduction and define

    W[rho,j]=L(X^(b rho) w_j(X)),
    Wsigma[rho,j]=L((qX)^(b rho) w_j(qX)).

These definitions do not assert that substitution descends to the quotient.

## Exact dual pencil

The inverse Toeplitz generating series U(t)=sum u_r t^r satisfies

    U(qt)/U(t)=(1-qt)/(1-qt/a).

Since sum_j w_j(X)t^j=U(t)/(1-Xt), coefficient comparison gives

    w_j(qX)-q w_(j-1)(qX)
        =q^j(w_j(X)-a^-1 w_(j-1)(X)).

Consequently the exact dual moment identity is

    lambda_j (Wsigma[rho,j]-q Wsigma[rho,j-1])
        =U_rho (a W[rho,j]-W[rho,j-1]).          (1)

Negative column indices mean zero. This is an actual dual pencil, but it involves BOTH functionals L and L composed with polynomial substitution. It does not show that the ordinary Cauchy displacement U W-W Lambda has bounded rank.

## Actual companion boundary and its cost

Write F(X)=X^J+sum_(n<J) f_n X^n and let C be its monomial-basis multiplication matrix. Let Q=diag(1,q,...,q^(J-1)), e=e_(J-1), and d_n=f_n(q^J-q^n). Then

    Q C-q C Q=d e^t.                             (2)

For columns before the last, multiplication simply raises degree and the two terms agree. In the last column C e=-sum f_n e_n, giving precisely d. Thus d is genuinely acquired in soft J from acquired F and a power walk. Equation (2) uses no inverses or target separation and holds over the actual composite ring, including repeated roots.

Its propagated form is

    Q C^n-q^n C^n Q
      =sum_(r=0)^(n-1) q^r C^r d e^t C^(n-1-r). (3)

This follows by induction from (2). In particular, the rank-one boundary does NOT remain rank one after propagation. Contracting (3) against any supplied vectors l,v gives the exact convolution

    l^t(Q C^n-q^n C^n Q)v
      =sum_(r<n) q^r (l^t C^r d)(e^t C^(n-1-r)v).

Both scalar sequences on the right obey the constant recurrence F. Their rational numerators really can be acquired in soft J from supplied l,d,v: first extend the functional's monomial moments from length J to length 2J using inversion of the reversed-F denominator (whose constant term is 1), then correlate that list with the coefficient vector d or v by one convolution. This produces the first J sequence terms, hence its numerator by another truncated multiplication. The geometric factor q^r only scales numerator and denominator coefficients. One selected coefficient of the product of these rational generating functions is then accessible by ordinary rational coefficient extraction in soft(J log n), with denominator constant term 1. This licenses isolated scalar boundary moments; it does not acquire all bT paired moments or their Cauchy-weighted contraction in that cost.

In particular Q acting on a reduced polynomial represents substitution only BEFORE an overflow through degree J. For p(X) of degree below J, L(p(qX)) is L represented by Q; for higher powers the correction is exactly the propagated boundary (3), rather than zero. Replacing Wsigma by a fixed Q action on all high-degree moments would drop that correction.

## What the fused query still requests

Applying L to the native partial-stripe formula gives exactly

    L(P_ell mod F)
       =sum_(rho<T-1,j<b)
           g_rho h_j W[rho,j]/(lambda_j-U_rho)
        +c_ell L(X^(b(T-1)) w_(r*)(X)).           (4)

The resonant contribution is retained in the final term. Every displayed Cauchy denominator is certified a global unit under the actual ell+b<16H guard. The companion calculation introduces no additional nonunit inversions.

A single terminal moment in (4) can be obtained by computing X^(b(T-1)) modulo F using ordinary modular powering, multiplying by the explicitly acquired degree-r* polynomial w_r*, and applying L. This costs soft(J log ell+b), with no separation assumption. The unresolved operation is the FIRST, doubly weighted term of (4). Equation (1) exchanges it for q-shifted moments; (2)-(3) describe the exact resulting companion boundary but do not sum those corrections against both the rho and j weights in soft(J+sqrt ell).

This calculation supplies real rank-one generators and a paid individual terminal operation. It does not claim a low-rank ordinary dual displacement, an unproved fixed-quotient q action, a generic lower bound, or a fast fused selector. No shared/frozen source or numerical campaign was changed.

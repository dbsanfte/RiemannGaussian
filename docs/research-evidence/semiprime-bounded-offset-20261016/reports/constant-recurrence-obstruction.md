# No constant-coefficient recurrence of order at most m for the chirped segment

2026-10-16. Classical finite-segment statement. The proof allows composite local orders and numerical frequency aliases, and requires no new exceptional-set deletion. It excludes the stated order range only: an order2m or O(m polylog m) constant recurrence remains outside this conclusion. No operation lower bound or improved query clock is asserted.

## 1. General field theorem

Let K be a field, g a unit of finite order R, d>=1 an integer, q=g^d, and L>=r>=1 integers. Define

 F(T)=product_(i=0)^(L−1)(1−q^i T)=sum_(k=0)^L c_k T^k,
 A_k=c_k g^(−binom(k,2)).

Assume

 R>2r²,      ord(q)>L+r,      (r+1)²<=L−r+1.                         (1)

Then there are no constants a_0,...,a_r in K, not all zero, satisfying

 sum_(t=0)^r a_t A_(k+t)=0 for every0<=k<=L−r.                        (2)

All coefficients may be supplied with full advice. The order and characteristic of the field need not be known computationally. No primality of R or coprimality of R with d is assumed. The ord(q) hypothesis rules out the short horizontal alias; the vertical alias is also impossible since R>=ord(q)>r.

## 2. Clear the finite q-binomial ratios

The standard finite coefficient identity is

 (1−q^(k+1))c_(k+1)=(q^L−q^k)c_k.

Since ord(q)>L, all c_k and A_k are nonzero. With X=q^k one obtains

 A_(k+t)/A_k=g^(−tk−binom(t,2))(-1)^t
             *product_(a=0)^(t−1)(q^a X−q^L)
             /product_(a=1)^t(1−q^a X).                            (3)

Every denominator on the finite segment is nonzero because k+t<=L. Let D_r(X)=product_(a=1)^r(1−q^a X). After division by A_k and multiplication by D_r(q^k), equation (2) becomes

 sum_(t=0)^r g^(−tk) B_t(q^k)=0,

where

 B_t(X)=a_t(-1)^t g^(−binom(t,2))
        *product_(a=0)^(t−1)(q^a X−q^L)
        *product_(a=t+1)^r(1−q^a X).

Each B_t has degree at most r and is zero exactly when a_t=0. Expand B_t=sum_(u=0)^r b_(t,u)X^u. The finite equations are

 sum_(t,u=0)^r b_(t,u) [g^(du−t)]^k=0.                              (4)

Group equal numerical bases g^(du−t). There are at most (r+1)² groups. By (1), the available consecutive equations include a square Vandermonde system on all distinct group bases. Therefore the sum of b_(t,u) in EVERY numerical frequency group is zero. This step uses field arithmetic only, with no generic-distinctness inference.

## 3. All short aliases are collinear

An alias difference (s,v)=(u−u',t−t') satisfies

 d s−v=0 modulo R,       |s|,|v|<=r.

For two such differences, R divides their determinant: substitute v_i=d s_i modulo R. The determinant has absolute value at most2r²<R, so it is exactly zero as an integer. Thus all nonzero short alias differences lie on one rational line.

If there are no nonzero alias differences, all bases in (4) are distinct; the Vandermonde conclusion makes every b_(t,u) zero and contradicts a nonzero a_t. Otherwise choose ANY one nonzero alias difference (s_0,v_0). Both coordinates are nonzero. Indeed s_0=0 would force R|v_0 with |v_0|<=r<R, while v_0=0 would force ord(q)|s_0 with |s_0|<=r<ord(q). Reverse its sign if necessary so v_0>0.

Introduce the formal Laurent polynomial

 P(X,Y)=sum_(t=0)^r Y^(−t)B_t(X).

Substitute X=x^(v_0), Y=x^(s_0). Every actual numerical frequency group maps to one formal power of x: any difference in that group is a short alias, collinear with (s_0,v_0), so v_0 Delta u−s_0 Delta t=0. Its coefficient sum has already vanished. Consequently

 P(x^(v_0),x^(s_0))=0 in K[x,x^(−1)].                               (5)

Importantly, formal powers MAY merge several different numerical frequency groups. This is harmless because each merged group already has coefficient sum zero. No primitive-direction saturation, converse identification of groups, or torsion-free lattice quotient is required. This is why the proof works for composite R as well as prime R.

## 4. A unique highest-shift pole contradicts the formal identity

Divide (5) by the nonzero D_r(x^(v_0)). It gives the exact rational identity

 sum_(t=0)^r a_t(-1)^t g^(−binom(t,2)) x^(−s_0 t)
       *product_(a=0)^(t−1)(q^a x^(v_0)−q^L)
       /product_(a=1)^t(1−q^a x^(v_0))=0.                           (6)

Let t_* be the highest index with a_(t_*)!=0. If t_*=0, the identity is the nonzero constant a_0=0, already impossible. Otherwise choose a nonzero x_0 in an algebraic closure satisfying

 x_0^(v_0)=q^(−t_*).

Such a root exists since v_0>0. All lower-index terms in (6) are regular there: their denominator exponents a−t_* are nonzero with absolute value less than ord(q). The highest-index term has a genuine pole. Its numerator factors are nonzero because a common zero would require

 q^(L+t_*−a)=1 for some0<=a<t_*,

where L+1<=L+t_*−a<=L+r<ord(q). Its scalar coefficient and x power are nonzero at x_0. Its other denominator factors do not vanish. Thus this pole cannot cancel with any lower term, contradicting (6).

If the characteristic divides v_0, the vanishing denominator can have higher multiplicity; the numerator remains nonzero and the pole remains genuine. No separability hypothesis is needed. This proves the theorem.

## 5. Canonical specialization, including the new uniform certified base

Put d=m²,L=2m²+2,m>=3. If1<=r<=m, then R>16m² implies R>2r², and ord(q)>16m² implies ord(q)>L+r. Also

 (r+1)²<= (m+1)² <=2m²−m+3 <=L−r+1,

where the middle inequality is (m−1)(m−2)>=0. Therefore the theorem excludes every nontrivial constant-coefficient recurrence of order at most m on the complete finite segment A_0,...,A_L.

This applies separately in BOTH hidden fields to the original qualified prime-order gamma. More generally it applies to the new paid coprime-refinement output beta: that theorem certifies both local beta orders and both local q=beta^(m²) orders exceed16m². These orders may be composite; no old prime-order counterfamily premise or additional arithmetic deletion is needed for this application. The conditional setup can return a factor instead, as its theorem states.

The argument is about the finite sequence and this recurrence format, not a theorem that every other representation or every selected-convolution algorithm costs superlinearly. In particular the threshold m is quantitative: it does NOT exclude order2m, orderO(m polylog m), high-degree q-dependent coefficients, another transform, or direct aggregate acquisition. The old unchirped c_k sequence retains its familiar first-order q-rational coefficient recurrence.

The finite coefficient ratio and paid strong-order/unit setup are inherited prerequisites, pinned in constant-recurrence-source-pins.json. The new step is grouping aliased frequencies, using small-determinant collinearity, and coarsening to a formal rational identity with an uncancelable pole. No native edit, Lean declaration, numerical experiment, operation lower bound, or full-query acquisition theorem is claimed.

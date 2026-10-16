# Positive block q-binomial transform and one-binomial-modulus acquisition

2026-10-15. New explicit paid primitive: arbitrary formal matrix-vector multiplication and transposition for selected consecutive coefficient blocks, and therefore the full q-factorial remainder modulo one binomial of degree about sqrt L in nearlinear time. This does not yet acquire the remainder modulo the original target polynomial D or its norm.

## 1. Exact block operator and cost

Let R=Z/N, q a supplied unit, L>=1, and

 P_L(t;q)=sum_(k=0)^L c_k t^k.

Assume every 1-q^r, 1<=r<=L, is a unit. Given width B>=1, nu public row starts a_j with 0<=a_j and a_j+B-1<=L, define

 C_(j,s)=c_(a_j+s), 1<=j<=nu, 0<=s<B.

There is a formal arbitrary-weight algorithm for C*v and for C^T*w in

 soft O(B+nu+sqrt L) ring operations,

with soft O(B+nu+sqrt L) residue storage. Row starts may be arbitrary supplied integers, input-dependent, and repeated. Their powers cost O(nu log(L+1)) ring operations, included in soft notation. In the balanced regime B,nu,sqrt L=Theta(m), this is soft O(m), not m independent sqrt-L queries.

The unit promise holds on the retained actual source q=gamma^(m^2), since both local prime orders exceed 16m^2 and L<=4m^2. No order or factors are algorithm inputs. The algorithm does not divide by a coefficient c_k or any row-collision value.

## 2. Rational Newton basis construction, including all preprocessing

The coefficient recurrence is

 (1-q^(k+1))c_(k+1)=(q^L-q^k)c_k.

Hence with X_j=q^(a_j),

 c_(a_j+s)=c_(a_j) R_s(X_j),
 R_0=1,
 R_s(X)=product_(r=0)^(s-1)(q^L-q^r X)/(1-q^(r+1)X).

The selected common-stream primitive acquires all c_(a_j) in soft O(sqrt L+nu). Compute all X_j and q^r for r<B, and set

 A_s(X)=q^L-q^s X,
 B_s(X)=1-q^(s+1)X.

For formal independent weights v_0,...,v_(B-1), compute the rational function

 V(X)=sum_(s=0)^(B-1) v_s R_s(X)=N_v(X)/Q(X),
 Q(X)=product_(s=0)^(B-2) B_s(X), deg N_v,deg Q<=B-1.

This is paid by a balanced product of upper triangular 2 by 2 polynomial matrices

 T_s=[[A_s, v_s B_s],[0,B_s]], 0<=s<B-1,

acting successively as y->v_s+(A_s/B_s)y, with terminal y=v_(B-1). The product encodes the nested expression

 v_0+(A_0/B_0)(v_1+(A_1/B_1)(...v_(B-1))).

Its resulting numerator is N_v and denominator Q. Divide-and-conquer polynomial matrix multiplication costs O(M(B)log(B+1)), and no polynomial division or weight inversion is used. Because the matrices are upper triangular and diagonal entries independent of v, the resulting numerator is formally linear in v. For B=1 take N_v=v_0,Q=1.

Monic multipoint trees evaluate N_v and Q at all X_j in soft O(B+nu), including repeated points. At each point

 Q(X_j)=product_(r=1)^(B-1)(1-q^(a_j+r))

is a unit by the band restriction. Batch-invert these values with one extended-gcd inversion, then output c_(a_j)N_v(X_j)/Q(X_j). This proves the forward bound and exact formal identity over R[v]. The inverses depend only on the public parameters, not weights, so they are precomputed constants.

For transposition, form the scalar sum_j w_j(Cv)_j and reverse its division-free straight-line program in the formal variables v. Its gradient is C^T*w. Reverse mode uses O(1) ring operations per gate and O(number of gates) stored residues over every commutative ring. Formal linearity, rather than numerical equality on a finite ring, ensures the identity. Thus transposition has the same soft bound, including the paid parameter preprocessing and independent unit inversions. This is a fully specified operator, not a black-box numerical inner-product assertion.

## 3. Full P_L remainder modulo one binomial, at any supplied scalar X

Take T=floor((L+1)/B), the complete row starts a_n=Bn for 0<=n<T, and let h=L+1-BT<B be the final partial width. For a supplied scalar X in R, transposition with w_n=X^n produces all B sums

 r_s=sum_(n=0)^(T-1)c_(Bn+s)X^n, 0<=s<B.

Acquire the remaining h coefficients c_(BT+s) by the same selected-term primitive and add X^T c_(BT+s) to r_s for s<h. Then

 P_L(t;q) mod(t^B-X)=sum_(s=0)^(B-1)r_s t^s.        (1)

This holds for arbitrary X, including nonunits or zero, because t^B-X is monic and the weight powers use no inversion. It uses no roots of unity or extension ring. All coefficient indices remain within [0,L], so no stronger q-order promise than section1 is silently used.

Total cost is soft O(B+L/B+sqrt L) ring operations and comparable residue storage. With B=Theta(sqrt L), the FULL remainder of degree<B is acquired in soft O(sqrt L). Modulo N the bit cost is soft O((B+L/B+sqrt L)log N), for polynomial-size index lengths, by integer polynomial encoding. Supplied exponent lengths and repeated-squaring costs are included as above. This is a genuine new quotient acquisition primitive, although its modulus is a binomial rather than the original split D.

## 4. Fraction-free mask and ALL decimated numerator values at any one scalar

Let B=2^k, D(t)=product_j(1-t/z_j), D_(2^h)(t)=product_j(1-t/z_j^(2^h)), and E_B=D_B(t^B)/D(t), as in the frozen decimation report. A fraction-free norm-complement identity is

 E_B(t)=product_(h=0)^(k-1) D_(2^h)(-t^(2^h)).       (2)

Indeed D_(2^h)(u)D_(2^h)(-u)=D_(2^(h+1))(u^2); multiplying these identities telescopes. Equation (2) is a polynomial identity over every commutative ring and does not require D to be invertible in a quotient.

For ANY supplied scalar X, including a root of D_B or a nonunit, its full remainder E_B mod(t^B-X) is acquired in soft O(J+B). Build all D_(2^h) from the J powered nodes in soft O(J log B). Set G_k=1 in the degree1 quotient R[u]/(u-X), and recursively, for h=k-1 down to 0, form

 G_h(u)=D_(2^h)(-u) G_(h+1)(u^2)
          mod(u^(B/2^h)-X).

The substitution is well defined because the child modulus becomes the parent modulus under u->u^2. Induction using (2) gives G_0=E_B mod(t^B-X). Reducing degree-J polynomials modulo each sparse monic binomial costs O(J) per level, plus paid powers of X; shrinking-degree multiplications total soft O(B). Storage is soft O(J+B), retaining O(log B) denominator levels or recomputing them at absorbed logarithmic overhead. There are NO scalar or polynomial inversions, gcd pivots, roots of unity or unknown-order parameters in this cofactor recursion. For B=1, the product is empty and E_1=1.

Multiply the remainder from (1) by this G_0 modulo t^B-X. Since F E_B=sum_(r=0)^(B-1)t^r N_(B,r)(t^B), the result is

 F(t)E_B(t) mod(t^B-X)
   =sum_(r=0)^(B-1) N_(B,r)(X)t^r.

Thus ALL B decimated numerator values N_(B,r)(X), at ONE arbitrary X, are acquired simultaneously in soft O(B+L/B+sqrt L+J), with the corresponding log N bit factor. This includes X=z_j^B, where D_B(X)=0, and saturated/nonunit X values: no inverse of D or D_B(X) is used. At J~B~sqrt L this is soft O(m). The algorithm materializes neither the B-by-(L/B) coefficient block nor the degree-J(B-1) mask. This stronger fraction-free cofactor construction replaces the initially contemplated unit-normalizer inverse; its polynomial identity is valid exactly at the collision-bearing moduli as well.

## 5. Remaining mixed contraction

The desired original query needs N_(B,r) at J powered target points z_j^B, or an equivalent aggregate. Section4 now pays ALL residue channels at any ONE of these points, including collision points, without a normalization obstruction. But applying the algorithm separately at J different scalar moduli still costs J times its bound. Transposition and the fraction-free mask do not by themselves pay that simultaneous mixed contraction. The existing exact transport formula identifies each target-point row payload with the original wanted value times a cheap unit.

Knowing fast applications of the coefficient-block matrix C and a mask operator separately does not by itself compute the diagonal or antidiagonal of their mixed product. No lower bound for that structured product is claimed. A fast simultaneous algorithm for the bilinear contraction remains a concrete positive route. The present report establishes only the exact block operator, binomial remainder, and one-point decimation-vector primitives at arbitrary moduli; no actual-source whole-query soft O(m) algorithm or improved factoring exponent follows yet.

## Provenance

The block construction is proved explicitly above from the finite q-binomial coefficient recurrence. Its selected-coefficient and formal reverse-mode prerequisites, the frozen exact tail/decimation interfaces, and actual-order source pins are recorded in manifest.json. No generic matrix displacement theorem or field-only fast inversion is silently imported. Previous reports remain byte-frozen.

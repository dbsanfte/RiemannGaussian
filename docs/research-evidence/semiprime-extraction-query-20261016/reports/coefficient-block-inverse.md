# Square block inverses and determinants are paid; the actual kernel is not a short separable sum

2026-10-16. A constructive extension of the paid block operator, an actual-source rank statement, and a bounded primary-literature check. No whole-query diagonal or determinant-deformation algorithm was obtained.

## 1. A square block minor is invertible on the actual branch

Let B=J, L>=J²-1, and assume every 1-q^h for 1<=h<=L+J-1 is a unit in Z/N. This slightly stronger promise holds on the retained actual source: J<=m-1, L<=4m² and both local prime orders exceed 16m². It is not asserted for arbitrary inputs meeting only the earlier through-L promise. Let

 C0_(n,s)=c_(Jn+s), 0<=n,s<J,
 X_n=q^(Jn), a=q^L,
 Q(X)=prod_(r=0)^(J-2)(1-q^(r+1)X),
 p_s(X)=prod_(r=0)^(s-1)(a-q^r X)
          *prod_(r=s)^(J-2)(1-q^(r+1)X).

Then C0_(n,s)=c_(Jn) p_s(X_n)/Q(X_n). All c_(Jn) are units: their finite numerator and denominator factors use exponents in [1,L]. Also Q(X_n) is a unit, since its exponents Jn+r+1 lie in [1,J²-1].

The polynomial basis p_s has a UNIT coefficient determinant. Set alpha_k=q^(L-k), 0<=k<J. The evaluation matrix p_s(alpha_k) is lower triangular: p_s(alpha_k)=0 if s>k. Its diagonal is

 p_k(alpha_k)=a^k prod_(h=1)^k(1-q^(-h))
                   *prod_(h=1)^(J-1-k)(1-q^(L+h)). (1)

Every factor is a unit. The alpha Vandermonde determinant is a unit because its differences use exponents of magnitude at most J-1. Hence the coefficient matrix of p_s is invertible over Z/N. The X_n Vandermonde determinant is also a unit, using exponents J|n-k|<=J(J-1)<=L. Therefore det C0 is a unit. This proves actual invertibility, not generic nonvanishing specialized without justification.

## 2. A paid inverse and inverse transpose

There is a ring-safe inverse algorithm in soft O(J+sqrt L), including shared setup. Given C0*v=w, divide w_n by the unit seeds c_(Jn), multiply by Q(X_n), and interpolate the unique degree<J polynomial N(X) at X_n. Recover v from N=sum_s v_s p_s by the following exact recursive conversion.

For an interval [l,r), use its local basis

 p_s^[l,r)=prod_(h=l)^(s-1) A_h *prod_(h=s)^(r-2) B_h,
 A_h=a-q^h X, B_h=1-q^(h+1)X.

At midpoint p, every local expansion splits uniquely as

 N=N_left V_right+U_left N_right,
 U_left=prod_(h=l)^(p-1)A_h,
 V_right=prod_(h=p-1)^(r-2)B_h,
 deg N_left<p-l, deg N_right<r-p.                 (2)

At the p-l distinct roots alpha_l,...,alpha_(p-1) of U_left, evaluate N and V_right, batch-invert the latter values, and interpolate N_left from N/V_right. These denominator factors are 1-q^(L+h+1-k), with h>=p-1 and k<=p-1: their exponents lie in [L+1,L+J-1], so they are units under the stated promise. Then compute N_right=(N-N_left V_right)/U_left by exact polynomial division, normalizing the unit leading coefficient of U_left. Recurse; at a leaf its constant is v_l.

Every level costs softly O(J) by product/remainder trees and unit-difference interpolation; logarithmic recursion overhead is absorbed. All node powers, product trees, seed inverses and value inverses are parameter-only setup. There are no field-Euclidean pivots, hidden orders or divisions by unknown row values. Transposition of the resulting formal linear inverse circuit gives C0^(-T) with the same clock and soft O(J+sqrt L) residue storage. Proper-gcd failures outside the promise can factor; gcd N is not an inverse.

Thus square block inversion really is paid here. It is not merely a proposed use of a field-only inverse theorem.

## 3. Its determinant also has a nearlinear explicit clock

Write V(x)=det(x_n^s)_(n,s=0)^(J-1)=prod_(i<j)(x_j-x_i). The triangular evaluation proof gives the exact signed formula

 det C0 = (prod_n c_(Jn)/Q(X_n))
             * V(X)/V(alpha) * prod_k p_k(alpha_k). (3)

No sign is omitted: the same increasing-index Vandermonde orientation is used for both evaluations. The seed product is a shared selected-coefficient acquisition. The two geometric Vandermondes use

 V(b r^n)=b^(J(J-1)/2) r^(J(J-1)(J-2)/6)
              *prod_(h=1)^(J-1)(r^h-1)^(J-h).

The diagonal product in (1) likewise collapses to J-1 weighted factors of each kind:

 prod_k p_k(alpha_k)=a^(J(J-1)/2)
       *prod_(h=1)^(J-1)[(1-q^(-h))(1-q^(L+h))]^(J-h).

Finally

 prod_n Q(X_n)=(q;q)_(J²-1)/prod_(n=1)^(J-1)(1-q^(Jn)).

The horizon-J² q-factorial costs soft O(J): form a degree-about-J block polynomial prod_(h=1)^b(1-q^h X), evaluate at successive q^b powers by a monic remainder tree, multiply the block values and the short residual. No inversion is needed for that acquisition. All other lists have O(J) factors with O(log J)-bit multiplicities; the few resulting scalar denominator products are units and may be inverted. Hence (3) costs soft O(J+sqrt L) ring operations and the usual soft log N bit factor, with public exponent lengths included.

This does not compute det(I+diag(theta)S). In a square/no-ragged factorization, det S factors as det A det C det W; the formal deformation introduces an identity-plus-product sum, and determinant multiplicativity does not apply. Canonical L~2m² and J~m also give rectangular complete factors rather than automatically a square C0 factorization. No shortcut for those extra terms follows from (3).

## 4. A precise actual-source restriction on a proposed bivariate collapse

Let M_(n,j)=sum_(s=0)^(J-1)c_(Jn+s)z_j^s, 0<=n<J, at the ACTUAL deduplicated target nodes. Its matrix is C0*W with W_(s,j)=z_j^s. The source unit-difference promise makes det W a unit; therefore det M is a unit too, in both hidden fields and in Z/N.

Consequently an exact representation on this actual grid of the form

 M_(n,j)=sum_(ell=1)^rho f_ell(X_n)g_ell(z_j)

requires rho>=J after reducing to either field. This includes rational separable terms whose denominators are valid units at every queried point, and independent unit row/column normalizations. It rules out replacing the mixed block kernel by only O(1) or polylog J SEPARABLE terms on the actual source. No input deletion, random specialization or generic degree argument is used.

This is NOT a bound on Cauchy/displacement rank: a single Cauchy kernel can have full ordinary matrix rank. It also does not bound circuit complexity, the rank of YS-SY, implicit representations, or diagonal extraction. Multiplication by the remaining rectangular Vandermonde can change rank; the theorem is about this explicitly specified block kernel and separable ansatz.

## 5. Fresh primary check of the generalized-displacement route

De Sa--Gu--Puttagunta--Re--Rudra, A Two-Pronged Progress in Structured Dense Matrix Multiplication, arXiv:1611.01569, full primary PDF/text freshly downloaded and inspected, particularly Theorems1.1--1.2 and sections7.1--7.2. https://arxiv.org/abs/1611.01569 . Theorem1.2 supplies fast actions and inverse actions for a matrix uniquely specified by LA-AR=E with supplied bounded-quasiseparable L,R and low-rank E. It is a field theorem with uniqueness/operator and generator prerequisites. Its closure discussion requires compatible types. It does not give a diagonal algorithm for an arbitrary factor product whose actions are fast, a nearlinear determinant of det(I+diag(theta)S), or a composite-ring pivot contract. Our paid rank-two block PENCIL is useful input structure, but normalizing it, proving uniqueness and bounded-quasiseparable operator representations, and then preserving the required output/parameter deformation are further obligations. Inverse C0 is instead proved ring-safely above without importing those obligations.

Krattenthaler, Advanced Determinant Calculus, Lemma3 (equation2.8), full primary author PDF/text freshly downloaded and inspected: https://www.mat.univie.ac.at/~slc/s/s42kratt.pdf . Its determinant of products of split linear factors contains the cleared rational-Newton basis evaluation as a specialization. The direct triangular proof above fixes the exact sign and unit hypotheses needed here. That product-form determinant evaluation does not cover the independently row-weighted identity-plus-mixed-product deformation. No claim that every possible determinant identity fails follows.

Searches for q-Sylvester determinant algorithms also returned noncommutative q-Manin/quantum determinant identities and q-adic Vandermonde inversion papers. Their titles alone do not establish an algorithm for this commutative finite-order q-shift pencil; no such theorem is imported. No applicable primary nearlinear mixed-diagonal/deformation theorem was identified in this focused pass.

## Result

Square block inverse, inverse transpose and determinant acquisition are genuinely paid, and the actual block kernel has full unit rank, excluding a short separable collapse. These advances leave the original mixed diagonal/common-gcd acquisition open. The missing operation is not inversion of C0; it is using the two different node transforms and their special coupling without paying the mixed contraction. No new overall exponent, all-input sixth-rate theorem, Lean build or repository change is claimed.

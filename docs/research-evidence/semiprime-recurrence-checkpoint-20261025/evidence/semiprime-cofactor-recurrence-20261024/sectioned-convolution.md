# Sectioned convolution and the initialized cofactor contraction

The strongest executed contraction in this note is the division-free three-state product below. It initializes the desired first cofactor moments with constant-size state and no q-factorial start. Its explicit polynomial block implementation still costs soft sqrt(JL). The new June 2026 polynomial-reduction paper does not lower that cost on this instance: its adjoint image has a visible factor F, so the two requested weights remain unreduced. This is an applicability calculation, not a lower bound on implicit block algorithms.

## 1. Actual contraction and paid block execution

Work over R=Z/NZ or the acquired finite étale quadratic algebra B. Let F be the acquired monic degree-J polynomial, with unit constant coefficient and the actual separated unit roots. Put x_i=q^i, 0<=i<L, and F_i=F(x_i). Define

    P_n=prod_{i<n} F_i,
    T_{s,n}=sum_{i<n} x_i^s prod_{r<n,r!=i} F_r,  s=0,1.

The state is (P_n,T_{0,n},T_{1,n}), with public initial state (1,0,0). Its step at x=q^n is

    P_next=F(x)P,
    T_0,next=F(x)T_0+P,
    T_1,next=F(x)T_1+xP.                         (1)

The formulas follow by separating the newly omitted factor from the old omissions. They remain valid at every zero and nonunit. Equivalently T_s is the derivative of prod_i(F(x_i)+u+v x_i) with respect to u or v at zero. This simplified contraction and its consumer are credited to the root derivation and the companion cofactor-contraction.md; they are not a new acquisition result of this literature note.

For a block of length b, form the constant-dimension polynomial matrix product M_b(X)=M(q^{b-1}X)...M(X), where M is (1). A product tree acquires it in soft(Jb) ring operations, including the initial F coefficients and all block entries. Its product entry has degree Jb; the cofactor entries have degree J(b-1) and J(b-1)+1. Evaluate these acquired polynomial entries at all floor(L/b) block starts q^{ab}, then apply the resulting matrices and the final short block. Standard ring-safe polynomial multipoint evaluation gives total soft(Jb+L/b), with all starts obtained by powering/multiplication. Thus b near sqrt(L/J) gives soft(J+sqrt(JL)); J~k,L~k^2 yields soft k^(3/2). No output factor is inverted. Native zero-divisor classification and the existing leaf consumer remain necessary after a scalar contraction is acquired; (1) alone does not produce its endpoint in soft k.

At a local field with exactly one zero F_i*, the final T_0 is the nonzero product of all the other F_i, and T_1=x_i* T_0. This explains the useful consumer but does not initialize either unknown final amplitude. In the wrong orientation there can be more zeros, and both moments can vanish. A promised unique-hit branch must retain its independently specified verified-failure/fallback contract.

## 2. Execute the 2026 adjoint reduction

Primary source: Rong-Hua Wang, Xiao-Ran Yang and Michael X.X. Zhong, *Polynomial reduction for q-holonomic sequences*, arXiv:2606.07061v1, 5 June 2026:
https://arxiv.org/abs/2606.07061
https://arxiv.org/pdf/2606.07061

Section 2.1 assumes a characteristic-zero field K and an indeterminate q; coefficients lie in K(q)[X,X^-1]. Lemma 2.2 gives the finite adjoint summation identity, including both endpoint terms. Theorem 2.4 characterizes Laurent-polynomial certificates subject to gcd(a_0(X),a_r(q^i X))=1 for every i>=0 and a minimal-order annihilator. Theorem 2.5 and the following reduction reduce weight degree modulo the adjoint image, with explicit exceptional highest/lowest-degree resonances. They do not state a fast finite endpoint algorithm, nor a composite-ring specialization theorem.

To test precisely the unit-weight cofactor sum, first work formally where the F_i are invertible and take a_n=1/F(q^n). An order-one annihilator is

    L=F(qX) sigma-F(X).

Its adjoint on a Laurent polynomial p is exactly

    L* p = F(X) (p(X/q)-p(X)).                    (2)

Thus every weight in this polynomial-certificate image is divisible by F in the Laurent polynomial ring. For J>1 and F(0) a unit, neither 1 nor X is in that image, even locally over a field. Both weights already lie below the degree-J scale; reducing high-degree weights is not the missing operation. In addition the extreme-degree coefficients of L*X^e have the factor (q^(-e)-1), so e=0 is a resonance: the nondegenerate reduction paragraph cannot simply be invoked without its exceptions. No theorem in the paper turns these remaining sums into their endpoint values.

For comparison the old q-factorial-weighted moment has a_n=lambda_n/F(q^n), lambda_(n+1)/lambda_n=rho(q^n),

    rho(X)=q^(2-L)(q^(L-1)-X)/(1-qX).

An annihilator after clearing this known q-denominator is

    L=(1-qX)F(qX)sigma-q^(2-L)(q^(L-1)-X)F(X),

and its adjoint is

    L*p=F(X)[(1-X)p(X/q)
                -q^(2-L)(q^(L-1)-X)p(X)].         (3)

The same common-F observation applies; the operator coefficient degree is J+1. This calculation does not assert a nonexistence theorem for rational certificates. The source's all-shifts gcd hypothesis is not supplied merely by separated native roots: distinct roots may be related by q-shifts. Rational certificates also require an actual acquisition and specialization proof. Directly evaluating 1/F(q^i), or multiplying a rational identity by the unknown full product while dividing through a collision, is not valid in the actual zero query. Equation (1), rather than that rational evaluation, is the safe initialized object.

The formulas (2)-(3) can be checked coefficientwise with soft J input work. They do not require unknown prime arithmetic. Transferring a formal coefficient reduction to B would additionally require every division used by the certificate algorithm to be certified a unit at the native specialization; public q-difference units alone do not certify arbitrary coefficient pivots.

## 3. Specific sectioned-convolution interface still required

For the Bostan-Mori representation write

    A(T)=prod_{i<L}(1-q^i T),
    D(T)=prod_j(1-V_j T),
    D_B(U)=prod_j(1-V_j^B U),
    K_B(T)=D_B(T^B)/D(T)
          =prod_j sum_{a=0}^{B-1}(V_j T)^a.

A stride-B numerator is the appropriate residue section of A(T)K_B(T); the residue is fixed by the requested coefficient index. The first selected band, the ordinary dense later-band cost, and their source credit are already established in unique-gcd.md in the preceding packet. They are not new obstructions claimed here.

A concrete alternative is to retain C=A/D and use its exact scalar equation

    (1-T)D(qT) C(qT)=(1-q^L T)D(T) C(T).         (4)

The acquired operator has coefficient degree J+1, and the initial prefix of C of length O(J) costs soft J from short A coefficients and formal division by D(0)=1. But the resulting coefficient recurrence has growing order O(J). The existence of this short equation, or a reduced polynomial weight, does not pay its far scalar coefficient.

Separated supplied roots give the further exact diagonalization

    1/D(T)=sum_j w_j/(1-V_j T),
    w_j=V_j^(J-1)/F'(V_j),
    [T^n]C=sum_j w_j V_j^n sum_{a=0}^n [T^a]A V_j^-a.   (5)

All w_j are acquired in soft J using derivative evaluation and certified unit inverses. The still requested statistic is the selected contraction of the truncated q-binomial sums in (5), not an arbitrary supplied vector action. The previously acquired fast q-binomial reshape matvec/transpose handles a single supplied vector; the row-dependent powers V_j^n and the moving truncations here do not provide that supplied vector for free. No reduction from this exact contraction to one such action has been established in this note.

Consequently the initialized block algorithm above is a complete zero-safe execution at the existing soft sqrt(JL) cost. The tested 2026 reduction supplies an explicit residual description, not a faster acquisition or a change in the guaranteed factoring exponent. Further work must compute the implicit blocks or the particular paired contraction, rather than substitute a polynomial-certificate theorem for endpoint initialization.

## Source pin

Cached primary PDF: sources/polynomial-reduction.pdf
SHA256 0fac298246672cc41c67795df940a4e7516239349a7c3bde0cf4f2008e515319.
The adjacent text cache is pdftotext output. Prior exact contracts used above: ../semiprime-unique-acquisition-20261024/unique-gcd.md (8eba0f3676ef0de414f4b48fa463a54058aed4fed97db3a0557be0189ec8c862) and ../semiprime-implicit-thin-encoding-20261024/all-mask-sharing.md (5f79d577ff7fddf72a6e3670d5bca3b7ff2ef72557f137553d388b9fea9c0f31).

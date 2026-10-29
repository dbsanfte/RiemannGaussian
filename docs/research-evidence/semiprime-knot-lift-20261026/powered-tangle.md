# Powered tangles and a genuinely fast cyclic norm: boundary audit

26 October 2026. Scratch only. Executed one cheap scalar completion, the cyclic-cover/Bloch norm, and one rational-tangle transfer candidate. The cyclic norm really costs soft O(L); its boundary imposes the wrong finite clock and need not preserve collision zeros. The rational transfer retains the correct zeros only while retaining the original shifted product. No improved whole-query bound is established.

## 1. A scalar completion that is actually cheap

Primary source: Silver–Williams, *Twisted Alexander polynomials detect the unknot*, https://arxiv.org/abs/math/0604084, Section2 equation(2.1), recalls the Fox–Weber cyclic-cover formula: homology order is the absolute value of the product of Alexander evaluations over roots of unity, with zero representing positive rank. We use the finite algebraic norm behind this identity, not the topological absolute value over Z. Hillar–Levine, *Polynomial recurrences and cyclic resultants*, https://arxiv.org/abs/math/0411414, https://lionellevine.github.io/hillarlevineAMSrevised.pdf, equation(1.1), writes the resultant as a product of powered root differences. Its Theorem1.4 gives an implicit polynomial relation, not a collision-safe algorithm for selecting its next value over Z/NZ.

For the supplied factorization

    K(T)=product_j (v_j-T)(v_j-T^-1)/(v_j-1)^2,

let c be any acquired unit. The division-free Laurent norm over T^m=c is exactly

    C_m(c)=Norm_(R[T]/(T^m-c))/R K(T)
      =product_j (v_j^m-c)(v_j^m-c^-1)/(v_j-1)^(2m).       (1)

Proof: T is a unit in this free rank-m algebra; product over its formal roots of v-T equals v^m-c, and inverse roots obey T^m=c^-1. This is an integral identity after inverting only c and v_j-1, hence remains true for repeated roots, composite rings, and zeros. One can also prove it by the resultant of the two monic binomials, without adjoining any roots.

Equation(1) is initialized: acquire every v_j^m by binary powering, all scalar differences, the product of the already-unit denominators, and its mth power. Cost O(L log m) ring operations, soft O(L) bit cost. There is no m-dimensional matrix evaluation left unpaid. The boundary parameter c can likewise be binary-powered. This meets the desired cost, but for a different scalar.

## 2. The exact cyclic boundary differs from the geometric prefix

For the actual odd-argument prefix write z=eta^3, q=eta² and index 0<=i<m. Its clock polynomial is

    B_m(T)=product_(i=0)^(m-1)(T-zq^i),

whereas the closed powered shift with Bloch boundary c has clock polynomial T^m-c. Explicitly the companion shift S_c sends e_i to e_(i+1) and e_(m-1) to c e_0; therefore S_c^m=cI. Fourier diagonalization, when legal, gives a coset of auxiliary mth roots of unity, NOT the list z,zq,...,zq^(m-1). Equation(1) computes det K(S_c).

For m>1 the coefficient of T^(m-1) in B_m is

    -z*(1-q^m)/(1-q),

a certified unit on the supplied short-order window; the coefficient in T^m-c is zero. No choice of c repairs this discrepancy. This is the boundary calculation for this specific proposed cyclic replacement, not a generic obstruction theorem about all finite transfers.

There is also an explicit collision diagnostic, requiring no numerical experiment or auxiliary roots. Take a single normalized factor with v=eta^5, keep z=eta^3, and choose c=z^m. The desired prefix is zero for every m>=2 because v is its second clock point. In (1), however,

    v^m-c=eta^(3m)(eta^(2m)-1),
    v^m-c^-1=eta^(-3m)(eta^(8m)-1).

Both are units when the given order guard includes 8m; v-1 is a unit too. Thus the cheap norm is a unit while the desired product is zero. The asymptotic native horizon m=Theta(k^1.5) lies inside this guard for sufficiently large k, and m=2 already gives the finite symbolic diagnostic in the prepared branch. The genus-one normalized factor is realizable by the paid integer twist lift, but this is NOT a claim that the full actual native row catalogue equals this one-factor input or attains this root. It refutes the universal norm substitution; a semiprime-specific use would require additional arithmetic coverage.

Keeping the correct B_m instead restores

    product_i K(zq^i)=Norm_(R[T]/B_m)/R K(T),

an exact zero-preserving identity. Its short descriptor does not inherit (1): B_m has m+1 coefficients and its companion does not satisfy S^m=cI. Acquiring/evaluating this norm by the existing geometric-product routine still costs soft O(L+sqrt(Lm)). The endpoint correction is the change of the entire clock polynomial, not a known unit factor.

## 3. Executed rational-tangle denominator transfer

Primary source for actual finite rational-link recurrence: Duzhin–Shkolnikov, *A formula for the HOMFLY polynomial of rational links*, https://arxiv.org/abs/1009.1800, primary journal text https://amj.math.stonybrook.edu/html-articles/Files-2015-2024/15-13/, Lemma5 and Theorem1. Conway specialization is taken polynomially before setting the HOMFLY parameter to1. It yields a two-coordinate recurrence x_n=z l_n x_(n-1)+r_n x_(n-2), not a product of independent evaluations. Repeating an identical acquired recurrence matrix permits O(log m) powering; it fixes the same coefficient/color. A geometric family requires its varying l_n,r_n to be acquired or a new exact summation.

To give this method its strongest favorable interface, allow formal Conway fractions (N,D) with no cancellation, and the exact tangle-addition rule

    (N,D)+(N',D')=(ND'+DN', DD').

Suppose a local gadget at the ith color has pair (1,K_i), K_i=K(zq^i). This is a conditional gadget interface, not an assertion that every K has an already acquired rational-tangle realization. Adding it updates

    [N_new,D_new]^t = [[K_i,1],[0,K_i]] [N,D]^t.

The transfer has constant matrix dimension. Starting at (0,1), after m additions the denominator is precisely P=product_i K_i, while the numerator is sum_i product_(h!=i)K_h. This retains zeros without ever inverting K_i. The matrices even commute, but that does not initialize their product from one matrix power: the diagonal scalar is already P. Multiplying the compact binary descriptions without evaluating the varying coefficients simply keeps this same uncomputed scalar. Cancelling the formal numerator/denominator or evaluating a rational torsion in a field may erase a zero factor and is not a legal zero-query replacement over R.

Consequently this particular rational-tangle realization has a paid scalar completion only at the existing geometric-product cost (or explicit O(Lm) evaluation). Its fixed2-by2 transfer dimension is not a new full-family bound. This is a precise failed powered-transfer candidate; it leaves other tangle constructions open.

## 4. Constructive remaining interface

The useful positive distinction is now sharp: a cyclic/Bloch powered transfer has an explicit soft-O(L) scalar algorithm, while the collision-preserving geometric transfer has the required finite clock but retains the harder norm. A successful surgery/cabling identity would need to change the latter clock into the former while preserving the native complete-family zero and providing recoverable original labels, with every additional norm/boundary factor paid and certified harmless. The straightforward boundary substitution fails by Section2. Neither the cyclic-resultant implicit recurrence nor rational continued fractions currently provides that surgery identity.

The compact connected-sum twist input from the pair packet remains fully usable and acquired; no expanded diagram is charged here. This report adds an exact initialized alternative norm and its finite boundary/collision audit, not a new factoring exponent, a numerical campaign, or a broad lower bound.

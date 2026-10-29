# Paid native twist-knot lift and its complete adjacent-pair scalar family

26 October 2026. Positive input/acquisition result, **not** a fast original collision query. A specified connected sum of twist knots realizes the complete acquired native Alexander polynomial. Its Links–Gould values along every reciprocal adjacent pair are represented by one degree-2L polynomial, acquired in soft O(L) bit cost. This removes the unacquired diagram issue for this choice of knot. The deformed scalar still lacks the required collision predicate, and its full orbit product is not acquired in soft O(L).

## 1. Choose the actual knot from the acquired native roots

The paid half-center preparation supplies unit roots v_j with v_j-1 also units, and

    K(T)=product_(j=1)^L [(T+T^-1-v_j-v_j^-1)/(2-v_j-v_j^-1)].

Set

    c_j=(2-v_j-v_j^-1)^-1= -v_j/(v_j-1)^2.

Every c_j is a unit. The j-th factor is exactly

    1+c_j*(T+T^-1-2).

Acquire all c_j by scalar or batched unit inversions. Choose their integer representatives cbar_j in [1,N-1], then set n_j=cbar_j-N and s_j=-n_j in [1,N-1]. Thus n_j is a negative O(log N)-bit lift of c_j; it is not an unknown discrete logarithm.

Use the twist knot T_n in Kohli's Definition 2.16, whose reciprocal Alexander polynomial is

    Delta_(T_n)(T)=1+n*(T+T^-1-2).

The source convention has T_0 the unknot, T_1 the trefoil, and T_-1 the figure-eight. Its displayed Alexander specialization after Proposition 2.18 fixes the sign. Independently, the genus-one Seifert matrix

    V_n=[[n,0],[-1,1]]

has T^-1*det(V_n-T*V_n^T)=1+n*(T+T^-1-2), checking the same convention. The native knot in this report is the explicitly named connected sum

    C = T_(n_1) # ... # T_(n_L).

Connected-sum multiplicativity gives Delta_C mod N=K exactly. This is an alternative integer/topological lift of the already acquired modular polynomial, not an identification with every earlier Seifert representative. Independently, the block-diagonal matrix made from the displayed V_(n_j) has size 2L and 3L nonzero entries and realizes the same modular Alexander polynomial. Equality of Alexander polynomials alone does not identify this matrix with a Seifert matrix of Kohli's exact twist-knot convention. The actual knot C is specified by its binary twist list, of O(L log N) bits; the scalar algorithm below uses the source's twist-knot formula and requires no such matrix-to-knot identification. No expanded crossing diagram or expanded integer Alexander coefficients are constructed.

Primary source: Ben-Michael Kohli, *The Links–Gould invariant as a classical generalization of the Alexander polynomial?*, Experimental Mathematics 27 (2018), 251–264, DOI https://doi.org/10.1080/10586458.2016.1255860. The inspected late arXiv upload is https://arxiv.org/pdf/2505.08296 . Relevant items are Proposition 2.5 (connected sums), Definition 2.16, Proposition 2.18 (negative twist formula), and the Alexander specialization in its proof. The arXiv identifier's 2025 date is not the original publication date.

## 2. Execute the source formula without singular divisions

Write a,b for the source's two Ishii parameters, u=ab, and B=(a-1)(b-1). For positive s define the polynomials

    A_s(u)=sum_(r=0)^(s-1) u^r,
    H_s(u)=A_s(u)+2*sum_(r=1)^(s-1) sum_(h=0)^(r-1) u^h.

Equivalently, as polynomial identities after clearing denominators,

    (u-1) A_s=u^s-1,
    (u-1) H_s=(u+1) A_s-2s.

Kohli's negative-twist expression simplifies exactly to

    LG(T_-s;a,b)
       =1+(1+u^-1)*A_s(u)*B+u^-1*H_s(u)*B^2.       (1)

Indeed (a^-1-1)(b^-1-1)=B/u, and substituting the source's geometric sum a_1(s)=A_s yields (1). Only a,b,u are inverted in (1). No value of an Alexander polynomial or a knot invariant is inverted. The formula is a Laurent-polynomial identity and therefore remains valid over the actual composite ring, including zeros and u=1. In particular H_s(1)=s^2 and A_s(1)=s.

The large twist count is genuinely cheap to acquire. Keep the tuple

    (s,U_s,A_s,H_s), U_s=u^s.

For concatenation of lengths r,s, exact finite-sum identities give

    U_(r+s)=U_r U_s,
    A_(r+s)=A_r+U_r A_s,
    H_(r+s)=H_r+U_r H_s+2s A_r.                    (2)

The zero tuple is (0,1,0,0); the length-one tuple is (1,u,1,1). Binary doubling/concatenation uses O(log s) ring operations. All integer counters can be retained in O(log N) bits and reduced modulo N when used as ring scalars. Equation (2) does not require division by u-1, and therefore does not hide the normalization at u=1. This is a known twist/skein evaluation, not a new general q-factorial algorithm.

## 3. All adjacent native parameters share the same u

For i>=1, use the reciprocal pair

    a_i=eta^(2i+1), b_i=eta^(-2i-3), u=a_i b_i=q^-1,
    B_i=1+q^-1-a_i-b_i.

Thus u is constant across the entire index family. Acquire A_(s_j)(u) and H_(s_j)(u) once per native root, by (2). Define the acquired quadratic

    F_j(B)=1+(1+u^-1)A_(s_j)(u) B+u^-1 H_(s_j)(u) B^2,

and then acquire

    F(B)=product_(j=1)^L F_j(B).                    (3)

A balanced product tree costs soft O(L) ring operations; the O(L log N) powering work is also soft O(L) at the stated bit scale. The resulting polynomial has degree at most 2L. By connected-sum multiplicativity,

    LG(C;a_i,b_i)=F(B_i)                            (4)

for every requested adjacent pair. Every normalization and every coefficient in this entire deformed scalar family is acquired in soft O(L) bit complexity, with the usual polylogarithmic factors in N. One chosen value can then be evaluated in O(L) ring operations, and its index needs only binary powering. No generic knot diagram, exponentially large module or list of all m indices is assumed supplied.

The variable u is a native unit; u-1 is also a certified unit, but the displayed implementation does not need that latter inverse. Nonunit leading coefficients of F_j cause no problem in product-tree multiplication. A zero F(B_i) is a legitimate deformed-invariant value, but has not been proved to identify an original collision leaf or a licensed beta-annihilator.

## 4. Explicit comparison with the desired pair

For a single row n=-s mod N, direct multiplication of the two ordinary Alexander factors at a,b gives

    P_-s(B)=Delta_(T_-s)(a)Delta_(T_-s)(b)
       =1-s*(u-1)^2/u+s*(1+u^-1)*B+s^2*B^2/u.     (5)

To verify it, put S=a+b=u+1-B and use

    (a+a^-1)(b+b^-1)=u+u^-1+S^2/u-2.

Equations (1) and (5) therefore have the exact correction

    F_j(B)-P_-s(B)
       =s*(u-1)^2/u
         +(1+u^-1)*(A_s-s)*B
         +(H_s-s^2)*B^2/u.                         (6)

At u=1 it vanishes, agreeing with the equal-argument Alexander-square specialization. At the actual u=q^-1, its constant term is a unit: s=-c_j mod N, c_j is a unit, and u-1 is a unit. This does NOT prove that the correction is a unit at every B_i, nor that F_j never shares an Alexander zero; it proves only that the correction cannot be dropped as an identically zero polynomial in the native ring.

The figure-eight scalar audit in this packet makes the failure of a universal zero-preserving substitution precise. It does not assert that its particular root specialization is attained by the complete semiprime catalogue or by the above negative-lift selection. Equations (3)–(6) instead provide the explicit polynomial family needed to study any semiprime-specific claim, with the knot choice and acquisition cost no longer implicit.

## 5. Whole-query cost and next test

For disjoint adjacent pairs, use i=1,3,5,... and handle one final unpaired factor directly if needed. The original product is still the product of (5) over rows and pair indices. Replacing it with (3) is unjustified without a new coverage and extraction theorem. Even if that implication were supplied, a degree-2L polynomial over roughly m/2 positions has the same degree-times-clock scale as the original L-by-m query; a single pairing alone does not improve the power exponent.

Accordingly this report pays for the previously missing native knot input and a complete family of deformed scalars, but does not establish the target soft(L+sqrt m) oracle. The next useful step must exploit (3)–(6) arithmetically or give a block contraction whose initialization and scalar readout cost improve the whole family. Evaluating more examples of (4) would not establish that result.

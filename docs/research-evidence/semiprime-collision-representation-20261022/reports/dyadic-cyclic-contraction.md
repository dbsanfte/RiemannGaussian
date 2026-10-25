# Dyadic cyclic contraction: exact rank-halving recurrences

Take m=2^k, N odd, gamma of odd local orders >16m², t²=gamma public, W=t(1+gamma X)/(X+gamma), R=W/X, B=W^N. All native tags and a are units, hence odd. The cyclic modulus remains X^m−1 throughout. This note derives a genuine norm-family closure and an additive trace decomposition. It does not establish a soft O(m) constructor for the requested varying diagonal.

## 1. Preparation is unit-safe for even m

For even m, the algebra norms of the two binomials differ by a sign and have magnitude gamma^m−1. This scalar is a unit: an odd local order dividing m=2^k would be 1, contrary to the retained order bound. Thus both binomial inverses, W and R are paid in soft O(m), with scalar gcd checks. Unlike the odd-m case, X+1 is NOT a unit; no safe Cayley division by X+1 is imported here.

## 2. Exact norm closure really halves the cyclic rank

Let Y=X², n=m/2. In A_n=(Z/NZ)[Y]/(Y^n−1), relative conjugation sends X to −X. Direct multiplication gives

 W_(gamma,t)(X)W_(gamma,t)(−X)=W_(gamma²,gamma)(−Y),
 R_(gamma,t)(X)R_(gamma,t)(−X)=R_(gamma²,gamma)(−Y).       (1)

Here the second subscript of W,R is the scalar numerator prefactor; t²=gamma ensures the displayed prefactor gamma. For n even, U=−Y again satisfies U^n=1 and gives an isomorphic cyclic algebra of half the rank. Odd automorphism tags commute with this change: (−X²)^j=−X^(2j). Parameters gamma and t are squared at each level; odd local orders remain unchanged. At the terminal rank2→rank1 step, U=−1 is the actual specialization and must be retained instead of pretending U=1.

Since relative norm is multiplicative,

 Norm(B)=Norm(W)^N,
 Norm(T_a)=rho_(a/b)(Norm(B)) Norm(R)^a,
 T_a=rho_(a/b)(B) R^a.                                  (2)

Thus the integrand's NORM has the same special-power functional form at half the rank, with tags reduced modulo n BUT the original integer a retained. If a=a0+n*epsilon is canonicalized, an extra fixed vector Norm(R)^n raised to epsilon remains. Computing the entire tower of fixed norm BASES costs soft O(m), since the ranks form a geometric sum; this does not acquire all varying norm integrands or their traces. This is a positive closure specific to actual cyclic Graeffe symmetry; it is not available from a fictitious X^m truncation.

## 3. The requested additive contraction has two branches

Write canonical degree<n representations

 B=B0(Y)+X B1(Y),   R^a=E_a(Y)+X O_a(Y).

For c=a/b modulo m represented by its canonical odd integer,

 H_a=CT_X[rho_c(B)R^a]
 =CT_Y[B0(Y^c)E_a(Y)+Y^((c+1)/2) B1(Y^c)O_a(Y)].       (3)

This is exact, including the cross-term X^(c+1). No coefficient discarded by cyclic reduction is omitted. If u=b^(-1) mod m and a=2s+1, then

 (c+1)/2 = u*s+(u+1)/2 modulo n,                         (4)

so the phase factor in (3) has a fully paid affine section; the quotient carry is a multiple of n and legitimately vanishes in the rank-n cyclic algebra. The INTEGER powers in E_a,O_a do not vanish this way.

Put r0=(R(X)+R(−X))/2 and r1=(R(X)−R(−X))/(2X). Direct calculation gives

 r0=t(gamma²−1)/(gamma²−Y),
 r1=t*gamma*(1−Y)/(Y*(gamma²−Y)).

All these denominators are units on the stated branch. Multiplication by R in the relative basis (1,X) is

 M_R(Y)=[[r0,Y*r1],[r1,r0]],
 (E_a,O_a)^T=M_R(Y)^a*(1,0)^T.                          (5)

Equivalently E_a=D_a(S,P)/2, where S=2r0 and P=Norm(R), and O_a=r1 U_(a−1)(S,P), with U the second-kind recurrence U0=1,U1=S,U_(j+1)=S U_j−P U_(j−1). For odd a=2s+1, the relevant powers are M_R*(M_R²)^s. This is an exact rank-two rational matrix-power representation, not substitution of the norm P for R².

## 4. The specific still-unpaid operation

Equation (1) alone does NOT give E_a or O_a. It gives P, the product of the two conjugate roots, whereas (5) also retains their sum and orientation. The actual weighted trace needs BOTH terms of (3), with weights B0(Y^c), B1(Y^c) varying with the same odd c. The fixed-weight rational resolvent can evaluate many powers for a fixed weight, but does not directly evaluate these moving weights.

A scalar replacement R²→Norm(R) would require R(−X)=R(X), which is not the present base. In fact r1 is nonzero on the relevant nontrivial components. Even when its occasional factors vanish, equality of norms is not equality of additive traces.

There are two exact recursions with different meanings:

- **Multiplicative recursion:** the special-power norm BASES in (2) close at half rank and are paid across the tower. Canonicalizing a retains its high-band vector correction. This does not acquire H_a or all norm integrands.
- **Additive recursion:** (3)–(5) is the actual H_a recurrence. It introduces parity strata and a rational 2x2 transfer matrix, while the exponent a still spans its original integer range. Merely repeating this decomposition does not prove a bounded total amount of weighted matrix-power work. The coefficient branches and the exponent bands a versus a+n must be shared, not counted as one unchanged scalar problem.

The concrete remaining theorem would be a simultaneous contraction of (3) with the matrices (5), sharing parity strata AND the high/low exponent bands, in soft O(m) total. Such a theorem must preserve (4), the nontrivial M_R² action, and the terminal U=−1 specialization. I have not derived it. No lower bound is claimed.

## 5. Why zero detection cannot replace the additive term by the norm

For any relative quadratic algebra and scalar seed s,

 Norm(T−s)=Norm(T)−s*Tr_relative(T)+s².                   (6)

Consequently a source-retaining norm recursion for DIFFERENCES still needs the additive trace coefficient. Knowing the paid unit Norm(T) does not determine whether Norm(T−s) vanishes. Likewise a component hit in one conjugate factor must not be promoted to a paired hit yielding the original scalar annihilator. Equations (3)–(6) locate the precise additive operation required by either value acquisition or zero-mask recursion.

## 6. Cost and primary algorithm scope

For one supplied level, constructing its fixed bases, relative parity decomposition, or matrix M_R costs soft O(m) scalar bit work. Its rank-halved norm tower costs soft O(m) total. Constructing all R^a or all varying transformed weights explicitly remains uncharged; no assertion that matrix operations are scalar-cost is made.

Kinoshita–Li, *Power Series Composition in Near-Linear Time*, arXiv:2404.05177v2, https://arxiv.org/abs/2404.05177, supplies a real Graeffe/bivariate power-projection framework for its stated power-series truncation interface. Here X^m−1 has a true Graeffe symmetry, so the norm step is legitimate; however identifying (3)'s two moving coefficient branches with that algorithm's supplied rational input/precision-halving invariant is a separate necessary reduction. No nilpotent substitution or root-of-unity replacement for gamma is made.

The dyadic selector and native scalar source conditions are being independently audited by root/compact agent. This report concerns the actual contraction attempt: a paid norm-family closure and the exact additive trace recurrence, with the shared contraction still open.

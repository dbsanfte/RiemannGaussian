# Dyadic special-power coordinates: safe closure and remaining additive contraction

This independent pass concerns m=2^k, odd N, the public unit t with gamma=t^2, and gamma having odd local orders greater than 16m^2. Put W=t(1+gamma X)/(X+gamma), R=W/X, B=W^N in A_m=(Z/NZ)[X]/(X^m-1). The requested varying diagonal is H_a=CT[rho_c(B)R^a], with odd a and c=a/b mod m, b=N mod m. It does not alone include the remaining native W_j^ell factor or solve the long seed query.

## A genuinely acquired special-power tower

For Y=X^2, relative conjugation is X -> -X. Write B=B_e(Y)+X B_o(Y). Its norm is

 B_e^2-Y B_o^2 = [W_(gamma^2,gamma)(-Y)]^N.

Likewise Norm(R)=R_(gamma^2,gamma)(-Y). For m>=4, -Y is a cyclic coordinate of rank m/2; odd rho_c commutes with this coordinate change. The terminal rank-two specialization is -Y=-1, not +1. The fixed norm bases and their Nth powers can be acquired along the whole tower with soft O(m) modular operations, including the O(log N) powering factor: the ranks sum to less than 2m. Coefficient bit lengths are O(log N). This is an actual closure of the special B, not an arbitrary norm oracle.

The original integer exponents remain. In particular a canonical reduction modulo m/2 leaves a high-band factor (Norm R)^(m/2). For a native equality, the seed still has the ORIGINAL exponent m^2 I after norming. Recasting it in a lower-row convention must carry the changed index explicitly; the inherited recentering gives I'=4I, not a fresh unrestricted small interval. Forward equality is preserved, not its converse.

## Why the tempting Cayley chart is not globally valid

W(1)=t and W(-1)=-t. Since N is odd, B_e(1)=0 exactly and B_o(1)=t^N. Thus dividing by B+sigma(B)=2B_e is invalid in the full cyclic algebra, even on these guaranteed public components. A guarded gcd may yield a factor on other components, but the public zero at Y=1 is not itself a factor certificate for N. Splitting that known component is possible and does not supply the remaining components' additive coordinates.

Safe coordinates are homogeneous: (B_e,B_o), with their one quadratic norm relation. Multiplication of (u,v), representing u+Xv, is

 (u,v)*(e,o)=(ue+Yvo,uo+ve).

The affine Cayley coordinate Xv/u, where its denominator is a unit, obeys the usual addition law. Its numerator AND denominator still have to be propagated. The norm supplies their quadratic difference, not either linear coordinate. Nor can a square-root reconstruction from the norm be counted as a public operation: its branch and orientation are precisely additional information.

## Exact missing term after using the special power

Write R^a=E_a(Y)+X O_a(Y), and choose the odd representative c of a/b modulo m. Then the actual even and odd coordinates of rho_c(B)R^a are

 C_a = B_e(Y^c) E_a + Y^((c+1)/2) B_o(Y^c) O_a,
 D_a = B_e(Y^c) O_a + Y^((c-1)/2) B_o(Y^c) E_a.

Hence H_a=CT_Y C_a. The acquired norm tower gives exactly

 C_a^2-Y D_a^2 = rho_c(Norm B) (Norm R)^a.

It does not give C_a. This remains true specifically for B=W^N: its two coordinates are the Lucas sum/difference of W(X)^N and W(-X)^N. Their exponents are shared, but multiplication against the varying conjugate of the OTHER power R^a requires the displayed mixed sum. A Lucas product formula would require the same conjugate pair; rho_c(W) and R are not identified by the present norm closure.

For completeness, the power coordinates have the paid fixed rational transfer matrix

 (E_a,O_a)^T = [[r0,Y r1],[r1,r0]]^a (1,0)^T,
 r0=t(gamma^2-1)/(gamma^2-Y),
 r1=t gamma(1-Y)/(Y(gamma^2-Y)).

All displayed denominators are units under the retained order promises. If u=b^-1 mod m and a=2s+1, the cross phase has the exact lower-rank form (c+1)/2 = u s+(u+1)/2 mod m/2. This removes that phase carry, but does not reduce the integer power a or its high band. Replacing the transfer matrix square by its determinant would remove the additive information.

For a scalar seed z, the collision-bearing norm is

 Norm(T-z)=Norm(T)-z Tr_relative(T)+z^2.

Thus a norm-based tag-prefix or zero-support descent needs the same missing additive coordinate (relative trace 2C_a). Unit norms alone cannot execute that descent; a norm collision is not a whole-algebra collision, and conjugate leaves must not be combined as though they were the same original leaf.

## Precise constructive interface still needed

A sufficient next algorithm is a simultaneous contraction returning all CT_Y C_a, or a restriction-stable collision-bearing contraction with scalar recovery, for the supplied special B=W^N and the displayed rational 2x2 matrix, over all odd a<m, in soft O(m) TOTAL bit work. It must share (i) the varying rho_(a/b) weights, (ii) both parity coordinates, and (iii) high/low integer exponent bands at every level. The O(m) total size of the fixed norm tower is paid; acquiring m rank-m power/weight vectors is not. One explicit vector power or one row contraction is soft O(m); doing that independently for m rows is soft O(m^2), not the desired bound. This observation is a cost of that implementation, not a lower bound on other algorithms.

I have not obtained the required additive state closure from the special-power identity. The positive result is the unit-safe homogeneous tower and exact retained mixed-coordinate interface above. It identifies the needed shared operation without assuming a free Cayley inverse, a square-root branch, or an uncharged native index change. No literature claim, numerical coverage evidence, or generic impossibility claim is made in this focused pass.

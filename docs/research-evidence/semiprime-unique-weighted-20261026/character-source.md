# Character marks on the native completed source: exact Fourier fusion, no colour oscillation

26 October 2026. Paper-only finite calculation; no frozen repository edits or tests. **A genuine cubic coefficient character and an exact constant-rank Fourier fusion are acquired below. On this native completion the character is constant across each entire quadratic colour fibre; the fusion keeps the full clock and its character numerator. No faster residue acquisition is obtained.** This investigates the source, not just a digit decoder.

Inputs read: `completed-source.md`, the frozen pure weighted common-tag and quadratic-lift reports, the one-moment consumer and `native-overlap.md`. The fixed-pair completion, its chirp collapse and the positive-count consumer retain their prior credit. The explicit ellipse count J<23K is used throughout; the older soft-K count guard/prepass is unnecessary and has been removed from `native-overlap.md`.

## 1. What an actually acquired low-order character would tell us

Let n=3^a, a=ceil(e/2)>=2. For a unit integer v modulo 9, choose epsilon(v) in {+1,-1} with epsilon(v)*v=1 modulo 3 and define

    ell(v)=[(epsilon(v)*v−1)/3]_3,
    chi(v)=zeta^ell(v), zeta²+zeta+1=0.            (1)

All arithmetic in (1) is in the PUBLIC rings modulo 9 and 3, before embedding into the native coefficient algebra. Normalizing the sign is multiplicative modulo 9, and multiplication in 1+3Z/9 is addition of the quotients, so chi is a genuine multiplicative character on units. For unit-square u one has u=1 modulo 3 and chi(u)=zeta^[(u−1)/3]_3. It reads u modulo 9, not an arbitrary higher ternary digit.

The extension B[zeta]/(zeta²+zeta+1) has fixed rank two over B and is finite étale because 3 is a unit. In a correct bin, all actual hits have the same u=[R²]_n and their count obeys 1<=d<J<23K<R. Consequently the source

    M_chi=Res_delta sum_(rows,i)
                   chi([j²]_n)/(1+delta−T_j*rho^i)       (2)

has good value d*chi(u). Its nonzero coefficient-vector patterns indeed distinguish the three values 1,zeta,zeta²=-1-zeta without needing the full integer d. This explains why it is a legitimate weak output. It does NOT acquire (2), and does not assume that the polynomial for zeta stays irreducible at the hidden prime: coefficient comparison is in the supplied free quotient algebra.

All order-three characters of the unit-square group modulo 3^a factor through modulo 9. One elementary proof uses the generator 4 of 1+3Z/3^a: successive cubing has v3(4^(3^r)−1)=r+1, so the kernel of any map to the order-three group contains the subgroup 1+9Z/3^a. Thus repeatedly choosing a different order-three character on the WHOLE original group does not reveal higher digits.

An adaptive restriction is possible in principle: after a genuine known prefix u=u0 modulo 3^r, the quotient u/u0 belongs to 1+3^r and ((u/u0−1)/3^r) modulo 3 is a homomorphism on that subgroup. But restricting the native row list and acquiring its next selected residue are additional operations; the character theorem does not supply those residues. A direct higher-order global character instead needs higher roots of unity, whose uniform extension rank grows with 3^r rather than staying constant. No hidden local field root is supplied for free.

## 2. Execute the coefficient character on every actual colour fibre

For a nonaxis completed pair let g=gcd(a,K)=gcd(b,K), Acoef=a/g, Bcoef=b/g. The actual stationary congruence gives

    j²=N*Bcoef/Acoef modulo K/g.

The completed ellipse has g²<=K/sqrt(3), so n divides K/g and in particular 9 divides K/g. Therefore EVERY colour of this pair, across both opposite branches and all lifts, has the SAME canonical u=[N*Bcoef/Acoef]_n. This is an arithmetic equality modulo public n; it is not division by the zero element N inside B.

Applying (1) gives the explicit separable coefficient mark

    chi(u)=chi(N)*chi(Bcoef)*chi(Acoef)^(-1).      (3)

This costs polylog N per acquired pair. It is constant across the ENTIRE quadratic colour-lift chirp. In particular, the hoped-for Gauss oscillation in its lift parameter is absent; even the primitive g=1 fibre consists only of opposite roots with the same character. Higher-content fibres also have constant u modulo n, not merely modulo 9. This applies to any tag digit depending only on u, once a legitimate colour restriction has been made.

Let S_(a,b)(delta) denote the ACTUAL finite sum over all compatible colours and the original clock, with canonical phases and starts retained. Then the full nonaxis source is exactly

    sum_(a,b) chi(N)*chi(Bcoef)*chi(Acoef)^(-1)
                  *S_(a,b)(delta),                         (4)

with filtered axis rows added separately using their actual j² marks. Equation (4) is an initialized source identity: all marks, pair supports and phases are acquired in soft K. It does not evaluate the S_(a,b). The axes cannot be assigned the ratio mark (3) with a zero coefficient.

The OLD quadratic-stratum identity therefore passes the character mark through unchanged. Each collapsed GP string gets its known square multiplicity times chi(u); there is no new cancellation among the colour lifts. The existing all-string-value engine computes (2) in soft K^(5/4), with constant-rank extension cost. A finite Fourier split of Acoef,Bcoef modulo 9 gives only constantly many coefficient classes and the same retained row/clock mass. Any useful cancellation ACROSS distinct coefficient pairs would need a new identity coupling their actual varying pi^ell*barpi^(a+bN) roots; separability of the coefficient mark alone does not give that contraction.

## 3. Execute a genuine constant-rank phase-Fourier fusion

There is nevertheless an exact finite character identity at the leaf source. Write A=1+delta, z=T_j*rho^i and chi(u)=zeta^k. Direct geometric-series filtering, or clearing the three denominators, gives

    sum_(b=0)^2 zeta^(-b)/(A−zeta^(b+k)*z)
       =3*A*zeta^k*z/(A³−z³).                    (5)

This is a finite rational identity over the constant-rank extension, not an analytic series specialization. It really encodes the digit in a Fourier coefficient. At a native hit z=1, the only singular term on the left is b=-k modulo 3, with residue zeta^k. The right side has A³−1=3delta+..., so its residue is also zeta^k, not three times that value.

All nontrivial phase rotations are certified unit at native delta=0 unless they rotate onto the unphased term: z belongs to the K-rough group generated by beta and W, whose orders are prime to 3 at EVERY local component. Hence zeta^c*z=1 with c=1,2 is impossible in the étale extension. No unknown local order, primitive native root of unity or numerical singular denominator is inverted. The unphased denominator still carries exactly the original collision.

Summing (5) over the ACTUAL finite rows and clock proves the source identity

    M_chi=Res_delta sum_(j,i)
            3*(1+delta)*chi(u_j)*T_j*rho^i
                      /((1+delta)³−T_j³*rho^(3i)).         (6)

All original canonical carries and endpoints remain inside the supplied T_j and i range. The denominator has cubed targets and clock, but still h positions; K-roughness preserves their orders. The numerator retains chi(u_j)*T_j*rho^i. Thus phase completion does not make the mark disappear or shorten the clock. It would be incorrect to take only the unweighted sum of the three rotated terms: the resulting Fourier mode has residue one and loses the character digit.

Equation (6) can be fully executed by the existing shared geometric engine on T_j³ and rho³. Acquire all row values, classify to flags or a factor, and sum chi(u_j) times the flags. Cubing is injective in the native group, so these are EXACT (2) flags. The cost is still soft(J+sqrt(Jh))=soft K^(5/4); no h-entry phase list or increasing Laurent precision is needed. A direct summation of the fractional numerator clock weight in (6) is a possible narrower future target, but has not been acquired at soft K.

## 4. Scope of cancellation and the remaining useful operation

The source experiment gives two different facts, both on the actual native input. First, a genuine coefficient character is cheap and separable, but it has NO oscillation within a fixed pair's completed colour fibre. Second, auxiliary phase-Fourier fusion retains the desired character pole with certified unit extra rotations, but simply cubes the denominator's geometric clock and keeps h and the character numerator.

These statements do not rule out a cross-pair Gauss/Weil or knot transform. Such a theorem would have to sum (4) across varying coefficient pairs with their actual phases and finite clock, or evaluate (6) without the old shared factorial remainder. It cannot use ordinary root-of-unity orthogonality on the native q clock, erase canonical carries, omit filtered axes, or transfer an original-bank tag to raw-torus aliases.

A constant-order character alone supplies only the first nontrivial ternary tag digit globally. An adaptive chain of restricted-subgroup digit sources is valid as an output specification, but its first unresolved aggregate acquisition already has the old J-by-h scale. No faster digit supplier, whole-query acquisition or new exponent is proved here.

# Guarded antipodal Dickson query and the period-specific dyadic test

24 October 2026. Scratch only. Read proposal.txt and the preserved torus-frobenius.md and structured-twist-addendum.md in semiprime-collision-representation-20261022 and semiprime-twist-character-20261022. No repository edits or examples. Rank-two torus rows alone are not a new factoring mechanism: the same character-Frobenius row formula works for an ordinary Cayley norm-one point. The period-specific identity is tested separately below.

## Inputs and native antipodes

Grant the proposed soft-m acquisition of U in B=R[tau]/(tau²-D), D=chi(-1)m, and its certified unit norm. Thus W=U/bar(U) is an acquired norm-one point. Throughout the row and fold formulas, W means consistently either this raw point or its guarded common public power from period-recovery.md; the period functional identities persist when that SAME public exponent is applied at every scalar point, while cheap palette-value acquisition does not certify palette orders or pay separate order screens. Rank-two operations cost O(1) residue operations; both 2 and D are units. Let d=m², q=W^d and

    T_j=W^E_j, E_j=ell_j+chi(j)*(N+a_j).

All E_j have O(log N) bits, so all O(m) T_j are genuinely acquired in soft m. This changes the older degree-m algebra row-acquisition cost but does not itself acquire the long comparisons.

For m=3 modulo 4, opposite tags have opposite character, equal a, and ell_j+ell_(m-j)=d*t_j with t_j in {-2,-1,0}. Therefore

    T_(m-j)=q^t_j/T_j.                               (1)

This keeps the integer carry t_j. The own-prime identity implies T_j=q^I for its original bounded I, but no order or decoder for q follows from the original beta order. For m=1 modulo 4, the character does not flip and (1) is unavailable in this form; retain the ordinary rank-two geometric query.

## An actual unit-safe scalar fold of every antipodal pair

Partition opposite pairs by t=t_j. For one class set a=q^t. Each pair has the same acquired element

    C_j=T_j+a/T_j.

Conjugation satisfies bar(C_j)=a^-1 C_j. To obtain an honest scalar rather than assume a square root of a, acquire a unit v with bar(v)=a^-1 v as follows.

* Try v1=1+a. Its norm is 2+tr(a), a scalar. A proper gcd of that norm with N factors N; a unit norm permits its explicit conjugate-over-norm inverse.
* If gcd(norm(v1),N)=N, tr(a)=-2 modulo N. Set v=tau*(1-a). Its conjugation law is the same and its norm is -D*(2-tr(a))=-4D, a certified unit. This branch uses neither a hidden local field nor a generic zero-norm-implies-zero assertion.

The remaining case is a proper factor, already returned. Thus a lawful v is always acquired in O(1) residue work per carry class. Now

    c_j=C_j/v,
    s_i=(q^i+a*q^-i)/v

are globally fixed by conjugation, hence are scalars in R. Fixedness implies vanishing tau coefficient because 2 is a unit. Opposite rows give the same c_j, and an own equality T_j=q^I implies c_j=s_I.

The seed sequence obeys the initialized Dickson recurrence

    s_(i+2)=(q+q^-1)*s_(i+1)-s_i,
    s_0=(1+a)/v, s_1=(q+a*q^-1)/v.

All startup values and the scalar recurrence coefficient are acquired in O(1). The target polynomial F_t(X)=product_(pairs in class t)(X-c_j) is acquired in soft J_t, with no interpolation or collision inverse. This is a genuine scalar antipodal contraction, but it is a generic torus operation rather than a period-specific advance.

## Full initialized terminal evaluator and its unchanged degree

The attempted query is V_t=product_(0<=i<L)F_t(s_i), L=2m²+2. It has a known local zero on the class containing the own tag. Build the explicit polynomial over B

    G_t(Y)=product_j (Y²-v*c_j*Y+a), deg G_t=2J_t.

At Y=q^i, each factor equals v*q^i*(s_i-c_j). Thus exactly

    V_t=v^(-J_t*L)*q^(-J_t*L*(L-1)/2)
            * product_(i<L)G_t(q^i).                 (2)

Every prefactor is a known unit. The polynomial is acquired by a product tree in soft J_t rank-two work. For block size b construct product_(r<b)G_t(q^r Y) by geometric doubling, degree 2J_t*b; evaluate at q^(bt) by monic MPE and multiply the answers, including the paid short tail. No value or point difference is inverted.

The complete cost is

    soft(J_t*b+L/b+J_t)=soft(J_t+sqrt(J_t*L)).

Carry classes are only three, so summing their costs stays soft(m+sqrt(mL))=soft m^(3/2). Pairing halves the target count, but the Laurent-to-geometric terminal polynomial has twice that degree. No exponent is saved. This is a fully initialized evaluator of the folded scalar product, not a mere recurrence specification. Each carry class has its own common seed recurrence; there are only three classes, so all three startup/target polynomials and their terminal computations are included in the displayed summed bound.

More importantly, folding can introduce other matches. Over either hidden field the exact factorization is

    v*(s_i-c_j)=(q^i-T_j)*(q^i-a/T_j)/q^i.

It represents the OR of two actual original period-row matches, because a/T_j=T_(m-j). This implication is valid even in split quadratic algebras: taking norms gives a product of two scalar norms, so a zero in the hidden field forces one norm zero; the norm-one collision lemma then gives equality of that corresponding pair. Scalar restriction/MPE can localize the folded product. At a saturated scalar leaf, compute the two actual difference norms. A proper gcd factors; otherwise a saturated difference norm is a global original-period-row collision. Conditional on the paid surviving-point/order guards in period-recovery.md, its signed sum/difference decoder factors from this leaf. Thus there is no extra fold-recovery gap on that guarded branch. Without those period-order guards there is still no inherited original-beta decoder: keeping the old beta channel does not supply W order for free.

## Period-specific positive identity and actual acquisition

For the Gauss period product, multiplication gives an additional identity absent for a generic Cayley point:

    U(x)U(-x)=U_χ(2)(-x²),
    W(x)W(-x)=W(-x²)^χ(2).                            (3)

Indeed each paired factor (x+zeta^r)(-x+zeta^r)=zeta^(2r)-x², and multiplication by 2 sends the quadratic-residue set to itself or its complement according to chi(2). Taking the conjugate quotient gives the second equation with the stated sign/exponent.

The points beta, -beta and -beta² are unit-safe under the original odd-order screen. Their period norms have numerators beta^m+1, 1-beta^m and 1-beta^(2m), respectively, and corresponding scalar denominators beta+1, 1-beta and 1-beta². All are units because the beta order is odd and >16m². Repeated dyadic beta powers preserve that odd order. A requested K of these unit-safe signed dyadic scalar evaluation points can be acquired, and the already acquired degree-(m-1)/2 period polynomials evaluated there by monic MPE in soft(m+K); norm inversions are certified and charged. Arbitrary scalar evaluation points do not inherit this unit promise. Values at K=m points therefore can be paid in soft m. This does not give all K*m native row powers for free: those explicit rank-two targets cost soft(K*m) to acquire in the present construction.

## Tested fused-query use of the dyadic identity

For each native difference exponent k=E_j-d*i, equation (3) gives

    W(beta)^k*W(-beta)^k=W(-beta²)^(chi(2)*k).         (4)

The residual of (4) is identically zero globally for EVERY supplied k, including wrong tags and indices. Using it as a selector therefore recreates an all-row invariant rather than exposing the own tag. Expanding a product of difference terms instead gives

    (W(beta)^k-1)*(W(-beta)^k-1)
      =W(-beta²)^(chi(2)*k)-W(beta)^k-W(-beta)^k+1.   (5)

Equation (5) is division free, but its right side is a SUM of three distinct exponential sequences. It is not a single shorter difference and does not halve the i horizon. Across all j and i, multiplying these sums is a new acquisition task. Because (5) equals the two original difference factors on its left, its aggregate can be acquired by TWO ordinary geometric-product queries, retaining the existing soft sqrt(JL) scale. Direct expansion of its right side produces multivariate geometric data and is not assigned a cheap univariate recurrence. No product of sums on the right is claimed acquired through (4).

There is also no zero-support cancellation rule: if ab=c, c=1 need not imply a=1 or b=1, while a=1 need not imply c=1. Thus replacing the beta leaf by the -beta² leaf is not certified by (4). At the own prime, native arithmetic makes all these norm-one bases hit at the own I, because each has order dividing P-chi(P), but that common coverage does not identify I or recover a proper factor from arbitrary/global hits. The stronger period bridge has not supplied the missing collision separator.

Iterating (3) introduces beta^(2^r) arguments and their signs. Congruences of 2^r modulo m permute period roots but do not close the scalar beta orbit: beta^(2^r)=beta would require an unavailable order relation. A full product over root twists can collapse to a scalar norm, but then removes the orientation/character data that this branch was meant to retain. No free iterates or completed-orbit theorem is used.

## Ledger and constructive status

| Operation | Acquired cost | Output/limitation |
|---|---:|---|
| Granted period polynomial/U and W | soft m | rank-two unit with extra beta link |
| All native rank-two rows | soft m | true constant-dimension acquisition |
| Guarded antipodal scalar fold | soft m | duplicate targets paired; no order assumed |
| Folded full product (2) | soft m^(3/2) | exact scalar product; guarded period decoder supplies recovery |
| K period point values | soft(m+K) | unit guards paid |
| All row powers at K points | soft(Km) | explicit cross-family acquisition charge |
| Dyadic residual (4) | O(1) per supplied exponent | globally zero, no selector |
| Fused product of sums (5) | no soft-m acquisition | old blocking only |

The positive delivered operation is a unit-safe scalar antipodal Dickson query with all startup data, explicit terminal conversion and actual cost. The period-specific dyadic identity is valid and cheaply evaluable, but the tested use preserves the full long-product acquisition. The guarded surviving period controller supplies folded-leaf recovery; unconditional supply of that guarded point remains unresolved. Neither rank two, character splitting nor period functional identities alone establish a new N^(1/6) whole query. A positive continuation must exploit (3) with a genuinely acquired smaller selector or a fused terminal product that avoids the remaining degree-times-length interaction.

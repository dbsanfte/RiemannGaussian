# Character cancellation and whole-family aggregates

22 October 2026. This continuation follows the user's request to give
twists, colour and character cancellation special focus. It acquires an
entire native weighted Gauss product, and a shared representation of all
antipodal target-pair products, without constructing their quadratic-size
coefficient table. The cost is soft O(ell+m) for a supplied auxiliary prime
ell. These are **unit aggregates**, not the collision product. No improved
whole-input factoring exponent or new Lean theorem follows yet.

The original covered scalar query still costs soft O(J+sqrt(JL)), with
J of order m and L of order m². Its sufficient soft-O(m) acquisition
theorem remains open. In particular, this packet does not count an exact
identity or a compact description as acquisition of its collision zeros.

## A weighted product really is acquired

Retain the canonical integer weights a_j=N*j^(-2) mod m in [1,m), for
1<=j<m. For the public auxiliary prime ell with m dividing ell-1, use the
previously acquired packed Gauss quotients in

    A=(Z/N)[X]/(X^m-1),   g_1^E=C_E*g_(E mod m),   g_0=-1.

Assume gcd(N,ell*m)=1. The proof-side Gauss sums g_j need not be expanded
in a joint additive/multiplicative character algebra. Acquire instead

    U=-C_m=g_1^m,
    E0=(1/m)*sum_(r<m) X^r,
    D=E0+(1-E0)*ell.

The trivial-character projector E0 is essential: g_j*g_(m-j) is ell on
each primitive character component and 1 on the trivial component. Thus
the full identities are

    g_j*g_(m-j)=D,       C_j*C_(m-j)=U/D.

Since a_(m-j)=a_j as INTEGERS, putting
A0=sum_(1<=j<=(m-1)/2) a_j gives the exact cancellation

    product_(1<=j<m) C_j^a_j = (U/D)^A0.

Only one acquired vector C_m, the explicit projector, and cyclic
polynomial powering are needed. The algorithm never asks for the m
separate length-m vectors C_j. All integer exponents have O(log N) bits
in the retained regime. The cost includes the existing soft-O(ell+m)
histogram construction; no small auxiliary-prime supply theorem is added.
See the [full proof](reports/gauss-weighted-norm.md) and
[independent review](reviews/review-gauss-weighted-norm.md).

## All antipodal target-pair products share three vectors

For the corrected Gauss targets from the preceding cancellation work,

    T_j=g_1^ell_j * g_j^a_j * rho_(j^-1)(C_N) * g_(N/j mod m),
    q_G=g_1^(m²)=U^m,

the centered native b representatives give
ell_j+ell_(m-j)=-m²*s_j with s_j in {0,1,2}. The reciprocal Gauss identity
then gives

    T_j*T_(m-j)=q_G^(-s_j)*D^(a_j+N).

This entire family has an acquired shared representation. Set

    W_s=(1-E0)*q_G^(-s)*D^N,  s=0,1,2.

Then each pair is ell^a_j*W_(s_j)+(-1)^s_j*E0. Three length-m vectors and
O(m) scalar/index data suffice; expanding all pair vectors would have
quadratic output size and is not included. With S=sum s_j and
h=(m-1)/2, the complete target product is one actually acquired vector:

    product_j T_j=q_G^(-S)*D^(A0+N*h).

Signed powers are safe without an unchecked polynomial inverse:
U*rho_(-1)(U)=D^m explicitly supplies U^(-1). All exceptional signs and
centered carries are retained. The same pairing formula works for any
public union of complete antipodal pairs, with the corresponding sums.

This is the information extracted by the cancellation: a whole weighted
unit product, pair norms, and the constant term of the conceptual target
polynomial. It does not acquire product_j(T_j-t), the other elementary
symmetric coefficients, or the long target-minus-seed product. Comparing
the unit aggregate with its proved formula gives an identity at both
hidden primes, rather than a factor separator.

There is also an exact conjugation identity,

    T_j*rho_(-1)(T_j)=D^E_j,   E_j=N+a_j+ell_j,
    q_G*rho_(-1)(q_G)=D^(m²).

A true equality T_j=q_G^I in the WHOLE local character algebra modulo a
hidden prime therefore projects to ell^E_j=ell^(m²*I) on primitive
components. The own-tag Frobenius equality has that scope. A hit in just
one character component need not survive at its conjugate component.
This projection is one-way and supplies no prepared-order or recovery
contract for ell; ell is not the original prepared scalar gamma.

## Twists and multiplier recursion: what is paid

The [coherent-root preparation](reports/coherent-root-preparation.md)
removes an unnecessary root-extraction requirement. Before forming the
rows choose gamma=gamma0^(2^d), d=ceil(log2(8m)). Odd local orders are
unchanged. All original target and step roots through d levels have
explicit public exponents and cost soft O(m) together. A nonzero
annihilator K of the rebased gamma is already an annihilator of gamma0,
since its odd orders divide 2^d*K exactly when they divide K.

Complete root-of-unity twist fibres also have a
[paid target-polynomial norm](reports/twist-norm-aggregation.md):

    F_b(Z)=product_j(Z-y_j^b),   b=2^d.

Its coefficients cost soft O(J), and
H_e(y_j^b;q^b) has exactly the same hidden-prime zero support as
H_e(y_j;q), because b-powering is injective on the odd subgroup. No
splitting algebra or companion-unit values need be acquired. An arbitrary
nonidentity element of an etale algebra is not automatically nonidentity
on every component; the proof uses scalar injectivity or componentwise
primitive labelled roots.

This norm collapses complete twist fibres. It does NOT collapse the
different geometric origins generated by the multiplier recursion.
The remaining resultant Res(F_b,H_e(.;q^b)) still contains the long H.
The [independent review](reviews/review-twist-norm.md) checks this
distinction explicitly.

The [multiplier-two identity](reports/multiplier-recursion.md) retains
the original q and its endpoint factors. If e'=Legendre(2,m)*e,
Q=q^m and D_K=K*(m+1)/2, write

    A(X)=H_e(X;q²,K),
    B(X)=Q^D_K*H_e(X/Q;q²,K).

Let Lodd and Uodd be the products over odd r in R_(e') of respectively
X-q^r and X-q^(r+2mK). Then

    Lodd(X)*A(X)*B(X)=Uodd(X)*H_(e')(X;q,2K).

The endpoints at any level are acquired, including nonunit recovery.
The complete explicit tree, however, costs soft O(m+J*K), because it
requests J*2^d shifted origins at depth d. This is a ledger for that
algorithm, not a lower bound. The
[native point analysis](reports/native-multiplier-closure.md) derives
exact Mobius candidates and bounded no-wrap maps, while retaining the
row-dependent cubic carries. Those tests concern literal integer-exponent
reuse; they do not exclude local-order coincidences. The
[review](reviews/review-native-multiplier.md) also proves a positive
original exponent gap for every recursive endpoint leaf.

## The remaining constructive query

For the ORIGINAL scalar source, all row translations and colour-mask
boundaries are already paid. A sufficient smaller output is

    R_e(S)=product_(j in S, sign_j=e) H_e(y_j),

for public groups S, uniformly in soft O(|S|+m). One path through a
balanced partition then selects a collision-bearing row; the original
unmasked interval descent costs soft O(sqrt L). It would also suffice to
support groups of complete antipodal pairs, select one pair, and evaluate
its two original scalar rows. Thus a new identity may preserve the pair
symmetry throughout localization. No such collision-bearing group query
has been acquired in this packet.

The current exact norm expression uses the degree-J target algebra and
K transitions of a degree-about-m seed-block polynomial. Forming the
degree-about-m² scalar transition polynomial, or all J*K quotient
vectors, exceeds the budget. A direct norm-only algorithm could avoid
both outputs; neither is a necessary lower bound. This is the specific
contraction sought in [direct-character-norm.md](reports/direct-character-norm.md).

Other investigated cancellations are recorded to preserve their exact
scope. The coupled-palette Casoratian has an acquired short coefficient
but retains the original long product as a multiplier. Additive Gauss
projection returns the previously acquired endpoint jets. The normalized
quartic collision mask is the union of two partial matchings, so its
deficit has only O(log J) bits, but that deficit is not acquired by its
sparse graph description. Public Gauss exponent palettes reduce to
C_E=U^floor(E/m)*C_(E mod m); the cocycle commutators are global identities.
None of these statements is a general impossibility theorem.

## Evidence and validation

The reports are final scratch reports copied verbatim; provenance maps
their historical paths. Three independent mathematical reviews cover the
weighted aggregate, twist/root preparation, and native multiplier/cost
identities. Review-requested component and integer-exponent qualifications
are incorporated, with exact fingerprints in validation.json. Earlier
unreviewed exploratory reports are labelled as such there.

Primary literature checks include finite elliptic products, modular
equations, fast explicit-input reciprocity, and Gauss distribution
identities. [The literature report](reports/finite-character-product-literature.md)
and source-pins.json distinguish full-text inspection from abstract-only
leads and inaccessible fetches. No inspected theorem is treated as an
implicit long-product evaluator. The weighted aggregate above has a
direct finite proof; it does not depend on a new analytic theorem.

All prior frozen packets are preserved. This continuation adds no Lean
backend, implementation, success-example campaign, broad build or
publication. The whole-input soft-O(m) collision acquisition, complete bit
proof and Lean composition remain open.

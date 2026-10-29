# Alternative expressions for the two factor-tag coefficients

26 October 2026. This follows the user's request to seek other expressions
and domains for the uniform two-coefficient target proved in the
[preceding handoff](../semiprime-axis-supplier-20261026/hybrid-handoff.md).

**Useful simplification:** the original coefficients can be replaced by
a pair that needs no derivative of the long clock polynomial. Residue,
matrix and spanning-tree expressions also give precise alternatives, and
short ordinary/tagged moment lists are acquired in soft O(K). None yet
provides the final ratio at that cost. The complete native query bound
remains soft K^(5/4); the simpler monic target's initialized fallback
remains soft K^(3/2). No sixth-exponent factoring algorithm is claimed.

## 1. Fixed inputs and recovery promise

Use either acquired monic family from the preceding packet, with J<=K
row roots y_j, weights w_j=[j]_n, q=pi^H, h=2H+1 and H=K^2.
One of the two families has exactly one zero among

    a_(j,i)=1-y_j*q^(-i),  0<=i<h,

at the nonsplit prime R. Its tag w_j is R mod n. The scalar/torus
preparation and this uniform promise are already proved; n|K and
n>=K^(1/3), with n=K always available. A pair with nonzero denominator
and that ratio at the good prime has the existing soft-K norm/gcd,
integer-label and HH recovery. No other-prime promise is required.

The exact original values are the sums of all products omitting one
leaf, with U additionally weighted by the omitted leaf's row tag.
Recovering their projective value allows different pairs with the same
good-prime ratio; exact global equality to U,V is unnecessary.

## 2. Five concrete expressions and their acquired inputs

Put G(X)=product_(i<h)(1-X*q^(-i)), R_j=G(y_j), and
C_j=product_(l!=j)R_l. Some reports instead use the monic G; it differs
by a known common unit and gives the same projective claims.

| Expression | Exact useful output | What is already acquired; what remains |
| --- | --- | --- |
| Row cofactor sum | V0=sum C_j, U0=sum w_j C_j | Valid replacement pair; removes G' entirely. Computing R_j or these two sums directly remains unpaid. |
| Directional resultant | D_F(g;H)=[epsilon]Res(F,g+epsilon H), with two supplied directions | F,H0,Hw are acquired in soft J without separation inverses. The remainder g=G mod F, or just the two directional scalars, is not. |
| Regularized linear solve | For M=diag(R_j)+11^t, M^(-1)1 is the hit coordinate vector at the good prime | Its weighted scalar is the tag, independent of amplitude. The missing matrix diagonal is exactly the long R_j list. |
| Cycle spanning trees | V is the cycle tree polynomial; U weights the omitted edge by its tag | The finite identity is exact. Cleared row contraction still needs G(y_j) and its derivative, so this direct graph algorithm pays the old cost. |
| Full-leaf moments / Stein equation | Short ordinary and tagged moments are acquired; the normalized singular solve selects the hit | O(J) moments cost soft J. The exact trace recurrence has order at least h from moment zero, so the usual short Krylov/Prony closure is not available. |

The first three formulas are developed in
[residue expressions](residue-expressions.md) and
[structured expressions](structured-expressions.md). The cycle, normalized
Stein equation and explicit moment-to-reset map are in
[combinatorial expressions](combinatorial-expressions.md).

## 3. The derivative-free replacement is proved, not assumed

At the good prime precisely R_(j*) is zero. Thus C_(j*) is nonzero
and every other C_j is zero. Therefore

    V0=C_(j*) != 0,
    U0/V0=w_(j*)=R mod n.

The original coefficients contain the additional nonzero scale
`hG(y_(j*))-y_(j*)G'(y_(j*))`. It is unnecessary for the ratio.
This reduces the requested information, without proving a complexity
separation between the two requests. If the R_j are supplied, prefix and
suffix products compute the new pair in O(J) operations without inverses.

For the resultant version, let F(X)=product_j(X-y_j) and acquire

    H0=X*F'-J*F=sum_j y_j F/(X-y_j),
    Hw=sum_j w_j*y_j F/(X-y_j).

These are exact polynomial cofactors, acquired by weighted product trees
in soft J. At the unique common root theta, H0(theta)=theta F'(theta)
is nonzero and Hw(theta)=w_(j*)H0(theta). Consequently the two directional
norm coefficients have the correct ratio even if other row roots repeat.
This avoids assuming a globally invertible Vandermonde or a separated
row alphabet. The derivative-free pair and the directional pair are
alternative output specifications, not two independent acquisition gains.

## 4. New paid short data, and the precise closure question

Let L=diag_(j,i)(1-y_j q^(-i)), of dimension Jh. For s<=2J,

    trace(L^s)=sum_(t=0)^s (-1)^t binom(s,t) p_t c_t,
    p_t=sum_j y_j^t,
    c_0=h, c_t=(1-q^(-ht))/(1-q^(-t)) for t>0.

The tagged version replaces p_t by sum_j w_j y_j^t. Product trees and
formal power series give both power-sum lists; one factorial convolution
per list gives the moments. All denominators are actually certified
units: t<=2J<=2K<16H, and integers through 2J are below both primes.
The long numerators are acquired by powering and are not inverted.
The total cost is soft J, including arrays and initialization.

This is useful new input for another method. It does not authorize a
short recurrence for L: one row already gives h distinct eigenvalues.
Every eigenvalue's multiplicity is between 1 and J, below the good
characteristic, so ordinary trace weights do not cancel. The full trace
sequence's homogeneous constant-coefficient recurrence order is at least
h; after dropping the initial zero-eigenvalue transient the bound is
at least h-1. Both exceed O(J). This is specific to the proposed full
diagonal/moment representation, not a lower bound against every possible
compressed observable or algorithm using the known q and F.

## 5. What the domain checks rule out, and what remains open

The row regularization has a cheap rank-two displacement
`diag(y)M-Mdiag(y)=y1^t-1y^t`. But this operator annihilates EVERY diagonal
matrix, so the generator contains none of the missing R_j. Making the
operator invertible reintroduces the unknown diagonal. The checked
structured-matrix algorithms require that missing input or an invertible
displacement description. Their hypotheses cannot be replaced by the
ordinary rank-two leaf array.

The exact one-clock three-state recurrence is fully initialized by
F, F' and the weighted cofactor polynomial. Its old blocked execution
still pays soft(J+sqrt(Jh)). For the particular rational-telescoping
proposal, f(X)=XF'(X)/F(X) cannot equal A(qX)-A(X) for a rational A:
the residues of f(X)dX/X around a nonzero q-orbit sum to the number
of F roots on that orbit, between 1 and J and nonzero in the good
field. A rational coboundary would have orbit residue sum zero.
This excludes that precise endpoint shortcut, not other ratio algorithms.

The strongest open acquisition target is now the two row cofactor sums
or directional norms directly from acquired F, y_j, w_j, q and h.
The cheap moment data and the normalized singular Stein equation offer
another concrete starting point. Computing a full row-value vector,
full adjugate or long minimal polynomial is sufficient but still too
expensive. No new method to avoid those costs has been established here.

## Review and preservation

Three Sol 6.1 investigations were checked against primary resultant,
structured-matrix, adjoint and spanning-forest literature. The formulas
used here are finite algebraic identities; probabilistic positivity and
unguarded field inversions were not transferred to the composite ring.
The independent review is [review-expressions.md](review-expressions.md).
Source scope, preservation and validation are recorded in
[sources.json](sources.json), [review.json](review.json) and
[manifest.json](manifest.json). No factoring implementation, numerical
campaign, Lean, public-asset changes, commit or push were performed.

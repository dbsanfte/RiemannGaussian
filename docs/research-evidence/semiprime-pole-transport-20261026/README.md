# Finite pole transport and correlated reductions of the long query

26 October 2026. This pass executes three decompositions with finite
boundaries and charged initialization. **A degree-J pole transport is
proved, but no faster whole-family acquisition algorithm is obtained.**
The retained uniform weighted query remains soft O(K^(5/4)); the requested
soft O(K), and hence the complete sixth-rate factoring proof, remain open.

These are reviewed paper derivations under the existing native preparation
and recovery contracts. There is no new implementation, Lean theorem,
numerical success campaign, commit or push in this packet.

## Preserve the right output

The [original six-domain target](../semiprime-six-domain-acquisition-20261026/README.md)
is the packed additive coefficient

    C = [delta^-1] sum_(j,i) w_j/(delta+1-T_j q^-i).

Writing D(Y)=prod_j(Y-T_j) and
A_w(Y)=sum_j w_j prod_(k!=j)(Y-T_k), the exact row collapse is

    C = [delta^-1] sum_(i<h)
          q^i A_w((1+delta)q^i)/D((1+delta)q^i).

D and A_w are acquired in soft J, including repeated rows. This collapses
the row sum but does not acquire the remaining clock functional. The
[existing packed-to-norm construction](../semiprime-separated-selector-20261026/packed-to-norm.md)
also expresses it as one marked logarithmic derivative of a geometric norm.

The new pole-transport calculation uses the separately proved **unique-hit
retuned family**, where a weak numerator pair with common nonzero amplitude
suffices. Changing that amplitude is legal for this pair. It is not an
identity for C when the original family has several hits.

## A pole can move without a growing denominator

Let L[f]=sum_(i<h) omega_i f(q^i), with
omega_i=(q^i)^(h-1)/W_h'(q^i). Define

    K_d(X)=prod_(s=1)^d (q^h-q^s X)/(1-q^s X).

Then the finite identity is

    L[f] = sum_(i<d) omega_i f(q^i) + L[K_d(X) f(q^d X)].

The weights telescope exactly. The numerator of K_d kills the last d
clock nodes, so there is no uncharged overhang term. For f=p/(F+delta),
after checking the first d actual leaves, reduce K_d p(q^d X) modulo
F(q^d X)+delta. The new numerator has degree less than J and preserves the
selected residue. The [transport proof](pole-transfer.md) includes an
interpolation implementation with certified unit denominators.

Composing shifts respects the moving quotient algebra. The missing step
in doubling is acquiring the multiplier at the new modulus, whose
denominator checks the next original clock strip. Its resultant is exactly
the prefix product, up to a known unit. No fixed-modulus obstruction is
misapplied to the valid moving substitution.

For J=O(K^(2/3)), the existing shared product engine checks a prefix of
length O(K^(4/3)) within soft K. This is a conditional cheap branch using
an existing engine, not a new coverage theorem. Covering the entire
h=O(K^2) clock by the evaluated adaptive method still costs
soft(J+sqrt(Jh)). On the unique branch one can omit K_d altogether and
retain only the rebased weak pair, but the skipped prefix still has to be
accounted for.

## Two other cancellations, with their remaining operations

| Decomposition | What is actually eliminated or acquired | What remains |
| --- | --- | --- |
| [Adjoint displacement](retuned-composition.md) | The interior matrix contraction becomes one rank-one boundary pairing; all bidiagonal pivots are certified units. | Computing that boundary still takes J known fast actions or h scalar steps. |
| [Moving graph correction](retuned-composition.md) | All powers of the degree-J quotient correction needed for one column are acquired in soft K. | The correlation between these powers and all implicit input columns is not acquired. |
| [Arithmetic phase fibres](arithmetic-transport.md) | Complete quadratic phase fibres, including axes and carries, become O(log g) geometric strings per parent. | The evaluated product/localization cost is soft(K^(5/4) g^(1/4)); fewer strings are longer. |

The arithmetic rebuild is a covered family with an actual leaf consumer.
It does not inherit the retuned selected bank's unique-hit theorem.
Its original-scale endpoint bounds and canonical phase wraps are checked.

Short explicit modular composition was already affordable in the earlier
repository audits. Rechecking the newer two-relation-matrix paper does not
change that credit: reducing the structured implicit input remains the
missing operation. The [divisor-cover audit](divisor-cover.md) likewise
distinguishes a conditional arithmetic coverage channel from a proved
shortcut for this clock query.

## Review and next test

See [pole review](review-pole-transfer.md),
[composition review](review-retuned-composition.md),
[arithmetic review](review-arithmetic-transport.md), and
[literature review](review-divisor-cover.md). The source and preservation
records are in `sources.json`, `review.json`, and the manifest.

The sharp remaining transport target is to account for both sides of a
long jump while acquiring only the useful residue or weak pair. A proposed
shortcut must either share the actual prefix work or preserve its boundary
residue cheaply; simply removing that boundary would lose coverage. The
decompositions above do not rule out such an algorithm.

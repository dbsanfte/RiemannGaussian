# Finite eta recovery of the complete expanding correction

Finite eta now recovers both original strip segments, including their
endpoints, and all genuine carrier poles in the actual real-bottom
rectangles. Along constructed expanding contours, one common truncation
at each scale approximates the full signed correction with error below
`1/(n+1)`. The independent arithmetic source ceiling remains open.

## The full completion domain

The same completion factor `H`, correction `L=H'/H`, and denominator
`D=eta'+(1+L)*eta` work throughout

```
0<Re(s),  s!=1,  pairedEtaFactor(s)!=0.
```

Lean proves `H*eta=xi`, `H*D=xi+xi'`, and the original spectral identity
`E(z)=H(s)*D(s)` for `s=1/2-i*z`. The completion is analytic and nonzero
there. No division by eta is introduced; the finite odd/even weights
remain exactly `1+L(s)-log(n)`.

The original open-strip results remain available. The wider results are
in [PairedEtaCompletionDomain.lean](../RiemannGaussian/PairedEtaCompletionDomain.lean)
and [SuzukiEtaExtendedCarrier.lean](../RiemannGaussian/SuzukiEtaExtendedCarrier.lean).

## Both complete strip segments

The dyadic completion exceptions form a countable set on spectral height
one half. Lean constructs vertical coordinates in every open interval
avoiding their real projections and the full xi/carrier singular
projections. Each compact segment above height minus one half on such a
line has uniform finite-carrier convergence. Eventual finite denominator
nonvanishing, continuity, and weighted integral convergence are proved.

This includes the full closed segment `0<=Im(z)<=1/2` and its continuation
into the safe upper half-plane. Arbitrarily large compatible rectangles
are constructed, rather than assumed. See
[the compact limits](../RiemannGaussian/SuzukiEtaExtendedLimit.lean) and
[the contour geometry](../RiemannGaussian/SuzukiEtaContourGeometry.lean).

## Preserving every genuine pole

A real zero of `E` is also a xi zero, so a genuine carrier pole cannot be
real. The actual pole set in a fixed closed rectangle is finite.
Consequently, a sufficiently small positive bottom lift preserves every
genuine carrier pole and can avoid every xi/carrier singular ordinate.

The bottom is chosen before the mixed nodes or complex weights. All pole
orders remain included. This does not require uniform convergence of the
finite carrier through shared real xi/denominator zeros. The theorem is
`exists_suzukiXiCarrier_admissible_bottom_same_genuine_poles` in
[SuzukiCarrierPoleWindowGap.lean](../RiemannGaussian/SuzukiCarrierPoleWindowGap.lean).

## The entire signed matrix

For the lifted bottom `b`, let `I_N` be the finite mixed contour integral
and `Z_b` its exact xi source. Define

```
K_N = I_N/(2*pi*i) - Z_b,
S_N = (finiteStripSides - conjugateTranspose(finiteStripSides))/(2*i),
T_N = 2*pi*K_N - S_N.
```

The source subtraction uses the source of the actual displaced contour,
with its sign and multiplicity. It is not absorbed into the error.
Entrywise, `K_N` converges to the complete genuine pole sum in the
original real-bottom rectangle, and `S_N` to the original strip matrix.
Thus `T_N` recovers the complete joint matrix.

The same bottom works for every finite complex weight family. Each
family uses one common truncation for all mixed entries and both strip
sides. The full complex weighted limit is proved before taking real
parts. No uniform absolute error over arbitrarily rescaled weights is
asserted. See [SuzukiEtaStripSides.lean](../RiemannGaussian/SuzukiEtaStripSides.lean)
and [SuzukiEtaJointRecovery.lean](../RiemannGaussian/SuzukiEtaJointRecovery.lean).

## A vanishing error as contours expand

For the canonical reflection difference, write `A_n=Re(Q_rho(T_{N(n)}))`
and let `J_n` be the actual joint correction at the nth outer rectangle.
Lean constructs the rectangles, bottom lifts, and truncations with

```
R(n) -> infinity,  N(n) -> infinity,
|A_n-J_n| < 1/(n+1)  for every n.
```

Under a hypothetical right-half zero, the actual source-energy identity
then gives

```
A_n -> 2*pi/m_rho + reflectionBoundaryEnergy(rho).
```

The terminal theorem is
`exists_suzukiXiEtaFiniteReflection_expanding_recovery` in
[SuzukiEtaExpandingRecovery.lean](../RiemannGaussian/SuzukiEtaExpandingRecovery.lean).

Truncation is chosen sufficiently long for each particular contour.
No explicit growth rate for `N(n)`, or uniform bound for independently
varying contour and truncation sizes, is claimed. The existing reflection
energy is strictly positive off the critical line. An independent bound
`A_n<=2*pi/m_rho+epsilon_n`, with `epsilon_n->0`, would therefore contradict
the positive excess. That arithmetic inequality is still missing; no new
zeta zero exclusion follows from approximation alone.

The same recovery is now available for any supplied compatible expanding
family. In particular, [favorable dyadic phase contours](suzuki-eta-phase-bounds.md)
retain this complete limit while giving independent signed bounds for
the dyadic completion term. The remaining eta interaction and joint
source ceiling are still open.

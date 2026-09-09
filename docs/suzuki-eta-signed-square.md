# Signed eta square bound and vanishing adverse remainder

On actual expanding contours, the integrated completed eta remainder's
negative part tends to zero with a quartic allowance, uniformly in
regular truncations. The full Suzuki source ceiling is still open.
Neither decay of the whole remainder nor a new zero exclusion follows.

The terminal theorem is
[`exists_suzukiXiEtaFiniteReflection_oriented_recovery`](../RiemannGaussian/SuzukiEtaOrientedRecovery.lean).
It constructs the contours and common truncations, proves their
regularity, retains every genuine pole and both strip segments, and
exports the vanishing adverse remainder together with the original
source-plus-energy limit. The underlying square is elementary complex
algebra; formalizing it is not itself a claim of mathematical novelty.

## Exact square for every complex weight

Write `ell=log(2)`, `s=1/2-i*z`, and use the actual definitions

```
e = eta_N(s)
f = F'(s)/F(s),              F(s) = 1 - 2*2^(-s)
R(s) = 1/s + 1/(s-1) - log(pi)/2 + digamma(s/2)/2
p = eta_N'(s) + (1 + R(s))*e
D = p - f*e
C = i*e/D
M = e*conj(p)
a_B = -Re(B*conj(f)).
```

For every complex `B`, Lean proves

```
|B|^2 |D|^2 - 4*a_B*Re(B*M)
  = |conj(B)*D - 2*a_B*e|^2,
Im(B*C) = Re(B*M)/|D|^2 + a_B*|C|^2.
```

If `a_B>0`, then `Re(B*M)/|D|^2 <= |B|^2/(4*a_B)`;
if `a_B<0`, the inequality reverses. In particular,
`a_B <= -c*|B|`, with `c>0`, gives the uniform floor
`Re(B*M)/|D|^2 >= -|B|/(4*c)`.

No quantitative separation of `D` from zero is required. The algebra
respects Lean's totalized division; genuine integrals below use
separately proved denominator nonvanishing on every observation path.
See
[`suzukiEtaFiniteCompletedNumerator_square_identity`](../RiemannGaussian/SuzukiEtaSignedSquareBound.lean)
and
[`im_mul_suzukiEtaFiniteCarrier_eq_completed_add_energy`](../RiemannGaussian/SuzukiEtaSignedSquareBound.lean).
The scalar test `B=1` has upper bound `1/(2*ell)` on negative-cosine
phases throughout `1/2 <= Re(s) <= 1`.

## Actual reflection weights and side orientations

For `alpha=zetaSpectralCoordinate(rho)`, the original reflection weight is

```
W(z) = -(1/(z-alpha) - 1/(z-conj(alpha)))^2
     = 4*Im(alpha)^2 / ((z-alpha)*(z-conj(alpha)))^2.
```

The quotient identity applies off its nodes. On `z=v+i*y`, with
`0<=y<=1/2` and `|v-Re(alpha)|>=100`, Lean proves
`Re(W)>=0`, `|Im(W)|<=Re(W)/32`, and `|W|<=2*Re(W)`.
If `0<R<=|v|` and `2*|Re(alpha)|<=R`, then also
`|W|<=64*Im(alpha)^2/R^4`.
See [the weight sector and quartic bound](../RiemannGaussian/SuzukiReflectionWeightSector.lean).

The right side uses `B=i*W`; the reversed left side uses `B=-i*W`.
Actual admissible contours are constructed with

```
cos(l*ell)<0,   sin(l*ell)<-1/2,
cos(r*ell)<0,   sin(r*ell)> 1/2.
```

These open phase bands permit full singular-set avoidance in the
original unit side windows. They give
`a_(i*W_right) <= -(ell/32)*|W_right|` and
`a_(-i*W_left) <= -(ell/32)*|W_left|` throughout the strip segments.
The opposite sine signs are essential to the signed estimate.
See [dyadic imaginary-part bounds](../RiemannGaussian/EtaDyadicQuadrantBounds.lean),
[constructed oriented contours](../RiemannGaussian/SuzukiEtaOrientedPhaseContours.lean),
and [reflection remainder bounds](../RiemannGaussian/SuzukiEtaReflectionRemainder.lean).

## Integrated bound and preserved cancellation

Let `H_N` be the right completed remainder minus the left completed
remainder, integrated over `0<=y<=1/2`. For `R>=200`, the actual
geometry above and a regular common truncation imply

```
H_N >= -epsilon_R,
max(-H_N,0) <= epsilon_R,
epsilon_R = 512*Im(alpha)^2/(ell*R^4).
```

This holds for every regular `N`, without a relation between `N` and
`R`. Every complex mixed carrier entry, completed remainder and energy
density has genuine interval integrability. See
[`suzukiXiEtaFiniteReflectionCompletedStrip_lower`](../RiemannGaussian/SuzukiEtaCompletedStripBound.lean)
and
[`suzukiXiEtaFiniteReflectionCompletedStrip_negativePart_le`](../RiemannGaussian/SuzukiEtaOrientedRecovery.lean).

Let `P_N=2*pi*Re Q_rho(K_N)` be the complete finite pole expression,
with its exact lifted xi source subtracted. The strip energy is

```
U_N = integral_0^(1/2) (
  -a_(i*W_right)*|C_right|^2 - a_(-i*W_left)*|C_left|^2).
```

It is nonnegative on these phases. The original full correction obeys

```
A_N = P_N + U_N - H_N,
A_N - max(-H_N,0) = P_N + U_N - max(H_N,0).
```

These are identities for the original mixed matrices, proved after
establishing integrability of every entry. See
[`suzukiXiEtaFiniteReflectionCorrection_eq_poles_add_energy_sub_completed`](../RiemannGaussian/SuzukiEtaStripEnergyComparison.lean)
and
[`suzukiXiEtaFiniteReflectionCorrection_sub_negativePart`](../RiemannGaussian/SuzukiEtaStripEnergyComparison.lean).

Under a hypothetical right-half zero, the constructed contours have
`R_n -> infinity`, `N_n -> infinity`, recovery error below `1/(n+1)`,
and `max(-H_(N_n),0) -> 0`. Both `A_(N_n)` and the retained combination
`P_(N_n)+U_(N_n)-max(H_(N_n),0)` tend to
`2*pi/m_rho + reflectionBoundaryEnergy(rho)`, with strictly positive
added energy. Thus removing the adverse component preserves both
the favorable remainder and the original source.

The remaining task is an independent upper ceiling `2*pi/m_rho+o(1)`
for that complete retained combination. No upper bound for `U_N` or
decay of the full `H_N` is proved. Dropping `max(H_N,0)` would discard
useful cancellation and impose a stronger sufficient condition.
The [preceding phase estimates](suzuki-eta-phase-bounds.md) and
[complete arithmetic recovery](suzuki-eta-expanding-recovery.md)
remain available in their original forms.

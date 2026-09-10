# Finite signed reflection integrals with an explicit allowance

The actual full reflection density now has a proved finite signed upper
bound after its mass-variation term is retained. All other terms have an
explicit inverse-radius allowance. This does not yet put the full global
area below its positive reflected-zero source.

## Global regularity through the carrier divisor

For the original entire functions `A = riemannXiSpectral` and
`E = suzukiXiEValue`, define

```text
d = |E|^2 + r^2*|A|^2
U = |A|^2/d
S = i*A*conj(E)/d.
```

[SuzukiCarrierNormalizedMass.lean](../RiemannGaussian/SuzukiCarrierNormalizedMass.lean)
proves `U` globally real smooth for every `r > 0`. At every xi zero the
existing multiplicity-preserving local carrier chart gives exactly

```text
U(z) = |(z-alpha)*q(z)|^2 / (1+r^2*|(z-alpha)*q(z)|^2),
q(alpha) = 1/m_alpha.
```

The chart includes the central common-zero value. Genuine carrier poles
are regular because `A != 0` there. The mass equals the literal eta mass
throughout the complete eta completion domain, including common zeros;
the nonzero complex completion factor cancels homogeneously.

Both fields have global bounds, and their product satisfies

```text
0 <= U <= 1/r^2
|S| <= 1/(2*r)
|U*S| <= 1/(2*r^3).
```

The carrier bound and its global smoothness were proved previously. The
new mass regularity removes the common-zero exclusion from the coupled
source representation.

## Exact horizontal identity

On `z = x+i*y`, primes in this section denote real horizontal derivatives.
[suzukiXiSmoothCarrierSource_eq_horizontal_mass_variation](../RiemannGaussian/SuzukiCarrierMassVariation.lean)
proves globally

```text
V = 2*i*r^2*(U*S' - S*U').
```

This orientation differs from the arithmetic vertical coordinate
`s=1/2-i*z`. The sign is proved for the actual spectral source, not inferred
by silently identifying those derivatives.

Let `W` be the original complex reflection weight, `B` the actual boundary
Gaussian, `H` the companion heat source evaluated at `i*z`, and `P = W*B`.
The complete density is `G = W*(B*V-i*S*H)`. Define

```text
J = P*U*S
M = P*S*U'
R = 2*i*r^2*P'*U*S + i*W*S*H.
```

[SuzukiReflectionMassCurrent.lean](../RiemannGaussian/SuzukiReflectionMassCurrent.lean)
retains the exact identity

```text
G = 2*i*r^2*J' - 4*i*r^2*M - R.
```

It proves the actual Gaussian globally real smooth and `P` smooth away
from the two reflection nodes. The current identity includes all genuine
carrier poles and all other xi zeros. No carrier denominator is assumed
bounded away from zero.

## Finite integration and the independent allowance

Let `[a,b]` be a forward horizontal interval containing neither reflection
node. All five functions `G`, `J'`, `M`, `R` and the explicit remainder
envelope are proved interval-integrable, including through the full
carrier divisor. The fundamental theorem of calculus gives

```text
integral_a^b G
  = 2*i*r^2*(J(b)-J(a)) - 4*i*r^2*integral_a^b M - integral_a^b R.
```

The complex remainder obeys the independent pointwise bound

```text
|R| <= |P'|/r + |W*H|/(2*r).
```

Consequently the following budget depends only on the reflection and heat
weights, the line and its endpoints; it is independent of `r` and of the
values of the xi/eta carrier:

```text
C = |P(b)| + |P(a)| + integral_a^b (|P'| + |W*H|/2).
```

Lean proves `C >= 0`, genuine integrability of its integrand, and

```text
|integral_a^b G + 4*i*r^2*integral_a^b M| <= C/r
Im(integral_a^b G) <= -4*r^2*Re(integral_a^b M) + C/r.
```

The terminal theorems in
[SuzukiReflectionMassIntegral.lean](../RiemannGaussian/SuzukiReflectionMassIntegral.lean)
are `norm_integral_suzukiXiSmoothReflectionSource_add_mass_variation_le_budget`
and `im_integral_suzukiXiSmoothReflectionSource_le_mass_variation`.
The real part of the signed complex variation remains in the inequality;
it is not replaced by an absolute value.

`tendsto_integral_suzukiXiSmoothReflectionSource_add_mass_variation`
proves that the combined complex error tends to zero as `r -> infinity`
on each fixed admissible interval. This grows the smoothing parameter;
it is not removal of smoothing, which uses `r -> 0` elsewhere in the repo.
The theorem does not say that the integral of `G` itself tends to zero.

## Remaining global obstruction

The retained `Re(integral M)` has no proved arithmetic sign or bound
strong enough for exclusion. Moreover, `W` is singular at the reflection
nodes. The weight-only budget need not stay bounded as a puncture shrinks.
Its inverse-radius factor therefore cannot be promoted to a vanishing
global allowance by exchanging the radius, puncture or exhaustion limits.

The subsequent [ordinary area development](suzuki-reflection-mass-area.md)
now preserves the cubic vanishing of `U*S`, proves the exact current smooth
at both reflection nodes, and establishes planar integrability of all
signed terms. It removes the puncture parameter at fixed smoothing radius
and proves an independent inverse-square bound for the two outer current
edges. The combined signed mass variation and complete remainder still
need an arithmetic bound. The weight-only envelope above is not promoted
to a global allowance.

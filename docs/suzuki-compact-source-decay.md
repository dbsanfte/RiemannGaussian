# Compact arithmetic decay and the surviving reflected node

The actual normalized arithmetic source now has absolute integral at
most `C_K/r` on every fixed compact upper spectral region `K`, including
all zeros and carrier poles. With the original reflection weight and
Gaussian, the exterior of a reflected radius-`epsilon` disk has bound
`C/(r*epsilon^2)`. The latter constant is independent of the selected
right-half zero, radius, and smoothing parameter. The independent
signed ceiling through the selected reflected node is still open.

The terminal bounds and moving-neighborhood limit are in
[SuzukiCompactSourceDecay.lean](../RiemannGaussian/SuzukiCompactSourceDecay.lean).
These are planar estimates. They do not assert integrability of a
simple pole along a line through it, a bound uniform over expanding
compact regions, or a new zero exclusion.

## Exact complex factorization

Write `A(z) = riemannXiSpectral(z)`, `E(z) = suzukiXiEValue(z)`, and
`Delta(z) = A'(z)/A(z) - E'(z)/E(z)`. Let `S_r` and `U_r` be the
actual smooth carrier and normalized mass. Away from their analytic
divisors, Lean proves

```text
V_r(z) = -2*i*r^2*U_r(z)*S_r(z)*conj(Delta(z)).
```

This is `suzukiXiSmoothCarrierSource_eq_logDerivative_difference`.
It retains the complex logarithmic derivative difference and the
carrier phase. The downstream norm bound uses
`0<=U_r<=1/r^2` and `|S_r|<=1/(2*r)` to give

```text
|V_r(z)| <= |Delta(z)|/r
```

almost everywhere in the whole plane. Both exceptional analytic
divisors have area zero; genuine nonzero values of `A` and `E` prove
that neither function is identically zero.

## Integrability through every divisor

[ComplexLogDerivativeIntegrability.lean](../RiemannGaussian/ComplexLogDerivativeIntegrability.lean)
proves that the logarithmic derivative near a finite-order analytic
zero is locally integrable in area. The exact decomposition is
`m/(z-a)` plus an analytic remainder. The complex simple pole is
integrable on compact disks, for every multiplicity `m`.

Applying this to the actual entire functions proves
`locallyIntegrable_suzukiXi_logDerivative_difference`, with finite
order discharged at every point. Therefore

```text
integral_K |V_r| <= (integral_K |Delta|)/r.
```

No zero neighborhoods are removed. The actual source is globally
continuous, including common zeros of its original numerator and
denominator.

## Arithmetic and all bounded weight families

On `Im(z)>=0`, equivalently arithmetic `Re(s)>=1/2` for `s=1/2-i*z`,
the already checked Gamma-curvature error has norm at most
`1/(4*r^2)`. Combining it with the exact source factorization proves
`exists_integral_norm_suzukiGammaShiftArithmeticSource_compact_bound`:

```text
C_K = integral_K (|Delta(z)|+1/4) >= 0
r>=1  ==>  integral_K |A_r(1/2-i*z)| <= C_K/r.
```

Here `A_r` denotes the normalized arithmetic source, not the entire
function `A` above. All integrability premises are proved for it.

The same constant works for every complex weight `P` that is strongly
measurable almost everywhere on `K` and satisfies `|P|<=M` almost
everywhere, where `M>=0`:

```text
integral_K |P(z)*A_r(1/2-i*z)| <= M*C_K/r.
```

This is `exists_suzukiGammaShiftArithmeticSource_compact_all_weight_bound`.
The family may vary with `r`; no coefficient search or fixed-family
restriction occurs in this theorem.

## The original singular reflection weight

For a selected right-half zero `rho`, set
`a = zetaSpectralCoordinate(rho)`, `beta=conj(a)`, and let `W_rho`
be the original reflection weight. Its exact quartic formula gives

```text
Im(z)>=0, z!=beta  ==>  |W_rho(z)| <= 4/|z-beta|^2.
```

The lower reflected node lies below the integration half-plane. Its
distance pays the entire numerator, giving a constant independent of
the distance of `rho` from the critical line. The exceptional point
`beta` is explicitly excluded from this pointwise formula.

For fixed compact `K` and fixed Gaussian parameters `c,tau`, the heat
has a finite norm bound on `K`. The arithmetic estimate therefore
gives one `C>=0` such that, for every selected right-half zero,
every `r>=1` and every `epsilon>0`,

```text
integral_(K \ ball(beta,epsilon)) |W_rho*B*A_r|
  <= C/(r*epsilon^2).
```

This is
`exists_integral_norm_suzukiGammaShiftWeightedArithmeticSource_outside_ball_bound`.
All other zeros and carrier poles remain in the domain.

## What remains

For an eligible fixed upper rectangle and `tau>0`, the existing exact
source theorem gives the integral limit `2*pi*i*B(beta)/m`, where `m`
is the analytic multiplicity. If `epsilon(r)>0` eventually and
`r*epsilon(r)^2` tends to infinity, the absolute exterior integral
tends to zero. Subtraction proves
`tendsto_suzukiGammaShiftWeightedArithmeticSource_moving_reflected_ball`:
the integral over the rectangle intersected with the moving ball
tends to that same full source. This includes shrinking radii with
the stated scale condition; shrinking is not assumed by the theorem.

The reflection weight is unbounded through `beta`, so the common
bounded-weight estimate cannot be applied to the entire reflected
source. The theorem controls the rest of a fixed rectangle and
locates the remaining contribution. It supplies no deficit at the
node: the independent signed arithmetic upper bound below
`2*pi*B(beta)/m` is still the goal. RH remains open.

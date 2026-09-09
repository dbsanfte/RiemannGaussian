# Signed normalization and the complete eta current

This local theorem slice identifies a cancellation that prevents counting
the unnormalized negative square as a free margin. It also expresses the
complete complex source as coupled variation of two bounded fields. It
does not prove a global upper bound below the reflected-zero source.

## Literal fields and domains

Write `s = sigma + i*t`, `f = pairedEtaCore`, and
`D = f' + (1+Q)*f`, where `Q` is the actual completion correction. For
fixed `r > 0`, set

```text
d = |D|^2 + r^2 |f|^2
S = i*f*conj(D)/d
U = |f|^2/d
V = 2*i*r^2*f^2*conj(f'*D-f*D')/d^2.
```

These are the repository's actual eta denominator, smooth carrier,
normalized mass, and spectral-coordinate source. The factor `i` in `V`
retains the reflected coordinate orientation. Primes on `f`, `D`, and `Q`
denote complex derivatives. Primes on vertical fields below denote real
derivatives with respect to `t`.

Derivative identities assume the exact eta completion domain and
`f(s) != 0` or `D(s) != 0`. They include genuine carrier poles. The value
bounds for `S` and `U` include common zeros. This slice does not prove
global smoothness of `U` at common zeros or transfer its derivative
identity through an area integral there. The previously proved global
smoothness and source formula for the original xi carrier remain intact.

## What happens to the negative square

In [ComplexSignedCurvature.lean](../RiemannGaussian/ComplexSignedCurvature.lean),
let `J = f*conj(f')`, `T = |f|^2*J`, and let `K` be any differentiable
complex vertical weight. The exact identity is

```text
Re(K*f^2*conj(f'^2-f*f''))
  = Im((K*T)') - Im(K'*T)
    - 4*Im(J)*(Re(K)*Im(J) + Im(K)*Re(J)).
```

For a nonnegative real weight the last term is nonpositive. For arbitrary
complex weights the checked upper bound retains the phase cost
`2*(|K|-Re(K))*|J|^2`. The exact identity remains available alongside it.

[SuzukiEtaSignedCurrent.lean](../RiemannGaussian/SuzukiEtaSignedCurrent.lean)
applies this with the literal `K = P/d^2`. It also retains the entire
completion term `-|f|^4*Re(K*conj(Q'))`. The derivative of `d` is taken;
neither it nor the complex weight is frozen.

For `P = W*B`,
[suzukiXiSmoothReflectionSource_im_le_current](../RiemannGaussian/SuzukiEtaSignedReflection.lean)
proves a pointwise upper expression for the full original reflection
density, including its signed companion heat term. Differentiability of
this actual `P` is proved away from the two reflection nodes. The upper
expression itself has no proved global sub-source bound.

At `D = 0`, `f != 0`, Lean now proves

```text
d' = 2*Im(Q)*d
2*(d'/d)*Im(K*T)
  = 4*Im(J)*(Re(K)*Im(J) + Im(K)*Re(J)).
```

The second equality is
[suzukiEtaNormalization_quadratic_cancellation_at_pole](../RiemannGaussian/SuzukiEtaNormalizationSlope.lean).
Since differentiating `K = P/d^2` contributes
`+2*(d'/d)*Im(K*T)` to the weighted identity, normalization cancels the
entire quadratic interaction at that point. This applies even to complex
`K`. It does not say that the complete source vanishes, or evaluate an
integral over a pole neighborhood.

The wrapper
`suzukiXiNormalization_quadratic_cancellation_at_upper_pole` starts only
from an actual upper xi carrier pole and a nonzero xi numerator. It
derives the eta domain, numerator and denominator conditions. No pole
simplicity is assumed.

## Coupled variation of bounded fields

[SuzukiEtaProjectiveCurrent.lean](../RiemannGaussian/SuzukiEtaProjectiveCurrent.lean)
proves the actual value bounds and exact quadratic relation

```text
0 <= U <= 1/r^2
|S| <= 1/(2*r)
|S|^2 = U - r^2*U^2.
```

The carrier bound is the previously proved `norm_suzukiEtaSmoothCarrier_le`.
The new theorem `suzukiEtaSpectralSmoothSource_eq_mass_current` proves

```text
V = 2*i*r^2*(S*U' - U*S').
```

All completion information remains inside the differentiated literal
denominator. No real or imaginary component of `V` is discarded.
`suzukiXiSmoothReflectionSource_eq_mass_current` carries this equality to
the complete actual density

```text
G = W*(B*2*i*r^2*(S*U' - U*S') - i*S*H_heat).
```

At a genuine carrier pole, `S = 0`, `U = 1/r^2`, and Lean proves an
actual real derivative `U' = 0`. The terminal theorem
`suzukiXiSmoothReflectionSource_eq_slope_at_upper_pole` gives exactly

```text
G(z) = -2*i*W(z)*B(z)*S'(-Re(z))
```

on the arithmetic line `sigma = 1/2 + Im(z)`. Again, its eta side
conditions follow from the original xi pole, with arbitrary pole order.
This is a pointwise formula, not a claim that these pole values alone
determine the area integral.

## Remaining obligation

The [bare-curvature Gaussian decay](eta-curvature-gaussian.md) controls
an integral before multiplication by the variable normalization and
reflection factors. The new identities do not transfer that decay to
the full source. Bounded fields alone do not bound their coupled
variation.

The active goal still needs an independent signed estimate for the
complete weighted area that is strictly below the proved positive
reflected-zero source. A prospective integration by parts must establish
regularity, integrability, boundary contributions and puncture limits
for the actual fields. Neither a new area-limit exchange nor a new zero
exclusion is claimed here. The dashboard's quantitative milestone remains
the proved bare-curvature Gaussian bound; the new identities are recorded
as structure and an obstruction audit.

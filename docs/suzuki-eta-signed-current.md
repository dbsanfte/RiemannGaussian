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

The subsequent [finite integral theorem](suzuki-reflection-mass-integral.md)
now proves global smoothness of the original normalized xi mass, including
common zeros, and a global horizontal source identity. It supplies the
actual finite integration-by-parts formula and an explicit inverse-radius
allowance. The [ordinary area theorem](suzuki-reflection-mass-area.md)
then proves integrability through both reflection nodes and removes the
puncture parameter. An independent source ceiling for the signed mass
variation remains open.

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

The subsequent [angular cancellation theorem](suzuki-reflection-angular-decay.md)
removes the complete reflection remainder and current edges in the
smoothing limit on each fixed eligible upper rectangle, including its
reflected node. The signed normalized mass variation still needs an
independent source bound; no expanding-area limit interchange is proved.

The [rescaled mass profile](suzuki-reflection-mass-profile.md) now shows
that this retained term tends to the entire positive source on fixed
eligible rectangles. Its constant angular component also survives
perpendicular phase coupling. Smoothing alone does not supply a deficit.

The [bare-curvature Gaussian decay](eta-curvature-gaussian.md) controls
an integral before multiplication by the variable normalization and
reflection factors. The subsequent [quartic Gaussian estimate](eta-quartic-gaussian.md)
now includes the two additional eta factors: the positive part of the
signed quartic integral tends to zero on every line to the right of
three quarters. It retains an exact negative phase square and uses the
literal eta height bound to control its positive allowance. Completion,
the variable denominator and the reflection weight remain outside that
estimate. Bounded fields alone do not bound their coupled variation.

The subsequent [shifted Gamma theorem](suzuki-gamma-reflection-decay.md)
now isolates the completion-curvature contribution in another exact
representation of the same actual carrier. This full complex error,
including the original reflection weight and variable normalization,
tends to zero in L1 on the entire upper half-plane as smoothing grows
at fixed positive Gaussian time. No reflection node is removed; the
actual mass's quadratic vanishing supplies the global dominator. The
same error vanishes on arbitrary moving spatial cutoffs. The completion's
first derivative is still inside the arithmetic denominator.

The [arithmetic band reduction](suzuki-arithmetic-band-reduction.md) now
also removes the complete companion heat contribution in global L1.
The full source is one normalized weighted arithmetic quartic plus two
proved negligible errors. A rectangle-independent boundary estimate
allows simultaneous spatial and smoothing growth. The actual zero-free
edge estimate now bounds logarithmic curvature on the entire closed
Euler half-plane. Its exact source identity gives the full weighted
arithmetic density an L1 bound `C/r^2` on `Im(z) >= 1/2`, including the
boundary. Removing that half-plane leaves the entire original positive
source in `0 <= Im(z) < 1/2`; the horizontal cutoff may grow. The
independent signed ceiling inside that strip remains open.

The [compact strip estimate](suzuki-compact-source-decay.md) now gives
the unweighted arithmetic density absolute integral at most `C_K/r`
on every fixed compact upper region, through all zeros and carrier
poles. The original reflection-weighted exterior of a radius-`epsilon`
disk costs at most `C/(r*epsilon^2)`, uniformly over selected right-half
zeros. Eligible moving disks retain the full selected source; the
independent inequality through the reflected node remains open.

The [normalized Gaussian decay theorem](suzuki-normalized-gaussian-decay.md)
now proves a finite-interval bound with the actual denominator retained.
The exact mass–carrier quadratic relation and a common rescaling law
give a continuous derivative-energy majorant through all zeros. The
complete scaled drift allowance has integral tending to zero on every
fixed compact upper horizontal set; both scaled current endpoints also
vanish. The normalized arithmetic Gaussian integral is therefore
eventually below every positive tolerance on a fixed finite interval.
The full complex weighted current identity remains available upstream.
The singular reflection weight and growing intervals are outside this
new decay estimate.

The [full arithmetic node profile](suzuki-arithmetic-node-profile.md)
now retains the singular weight and identifies a positive radial core.
Convergence is uniform over every angle at fixed nonzero rescaled radius.
One threshold preserves this core for all finite complex angular mixtures
whose coefficients sum to one and whose total absolute weight has a fixed
bound, including growing and changing families. This is a proved method
obstruction; it does not supply the missing arithmetic upper bound.

On the complementary Suzuki floor route, [variable-damping recovery](suzuki-relative-recovery.md)
now proves positive values in every sufficiently late logarithmic-time
interval `[a,K*a]`, for every fixed `K > 1`. The complete signed moments
and both tail bounds are retained. Deep excursions have balanced minima
between `t/K` and `K*t`, so a balanced-cell floor `N^delta` transfers to
the literal signal with every exponent `epsilon > delta`. This sharpens
recovery and removes the old factor 4096 from that transfer; the independent
arithmetic depth estimate remains open.

The active goal still needs an independent signed estimate below the
proved positive reflected-zero source. Regularity, finite-area
integration by parts, node integrability and current-edge bounds are now
available for the actual fields. The latest angular cancellation removes
the complete earlier analytic remainder as smoothing grows on each
fixed eligible rectangle. Gamma curvature, companion heat, and the
arithmetic contribution a fixed distance beyond the known zero strip
now have global L1 decay. The source's simultaneous cutoff limit is
proved. The latest finite-interval ceiling now includes the variable
normalization and its complete drift, but the independent arithmetic
ceiling with the singular reflection weight inside the surviving band
remains open; no new zero exclusion is proved.

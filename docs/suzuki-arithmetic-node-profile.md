# The full weighted arithmetic core survives angular averaging

Lean identifies the rescaled profile of the actual normalized arithmetic
source with its original complex reflection weight retained. At a
hypothetical upper reflected zero, that profile is positive imaginary
and depends only on radius. Convergence is uniform over every angle at
each fixed nonzero rescaled radius.

The terminal theorem
[`eventually_all_suzukiGammaShiftWeightedArithmeticSource_phase_mixtures_positive`](../RiemannGaussian/SuzukiArithmeticNodeProfile.lean)
supplies one threshold for every finite complex angular mixture whose
coefficients sum to one and whose total absolute weight is bounded by a
fixed positive constant. The number of phases, directions and coefficients
may all change with smoothing. Every such mixture retains a positive core.

This closes a method audit, not the active RH goal. It rules out reducing
this leading core by that class of angular averages. No independent upper
bound below the reflected source, new zero exclusion, or weighted area
limit exchange is asserted.

## The exact arithmetic chart

Use the actual fields from the
[arithmetic band reduction](suzuki-arithmetic-band-reduction.md):
`H_r(z)=W(z)*B(z)*A_r(1/2-i*z)`. Fix a selected off-line spectral node
`a`, of analytic multiplicity `m`. A single analytic coefficient `q`
and real-smooth complex weight numerator `g` give

```text
q(a)=1/m, g(a)=-B(a), u=z-a
S_r(z)=u*q(z)/(1+r^2*|u*q(z)|^2)
W(z)*B(z)=g(z)/u^2.
```

The actual quartic has the uniform punctured chart

```text
H_r(z) = -2*i*r^2*g(z)*q(z)^2
  *conj(q(z)+u*q'(z)-u^2*q(z)^2*Q'(1/2-i*z))
  /(1+r^2*|u|^2*|q(z)|^2)^2.
```

This is
[`exists_suzukiGammaShiftWeightedArithmeticSource_node_chart`](../RiemannGaussian/SuzukiArithmeticNodeProfile.lean).
Primes here are complex derivatives. Both the coefficient derivative
and differentiated Gamma correction remain inside the exact expression.
The latter carries two powers of displacement. No constant-coefficient
or simple-zero hypothesis is assumed. All holomorphy conditions follow
from the original nontrivial zero and the shifted completion domain.

## The complete rescaled profile is radial

For fixed `w != 0` and `r -> infinity`, Lean proves

```text
H_r(a+w/r)/r^2 -> L_a(w)
L_a(w)=2*i*B(a)/(m^3*(1+|w|^2/m^2)^2).
```

At the upper reflected node `beta=conj(spectralCoordinate(rho))` of a
hypothetical `Re(rho)>1/2`, `B(beta)` is real and strictly positive.
Consequently `Im(L_beta(w))>0`. The complete arithmetic profile has no
angular dependence. The earlier
[mass-variation profile](suzuki-reflection-mass-profile.md) retained a
constant angular component and a second harmonic. Their full combination
in the actual arithmetic density produces the radial profile above.
No phase is replaced by its norm to obtain this conclusion.

The theorem excludes `w=0`: it is a punctured profile of the genuine
singular weight, not a continuity assertion for its totalized central
value. It also does not integrate the limit over a moving neighborhood.
Existing signed area theorems separately retain the full positive source.

## One threshold for all angular directions and finite mixtures

For fixed `w != 0` and every `epsilon>0`, one smoothing threshold gives

```text
|H_r(beta+v*w/r)/r^2-L_beta(w)| < epsilon
```

for every complex `v` with `|v|=1`. This is
[`eventually_uniform_suzukiGammaShiftWeightedArithmeticSource_reflected_profile`](../RiemannGaussian/SuzukiArithmeticNodeProfile.lean).
The exact chart becomes a continuous function of `z` when
`r^2*|z-beta|^2=|w|^2`; every direction has the same distance `|w|/r`
from the node. Continuity supplies the common threshold.

For any fixed finite family with arbitrary complex coefficients `p_j`
and unit phases `v_j`, the full complex limit is

```text
sum_j p_j*H_r(beta+v_j*w/r)/r^2 -> (sum_j p_j)*L_beta(w).
```

The sum of coefficients, including its phase, is preserved exactly.
A zero sum cancels the leading contribution; a sum of one preserves it.

Uniformity also handles changing families. Fix `C>0`. Beyond one
threshold, every finite family satisfying

```text
|v_j|=1, sum_j p_j=1, sum_j |p_j|<=C
```

obeys the proved lower bound

```text
Im(sum_j p_j*H_r(beta+v_j*w/r)/r^2) > Im(L_beta(w))/2.
```

The proof bounds the complete difference from `L_beta(w)` by `C*epsilon`
only after retaining the exact coefficient sum. It covers every finite
family at that radius, including an unbounded count of phases as `r`
grows. No coefficient search or selected numerical family is used.

## Consequence for the active goal

The [normalized Gaussian drift estimate](suzuki-normalized-gaussian-decay.md)
already decays on fixed unweighted horizontal intervals. The singular
reflection factor retains a positive arithmetic core even when all
angular directions are coupled in the class above. Increasing the phase
count alone cannot create the needed deficit there.

This is not an impossibility theorem for every global test function.
It fixes a nonzero rescaled radius and a bound on total absolute
coefficient weight. Infinite measures, unbounded coefficient norms,
changing radial scales and global arithmetic correlations require their
own estimates. The active goal still needs an independent signed
arithmetic inequality beating the full positive source after the proved
errors. Smoothing and the audited angular mixtures do not supply it.

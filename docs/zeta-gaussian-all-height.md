# An explicit Gaussian zero-free curve with no upper height ceiling

This records the preceding explicit curve and the dilation still used by
the subsequent multiplicity and energy theorems. The
[current stronger explicit region](zeta-gaussian-retained-region.md)
keeps the fixed and logarithmic costs separate and contains this curve.

[ZetaGaussianAllHeight.exact_strip_min](../RiemannGaussian/ZetaGaussianAllHeight.lean)
proves, for every actual nontrivial zeta zero `rho=beta+i*t`,

```math
|t|\ge 10^6,\qquad L(t)=\log(|t|+2),\qquad
d(t)=\min\left\{\frac1{450000},\frac{32}{45L(t)}\right\}
\quad\Longrightarrow\quad d(t)\lt\beta\lt1-d(t).
```

The starting height is explicit, both signs of the ordinate are covered,
and there is **no upper height ceiling**. The same module's `nonvanishing`
proves literal zeta nonvanishing on the closed right edge. Every arithmetic,
analytic and phase-family premise is discharged. This is not RH: the
interior strip remains unresolved and the explicit width tends to zero.

The [multiplicity refinement](zeta-gaussian-multiplicity-depth.md) retains
the same Gaussian budget and proves a larger excluded layer for multiple
zeros. It also discharges simplicity and the exact eta head-current formula
within `13/6` times this width of either edge. The universal zero-free
curve itself is unchanged.

## Exact scaling of the complete cost

The [original full signed Gaussian inequality](zeta-gaussian-phase-band.md)
remains the source. It retains the three coupled prime responses, the true
zero multiplicity, the constant-channel Euler charge, both strip boundaries,
the rational corrections and the complete Archimedean allowance.

For every real `q>=1`, use

```math
w_q=\frac{1}{450000q},\qquad x_q=\frac{w_q}{1000},\qquad
B_q=4w_q^2,\qquad k=9.
```

The exact identity `q*F_(B*q²)(x*q)=F_B(x)` scales the selected
half-Gaussian and the constant channel together. The derivative order stays
fixed. The contour half-width is `delta_9+x_q`; it is **not** silently
scaled along with the Gaussian parameters.

[ZetaGaussianScaledBandBudget](../RiemannGaussian/ZetaGaussianScaledBandBudget.lean)
proves these bounds whenever `|t|>=1000000` and `L(t)<=320000*q`:

| Quantity | Checked bound |
| --- | --- |
| Selected half-Gaussian `F_(B_q)(x_q+w_q)` | At least `152000*q` |
| Constant half-Gaussian `F_(B_q)(x_q)` | At most `199575*q` |
| Complete constant-channel allowance | At most `200142*q` |
| Complete left Euler allowance | At most `(320000/2046+24)*q` |
| Complete family budget | At most `47500*q` |
| Selected zero contribution, including multiplicity and reserve | At least `48000*q` |

The last source bound and resulting contradiction are in
`ZetaGaussianAllHeight.selected_source_lower` and `family_margin`.
They hold for every eligible nonnegative summable phase family with
nonnegative full kernel and the same coarse bounds
`a_0<=37/200`, `a_1>=79/250`, `W<=61/100`, `J<=1/4`.
The existing mathematically defined contact family supplies all premises;
no new coefficients or numerical oracle enter the proof.

Choosing `q(t)=max(1,L(t)/320000)` discharges the height constraint at every
eligible ordinate. `explicitWidth_eq_min` proves the displayed formula.
`explicitWidth_eq_plateau` proves that the former constant-width component
is contained exactly, including its upper endpoint.

## Union and benchmark scope

`union_with_eventual` combines this curve with the proved eventual
Littlewood component using their maximum wherever both apply. The eventual
component retains its coefficient-dependent, **unevaluated** threshold.

The [literature-frontier table](zero-free-literature-frontier.md) and the
existing exact crossover comparisons remain valid on their stated plateau
interval. Those comparisons have not been extended beyond the old ceiling
to determine the new curve's full comparison range. In particular this
slice makes no exhaustive record or historical-novelty claim.

## Transport into the actual arithmetic response

[ZetaSquarefreeGaussianAllHeight](../RiemannGaussian/ZetaSquarefreeGaussianAllHeight.lean)
discharges the actual doubled denominator window for every `|y|>=500002`.
Its explicit radius is

```math
m(y)=\min\left\{\frac1{450000},
  \frac{32}{45\log(2|y|+5)}\right\},\qquad R(y)=1+\frac{m(y)}2>1.
```

`analyticOnNhd_response` proves that the literal quotient `zeta(s)/zeta(2*s)`
is analytic on a neighbourhood of the full closed disc of radius `R(y)`
about `3/2+i*y`. The plus five includes the doubled-window allowance and the
zero-free theorem's enlarged height. All pole and denominator exclusions
are proved, at both signs of the center and without a height ceiling.

`exists_response_bound` transports this radius to every original marked
squarefree response, polynomial, derivative order and eligible prime set.
The full signed two-harmonic prime envelope is retained. Its finite
constant may depend on `y`; there is no claim of one uniform constant over
the unbounded domain. The older compact-band uniform matrix theorem remains
available on its own domain.

The independent ordinary-prime floor is still open. The
[all-filter prime-window obstruction](zeta-prime-window-obstruction.md)
shows why this estimate must retain cancellation between windows or use a
centered arithmetic error. A larger analytic disc alone does not establish
that signed estimate.

## Local validation

All three modules are imported by the root library. Validation uses direct
warning-as-error elaboration, focused and full builds, whole-project
declaration lint, terminal transitive axiom audits and generated inventory
and explorer checks. Only `propext`, `Classical.choice` and `Quot.sound`
are permitted. This slice is being kept local; no new remote CI result is
claimed.

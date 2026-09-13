# The signed left mean is the remaining source-scale budget

[ZetaGaussianSignedBudgetReduction](../RiemannGaussian/ZetaGaussianSignedBudgetReduction.lean)
now proves that the full signed Gaussian source budget differs from the
original clipped left boundary mean by a term negligible at the source
scale. This is a two-sided difference estimate. It retains every correction
before bounding it, applies to the current dilation and carries the
actual finite-zero source constraint through the reduction.

**The left mean itself still needs a source-beating bound. This result does
not prove RH or enlarge the zero-free region.**

## Exact remaining quantity

Use the original fixed-order geometry and keep the two logarithmic
heights distinct:

```math
L_{26}(t)=\log(|t|+26),\quad L_2(t)=\log(|t|+2),\quad
q(t)=\max\{1,L_2(t)/320000\}.
```

At arbitrary dilation `q>=1`, write `x_q=shift(q)`, `B_q=gaussianScale(q)`,
`eta_q=halfWidth(9,x_q)`, `r_q=rightLine(9,x_q)` and
`b_q=2*eta_q/pi`. The left mean is

```math
\mathcal L_q=
\frac1{2\eta_q}\sum_{n\ne0}a_n
 \int_{\mathbb R}d(u)\,
 \log\max\!\left\{
   \left|R\bigl(\operatorname{line}(9)+i(\omega_nt+b_qu)\bigr)\right|,
   e^{-M}\right\}\,du,
\qquad R(s)=\frac{\zeta_1(s)}{s+1}.
```

Here `d(u)` is the original normalized `SechVerticalKernel.density`,
and `zeta_1` is the actual pole-removed zeta function. Finite clipping
retains negative logarithmic values down to `-M` and makes the logarithm
continuous at zeros. **No passage to an unclipped infinite negative depth
is asserted.** The original source theorem permits every finite `M>=0`.

`signedBudget_eq_left_add` proves exactly

```math
\mathcal B_{\rm signed}=\mathcal L_q+\mathcal C_q,
```

where `correction` preserves the rational boundary mass divided by
`2*eta_q`, the complete signed Gaussian pole/completion correction, and
the full nonconstant right response with its original multiplier.
This correction is independent of the clipping depth.

## The multiplier carries previously unused decay

The right response is the real part of
`1/(s-1)+zetaGlobalRegularCorrection(s)`. It contains a logarithmic
completion term and is not a uniformly bounded Euler prime sum.
Its actual multiplier is

```math
f_q=\frac{24B_q}{\eta_q^2},\qquad
q^2f_q=\frac{24B_0}{\eta_q^2}\le\frac1{50000}.
```

`factor_mul_sq_eq` keeps this identity before the half-width is bounded;
`factor_le_inverse_square` proves `f_q<=1/(50000*q^2)`.
The earlier uniform cap discarded this additional decay.

The complete complex Gaussian correction has norm at most `15` on each
nonconstant working channel. The rational family mass is between zero
and the nonconstant coefficient mass `m`. The inverse factor
`1/(2*eta_q)` is at most `94`. The full signed right-response sum has
absolute value at most `3*(m*L_26(t)+F)`, where `F` is the first logarithmic
frequency cost.

Combining these results, `abs_signedBudget_sub_left_le` proves

```math
\left|\mathcal B_{\rm signed}-\mathcal L_q\right|
\le109m+\frac{3\{mL_{26}(t)+F\}}{50000q^2},
\qquad q\ge1,\quad |t|\ge10^6.
```

This holds for every nonnegative summable family with `omega_n>=1` away
from index zero and a summable first logarithmic moment. It needs no
finite frequency support, second logarithmic moment or coefficient search.
All prime, zero and boundary objects retain their original definitions.

## What reaches the zero source

For arbitrary moving eligible families, bounded `m`, `F` and
`L_26(t)/q`, and both dilation and absolute height tending to infinity,
`tendsto_normalized_signedBudget_sub_left` proves

```math
\frac{\mathcal B_{\rm signed}-\mathcal L_q}{q}\longrightarrow0.
```

`tendsto_current_signedBudget_sub_left` discharges the actual current
dilation, whose height ratio is at most `320000+log(13)`. The clipping
depth may vary arbitrarily; the correction bound has no clipping cost.
These statements concern normalized corrections, not unnormalized
vanishing of every individual term.

The preceding [energy decay theorem](zeta-gaussian-prime-energy-decay.md)
already controlled the actual positive source surplus over the full
signed budget. Keeping its complete squared error during the change of
budget gives `tendsto_current_source_surplus_over_left_sq`:

```math
\frac{\max(0,S_Z-\mathcal L_q)^2}{q(t)^2}\longrightarrow0.
```

`S_Z` is the original coefficient-weighted compensated finite-zero source,
with every multiplicity retained. Finite zero windows, families and
nonnegative clipping depths may all move. The original phase-kernel,
anchor, frequency and scale hypotheses remain explicit.

The remaining task is a signed comparison between this actual left mean
and the compensated source. A positive surplus on the dilation scale
would contradict the proved limit, but that surplus has not been proved.
The large-height statement does not settle a fixed interior zero or the
separate centered prime carrier's independent cofinal floor.

The subsequent [source-support audit](zeta-gaussian-source-support.md)
proves the precise restrictions: the order-nine source vanishes on and
left of `2035/2046`, and every fixed bounded-height zero window eventually
leaves it as detector height diverges. These are source cutoffs, not
zero-free conclusions. A global contradiction needs a retained fixed-zero
source in addition to an independent signed estimate.

The module is imported by the root, assigned to the signed-strip family,
and shown in the **Signed budget** explorer endpoint. No new historical
novelty, numerical certificate or zero-free region is claimed. Work remains
local under the no-commit instruction.

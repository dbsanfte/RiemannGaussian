# The global deviation window

The exact logarithmic deviation profile classifies all successful positive
exponential tilts and gives a smaller retained carrier for every exposed
right-half zero. The removed error is uniform across a bounded interval of
source radii, including arbitrarily moving radii and heights.

The actual source endpoint is
[`tendsto_universal_physicalDeviation_exposed`](../RiemannGaussian/ZetaRieszDeviationCarrier.lean).
Its negative multiplicity limit remains conditional on a hypothetical
exposed zero. The independent signed bound inside the window is open.

## The exact tilt criterion

The Mathlib-only module
[`LogarithmicDeviation`](../RiemannGaussian/LogarithmicDeviation.lean) defines

```math
I(x)=x/2-1-\log(x/2),\qquad I(x)\ge0,\qquad I(2)=0.
```

For a cutoff below `2` or above `2`, a successful summable positive
exponential tilt exists exactly when `log(2u) < I(x)`. Both implications
are proved for **all** positive tilt parameters and all summability
exponents greater than one, with the appropriate cutoff orientation.
The identity behind the classification is

```math
\log(u/q)+(\sigma-3/2+q)x
 =\log(2u)-I(x)+(qx-1-\log(qx))+(\sigma-1)x.
```

The last two costs are nonnegative. This classifies this norm method;
it does not classify all signed estimates or arbitrary coefficient families.
In particular, the central scale `x=2` has no successful such tilt when
`u >= 1/2`.

## Uniform arithmetic deletion

[`ZetaArithmeticDeviationBounds`](../RiemannGaussian/ZetaArithmeticDeviationBounds.lean)
keeps every fixed factorial-filter shift and the original divisor-log
majorant. For any admissible cutoff pair at an upper radius `U > 0`, one
common `r < 1` and finite `C` bound the removed two-tail response by
`C r^N` for **every** `0 <= u <= U`, every height, finite integer mask and
majorized coefficient family. The same estimate covers moving radii,
heights, masks and coefficients. No convergence of those moving parameters
is assumed, and no hypothetical-zero premise is used.

Exact scalar inequalities certify the universal window

```math
\frac9{20}N\lt\log n\le\frac{11}{2}N
\qquad(0\le u\le1).
```

Its endpoints improve the older global logarithmic window
`(2N/5, 8N log 2]`. It does not replace the already stronger central window
on the separate local source range.

## The original carrier and what remains

`physicalDeviationBand` intersects the actual annular residual with this
logarithmic window and the exact lower physical condition `X_N < n`.
The lower physical deletion is an exact equality. Every earlier arithmetic
mask, the damped integer floor, complex phase and factorial normalization
is kept. The additional removed error tends to zero even for moving
`u_N in [0,1]` and arbitrary moving heights.

For **every** exposed nontrivial zero with `Re rho > 1/2`, the narrowed
constant-filter carrier still tends, after its original normalization,
to minus the full analytic multiplicity. There is no additional local
restriction on `u = 3/2-Re rho`. The zero and exposure assumptions are
explicit. Uniformity of earlier source transport is not inferred from the
uniformity of this new deletion.

This does not extend the head/central/three-unpaid decomposition outside
its original range, estimate the retained signed sum, or prove a new
zero-free region. The next work concerns
[cancellation inside that sum](zeta-riesz-signed-frequency.md).

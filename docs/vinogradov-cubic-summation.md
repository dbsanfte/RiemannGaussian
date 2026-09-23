# Summing the retained cubic profile

The complete scale sum now yields an actual zeta bound with logarithmic
exponent `2/3` and the unconditional eventual zero-free family
`0<C<3*pi/10640`, including `C=1/1150`. Its coefficient ceiling is exactly
`20/19` times the preceding cubic-profile ceiling. The starting height is
finite but unevaluated; published benchmark constants remain stronger.
This is separate from the still open fixed-height Riesz arithmetic floor.

## One envelope covering every original block

Retain the [physical-scale profile](vinogradov-cubic-profile.md), with
`v=log(X)/log(t)`, `Delta_n=1/(4096*(2*n+1)^2)` and
`a_n=40*Delta_n^(3/2)`. The exact inequality

```math
 \delta v-\frac{v^3}{10368}
 \le40\delta\sqrt\delta-\frac{v^3}{2097152}
```

keeps cubic decay after paying the growth maximum.
[`VinogradovCubicDecay.block_bound`](../RiemannGaussian/VinogradovCubicDecay.lean)
proves that every original canonical block with `X<=4t`, at
`1-Delta_n<=sigma` and `t>=T_(8n)`, is at most

```math
 512t^{a_n}\exp\left(-\frac{(\log X)^3}{2097152(\log t)^2}\right).
```

Here `n>=48` and `T_m=(16*(2*m+1)^2)^(2*m)`. The small-block mass, the
finite lower-degree range, damping boundary, and both terms of each long
derivative profile all pay the same reserve. The exact profile-shift
identity retains both complementary derivative terms.

## The full sum, not a block-count maximum

For every `L>=1` and every finite depth `J`,
[`VinogradovCubicSummation.sum_le`](../RiemannGaussian/VinogradovCubicSummation.lean)
proves

```math
 \sum_{j<J}\exp\left(-\frac{(j\log2)^3}{2097152L^2}\right)
 \le1024L^{2/3}.
```

The proof uses `x^2-1<=x^3`, a Gaussian comparison with width `256*L^(2/3)`,
and the existing full Gaussian sum/integral estimate. It retains the actual
finite dyadic indices. Therefore the prefix has bound
`524288*t^a_n*log(t)^(2/3)`.

Direct Euler reconstruction, its additive remainder, and conjugation give
[`ZetaVinogradovSummedBound.bound_strip_abs`](../RiemannGaussian/ZetaVinogradovSummedBound.lean):

```math
 |\zeta(\sigma+it)|\le1048576|t|^{40\Delta_n^{3/2}}(\log|t|)^{2/3},
 \quad 1-\Delta_n\le\sigma\le3/2,\quad |t|\ge T_{8n}.
```

The absolute constant increases while the logarithmic exponent decreases.
The previous adjacent-band estimate remains available; no new summed
adjacent-band theorem is asserted.

## The paid zero detector

The same natural degree and height schedule pay the entire analytic discs
at both heights. Their normalized profiles tend to `17/3`; the full
Euler-center allowance still costs `2/3`. The resulting actual signed
cost tends to `10640*C/(3*pi)`.

[`ZetaVinogradovSummedCost`](../RiemannGaussian/ZetaVinogradovSummedCost.lean)
discharges the analytic hypotheses, and
[`ZetaVinogradovSummedZeroFree`](../RiemannGaussian/ZetaVinogradovSummedZeroFree.lean)
discharges the eventual cost inequality. Both zero-strip edges, closed
right-edge nonvanishing and the full union with prior components are
proved. The compact union holds for `C>=1/1150`.

See the [complete zero-free statement](vinogradov-zero-free.md) for the
width formula and all quantifiers. Sharper incomplete-system moments,
asymmetric block estimates, leading constants and finite starting-height
evaluation remain open. This classical mechanism is not claimed as a
historically new theorem or a world-record zero-free region.

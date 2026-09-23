# Complete near-one zeta growth from the actual Vinogradov moments

The current endpoint is
[`ZetaVinogradovSummedBound.bound_strip_abs`](../RiemannGaussian/ZetaVinogradovSummedBound.lean).
For `n>=48`, `1-Delta_n<=sigma<=3/2` and `|t|>=T_(8n)`, it proves

```math
 |\zeta(\sigma+it)|\le1048576|t|^{40\Delta_n^{3/2}}(\log|t|)^{2/3},
 \qquad \Delta_n=\frac1{4096(2n+1)^2}.
```

The [complete scale summation](vinogradov-cubic-summation.md) explains the
larger absolute constant and sharper logarithmic exponent. The same height
schedule feeds the [latest zero-free family](vinogradov-zero-free.md).
The remaining sections document its unsummed predecessor, including the
separate adjacent-band theorem; they do not claim a new summed band theorem.

## Unsummed predecessor and retained band estimate

[`ZetaVinogradovCubicBound.bound_abs`](../RiemannGaussian/ZetaVinogradovCubicBound.lean)
proves an unconditional bound for the actual Riemann zeta function. Put

\[
 \Delta_n=\frac{1}{4096(2n+1)^2},\qquad
 a_n=40\Delta_n^{3/2},\qquad
 T_n=\bigl(16(2n+1)^2\bigr)^{2n}.
\]

For every integer `n>=48`, at `sigma=1-Delta_n` and `|t|>=T_(8n)`,

\[
 \boxed{\left|\zeta(\sigma+it)\right|
 \le8192|t|^{a_n}\log|t|.}
\]

Every moment estimate, block scale, degree, damping weight, Euler endpoint
and infinite Euler remainder is paid. No independent analytic estimate is a
hypothesis of this theorem. The thresholds and coefficients are explicit
but conservative. At a fixed index `n>=48`, the strip keeps its displacement
and the growth exponent is less than `5/32` of its predecessor. The larger
starting height `T_(8n)` is paid by the joint schedule. The growth estimate feeds
a [complete proved VK zero-free region](vinogradov-zero-free.md), with a
conservative coefficient and an unevaluated starting height.

## Continuous coverage and the three-halves exponent

`bound_strip_abs` covers the entire strip
`1-Delta_n <= sigma <= 1`, including the one-line. Its coefficient is
independent of the displacement from one. The existing profile decreases
as sigma increases, so this extension requires no complex interpolation
or boundary assumption.

[`VinogradovCubicBudget.growth_eq_displacement`](../RiemannGaussian/VinogradovCubicBudget.lean)
proves the exact coefficient forty. The retained radius satisfies
`Delta_n <= 4*Delta_(n+1)`. Consequently the fully
compiled `bound_band_abs` gives, throughout each continuous band
`1-Delta_n <= sigma <= 1-Delta_(n+1)`,

\[
 \boxed{\left|\zeta(\sigma+it)\right|
 \le 8192
 |t|^{320(1-\sigma)^{3/2}}\log|t|
 \qquad (|t|\ge T_{8n}).}
\]

The bound retains its explicit band-dependent height threshold. The
[downstream schedule and zero detector](vinogradov-zero-free.md) now pay
that threshold along a growing degree and prove actual nonvanishing.
Matching the published constants remains open. The older eta-based bound in `ZetaVinogradovBound` has a
factor `1/(1-sigma)`. The stronger endpoint removes it by the existing
direct Euler reconstruction, with the actual pole endpoint and remainder
paid independently.

The stronger endpoint uses [shorter actual moments](vinogradov-narrow-packet.md),
`VinogradovCubicBudget.canonical_block_bound` and direct Euler reconstruction;
every scale, including `12<=k<48`, is explicitly paid.

## The actual dyadic blocks

[`VinogradovShortDyadic.original_block_bound`](../RiemannGaussian/VinogradovShortDyadic.lean)
converts the [fixed-coefficient block estimate](vinogradov-narrow-packet.md)
to the literal sum over `[X,2X)`. For `M^4<=X<=2M^4`, it proves

\[
 \left|\sum_{m=0}^{X-1}(X+m)^{-s}\right|
 \le 6X^{1-\sigma-\varepsilon_k/4}+2X^{1/2-\sigma}.
\]

Here `epsilon_k=1/(512k^2)` for `k>=48` and `1/(1600k^2)` otherwise.
It retains `k>=12`, `M>=(4k+1)k`, and
`M^(2k-2)<=t<=M^(2k)`. The initial damping weight pays the full shift
boundary. The integer fourth root fits the required twofold interval
once it is at least six.

[`VinogradovScaleSelection.exists_window_parameters`](../RiemannGaussian/VinogradovScaleSelection.lean)
then constructs the parameters for every actual middle block. At index `8n`, for
`t>=T_(8n)` and `t^(1/(4n))<=X<=t^(2/11)`, take

\[
 M=\lfloor X^{1/4}\rfloor,\qquad
 k=\left\lfloor\frac{\log t}{2\log M}\right\rfloor+1.
\]

Lean proves all original size and time conditions, including
`12<=k<=16n+1`. For `k>=48`, the retained degree/logarithm relation
gives `delta*v-v^3/10368<=40*delta^(3/2)`, where `v=log(X)/log(t)`.
The lower-degree range keeps its separate four-degree moment bound. Thus
the entire middle block is at most `8*t^a_n`. See the
[exact unmaximized estimate](vinogradov-cubic-profile.md).

The remaining scales have independent estimates:

| Actual scale | Proved bound on the original block |
| --- | --- |
| `X<=t^(1/(4n))` | `t^a_n`, from the full damped mass |
| `t^(1/(4n))<=X<=t^(2/11)` | `8*t^a_n`, from the retained cubic profile |
| `t^(2/11)<=X<=t^(1/3)` | `320`, from the sixth-derivative profile |
| `t^(1/3)<=X<=4t` | `512`, from the fourth-derivative profile |

Both terms of each classical profile are bounded in
[`VinogradovLongBlocks`](../RiemannGaussian/VinogradovLongBlocks.lean).
The four cases exhaust every block in the actual canonical eta cutoff.
`canonical_block_bound` therefore gives `512*t^a_n` with no supplied
degree, scale or moment premise.

## Complete zeta reconstruction and limits of the result

`ZetaVinogradovBound.of_block_bound` proves that a uniform bound `B`
on the actual blocks through canonical depth `J` implies

\[
 |\zeta(s)|\le\frac{6((J+1)B+1)}{1-\operatorname{Re}s}.
\]

This first transport uses the existing eta reconstruction, paying both
prefixes, their exact multiplier, the endpoint and the infinite tail.
It yields coefficient `32768/Delta_n` on the selected line.

The stronger endpoint uses
[`ZetaEulerLineBound.norm_le_prefix_add_six`](../RiemannGaussian/ZetaEulerLineBound.lean).
That theorem reconstructs zeta directly from the same ordinary dyadic
prefix, with a uniform additive cost of six. The new unconditional block
bound and the proved count `J+1<=8*log(t)` then give coefficient `8192`,
with no eta division. Conjugation supplies negative heights.

This result closes the all-scale transport gap for the explicit
fixed-width-packet moment estimate. It does not bound the fixed-height
Riesz arithmetic tail: the harmonic Type-II applicability obstruction
is unchanged. The VK zero-free width is now proved downstream; the
independent Riesz signed floor, benchmark matching and RH remain open. No historical novelty is
claimed for the classical growth mechanism formalized here.

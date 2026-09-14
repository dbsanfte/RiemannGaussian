# Gaussian degree windows and actual Dirichlet-sum cancellation

Lean now proves a power saving for the **original Dirichlet block**, uniformly
on continuous height and starting-point intervals. For every integer `k >= 12`,
there are `C > 0` and an integer `M₀` such that all integers `M >= M₀` and
all real parameters

```math
M^{2k-2}\le t\le M^{2k},\qquad M^4\le z\le 2M^4
```

satisfy

```math
\left|\sum_{n=0}^{M^4-1}(z+n)^{-it}\right|
\le C M^{\,4-1/(128k^2)}.
```

The endpoint is
[`VinogradovDirichletSaving.exists_dirichlet_block_saving`](../RiemannGaussian/VinogradovDirichletSaving.lean).
Its `block` and `dirichletTerm` are the existing literal sum and complex
power. Every moment, resonance, smoothing, Taylor and averaging cost is paid.
Constants and starting thresholds are **unevaluated for each fixed degree**.
This is a finite Dirichlet-sum theorem. Uniform control as the degree varies,
all-scale zeta growth and a new Vinogradov–Korobov zero-free region remain open.
The proved zero-free union and the independent signed Riesz obstruction are
unchanged. No historical novelty or benchmark record is claimed here.

## Partial blocks and the original signed identity

The stronger interface
[`exists_partial_dirichlet_saving`](../RiemannGaussian/VinogradovDirichletSaving.lean)
retains every integer partial length `0 <= L <= 2M^4`:

```math
\left|\sum_{n=0}^{L-1}(z+n)^{-it}\right|
\le C L M^{-\delta}+2M^2,\qquad \delta=\frac1{128k^2}.
```

This comes from the existing
[exact product-shift identity](../RiemannGaussian/VinogradovKorobovBlock.lean).
Its complex boundary correction and every outer base phase survive upstream.
The named downstream bound first pays the actual product-sum norm and the
complete endpoint correction, then divides by the positive averaging mass
`M²`. The boundary costs at most `2M²` after division. At `L=M⁴` this is
absorbed below the displayed power-saving bound. No independence of shifts,
vanishing boundary, or cancellation in the Taylor remainder is assumed.

## Every decreasing amplitude, including the literal zeta coefficients

[`VinogradovDampedSaving`](../RiemannGaussian/VinogradovDampedSaving.lean)
proves an exact affine-cost Abel bound. For every nonnegative decreasing
real weight family, under the same fixed-degree rectangle conditions,

```math
\left|\sum_{n=0}^{N}w_n(z+n)^{-it}\right|
\le C M^{-\delta}\sum_{n=0}^{N}w_n+2M^2w_0,
\qquad N+1\le2M^4.
```

The linear cancellation term pays the **actual total amplitude**. The
constant endpoint error pays only the initial amplitude. The exact complex
Abel identity remains upstream from this named norm estimate.

The theorem `exists_feature_block_saving` instantiates the weights for every
`Re(s)=sigma >= 0`, positive integer starting point `a` in `[M^4,2M^4]`,
`Im(s)` in the displayed height interval, and `N+1 <= 2M^4`:

```math
\left|\sum_{n=0}^{N}(a+n)^{-s}\right|
\le C M^{-\delta}\sum_{n=0}^{N}(a+n)^{-\sigma}
+2M^2a^{-\sigma}.
```

Its Lean statement uses the existing literal `zetaPrimeFeature` and
`zetaPrimeExpWeight`; these are the ordinary coefficients at **every**
integer in this block. No estimate for extra prime, sieve or arbitrary
oscillating weights is inferred.

## The actual product sum on a continuous rectangle

[`VinogradovRectanglePowerSaving`](../RiemannGaussian/VinogradovRectanglePowerSaving.lean)
proves, for each `k >= 12`, all sufficiently large integers `M`, every finite
`B ⊆ {1,...,M}`, and every point of the larger rectangle

```math
M^{2k-2}\le t\le M^{2k},\qquad M^4\le z\le 4M^4,
```

that

```math
\left|\sum_{a=1}^{M}\sum_{b\in B}(z+ab)^{-it}\right|
\le C M^{\,2-1/(128k^2)}.
```

The fourfold starting-point interval contains every `z+n` used by the
partial-block averaging theorem. Its constants are uniform over this entire
rectangle and all such subsets `B`, for the fixed degree. The full logarithmic
approximation error for each product sum is at most `1/(k+1)`, and its base
phase has unit modulus.

## Exact structure of the full degree window

Write `q=1,...,k`, `r=k(k+1)`, and use reciprocal scales
`a_q=(r M^q)^(-2)`. The actual logarithmic Fourier coefficients are

```math
\gamma_q=\frac{-t(-1)^{q-1}}{2\pi qz^q}.
```

The actual difference support obeys `|h_q| <= r M^q`. At the corner
`t=M^(2k), z=M^4`, every degree `q>2k/3` is unwrapped once `M>=r`.
Its complete Gaussian coordinate costs a constant times `M^(4q-2k)`;
a full coordinate count would cost `M^(2q)`. Using every eligible degree
gives the exact gain

```math
S=m(m-1),\qquad m=k-\left\lfloor\frac{2k}{3}\right\rfloor.
```

[`VinogradovDegreeWindow`](../RiemannGaussian/VinogradovDegreeWindow.lean)
proves this identity and the bound `k² <= 16(S-1)` for `k>=12`.
[`VinogradovFullResonance`](../RiemannGaussian/VinogradovFullResonance.lean)
transfers it to the **complete actual** resonance product.
After paying both critical moments plus `epsilon=1/2`,
[`VinogradovFullPowerSaving`](../RiemannGaussian/VinogradovFullPowerSaving.lean)
obtains the sharper corner product saving `1/(64k²)`. The earlier
[one-degree theorem](../RiemannGaussian/VinogradovKorobovPowerSaving.lean),
valid already for `k>=4`, remains available with saving `1/(2r²)`.

For the continuous rectangle, the upper coefficient bound preserves the
same no-wrap condition. The lower bound costs at most `4^q M²` in the
Gaussian width. Thus the selected coordinate exponent becomes
`4q-2k+2`. Using every degree with `2k<3q` and `q<k` gives exactly

```math
S'=(m-1)(m-2),\qquad k^2\le32(S'-1)\quad(k\ge12).
```

These corner comparisons are proved in
[`VinogradovPhaseRectangle`](../RiemannGaussian/VinogradovPhaseRectangle.lean);
the exact gain and complete resonance bound are in
[`VinogradovRectangleResonance`](../RiemannGaussian/VinogradovRectangleResonance.lean).
The gain remains quadratic after paying the continuous parameter variation.

## Every Gaussian and moment cost

The [upstream weighted fibre identity](../RiemannGaussian/VinogradovGaussianResonance.lean)
retains complex coefficients and full attainable difference vectors. Only a
named downstream estimate enlarges this support to its proved coordinate box.
For each nonzero, unwrapped coordinate, the
[full translated Gaussian bound](../RiemannGaussian/VinogradovGaussianSpacing.lean)
pays

```math
\frac{2}{\sqrt a(1-e^{-\pi/a})}
\min\left\{|S|,1+\frac{\sqrt a}{|\gamma|}\right\}.
```

Every other coordinate pays its full support count. The general allowance in
[`VinogradovIntervalResonance`](../RiemannGaussian/VinogradovIntervalResonance.lean)
uses all eligible actual degrees. No translated tail is omitted.
The original reciprocal-scale support cost is exactly `k*pi`; the existing
centering theorem quarters it in the product bound.

Both moment orders are `r=k(k+1)` and use the proved critical exponent plus
`1/2`. On the rectangle, the complete polynomial product therefore satisfies

```math
|\text{actual polynomial product sum}|^{2r^2}
\le C M^{\,4r^2-(S'-1)}.
```

Taking the positive moment root yields saving `(S'-1)/(2r²)`, which Lean
bounds below by `1/(128k²)`. Paying the full bounded Taylor error gives the
literal imaginary-power theorem, then the signed shift identity gives the
original Dirichlet-block result.

## Uniform Gaussian constants

[`actual_resonance_le_explicit`](../RiemannGaussian/VinogradovRectangleResonance.lean)
now exposes the exact parameter constant previously constructed inside the
existence proof. Its original existence theorem remains available as a wrapper.
[`VinogradovGaussianCost`](../RiemannGaussian/VinogradovGaussianCost.lean)
then bounds the actual complete joint resonance times the quartered support
exponential by `2^(9*k^2) * M^(k(k+1)-S')`, uniformly for `k>=12`.
In particular, at the actual order `r=k(k+1)`,

```math
\left[
 e^{k\pi/4}
 \left(4^k\frac{2r}{1-e^{-\pi}}
 \left(2r+2+\frac{2\pi k}{r}\right)\right)^k
\right]^{1/(2r^2)}\le2.
```

Every translated tail and reciprocal-scale prefactor is included. This
bounds the complete Gaussian constant after the actual moment root;
the homogeneous moment constants remain separate.

## Remaining analytic work

The degree-window saving is now quadratic and the actual block transfer is
proved. The next major requirement is quantitative control of moment
constants and starting thresholds **as the degree varies**, together with
all-scale block decomposition and zeta-growth transport. The literal damping
transfer and uniform Gaussian constants are already proved. Existential
constants at each fixed degree do not supply that uniform theorem.
The original Riesz carrier separately needs its combined signed correlation
saving. No new zero-free width follows from the present block theorem alone.

The compiled endpoints appear in the **Critical moments** view of the
[RH explorer](https://dbsanfte.github.io/RiemannGaussian/rh-proof/) and the
Vinogradov–Korobov view of the [main explorer](https://dbsanfte.github.io/RiemannGaussian/).
Their metadata, exact source locations and transitive axiom audits come from
the ordinary Lean root.

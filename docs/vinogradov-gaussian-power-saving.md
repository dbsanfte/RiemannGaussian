# Gaussian resonance and an actual imaginary-power saving

Lean proves a genuine saving for the literal shifted imaginary-power product
sum at an explicit set of related scales. For every integer `k >= 4`, put
`r = k(k+1)`. There are `C > 0` and an integer `M₀` such that every integer
`M >= M₀` and every finite `B ⊆ {1,...,M}` satisfy

```math
\left|\sum_{a=1}^{M}\sum_{b\in B}(M^4+ab)^{-iM^{2k}}\right|
\le C M^{\,2-1/(2r^2)}.
```

The endpoint is
[`exists_shifted_imaginary_power_saving`](../RiemannGaussian/VinogradovKorobovPowerSaving.lean).
The Lean statement uses the existing literal `dirichletTerm`, whose definition
is the displayed complex power. The bound is uniform over all such subsets
`B`; the full support bound would be `M²`. Constants and starting thresholds,
including their dependence on `k`, are **not numerically evaluated**.
This is the displayed regime `t=M^(2k), z=M^4`. It does not yet establish
uniform zeta growth, a new zero-free region, or the signed Riesz contradiction.

## The general resonance bound

The upstream [exact weighted fibre identity](../RiemannGaussian/VinogradovGaussianResonance.lean)
retains every complex coefficient and the complete attainable difference
vector. Its positive resonance sum has the form

```math
\mathcal R_s(a,\gamma;B)
=\sum_{h\in\mathcal D_s(B)}\prod_{j=1}^{k} K_{a_j}(\gamma_jh_j),
\qquad
K_a(x)=a^{-1/2}\sum_{m\in\mathbb Z}e^{-\pi(m-x)^2/a}.
```

[`VinogradovGaussianSpacing`](../RiemannGaussian/VinogradovGaussianSpacing.lean)
proves the full integer Gaussian sum is at most `1+sqrt(pi/c)`. It identifies
the integer distance with `|x|` when `|x| <= 1/2`. Including all translated
tails, every finite unwrapped sample set `S` at nonzero spacing `gamma` has

```math
\sum_{n\in S}\operatorname{tailEnvelope}(a,\gamma n)
\le \frac{2}{\sqrt a(1-e^{-\pi/a})}
\min\left\{|S|,1+\frac{\sqrt a}{|\gamma|}\right\}.
```

The two individual bounds and their selected-coordinate combination are
proved in that module. No omitted Gaussian translate is hidden in an error.
[`VinogradovIntervalResonance`](../RiemannGaussian/VinogradovIntervalResonance.lean)
proves the actual difference support satisfies `|h_j| <= sY^j` for every
`B ⊆ {0,...,Y}`. Its named downstream box estimate is a finite product:
each coordinate with nonzero `gamma_j` and
`|gamma_j| sY^j <= 1/2` uses the better of `2sY^j+1` and
`1+sqrt(a_j)/|gamma_j|`; every other coordinate pays its full count.
The canonical selection includes **all** eligible degrees.
The original joint support and signed identity remain available upstream.

[`VinogradovExplicitKorobov`](../RiemannGaussian/VinogradovExplicitKorobov.lean)
combines that allowance with both proved critical moments in the actual
product sum. This general inequality has no supplied spacing or moment
estimate as a premise. It can still be too large in a particular regime;
the cost calculation below is what establishes a net saving.

## Paying the complete cost

Use reciprocal scales `a_j=(r M^j)^(-2)`. Lean proves their actual first-family
support cost is exactly `k*pi`; the existing centering theorem quarters this
in the product-sum bound. The translated-tail prefactor is bounded by a
constant times `r M^j`, uniformly for `M >= 1`.

The actual logarithmic coefficients retain their Fourier normalization:

```math
\gamma_j=\frac{-t(-1)^{j-1}}{2\pi jz^j}.
```

At `t=M^(2k), z=M^4`, their difference range is
`s M^(2k-3j)/(2*pi*j)`. Consequently every `j>2k/3` is unwrapped once
`M>=s`. Its complete Gaussian coordinate cost is at most a fixed constant
times `M^(4j-2k)`, whereas the full count costs `M^(2j)`.
These identities and inequalities are proved in
[`VinogradovResonanceScaling`](../RiemannGaussian/VinogradovResonanceScaling.lean)
and [`VinogradovResonanceWindow`](../RiemannGaussian/VinogradovResonanceWindow.lean).

For every `k>=4`, degree `j=k-1` belongs to that window and saves two powers.
[`VinogradovResonancePower`](../RiemannGaussian/VinogradovResonancePower.lean)
pays all other degrees and proves the **complete** resonance product is at
most `C M^(k(k+1)-2)`. This concrete result uses one eligible degree; the
general bound retaining all eligible degrees is stronger and remains available.

Both moment orders are `r=k(k+1)`. Each uses the proved critical exponent
plus `epsilon=1/2`. After every Holder prefactor and the Gaussian cost is
restored, Lean obtains

```math
|\text{actual polynomial product sum}|^{2r^2}
\le C M^{4r^2-1}.
```

Taking the positive moment root gives the asserted strict saving. The entire
logarithmic-to-polynomial error is at most `1/(k+1)`; its exact base phase has
unit modulus. Paying this bounded error transfers the saving to the literal
imaginary-power sum without assuming cancellation in the remainder.

## What remains

A useful next step is to retain the savings of the whole eligible degree
window and extend the rigid scale relation to continuous parameter bands
usable in the existing product-shift averaging identity. Uniform quantitative
control of the degree-dependent moment constants and thresholds is also
needed for a Vinogradov–Korobov zero-free theorem. The original Riesz carrier
still needs its combined signed correlation saving. These are open tasks;
this product-sum theorem supplies no new zero-free width by itself.

The compiled endpoint appears in the **Critical moments** view of the
[RH explorer](https://dbsanfte.github.io/RiemannGaussian/rh-proof/) and the
Vinogradov–Korobov view of the [main explorer](https://dbsanfte.github.io/RiemannGaussian/).
Their metadata and axiom audits are generated from the ordinary Lean root.

# Anchored prime correlations with the real phase retained

[ZetaGaussianPrimeCorrelation](../RiemannGaussian/ZetaGaussianPrimeCorrelation.lean)
connects the complete Gaussian prime measure to an anchored Schur
inequality for every nonnegative summable phase spectrum. It retains
prime ratios and products together, isolating the exact cosine energy
needed for the signed real response. The resulting necessary correlation
constraint reaches the original finite-zero budget.

The independent upper gap for this energy remains unproved. The conditional
floor criterion explicitly assumes it. This slice does not enlarge the
zero-free region or establish the independent centered-carrier floor or RH.
The matrix principle is classical; the new work here is its checked
projection and transport to the repository's actual arithmetic quantities.
No historical novelty claim is made.

## The common arithmetic measure

Use the full positive amplitude `W` from
[ZetaGaussianPrimeBlocks](../RiemannGaussian/ZetaGaussianPrimeBlocks.lean),
including the Gaussian, shifted Euler and averaged logarithmic responses
with their original multipliers. Write

```math
P(v)=\sum_n a_n\cos(\omega_n v),\qquad
A=\sum_n a_n,\qquad c=a_0,\qquad \omega_0=0.
```

For a finite positive support `S`, set

```math
M_S=\sum_{p\in S}W(p),\qquad
b_S=\sum_{p\in S}W(p)P(t\log p),\qquad
\mathcal W=\operatorname{mixedWork}.
```

When `P` is nonnegative, `b_S<=mathcal W` follows from the convergent
common-measure identity. No prime response is charged separately.
The general matrix statements even allow signed finite test weights;
the actual Gaussian transport uses its nonnegative weights. Positive
support need not consist only of primes: the actual measure also retains
all proper prime powers.

## Ratios alone pay an unnecessary sine cost

The two exact finite pair forms are

```math
\begin{aligned}
R_S&=\sum_{p,q\in S}W(p)W(q)P\bigl(t\log(q/p)\bigr),\\
T_S&=\sum_{p,q\in S}W(p)W(q)P\bigl(t\log(pq)\bigr),\\
Q_S&=\frac{R_S+T_S}{2}.
\end{aligned}
```

`realPrimeEnergy_eq_log_products` proves these coordinates without
discarding either phase. For each frequency put
`C_n=sum_(p in S) W(p)*cos(omega_n*t*log p)` and
`S_n=sum_(p in S) W(p)*sin(omega_n*t*log p)`. The convergent identities are

```math
Q_S=\sum_n a_n C_n^2,\qquad
R_S-Q_S=\sum_n a_n S_n^2\ge0.
```

These are `hasSum_realPrimeEnergy` and `hasSum_sineDefect`.
`realPrimeEnergy_le_ratioEnergy` proves the smaller allowance. The proof
mirrors every phase about zero before taking the energy bound: the signed
work is unchanged, and the sine sums cancel exactly. The product phases
retain the common phase that the ratio differences alone do not record.
No assumption that distinct prime phases are independent is introduced.

## The arithmetic target, with its costs

The sharper anchored Schur inequality is

```math
(b_S-cM_S)^2\le(A-c)(Q_S-cM_S^2).
```

`cosine_schur` proves this for arbitrary finite phase configurations and
countable coefficient families. The zero-frequency contribution is removed
exactly before applying the quadratic discriminant inequality.
For the actual Gaussian weights, `gaussian_forced_correlation` gives

```math
cA M_S^2\le(A-c)Q_S+2cM_S\mathcal W.
```

Thus small actual work forces substantial collective **real** pair energy.
For `c>0`, `M_S>0`, a simple sufficient independent estimate is

```math
(A-c)Q_S\le c(A-2\delta)M_S^2.
```

`gaussian_work_of_energy_gap` then proves
`mathcal W>=delta*M_S`. For a useful positive floor choose `delta>0`.
The energy estimate is an explicit hypothesis, not a discharged theorem.
This sufficient criterion drops the nonnegative `b_S^2` term; the full
squared Schur inequality remains available for sharper comparisons.

Let `mathcal S_Z` be the original coefficient-weighted, compensated
Gaussian source of an actual finite zero group, and let `mathcal B_exact`
be the original signed budget. The existing theorem is
`mathcal S_Z+mathcal W<=mathcal B_exact`. The new
`finite_source_correlation_constraint` proves, with every original
frequency, strip and summability hypothesis retained, the stronger squared
constraint

```math
\left[\max\{0,cM_S+\mathcal S_Z-\mathcal B_{\rm exact}\}\right]^2
\le (A-c)(Q_S-cM_S^2).
```

The actual left boundary mean, pole and completion terms remain signed
inside this budget. The full square is kept through the terminal theorem;
the constant frequency is removed exactly from the energy on the right.
A separate upper bound on that right side would need to beat the complete
source surplus on the left to exclude the zero configuration.
The necessary inequality alone is compatible with the zero hypothesis.

## Product and ratio coordinates also separate the Gaussian weight

For primes `p,q`, let `U=log p+log q`, `V=log q-log p`, and let
`G(p)=log(p)*exp(-sigma*log p)*exp(-B*(log p)^2)` be the actual Gaussian
part of the common amplitude. `gaussian_pair_coordinates` proves

```math
G(p)G(q)=\frac{U^2-V^2}{4}\,
e^{-\sigma U}\,e^{-BU^2/2}\,e^{-BV^2/2}.
```

The phase coordinates and heat coordinates therefore agree. The exact
separation factor `U^2-V^2` remains available, including when `p=q`.
The existing
[`zetaDistinctPrimePairCoefficient_separation`](../RiemannGaussian/ZetaPrimePairSeparation.lean)
retains the corresponding product-minus-separation structure for the
distinct-prime-power arithmetic coefficient.

This provides a concrete way to group the pair sum by product size and
logarithmic ratio while keeping both oscillations. It is an identity,
not a bound on the resulting sum. It describes the Gaussian-Gaussian
part of the full weight: a bound for the complete `Q_S` must also handle
all mixed Euler and averaged-response terms, including the diagonal.

## What would count as the next advance

The next target is an independent estimate for this real pair energy,
or for its joint contribution with the signed boundary budget, on sets
carrying enough actual arithmetic mass. Increasing block lengths in the
[triangular minorant class](zeta-gaussian-prime-blocks.md) cannot supply
the leading gain. Assuming phase independence, taking separate absolute
values, or deriving the required upper gap from the hypothetical zero
would not establish an independent estimate.

The [ordinary-prime reduction](zeta-gaussian-prime-reduction.md) now pays
the proper prime powers, both auxiliary responses and all their mixed
quadratic terms. At the current dilation, its normalized additive allowance
tends to zero for bounded nonconstant mass. The remaining independent
estimate can therefore target ordinary Gaussian-prime energy, with the
same signed source budget retained.

For a leading gain, the retained mass and the energy estimate must be
controlled together at the growing source scale. No such joint
large-height estimate is asserted here. The
[carrier information audit](signed-prime-carrier-information-audit-2026-09-12.md)
keeps the separate direct target: only a cofinal real margin above the
negative source is required, rather than complete norm decay.

The root library imports the module; its public declarations are in the
compiled status inventory. The **Prime correlations** explorer endpoint
links the actual constraint, conditional floor, exact phase coordinates,
Gaussian coordinates and proven projection improvement. Local validation
and publication remain separate; this slice is held locally under the
current no-commit instruction.

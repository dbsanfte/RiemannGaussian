# Independent upper bound for the complete ordinary-prime energy

[ZetaGaussianPrimeEnergyBound](../RiemannGaussian/ZetaGaussianPrimeEnergyBound.lean)
supplies an independent upper bound for the ordinary Gaussian-prime energy.
It applies to countable moving coefficient families using their existing
mass and first logarithmic frequency moment. It also connects that bound
to the actual squared finite-zero source.

The bound has not been shown small enough to give a new zero exclusion.
Its normalized decay requires logarithmic height to be negligible relative
to dilation; a separate theorem proves that the current region's dilation
does not supply that condition beyond its plateau. RH remains open.

## The complete arithmetic object

Use the existing `k=9` dilation, with `q>=1`, `x=shift(q)` and
`B=gaussianScale(q)`. For the original ordinary-prime amplitude `P_q` from
[the complete remainder reduction](zeta-gaussian-prime-reduction.md), put

```math
g_q(v)=\sum_{p\ {\rm prime}}(\log p)p^{-1-x}
  e^{-B(\log p)^2}\cos(v\log p),
\qquad L(t)=\log(|t|+26).
```

`primeCosine` is this genuinely convergent complete sum. No subset of
primes is selected according to its sign. The `+26` in this Euler
dominator differs from the `+2` in the displayed zero-free curve.

For `a_n>=0`, summable `a`, and `omega_n>=1` whenever `n!=0`, define

```math
\widetilde a_0=0,\qquad \widetilde a_n=a_n\ (n\ne0),\qquad
m=\sum_n\widetilde a_n,\qquad
\mathcal F=\sum_n\widetilde a_n\log\omega_n.
```

```math
Q(q,t)=\sum_n\widetilde a_n\,g_q(\omega_n t)^2.
```

The Lean definition `fullEnergy` takes the complete cosine sum before
squaring. `tendsto_range_energy` proves it is the limit of the original
finite real pair energies along complete prime prefixes. Thus it retains
the product phases, ratio phases and diagonal from the
[anchored Schur theorem](zeta-gaussian-prime-correlation.md).

## Two independent response bounds

`primeSum_eq_transform_sub_regularMean` first proves the complete complex
identity

```math
G_{\sigma,B}(t)=H_B(\sigma-1+it)
-\int_{\mathbb R}\nu_B(y)
  \frac{\zeta_1'}{\zeta_1}(\sigma+i(t-y))\,dy.
```

Here `zeta_1` is the original pole-removed zeta function, `nu_B` is the
normalized vertical Gaussian, and `H_B` is the full complex half-Gaussian
transform. All integrability obligations are discharged on `sigma>1`.
The identity precedes projection or estimation.

The existing
[Euler-boundary theorem](../RiemannGaussian/ZetaEulerBoundaryControl.lean)
bounds the real logarithmic derivative of `zeta_1` by a constant times
`L(t)`, uniformly through the closed Euler boundary. The new proof averages
that signed response using the exact first absolute Gaussian moment.
The original pole is bounded separately, and the proved proper-power
allowance transfers the result to ordinary primes.

`exists_prime_bounds` proves that positive constants `D,K` exist such that

```math
|g_q(v)|\le Dq\quad(v\in\mathbb R),\qquad
|g_q(v)|\le K L(v)\quad(|v|\ge1).
```

The first estimate comes from the actual positive Euler mass. The second
uses cancellation in the complete signed response. Both constants are
independent of dilation, height, coefficients and frequencies. Their
existence is proved; no numerical enclosure or optimized value is claimed.

## Squared energy with only the first logarithmic moment

For `omega>=1`, `L(omega*t)<=L(t)+log(omega)`. Combining the two caps
before squaring gives

```math
g_q(\omega t)^2\le
4K^2L(t)^2+2DKq\log\omega.
```

`exists_fullEnergy_bound` consequently proves, for all `q>=1` and
`|t|>=1`,

```math
Q(q,t)\le4K^2mL(t)^2+2DKq\mathcal F.
```

No second logarithmic moment, finite frequency support or independence of
prime phases is assumed. A crude square of the logarithmic cap alone
would demand a second moment; the linear-dilation cap pays the high
frequency contribution using the first moment already in the theorem chain.

For arbitrary moving families, masses bounded by `A`, frequency costs
bounded by `F`, dilations tending to infinity, and `L(t_N)/q_N->0`,
`tendsto_normalized_fullEnergy` proves

```math
\frac{Q(q_N,t_N)}{q_N^2}\longrightarrow0.
```

This is decay of the complete ordinary-prime energy in the stated regime,
in addition to the earlier decay of its auxiliary allowance.

## The actual source and the remaining obstruction

Let `S_Z` denote the original coefficient-weighted compensated source of
an actual finite zero group. Define `B_signed` by subtracting the exact
constant channel `a_0*constantWork` from the original `exactBudget`.
The signed left mean, rational response, pole, completion and shifted
right response all remain. Complete prime-prefix convergence cancels the
constant mass algebraically.

`finite_source_le_fullEnergy` proves

```math
\max(0,S_Z-B_{\rm signed})^2
\le(1+q^{-1})mQ(q,t)+E(q,m).
```

Here `E(q,m)=(1+q)m^2C^2` is exactly the already proved full remainder
allowance. `exists_source_growth_bound` inserts the independent estimate
for `Q`, with every original phase and source hypothesis retained:

```math
\max(0,S_Z-B_{\rm signed})^2
\le(1+q^{-1})m\bigl(4K^2mL(t)^2+2DKq\mathcal F\bigr)+E(q,m).
```

This is a proved necessary constraint on actual zeros. The remaining
contradiction requires a positive source surplus larger than this cost,
or a sharper bound exploiting its correlation with the signed boundary.

The current explicit-region schedule is
`q(t)=max(1,log(|t|+2)/320000)`. The theorem
`current_dilation_height_ratio_lower` proves, whenever
`log(|t|+2)>=320000`,

```math
\frac{L(t)}{q(t)}\ge320000.
```

The height term remains in this particular upper bound at that schedule.
The subsequent [signed Poisson comparison and energy decay](zeta-gaussian-prime-energy-decay.md)
removes this limitation using the existing log-log zero-free gap. It proves
actual normalized energy decay whenever absolute height diverges and
the height-to-dilation ratio is bounded, including the current schedule.
The ratio lower bound above remains valid. Taking a larger dilation also
changes the zero source and cannot by itself exclude a fixed interior zero.
The signed source budget and the independent cofinal floor for the separate
centered prime carrier remain open. No historical novelty or larger
zero-free region is claimed.

The root import and compiled inventory retain this independent bound and
complete source transport. The **Prime energy** explorer endpoint now ends
at the subsequent current-dilation decay and actual source-surplus limit.
The slice remains local under the current no-commit instruction.

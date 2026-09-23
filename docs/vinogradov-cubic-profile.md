# Retaining the physical-scale cubic saving

The scale profile below is the input to the current
[complete summed endpoint](vinogradov-cubic-summation.md), with family
`0<C<3*pi/10640`, including `1/1150`. The unsummed predecessor described
here remains proved at `0<C<3*pi/11200`, including `1/1250`, with its
exact `17/5` gain over the shorter-moment ceiling. Both starting heights
are finite and unevaluated; published benchmark coverage remains open.

## The information that changes the estimate

The [shorter actual moments](vinogradov-narrow-packet.md) already bound an
original damped block on `[X,2X)` by

```math
6X^{1-\sigma-\varepsilon_k/4}+2X^{1/2-\sigma},\qquad
\varepsilon_k=\frac1{512k^2}\quad(k\ge48).
```

The preceding reconstruction replaced the middle-block power by a uniform
ceiling and paid the smaller blocks trivially. This lost its dependence on
`X`. The chosen degree and fourth root satisfy
`M^(2k-2)<=t` and `X<=2*M^4`. With `M>=16` and `k>=48`,
[`degree_log_bound`](../RiemannGaussian/VinogradovCubicSaving.lean) proves

```math
 k\log X\le\frac94\log t.
```

Consequently, for `v=log(X)/log(t)` and `1-sigma<=delta`,
`power_le_cubic_profile` retains the stronger inequality

```math
 X^{1-\sigma-\varepsilon_k/4}
 \le \exp\!\left((\delta v-v^3/10368)\log t\right).
```

This unmaximized profile is a public theorem, available for further summation
over scales. No bound for a hypothetical replacement sum is assumed.
`cubic_le` proves its numerical maximum is at most
`40*delta*sqrt(delta)`. The proof keeps the nonnegative factor
`(v-a)^2*(v+2a)` with `a=sqrt(3456*delta)` and pays its exact coefficients.

This is an application of the classical cubic VK block-to-growth mechanism,
not a historical novelty claim. Compare
[Bellotti, pinned v1, Lemma 2.12 and Section 5](https://arxiv.org/html/2306.10680v1).
The sharper logarithmic factor is now proved by the downstream summation;
the published leading constants are not imported.

## All scales and the changed starting height

Use the unchanged target displacement

```math
\Delta_n=\frac1{4096(2n+1)^2},\qquad
 a_n=40\Delta_n^{3/2},\qquad
 T_m=(16(2m+1)^2)^{2m}.
```

The actual parameter construction is now applied at index `8n`, so the
middle window starts at `t^(1/(4n))`. This requires `t>=T_(8n)`.
The complete small-block mass is at most `t^(Delta_n/(4n))`, which is at
most `t^a_n` for `n>=2`. The finite degree range `12<=k<48` keeps its
original four-degree moment saving and is paid separately. Both derivative
profiles pay every remaining block through `4t`, including their second
terms. The shift boundary remains at most two per block.

[`VinogradovCubicBudget.canonical_block_bound`](../RiemannGaussian/VinogradovCubicBudget.lean)
therefore bounds every original canonical block by `512*t^a_n` for `n>=48`.
Direct Euler reconstruction proves

```math
 |\zeta(\sigma+it)|\le8192|t|^{40\Delta_n^{3/2}}\log|t|,
 \qquad 1-\Delta_n\le\sigma\le1,\quad |t|\ge T_{8n}.
```

`growth_lt_previous` proves that, at a fixed displacement, this exponent is
strictly less than `5/32` of the preceding `2*Delta_n/n` exponent.
**The starting height has increased from `T_n` to `T_(8n)`.** Both statements
must travel together. The older theorem remains available at its earlier
height. Adjacent bands have displacement coefficient 320.

## The actual zero exclusion

On the natural degree `n=floor((L/log L)^(1/3)/64)`,
[`VinogradovCubicSchedule`](../RiemannGaussian/VinogradovCubicSchedule.lean)
proves `8n` is at most the already paid balanced index. This pays the enlarged
threshold on the same moving schedule, with the unit disc buffer included.
The normalized radius tends to `1/4`; the growth cost tends to five second
logarithms. Each complete profile costs six, and the Euler-center allowance
still costs `2/3`. The entire signed contradiction cost therefore tends to

```math
 \frac{11200C}{3\pi}.
```

[`ZetaVinogradovCubicCost`](../RiemannGaussian/ZetaVinogradovCubicCost.lean)
discharges both actual analytic-disc hypotheses, retaining the exact divisor,
multiplicity, signed boundary moment and radial correction.
`ZetaVinogradovCubicZeroFree` proves the resulting nonvanishing and complete
union, with no unpaid analytic or arithmetic estimate as a hypothesis.

The downstream [complete summation](vinogradov-cubic-summation.md) now
retains a cubic reserve on every scale and reduces the logarithmic allowance
to exponent `2/3`. Stronger incomplete-system moment estimates and the sharp
published constants still need proofs. Finite starting-height evaluation,
the independent fixed-height Riesz floor and RH remain open.

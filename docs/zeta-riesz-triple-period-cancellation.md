# Literal triple cancellation in both whole-sum comparisons

The new estimate bounds a signed sum over actual primes before taking its
absolute value. It applies to a nonempty unbalanced-triple population inside
the original core, and reaches the same whole `J+C` used by the source
contradiction. It uses no zero, exposure or simplicity hypothesis.

The final numerical whole floor and ceiling remain open. This is a local
radial payment, not source-normalized decay of the selected population.

## The paid population

Fix `54 <= abs(y)` and `1/2 < u <= 10001/20000`. On the original dyadic
schedule, choose a negative phase peak `v` with `2N <= v <= 2N+1/2`.
The selected integers are the distinct squarefree triples `n=p*q*r`, where

```math
\frac9{25}v<\log q\le\frac25v,\qquad
\frac2{25}v<\log r\le\frac1{10}v,\qquad
v-\frac\pi{|y|}<\log n\le v+\frac\pi{|y|}.
```

The last-prime interval has its exact cofactor-dependent endpoints; it is
not completed or replaced by a density model. The geometry proves `p>q>r`,
all original core masks, and largest-prime share at most `9/16`. It also
proves disjointness from the earlier balanced-triple population. Literal
prime-count estimates prove eventual nonemptiness.

In this chamber the original coefficient is exactly

```math
c_L(pqr)=\frac{\log(pqr)}L\log r.
```

For fixed `q,r`, its real atom is therefore

```math
\frac{\log r}{Lqr}\,
 \frac{e^{-T/2}T^{N+1}}{N!}\frac{\cos(yT)}p,
\qquad T=\log p+\log(qr).
```

## Cancellation and the explicit debit

The proof partitions the complete period into `8m` half-open log cells,
with a mesh fixed independently of `N`. Opposite cosine values cancel
exactly. The proved sharp prime counts, the actual factorial variation and
the within-cell phase error together leave at most `1/500` of the common
weighted period mass. The phase is retained inside each literal prime sum;
this is not a termwise `abs(cos)` bound.

The two cofactor prime sums have harmonic mass at most `7/250`. With
`h=pi/(4m*abs(y))` and a common radial minimum `V`, the full raw rectangle
costs at most `m*V*h/6250`. Crucially, the theorem also proves

```math
0<V\le\frac{e^{-v/2}v^N}{N!}\le\frac{501}{500}V,
```

so `V` is bounded by the actual kernel rather than a free allowance.

Write `D` for this population, `S=coreBand`, and `f_N` for the **original
residual atom**, including `1-boundedShare`. Existing geometric estimates
pay the allocation difference once for the entire population. The already
proved core-to-whole comparison pays its separate vanishing error. The
terminal theorem gives a nonnegative sequence `e_j -> 0` such that eventually

```math
\left|\Re\left[u^{N+1}
 \left((J_N+C_N)-\sum_{n\in S\setminus D}f_N(n)\right)\right]\right|
\le
\frac\pi{25000|y|}\,u^{N+1}\frac{e^{-v/2}v^N}{N!}+e_j.
```

This supplies both a lower and an upper comparison with the **same exact
signed complement**. Every cofactor count, period and core condition is
discharged. Starting orders remain unevaluated. The explicit radial debit
can grow at source scale for `u>1/2`; no source-`o(1)` prime-density
approximation is asserted.

## Relation to the existing payments

The [combined whole comparison](zeta-riesz-combined-triple-payment.md) now
spends this payment alongside the expanded `P,I,D,H` populations. Exact
disjointness keeps every earlier payment intact, and the triple cost is
deducted before deriving the new margin
`(2/25*sqrt(N+1)-1/8)*G_N`. The final rest is exactly
`S\\(P union I union H union Q union D)`, where `Q` is this triple population.
Both comparisons retain the favorable real part of the coupled `Q` sum.
Neither older, larger margin may be paired with this smaller remainder.

The whole-sum targets are still the independent cofinal `-79/1000-o(1)`
floor for simple-zero sources and `3/2+o(1)` ceiling for multiple-zero
sources. Other triple geometry, other counts and other periods remain in
the signed complement. No zero exclusion follows from this local estimate.

## Checked declarations

- [Signed period and actual factorial kernel](../RiemannGaussian/ZetaRieszPrimePeriodCancellation.lean):
  `eventually_weighted_prime_period`, `eventually_factorial_prime_period`.
- [Literal triple payment and whole comparison](../RiemannGaussian/ZetaRieszTriplePeriod.lean):
  `coefficient_two_large`, `eventually_raw_population_bound`,
  `population_subset_core`, `eventually_population_nonempty`,
  `tendsto_allocationBound`, `eventually_whole_saddle_bound`.
- [Compiled status](proof-status.json) and
  [RH explorer audit](rh-proof-explorer/audit.json) expose the supporting
  `triple-period-cancellation` endpoint. The main RH endpoint is unchanged.

This standalone triple theorem imports no generated cover. The separate
combined application uses the now-checked full positive-five cover and the
older four/negative-five covers; all remain outside ordinary builds.

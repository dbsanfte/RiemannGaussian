# A wider explicit region from the complete Gaussian cost

[ZetaGaussianRetainedRegion.exact_strip_min](../RiemannGaussian/ZetaGaussianRetainedRegion.lean)
proves, for every genuine nontrivial zeta zero `rho=beta+i*t`,

```math
\begin{gathered}
|t|\ge10^6,\qquad L=\log(|t|+2),\qquad C(L)=L+2052\log L+30240,\\
d(t)=\min\left\{\frac1{450000},\frac{221}{250C(L)}\right\}
\quad\Longrightarrow\quad d(t)\lt\beta\lt1-d(t).
\end{gathered}
```

The threshold is explicit and there is no upper height ceiling. The same
module's `nonvanishing` includes the closed right edge for literal zeta.
All arithmetic, phase-family and analytic premises are discharged.
The interior strip and RH remain unresolved.

## What improves the budget

The original signed Gaussian identity and its three complete prime
responses remain upstream. The same exact contact family supplies all
coefficient and phase-positivity premises; there is no new coefficient
search. Keep the original analytic parameters

```math
q\ge1,\qquad w=\frac1{450000q},\qquad x=\frac w{1000},\qquad B=4w^2,
\qquad k=9.
```

The [retained-cost theorem](../RiemannGaussian/ZetaGaussianRetainedCost.lean)
holds for every eligible family with
`a_0<=37/200`, `a_1>=79/250`, nonconstant mass `W<=61/100` and logarithmic
frequency cost `J<=1/4`. Its complete upper bound is

```math
\operatorname{budget}\le36922q+\frac L{36}+57\log L+840.
```

Only the half-Gaussian part of the constant channel is charged linearly in
`q`: the full constant bracket is at most `199575*q+560`. The left
allowance is at most `L/2046+log(L)+11`, and its inverse half-width is at
most `93`. Rational tails, completion, right response and frequency terms
are all included before the displayed rounding. This estimate has no
condition linking height to dilation.

Choose

```math
q(t)=\max\left\{1,\frac{C(L)}{397800}\right\}.
```

Then `C(L)/36<=11050*q`, so the budget is at most `47972*q`. A zero in the
proposed strip forces the **same original source** to be at least
`48000*q`. Its multiplicity and favorable Poisson reserve are retained.
The strict contradiction proves the new curve; it does not assume a bound
for the separate interior prime carrier.

## Exact comparison and scope

`previous_width_le` contains the complete
[preceding explicit curve](zeta-gaussian-all-height.md).
`previous_width_lt` proves strict improvement whenever `L>320000`.
`explicitWidth_eq_plateau` proves that the width remains `1/450000`
through `L=340000`; this is an included interval, not a claim that 340000
is the exact transition. The defining minimum gives the actual transition
without a numerical root approximation.

These improvements occur at extremely large heights. They are comparisons
between two compiled repository bounds, not an exhaustive world-record
claim. The [literature table](zero-free-literature-frontier.md) retains its
previous exact comparison interval. Extending its external benchmark
comparisons is separate work.

`union_with_eventual` combines the new explicit curve with the existing
log-log component by maximum where both height conditions hold. The latter
threshold remains coefficient-dependent and unevaluated.

The earlier multiplicity, separation, pole-filter-cost and Gaussian-energy
theorems retain their explicitly stated width and dilation. They are not
silently widened by this new universal zero-free theorem.

## Arithmetic consequence

[ZetaSquarefreeGaussianRetainedRegion](../RiemannGaussian/ZetaSquarefreeGaussianRetainedRegion.lean)
uses `H_y=log(2*abs(y)+5)` and

```math
m(y)=\min\left\{\frac1{450000},\frac{221}{250C(H_y)}\right\},
\qquad r(y)=1+\frac{m(y)}2.
```

For every `abs(y)>=500002`, the literal quotient `zeta(s)/zeta(2*s)` is
analytic on a neighborhood of the full closed disc centered at `3/2+i*y`
with radius `r(y)>1`. The entire doubled-ordinate window and the pole
exclusions are paid. `previous_radius_le` retains the previous radius;
`previous_radius_lt` improves it strictly when `H_y>320000`.

`exists_response_bound` transports this larger radius to **every** original
eligible prime subset, squarefree mark, fixed polynomial and moment order,
with the signed two-harmonic prime envelope unchanged. A single finite
constant works at each fixed center; uniformity over all unbounded centers
is not asserted. For a newly available fixed radius, the geometric factor
`r^(-N)` is stronger, while its constant and polynomial budget stay explicit.

The full signed ordinary-prime remainder remains outside this estimate.
Its independent cofinal lower bound at the retained zero-source scale is
still the missing contradiction step.

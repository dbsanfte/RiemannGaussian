# The complete explicit Gaussian union

For every actual nontrivial zeta zero `ρ = β + it` with `|t| ≥ 1000000`,
[exact_strip](../RiemannGaussian/ZetaGaussianRegionUnion.lean) proves
`d(t) < β < 1-d(t)`. The same module proves literal nonvanishing on the
closed right edge. There is no upper height ceiling.

With `L = log(|t|+2)`, the complete width is

```math
\begin{aligned}
C_1(L)&=L+2052\log L+30240,\\
C_2(L)&=L+1995\log L+29400,\\
d(t)&=\max\left\{
\min\left\{\frac1{450000},\frac{221}{250C_1(L)}\right\},
\min\left\{\frac1{40500},\frac{1547}{1800C_2(L)}\right\}
\right\}.
\end{aligned}
```

[width_eq_max_min](../RiemannGaussian/ZetaGaussianRegionUnion.lean)
checks this formula. The existing eventual Littlewood component joins by
another maximum when both height conditions hold. Its coefficient-dependent
starting height is still unevaluated.

## Why smaller dilations work

The physical parameters are `w=1/(450000*q)`, `x=w/1000`, `B=4*w^2`,
at derivative order nine. The new
[geometry](../RiemannGaussian/ZetaGaussianExpandedScale.lean) works for
every `q ≥ 9/100`. Exact Gaussian homogeneity needs only `q>0`.
The larger response multiplier is explicitly bounded by `1/400`.

The [selected source](../RiemannGaussian/ZetaGaussianExpandedSource.lean)
remains at least `48000*q`. Its statement keeps multiplicity and the whole
positive Poisson reserve. The cotangent subtraction costs at most two.
The [full cost](../RiemannGaussian/ZetaGaussianExpandedCost.lean) is

```math
36922q+\frac L{35}+57\log L+840.
```

Choosing `q=max(9/100,C_2(L)/386750)` makes this at most `47972*q`,
strictly below the source. The general family theorem is instantiated with
the existing exact phase family; no new coefficient search or unproved
arithmetic estimate is used.

## Proven gain and arithmetic transport

[tenfold_previous_le](../RiemannGaussian/ZetaGaussianRegionUnion.lean)
proves at least a tenfold width increase throughout `1 ≤ L ≤ 64`.
For actual exclusion, retain `|t| ≥ 1000000` as well. In particular the
width is at least `1/45000` on that domain. The two curves have different
large-height costs; their maximum retains the previous curve everywhere.

For each arithmetic center `|y| ≥ 500002`, use `m(y)=d(2|y|+3)` and
`r(y)=1+m(y)/2`. The
[complete squarefree transport](../RiemannGaussian/ZetaSquarefreeGaussianRegionUnion.lean)
proves analyticity on the full closed disc and bounds every original marked
response there. It also proves at least a tenfold increase in `r(y)-1`
when `log(2|y|+5) ≤ 64`. The response constant may depend on the center;
the signed prime envelope, marks and polynomial coefficient cost remain.

The independent cofinal signed arithmetic floor and RH remain open.
Older multiplicity, separation and filter-cost theorems retain their stated
widths. The [literature comparison](zero-free-literature-frontier.md) retains
its compiled interval. The [Vinogradov–Korobov work](vinogradov-korobov-framework.md)
has not yet proved its analytic region; it is not included in this union.

# Logarithmic cancellation and the full squarefree cutoff family

[Lean proof](../RiemannGaussian/ZetaSquarefreeVaughanBudget.lean)
· [Original squarefree projection](zeta-squarefree-vaughan-projection.md)
· [Theorem explorer](theorem-explorer/)

The complete projected logarithmic prefix has bound `C_y*sqrt(U)` times
the original polynomial coefficient norm. Keeping its two logarithms
together removes the extra moment-order and cutoff-logarithm costs of
the preceding estimate. The whole projected small part consequently has
the original square-root product budget for every cutoff pair. This is
an independent analytic bound, with no zeta-zero hypothesis.

## The cancellation before the norm

Keep the literal quotient and its marked local factors:

\[
Q(s)=\frac{\zeta(s)}{\zeta(2s)},\qquad
A_s(a)=\prod_{r\mid a}\frac{r^{-s}}{1+r^{-s}},\qquad
L_a(s)=\sum_{r\mid a}\log r\,A_s(r),
\]

where the products and sums run over prime divisors and `a` is squarefree.
The arithmetic coefficient of the marked logarithmic term is
`1_(a|n, n squarefree)*(log(n)-log(a))`. Lean proves its actual convergent
Dirichlet series equals

\[
-\frac{d}{ds}\bigl(A_s(a)Q(s)\bigr)-\log a\,A_s(a)Q(s)
=-A_s(a)Q'(s)-A_s(a)Q(s)L_a(s).
\]

`markedLogResponse_eq` proves this identity before any norm. The derivative
of the mark contributes `-log(a)*A_s(a)`; the external divisor logarithm
cancels precisely that term. There is no division by `Q`, so zeros of
the numerator do not invalidate the identity or its analytic continuation.
`LSeriesHasSum_markedLogResponse`, `hasSum_head_moment` and
`hasSum_head_filter` identify the original convergent arithmetic at every
factorial order and every polynomial filter.

## Why the remainder is summable after averaging

The preceding averaged Euler bound is
`sum_(a<=U, a squarefree) |A_s(a)| <= 2*D(3/2)*sqrt(U)` on `Re(s)>=1/2`,
where `D(3/2)=sum tau(d)^2*d^(-3/2)` genuinely converges.

For a prime `r`, the exact squarefree incidence `r|a` is the coprime
dilation `a=r*m`. Thus its contribution to the logarithmic correction
contains **two copies** of `A_s(r)`:

\[
\sum_{a\le U\atop a\ {
m squarefree}} |A_s(a)|\,|L_a(s)|
\le 32\mathcal D(3/2)\sqrt U
 \sum_{n\ge1}\frac{\Lambda(n)}{n^{3/2}}.
\]

The prime-power series on the right is absolutely convergent. The proof
retains the exact coprime incidence before applying its upper bound;
it does not assume cancellation in a Möbius sum. `exists_markLog_average_bound`
records a positive constant including this full cost.

On the existing unit disc centered at `3/2+i*y`, with `abs(y)>1`, both
`Q` and `Q'` have fixed compact bounds. Cauchy estimates therefore give,
for every complex divisor-weight family satisfying `|w(a)|<=1`,

\[
\left|\sum_n\sum_{a\le U\atop a\mid n,\ n\ {
m squarefree}}
 w(a)(\log n-\log a)K_{p,N}(3/2+iy,n)\right|
\le C_y\sqrt U\sum_k|p_k|.
\]

This is `exists_head_filter_bound`. The constant is independent of the
cutoff, moment order and bounded divisor weights. It may depend on the
fixed ordinate. The displayed arithmetic equality and convergence hold
before the bound is applied.

The preceding enlarged-disc estimate with geometric moment decay remains
available. The new unit-disc bound improves the cutoff dependence; it
complements that estimate rather than dominating it for every cutoff and
order.

## All admissible pairs and finite probability mixtures

Combining the improved logarithmic term with the already controlled
coprime cross term and finite prime head proves

\[
|\text{projected small}_{U,V;p,N}|
\le C_y\sqrt{U+1}\sqrt{V+1}\sum_k|p_k|.
\]

Consequently the complete nonsquarefree response and original finite-band
contribution independently vanish whenever
`u^(N+1)*sqrt(U_N+1)*sqrt(V_N+1) -> 0`, for `0<u<1`.
No equal-cutoff restriction remains.

At each order, take **any finite probability distribution** `w_(N,i)`
on cutoff pairs, with nonnegative weights summing to one. Its entire
source is retained whenever the explicit average budget tends to zero:

\[
u^{N+1}\sum_i w_{N,i}\sqrt{U_{N,i}+1}\sqrt{V_{N,i}+1}\longrightarrow0.
\]

`tendsto_actual_mixture_band_of_budget` proves the original conditional
limit `-m_rho` for this mixture on the complete original squarefree band.
The number of pairs, their values and their weights may all change with
the order. The finite-band majorant stays uniform because the weights
are nonnegative and have unit total mass.

There is a concrete sufficient region with every premise discharged:

\[
D_N=\left\lfloor\frac{u^{-N}}{N+1}\right\rfloor,\qquad
(U_{N,i}+1)(V_{N,i}+1)\le(D_N+1)^2.
\]

`tendsto_actual_hyperbolic_mixture_band` covers every such moving finite
probability mixture. It does not select a preferred coefficient family.
The symmetric cutoff is unchanged; the theorem also permits asymmetric
allocations throughout this product region.

## What remains

The independent cofinal signed lower bound for the surviving source is
still open. These estimates pay reduction errors; they do not bound that
remaining signed band, improve the zero-free region or prove RH. No
historical novelty is claimed for the Euler, divisor or Cauchy tools.

The [exact logarithmic average](zeta-vaughan-log-average.md) is now proved
in the subsequent modules, including its measurable floor-cell partition,
normalization and prime correction. It gives a composite-restricted Riesz
band with the original source and a fully paid average budget. Exact
Möbius reflection explains opposite signs within its profile; the
independent signed lower bound is still open.

| Compiled theorem | Role |
|---|---|
| `markedLogResponse_eq` | Exact physical-minus-divisor logarithmic cancellation |
| `exists_markLog_average_bound` | Pay the complete double-atom prime incidence |
| `exists_head_filter_bound` | Uniform square-root bound for all bounded divisor weights |
| `exists_projected_small_budget_bound` | Pay every asymmetric cutoff pair |
| `tendsto_nonsquarefree_band_of_budget` | Independent deletion in the original finite band |
| `tendsto_actual_mixture_band_of_budget` | Preserve the source for all paid finite probability mixtures |
| `tendsto_actual_hyperbolic_mixture_band` | Discharge the budget throughout the concrete product region |

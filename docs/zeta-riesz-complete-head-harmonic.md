# Completion errors and the explicit complete-head cost

The complete negative prime head now has a checked two-sided arithmetic
estimate: its source-normalized value is an explicit negative harmonic
weight times the full zero multiplicity squared, with error tending to
zero. Both reflected completion products and both low-head completion
corrections have been paid before this reduction is used.

The terminal theorem is
[`tendsto_three_higher_taper_budget`](../RiemannGaussian/ZetaRieszCompleteHeadHarmonic.lean).
It retains the original source and names the three unpaid arithmetic
components. It does not prove their joint signed lower bound or RH.

## Exact setting and scope

Let `rho = beta + i gamma` be a hypothetical nontrivial zero, `m` its full
analytic multiplicity, and `u = 3/2 - beta`. The source transport keeps the
existing exposed-zero hypotheses and the annular interval
`1/2 <= u < exp(-2/3)`. The currently transported filter is `P = 1`.
No simplicity assumption is imposed and no parameter range is enlarged.

The literal endpoints and moments are

```math
\begin{gathered}
 D_N=\left\lfloor\frac{u^{-N}}{N+1}\right\rfloor,
 \quad X_N=(D_N+2)^2,\quad L_N=\log X_N,\quad M=N+1,\\
 A_N=\{p\text{ prime}:N^2\lt p\lt X_N\},\qquad
 K_k(s,p)=p^{-s}\frac{(\log p)^k}{k!},\qquad s=\frac32+iy,\\
 F_{N,k}=\sum_{p\in A_N}K_k(s,p),\qquad
 B_k=\sum_{p\text{ prime}}K_k(s,p).
\end{gathered}
```

The complete unlogged prime series is genuinely absolutely convergent at
this `s`. Every older squarefree, physical, cofactor, prime and central
window restriction remains in the composite responses below.

## Independent reflected completion

The original shared head/pair atom is

```math
J_k=\frac12F_{N,k}F_{N,M-k}
 -\frac{k+1}{L_N}F_{N,k+1}B_{M-k}.
```

The selected lower wing retains the actual middle orders satisfying
`M < 8k < 7M` and `32k <= 15N+64`. Its reflected image is disjoint for
`N >= 256`; the sum counts each original order once. That threshold
concerns the order partition, not the eventual phase estimates.

Writing `l=M-k`, the endpoint-tapered moment is

```math
T_l=\sum_{p\in A_N}\left(1-\frac{\log p}{L_N}\right)K_l(s,p)
    =F_{N,l}-\frac{l+1}{L_N}F_{N,l+1}.
```

The exact reflected identity retains

```math
J_k+J_l=B_kT_l-\frac{k+1}{L_N}B_{k+1}B_l
 +(F_{N,k}-B_k)F_{N,l}
 -\frac{k+1}{L_N}(F_{N,k+1}-B_{k+1})B_l.
```

[`ZetaRieszCompletionProduct`](../RiemannGaussian/ZetaRieszCompletionProduct.lean)
pays the two genuine omitted prime ranges at their full product scale.
The complementary finite or complete moment, the derivative successor and
the original normalization are included in the estimate. Summing the actual
reflected error, including its source prefactor, gives

```math
\left|u^{N+1}E_N^{\rm wing}\right|
 \le 8e^2 Z^2(N+1)^4e^{-5N/4096}\longrightarrow0,
\qquad
Z=1+\sum_{n\ge1}\exp\left(-\frac{1025}{1024}\log n\right).
```

`Z` denotes the repository's exact summable real majorant, including the
extra unit from its natural index zero. This bound is independent of any zero
hypothesis, holds on `0 < u < exp(-2/3)`, and is uniform over all heights,
including moving heights. The signed tapered core is kept separately.

## Completing the low head

The remaining low head uses the actual orders `8k <= M`. Its small-prime
correction includes orders below the linear completion range. Rather than
paying each order with a growing count, Lean proves the general estimate

```math
\sum_{k\in S}\left|k u^k
  \sum_{p\le N^2\atop p\ {m prime}}K_k(s,p)\right|
 \le 600\sqrt{N+1}\,Z
```

for every finite order set `S`, uniformly in height, on
`0 <= u < exp(-2/3)`. The original head length factor turns the relevant
allowance into a constant times `sqrt(N+1)/L_N`, which tends to zero.
The upper-prime correction has a separate geometric allowance.

[`ZetaRieszLowHeadCorrection`](../RiemannGaussian/ZetaRieszLowHeadCorrection.lean)
includes the full complementary prime leg in both estimates. Its needed
complete-leg bound is discharged by the exposed-zero phase theorem.
Consequently the actual low head minus the complete low head tends to
zero at the original source scale for every eligible moving order set.
This final product statement is source-conditioned; the prefix and
upper-prime estimates themselves are independent of a hypothetical zero.

## Central subset and complete head

Remove the two disjoint reflected wings from the original middle range.
The exact remaining order set `Omega_N` is a subset of the previously
bounded wider matched block. For its actual contribution `C_N`, Lean proves

```math
-\frac{m^2}{8}\le\operatorname{Re}(u^{N+1}C_N)\le0
```

eventually under the original exposed-zero hypotheses. The all-subsets
theorem permits this partition without adding overlapping block budgets.
The cost is not asserted to be subunit for unrestricted `m`.

The low and reflected negative complete heads combine without overlap.
Their exact order set is

```math
S_N=\left\{0,\ldots,\left\lfloor\frac{15N+64}{32}\right\rfloor\right\},
\qquad N\ge256.
```

The resulting complete head and its explicit reference weight are

```math
H_N=-\frac{M}{L_N}\sum_{k\in S_N}(k+1)B_{k+1}B_{M-k},
\qquad
h_N=\frac{M}{uL_N}\sum_{k\in S_N}\frac1{M-k}.
```

The finite harmonic weight is nonnegative. The checked arithmetic estimate is

```math
u^{N+1}H_N+m^2h_N\longrightarrow0.
```

In particular, for every `epsilon > 0`, eventually the normalized real head
lies between `-m^2 h_N - epsilon` and `-m^2 h_N + epsilon`. This removes its
prime-dependent error while retaining its negative leading cost. It does
not assert that the head itself vanishes or that the cost beats the source.

The reusable mechanism is
[`HarmonicProductContinuity`](../RiemannGaussian/HarmonicProductContinuity.lean),
which imports only Mathlib. For every complex sequence `a_j -> b` and
every moving selection with `2k <= N+1`, it proves

```math
\sum_{k\in S_N}
 \frac{a_{k+1}a_{N+1-k}-b^2}{N+1-k}\longrightarrow0.
```

Both order marginals are injective selections of one finite prefix. Their
centered norm sums are controlled by the same Cesaro average. The reference
phase `b^2` is preserved before estimating the error. The prime application
uses the checked full-array limit `k u^k B_k -> -m`; no particular numerical
coefficient family is selected. No claim of historical novelty is made.

## The three unpaid arithmetic components

Let `V_N` be the actual tapered wing
`M * sum_lowerWing B_k T_(M-k)`. Let `Q_3,N` and `Q_>=4,N` denote the
existing actual three-prime and four-or-more-prime responses, with every
previous mask and logarithmic kernel. The complete terminal source is

```math
u^{N+1}(Q_{3,N}+Q_{\ge4,N}+V_N+C_N)-m^2h_N\longrightarrow-m.
```

The remaining arithmetic task is a sufficient **joint signed lower bound**
for `Q_3,N + Q_>=4,N + V_N`, retaining their mutual correlations. The
three-prime coefficient is nonnegative but its product cosine phase is
unpaid. The higher-prime response retains its squarefree parity and Riesz
cutoff correlations. The tapered wing retains the positive endpoint weight
together with two complex prime moments; positive weights do not give
positivity of that product.

The central-block budget and explicit harmonic head cost must both be
included in any contradiction. A contradiction in this exposed annular
regime would still leave the other global source ranges and zero-coverage
obligations. This slice proves no new zero-free region or RH.

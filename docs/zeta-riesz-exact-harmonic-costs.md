# Exact head and central costs

Lean now evaluates both the entire complete prime head and the actual
central matched block. Their combined leading cost is an explicit
function of the source radius, multiplied by the full multiplicity square.
The three remaining arithmetic sums are retained together with their
exact shifted source.

The terminal theorem is
[`tendsto_three_unpaid_exact_source`](../RiemannGaussian/ZetaRieszCentralHarmonicCost.lean).
The component estimate is
[`eventually_head_central_gt_neg_multiplicity_square`](../RiemannGaussian/ZetaRieszCentralHarmonicCost.lean).
Neither proves the independent signed bound for the three remaining sums,
RH, or a new zero-free region.

## Original setting and scope

Keep a hypothetical nontrivial zero `rho = beta + i gamma`, its full
analytic multiplicity `m`, and `u = 3/2 - beta`. The whole source transport
uses `P = 1`, the existing exposed-zero hypothesis, and
`1/2 <= u < exp(-2/3)`. In particular, every other nontrivial zero is farther
from `3/2 + i gamma` than `u`. These conditions remain visible in the
compiled theorem statements. Simplicity is not assumed.

The original definitions are

```math
\begin{gathered}
D_N=\left\lfloor\frac{u^{-N}}{N+1}\right\rfloor,\qquad
X_N=(D_N+2)^2,\qquad L_N=\log X_N,\qquad M=N+1,\\
A_N=\{p\text{ prime}:N^2\lt p\lt X_N\},\qquad
B_k=\sum_{p\text{ prime}}p^{-3/2-i\gamma}\frac{(\log p)^k}{k!}.
\end{gathered}
```

The complete unlogged prime moments genuinely converge. Every squarefree,
physical, cofactor, prime and central-window mask of the composite responses
is unchanged. The exposed-zero phase estimates concern the fixed height
`gamma`, uniformly over the stated order selection after one common,
unevaluated threshold.

## Exact integer intervals and length

Let `K_N = floor((15N+64)/32)` and `B_N = N-K_N`, using the latter symbol
only for the integer endpoint in this paragraph. For `N >= 256`, Lean proves
that the complete head uses exactly `0 <= k <= K_N`, and the central block
uses exactly `K_N+1 <= k <= B_N`. The central set is invariant under
`k -> M-k`. The value `256` is a structural partition threshold, not a phase
or zero-height threshold.

[`ZetaRieszLengthAsymptotic`](../RiemannGaussian/ZetaRieszLengthAsymptotic.lean)
keeps the actual floor and logarithmic damping to prove, independently of
hypothetical zeros, for `0 < u <= 3/5`,

```math
\frac{L_N}{M}\longrightarrow-2\log u,
\qquad
\frac{M}{uL_N}\longrightarrow\frac1{-2u\log u}.
```

[`HarmonicIntervalLimit`](../RiemannGaussian/HarmonicIntervalLimit.lean)
imports only Mathlib. For any two diverging integer endpoints whose ratio
tends to a nonzero constant `r`, their harmonic-number difference tends to
`log r`. Applying this general theorem to the actual endpoints gives

```math
\sum_{k=0}^{K_N}\frac1{M-k}\longrightarrow\log\frac{32}{17},
\qquad
\sum_{k=K_N+1}^{B_N}\frac1k\longrightarrow\log\frac{17}{15}.
```

## Evaluating the prime-dependent components

Write `H_N` for the entire negative complete head and `C_N` for the actual
central matched block. The previous
[completion and head slice](zeta-riesz-complete-head-harmonic.md)
already paid both reflected completion products and both low-head errors.
The new complete-head result also works on the larger component range
`u <= 3/5`, under the same exposed-zero hypotheses. This does not enlarge
the range of the whole source theorem.

For the central block, both weighted products converge uniformly to `m^2`
over its actual order interval. This includes the finite/finite product
and the derivative-successor/complete product. The convergence threshold is
common to every central order, at arbitrary precision.

[`FiniteWeightedUniformConvergence`](../RiemannGaussian/FiniteWeightedUniformConvergence.lean)
imports only Mathlib. Its general theorem transports uniformly small
errors through any moving complex weights with bounded total variation.
For nonnegative weights with convergent total mass, it retains the exact
limiting reference phase. Applied here, it bounds the centered error and
keeps the leading signed products. Reflection then combines the pair's two
reciprocal marginals without losing its factor one half.

With `d(u)=-2u log u`, Lean proves

```math
\begin{aligned}
u^{N+1}H_N&\longrightarrow-m^2\frac{\log(32/17)}{d(u)},\\
u^{N+1}C_N&\longrightarrow m^2\log(17/15)\left(1-\frac1{d(u)}\right),\\
u^{N+1}(H_N+C_N)&\longrightarrow-m^2c(u),\\
c(u)&=\frac{\log(32/15)}{d(u)}-\log(17/15)\lt1.
\end{aligned}
```

The strict scalar inequality holds throughout the original annulus and is
proved independently of hypothetical zeros in
[`RieszHarmonicCostBounds`](../RiemannGaussian/RieszHarmonicCostBounds.lean).
Consequently the actual normalized real head plus central block is
eventually greater than `-m^2`. Their prime-dependent errors are controlled;
their leading cost does not vanish.

The source is `-m`, whereas this cost is quadratic in `m`. For a simple
zero, `c(u)<1` puts the two paid components strictly below the unit source
magnitude. For unrestricted multiplicity, it does not establish
`m^2 c(u)<m`. No simplicity premise is silently inserted.

## Exactly three unpaid arithmetic components

The remaining terms are:

| Component | Content retained | Required further control |
| --- | --- | --- |
| `T3` | The actual masked squarefree three-prime response, with its full product phase | Its contribution to the joint signed bound |
| `T>=4` | The actual masked response with at least four distinct prime factors | Its contribution to the same joint bound |
| `V` | The complete lower prime leg coupled to the endpoint-tapered finite high leg | Its correlations with both prime-factor sums |

The exact tapered wing is

```math
V_N=M\sum_{k\in\mathrm{lowerWing}_N}B_k
 \sum_{p\in A_N}\left(1-\frac{\log p}{L_N}\right)
 p^{-3/2-i\gamma}\frac{(\log p)^{M-k}}{(M-k)!}.
```

After the two evaluated components are removed, the full source theorem is

```math
u^{N+1}\bigl(T3_N+T{\geq}4_N+V_N\bigr)
 \longrightarrow -m+m^2c(u).
```

This is a source-conditioned identity, not an independent signed bound.
A cofinal lower bound beating this limiting real value by a fixed positive
margin would contradict these exposed-zero assumptions in this range.
For a simple zero, a nonnegative asymptotic lower bound would suffice;
that bound has not been proved. The general joint arithmetic bound and
coverage of the other global source ranges remain open.

The supporting explorer endpoint is `exact-harmonic-costs`. Its graph,
source lines and transitive axiom reports are exported from Lean. The
default whole-carrier endpoint, proved zero-free region, numerical
certificate and both top-ten README lists are unchanged. These reusable
continuity and harmonic arguments are not claimed as historically novel.

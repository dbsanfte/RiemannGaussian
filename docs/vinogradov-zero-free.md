# A complete Vinogradov–Korobov zero-free family

[`ZetaVinogradovSummedZeroFree.exists_eventual_strip`](../RiemannGaussian/ZetaVinogradovSummedZeroFree.lean)
proves an unconditional region for the actual zeta zeros. Write

```math
L(t)=\log(|t|+2),\qquad
w_C(t)=\frac{C}{L(t)^{2/3}(\log L(t))^{1/3}},\qquad
0<C<\frac{3\pi}{10640}.
```

For each such `C` there is a finite `T(C)>=4` such that every nontrivial
zero `rho=beta+it` with `|t|>=T(C)` satisfies
`w_C(t)<beta<1-w_C(t)`. `exists_eventual_nonvanishing` proves literal zeta
nonvanishing on the closed right edge. **The starting height has not been
numerically evaluated.** There are no assumed moment, growth, zero-free-disc
or arithmetic estimates. Actual multiplicities are retained.

`rational_coefficient_lt` proves that `C=1/1150` is admissible.
`coefficient_gain` proves that the coefficient ceiling is exactly `20/19`
times the preceding cubic-profile ceiling. `previous_limit_lt_rational` proves that
the new rational member already exceeds the whole preceding cubic-profile coefficient
interval. These are eventual component comparisons, not an enlargement of
the full pointwise union at every finite height. The family remains weaker
than the published sharp VK constants; no world-record or historical novelty
claim is made.

## What is paid in the proof

The [shorter actual moments](vinogradov-narrow-packet.md) have orders
`(3k+1)k` and `(4k+1)k`, defects `k^2/40` and `k^2/100`, and complete
coefficient `(2^41*k^6)^(k^3)`. Both moment coefficients and the full
variable-order Gaussian factor fit the actual root with multiplier two.
The original Dirichlet block has bound `5*M^(4-epsilon_k)`, where
`epsilon_k=1/(512*k^2)` for `k>=48` and `1/(1600*k^2)` for `12<=k<48`.
The complete range and damping boundary are retained.

The [complete near-one growth theorem](vinogradov-near-one-growth.md) has
`Delta_n=1/(4096*(2*n+1)^2)`, `a_n=40*Delta_n^(3/2)`, and
`T_m=(16*(2*m+1)^2)^(2*m)`. For `n>=48`, its actual zeta bound is
`1048576*|t|^a_n*log(|t|)^(2/3)` on the closed strip from `1-Delta_n` to `3/2`,
above `T_(8n)`. The [retained cubic block profile](vinogradov-cubic-profile.md)
reduces the exponent to less than `5/32` of its predecessor at the same
displacement. The larger starting height is explicit and is paid on the
joint schedule. Every dyadic scale and the lower-degree range retain a cubic decay reserve.
The [complete Gaussian comparison](vinogradov-cubic-summation.md) sums the
decaying block bounds, reducing the logarithmic exponent to `2/3`.

| Step | Checked result |
| --- | --- |
| [Exponential defect](../RiemannGaussian/VinogradovExponentialDefect.lean) | The literal moment defect is at most `(k^2/2)*exp(-n/k)`. |
| [Actual shorter moments](../RiemannGaussian/VinogradovShortMoment.lean) | Complete coefficients hold at every positive endpoint, with both original moments paid. |
| [Original Dirichlet blocks](../RiemannGaussian/VinogradovShortDirichlet.lean) | Stronger saving survives Taylor approximation, averaging, the boundary and literal zeta damping. |
| [Retained cubic profile](../RiemannGaussian/VinogradovCubicSaving.lean) | The actual degree retains `delta*v-v^3/10368` at `v=log(X)/log(t)`. |
| [All-scale decay](../RiemannGaussian/VinogradovCubicDecay.lean) | Every small, middle and long block retains the same cubic reserve above `T_(8n)`. |
| [Complete scale summation](../RiemannGaussian/VinogradovCubicSummation.lean) | The full dyadic cubic tail is at most `1024*L^(2/3)`. |
| [Full local disc](../RiemannGaussian/ZetaVinogradovSummedDisc.lean) | Actual zeta growth covers the whole radius-`Delta_n` disc at `1+x+it`, for `0<x<=Delta_n/4`, above `T_(8n)+1`. |
| [Signed angular detector](../RiemannGaussian/ZetaAngularDiscBudget.lean) | The boundary moment costs `2*allowance/(pi*Delta_n)`; the exact divisor, multiplicities and radial correction survive. |
| [Coefficient-aware degree](../RiemannGaussian/VinogradovCubicSchedule.lean) | `n=floor((L/log L)^(1/3)/64)` pays the enlarged `T_(8n)` with natural rounding. |
| [Actual moving scale](../RiemannGaussian/ZetaVinogradovCubicScale.lean) | Both heights use the same degree; the proposed width is negligible against the analytic radius. |
| [Complete actual cost](../RiemannGaussian/ZetaVinogradovSummedCost.lean) | Both analytic-disc hypotheses are discharged, and the complete cost tends to `10640*C/(3*pi)`. |

More precisely, put `ell=log L(t)`, `d=w_C(t)`, and `x=6*d`. Define

```math
\begin{aligned}
P_n(t)&=\log1048576+a_nL(t)+\frac23\log L(t),\\
A_n(x,t)&=P_n(t)+\log(1+1/x),\\
B_n(x,t)&=1344\log22+
  \frac{8A_n(x,t)+2A_n(x,2t)}{\pi\Delta_n}.
\end{aligned}
```

For a genuine zero, `d>0`, `d<Delta_n/28`, and

```math
14dB_n(6d,t)+392d^2/\Delta_n^2<1
```

imply `d<1-Re(rho)`. The generic detector states its analytic hypotheses
explicitly; `ZetaVinogradovSummedCost.margin_of_budget` discharges them
using actual zeta growth. The eventual endpoint discharges the complete
cost inequality as well. A proved analyticity disc is used, with no assumed
zero-free disc.

The checked moving-degree limits are

```math
\begin{gathered}
\Delta_n(L/\ell)^{2/3}\longrightarrow1/4,\qquad
 a_nL/\ell\longrightarrow5,\\
P_n(t)/\ell\longrightarrow17/3,\quad
P_n(2t)/\ell\longrightarrow17/3,\quad
\log(1+1/(6d))/\ell\longrightarrow2/3,\\
 d\ell/\Delta_n\longrightarrow4C,\qquad
 d/\Delta_n\longrightarrow0,\\
14dB_n(6d,t)+392d^2/\Delta_n^2
 \longrightarrow\frac{10640C}{3\pi}.
\end{gathered}
```

The full reciprocal-zeta center allowance is leading order and is paid.
The doubled height does not require a factor-two leading majorant.
The enlarged threshold, rounding and unit disc buffer are checked on the same
schedule; no fixed-degree limit is substituted at a growing degree.

## Union, comparison and remaining work

`exists_eventual_union` and `exists_eventual_union_nonvanishing` retain
the maximum of the new width, the older fixed VK width, the
[complete explicit region](zeta-unified-zero-free.md), and each admissible
[earlier log-log component](zeta-log-log-zero-free.md). The explicit
component remains valid at every height. Eventual components keep their
finite, unevaluated thresholds.

For `C>=1/1150`, `exists_eventual_union_compact` absorbs the older fixed
VK component and proves the three-component README formula. The common
width's `ZetaVinogradovAngularZeroFree.eventually_dominates_previous_loglog`
proves that every positive member eventually exceeds each fixed positive
ordinary-logarithm coefficient; its crossover is unevaluated. The stronger
coefficient interval contains the entire preceding cubic-profile interval, so all
its members remain proved.

The [first complete VK proof](../RiemannGaussian/ZetaVinogradovZeroFree.lean),
[earlier signed family](../RiemannGaussian/ZetaVinogradovAngularZeroFree.lean)
and [shorter-moment family](../RiemannGaussian/ZetaVinogradovSharperZeroFree.lean)
remain intact. The last has ceiling `3*pi/38080`; the first is retained
in the full union even for arbitrarily small new `C`.

The [complete scale summation](vinogradov-cubic-summation.md) now pays the
classical logarithmic exponent. The [preceding cubic-profile family](../RiemannGaussian/ZetaVinogradovCubicZeroFree.lean),
with ceiling `3*pi/11200`, remains proved. Further quantitative work is required. The published route uses stronger incomplete-system
moments on smooth support and shorter-block bounds, as well as a sharper
zero detector: see [Bellotti, pinned v1, Theorems 1.1–1.5 and Sections 2–4](https://arxiv.org/html/2306.10680v1).
In particular, completing the classical logarithmic shape does not import
those estimates. Published benchmark constants and numerical starting-height
evaluation remain open; consult the [audited frontier](zero-free-literature-frontier.md).
The graph continues to show only explicit-height coverage, with no
invented starting point for an eventual curve.

The independent fixed-height Riesz signed floor and harmonic Type-II
estimate remain open. This growing-height zero-free theorem does not
discharge either premise. RH remains open.

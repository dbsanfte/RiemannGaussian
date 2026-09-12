# Complete near-one line bounds for zeta

[ZetaNearOneLineBound.bound_abs](../RiemannGaussian/ZetaNearOneLineBound.lean)
proves the following bound for the actual Riemann zeta function:

\[
\boxed{
|\zeta(\sigma_k+it)|\le
\frac{32768}{1-\sigma_k}\,|t|^{\alpha_k}\log|t|,
\qquad k\ge1,\quad |t|\ge2,
}
\]

where

\[
\alpha_k=\frac1{2^{k+2}-2},\qquad
\delta_k=(k+2)\alpha_k,\qquad \sigma_k=1-\delta_k.
\]

There is no remaining finite-budget, order-selection or tail hypothesis.
The exponent is the classical higher-derivative exponent. The coefficient
is deliberately coarse; the eta division cost `1/delta_k` is explicit.
This line estimate is now an input to the
[proved arbitrary-coefficient logarithmic region](zeta-arbitrary-log-zero-free.md).
The downstream argument also discharges the local signed zero detector
and prime phase budget. RH remains open.

## Exact comparison of every pair of derivative orders

Write `p_k=2^(-k)` and `theta_k=1/(k+p_k)`. The preceding
[complete finite bound](zeta-dyadic-power-bound.md) controls a dyadic
block of scale `X` by the profile

\[
P_r(\sigma_k,t,X)=
256t^{\alpha_r}X^{\delta_k-\delta_r}
+64t^{-\alpha_r}X^{\delta_k-p_r+\delta_r}.
\]

[DerivativeOrderComparison](../RiemannGaussian/DerivativeOrderComparison.lean)
proves that both `delta` and `theta` decrease, and proves the exact secant
identity

\[
\alpha_r-\alpha_{r+1}
=\theta_{r+1}(\delta_r-\delta_{r+1}).
\]

Telescoping this identity gives, for **every** `r <= k`,

\[
\alpha_r+\theta_{r+1}(\delta_k-\delta_r)\le\alpha_k.
\]

The first block exponent is nonpositive. The second is nonnegative,
because `p_r <= delta_r` and `delta_k > 0`. Consequently the lower endpoint
of the interval controls the first term and the upper endpoint controls
the second. The latter also has the exact balance

\[
-\alpha_r+\theta_r(\delta_k-p_r+\delta_r)
=\alpha_r+\theta_r(\delta_k-\delta_r).
\]

Thus

\[
t^{\theta_{r+1}}\le X\le t^{\theta_r}
\quad\Longrightarrow\quad
P_r(\sigma_k,t,X)\le320t^{\alpha_k}.
\]

[DirichletTransitionWindows.profile_le_on_window](../RiemannGaussian/DirichletTransitionWindows.lean)
proves this for the complete profile. The same module proves coverage:
the initial interval `X <= t^theta_k` and these successive windows cover
all positive scales `X <= t`. Both profile terms remain present until
their endpoint comparisons are applied.

## Closing the last blocks and the actual zeta estimate

For `t <= X <= 4t`, the second-derivative profile suffices because
`sigma_k >= 1/2`. Its two height exponents are bounded by `alpha_k`,
and `4^delta_k <= 4`. This gives

\[
P_0(\sigma_k,t,X)\le512t^{\alpha_k}.
\]

[DirichletFullRange.exists_order_bound](../RiemannGaussian/DirichletFullRange.lean)
therefore supplies a proved derivative order `r <= k` at every positive
scale `X <= 4t`.

At the canonical eta depth `J`, the exact cutoff and tail results give

\[
2^J<\|\sigma_k+it\|+2\le t+3\le4t,
\qquad J+1\le8\log t.
\]

Every block in the full prefix `B_(J+1)` is covered. The theorem
[ZetaNearOneLineBudget.exists_prefix_budget_bound](../RiemannGaussian/ZetaNearOneLineBudget.lean)
constructs suitable orders and proves

\[
B_{J+1}\le512(J+1)t^{\alpha_k}.
\]

The already proved eta reconstruction supplies
`|zeta(s)| <= 6*(B_(J+1)+1)/(1-sigma_k)`. Since `t^alpha_k >= 1` and
`J+1 >= 1`, the numerator is at most
`6*513*8*t^alpha_k*log(t)`. The constant `32768` dominates this exact
coefficient. Conjugation covers negative heights. All constants are
uniform in `k` and `|t| >= 2`, with the displayed displacement factor
retained.

The exact complex eta multiplier, signed endpoint and adjacent-ratio
tail remain in
[ZetaDyadicTruncation](../RiemannGaussian/ZetaDyadicTruncation.lean).
The final norm bound is a downstream consequence of that richer identity.

## Entry points

The theorem names have the namespace of the linked module.

| Module | Main theorem | Role |
| --- | --- | --- |
| [DerivativeOrderComparison](../RiemannGaussian/DerivativeOrderComparison.lean) | `adjacent_identity`, `order_comparison` | Exact secants and every-order comparison. |
| [DirichletTransitionWindows](../RiemannGaussian/DirichletTransitionWindows.lean) | `profile_le_on_window`, `exists_order_bound` | Complete profiles throughout every scale below the height. |
| [DirichletFullRange](../RiemannGaussian/DirichletFullRange.lean) | `profile_le_above_height`, `exists_order_bound` | All remaining scales through four times the height. |
| [ZetaNearOneLineBudget](../RiemannGaussian/ZetaNearOneLineBudget.lean) | `canonical_count_le`, `exists_prefix_budget_bound` | Discharged order selection and full logarithmic budget. |
| [ZetaNearOneLineBound](../RiemannGaussian/ZetaNearOneLineBound.lean) | `bound`, `bound_abs`, `bound_displacement` | Actual zeta estimate at both signs of height. |

## Next step and literature scope

The block-order strategy follows the classical method described in
[Yang, JMAA 2024, Section 3](https://arxiv.org/html/2301.03165v2#S3).
Our formalization uses the repository's eta truncation and coarser
constants. It does not reproduce Yang's optimized numerical coefficient
or his zero-free-region constant, and makes no historical novelty claim.

The [vertical logarithmic package](zeta-sech-vertical-bound.md) now proves
an all-height positive-log profile, the complete weighted positive
integral, and genuinely integrable finite signed windows with their
negative mass retained. The signed limiting zero detector and its local
zero terms remain on that contour route. The
[Gaussian local-disc route](zeta-gaussian-local-jensen.md) now propagates
the line bound across a strip and controls the complete local Jensen
divisor with an explicit Euler center cost. Its
[complete signed logarithmic-derivative argument](zeta-arbitrary-log-zero-free.md)
now proves eventual zero-free width `A/log(abs(t))` for each fixed `A>0`.
It chooses the order after the coefficient, then takes the height limit.
The [joint-order extension](zeta-log-log-zero-free.md) now controls the
explicit `1/delta_k` cost, every logarithmic factor and the moving Euler
center. It proves a specified log-log region and transports it to the
original arithmetic response. Fixed-order eventual statements alone do
not supply this rate; the additional uniform estimates are essential.

Published stronger regions and the paired-zero Fermi smoothing route
are recorded in that transport document. These remain external research
targets until their antecedents are discharged in Lean. Their shrinking
edge widths do not alone reach every fixed point of the remaining
interior strip. The independent signed ordinary-prime estimate in the
fixed-ordinate, growing-moment contradiction remains open.

## Validation

All five modules pass strict direct Lean elaboration and the focused
build. The full warning-as-error build passes all 10,234 jobs. Whole-project
declaration lint and verbose lint of all five new modules pass. All 27
public theorems use only `propext`, `Classical.choice` and `Quot.sound`.

The generated inventory contains 1,387 project modules, 29,895 declarations
and 26,191 theorems including generated declarations, with no project
axioms or placeholder-dependent declarations. The source scan covers all
1,530 Lean files. All 581 checked local Markdown links resolve; source
whitespace and the README regime pass. A second strict generator run
leaves both JSON and SVG byte-identical. These are local checks; work
remains uncommitted under the user's hold.

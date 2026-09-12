# A closed Dirichlet power bound uniform in derivative order

The finite derivative recurrence now has a proved analytic cutoff and a
closed two-term bound with coefficient **32 at every order**. For the
actual logarithmic derivatives, the remaining amplitude factor is at most
four. The terminal theorem bounds the original complex Dirichlet terms
with their full real damping; it has no unproved cancellation premise.

This discharges the quantitative target in the
[all-order recurrence](all-order-dirichlet-recursion.md). The
[complete zeta line estimate](zeta-near-one-line-bound.md) now controls
all dyadic ranges and the infinite eta tail, uniformly in order and
height. Zero detection remains before a stronger region can enter the
[arithmetic transport](zero-free-region-transport.md).
The displayed zero-free region is unchanged, and RH remains open.

## The actual finite theorem

For every natural `k`, set

\[
\alpha_k=\frac1{2^{k+2}-2},\qquad
p_k=2^{-k},\qquad \beta_k=1-2^{-k}.
\]

Let `s = sigma + i*t`, where `sigma >= 0` and `t > 0`. Let `X > 0`,
and let `a,N` be natural numbers satisfying `a >= X` and `a+N <= 2X`.
Put

\[
\ell_k=\frac{t(k+1)!}{(2X)^{k+2}}.
\]

[UniformDirichletPowerBound.uniform_bound](../RiemannGaussian/UniformDirichletPowerBound.lean)
proves

\[
\boxed{
\left|\sum_{n<N}(a+n)^{-s}\right|
\le 32a^{-\sigma}
\left(4N\ell_k^{\alpha_k}
+N^{\beta_k}\ell_k^{-\alpha_k}\right).
}
\]

The constants are independent of the derivative order, height, block and
scale. Every factorial, derivative sign and dyadic ratio is discharged
for these actual terms. No resonance avoidance, upper bound on height,
or restriction to small derivative scales is assumed. The estimate
also includes `N = 0`; its envelope need not be sharp in that case.

In Lean the summands are literally `zetaPrimeFeature s (a+n)`, and the
damping is `zetaPrimeExpWeight s.re a = exp(-sigma*log(a))`. The conditions
imply `a > 0`, so the displayed complex powers are unambiguous. The
stronger intermediate `feature_bound` retains the exact dyadic ratio
factor instead of replacing it by four.

## The general derivative theorem

[UniformDerivativePowerBound.phase_bound](../RiemannGaussian/UniformDerivativePowerBound.lean)
applies to a real phase with a genuine derivative family through order
`k+2` on the original closed interval `[a,a+N]`. If

\[
F_r'=F_{r+1}\quad(r<k+2),\qquad
0<\ell\le F_{k+2}(x)\le A\ell,\quad A\ge1,
\]

then for every common cap `L >= N`,

\[
\left|\sum_{n<N}e^{iF_0(a+n)}\right|
\le32\left(A^{p_k}L\ell^{\alpha_k}
+L^{\beta_k}\ell^{-\alpha_k}\right).
\]

There is no monotonicity hypothesis on the highest derivative. The
coefficient is uniform even when the top derivative order changes:

| Derivative order | `alpha_k` | `p_k` | `beta_k` |
| --- | --- | --- | --- |
| 2 | `1/2` | `1` | `0` |
| 3 | `1/6` | `1/2` | `1/2` |
| 4 | `1/14` | `1/4` | `3/4` |

This is a classical derivative test with a coarse explicit constant.
It does not claim historical novelty or the sharper constants in
[Yang's higher-derivative argument](https://arxiv.org/html/2301.03165v2#S2).

## Why the constants stay bounded

The exact exponent identities include

\[
\alpha_{k+1}=\frac{\alpha_k}{2+2\alpha_k},\qquad
\alpha_k(1-2\alpha_{k+1})=2\alpha_{k+1},\qquad
p_{k+1}=p_k/2,\qquad \beta_{k+1}=(\beta_k+1)/2.
\]

Use the single analytic shift rule

\[
u=\ell^{-2\alpha_{k+1}},\qquad H=\lceil u\rceil.
\]

This is an exact mathematical rule for every order and scale. When
`0 < ell <= 1`, Lean proves `1 <= u <= H <= 2u`. The identities

\[
(u\ell)^{\alpha_k}=\ell^{2\alpha_{k+1}},\qquad
(u\ell)^{-\alpha_k}=u
\]

balance both terms of the successor estimate. Rounding costs at most a
factor of two in the positive power and nothing in the negative power.

The full triangular lag sum is bounded using

\[
\sum_{j<H}(H-j-1)(j+1)^{\alpha_k}
\le H^2H^{\alpha_k},
\]

\[
\sum_{j<H}(H-j-1)(j+1)^{-\alpha_k}
\le 2H^2H^{-\alpha_k}.
\]

The negative power sum is controlled by its integral, using
`0 < alpha_k <= 1/2`. Every lag retains its own derivative scale until
these finite sum estimates are applied. No maximum replaces the entire
lag family.

Write the successor's leading and complementary terms as

\[
M=A^{p_{k+1}}L\ell^{\alpha_{k+1}},\qquad
E=L^{\beta_{k+1}}\ell^{-\alpha_{k+1}}.
\]

When `H <= L`, the complete radicand in the proved recurrence is at most

\[
258M^2+256E^2\le[32(M+E)]^2.
\]

The square-root base also satisfies the coefficient 32. Induction
therefore keeps that same coefficient at every order.

The remaining cases are proved explicitly. If `ell >= 1`, the leading
term covers the trivial length bound. If `H > L`, the ceiling property
gives `L < u`, and the complementary term covers the length. The empty
cap has its own proof. There is no omitted short-interval or large-scale
regime.

For the actual logarithmic family the upper/lower derivative ratio is
`A_k = 2^(k+2)`. Lean proves

\[
A_k^{p_k}\le4
\]

for every `k`. Exact conjugation handles the original derivative sign;
the common cap controls all prefixes, so the exact Abel identity carries
the full decreasing real damping with initial cost `a^(-sigma)`.

## Compiled entry points

Names in the second column have the namespace of their linked module.

| Module | Main theorems | Purpose |
| --- | --- | --- |
| [FiniteLagPowerBounds](../RiemannGaussian/FiniteLagPowerBounds.lean) | `negative_sum_integral`, `weighted_positive`, `weighted_negative` | Complete positive and negative finite power sums. |
| [DerivativePowerExponents](../RiemannGaussian/DerivativePowerExponents.lean) | `alpha_succ`, `alpha_balance`, `amp_succ`, `beta_succ` | Exact exponent recurrences and their domains. |
| [AnalyticDerivativeCutoff](../RiemannGaussian/AnalyticDerivativeCutoff.lean) | `count_eq`, `count_le_twice`, `length_lt_ideal`, `count_positive_power`, `count_negative_power` | Exact analytic shift, integer rounding and long-shift branch. |
| [DerivativePowerEnvelope](../RiemannGaussian/DerivativePowerEnvelope.lean) | `main_square`, `error_square`, `main_ge_length`, `error_ge_length`, `base_bound` | Exact successor squares, trivial fallbacks and uniform base. |
| [DerivativePowerStep](../RiemannGaussian/DerivativePowerStep.lean) | `weighted_budget_le`, `argument_le_squares`, `successor_bound` | Complete lag sum and order-independent successor estimate. |
| [UniformDerivativePowerBound](../RiemannGaussian/UniformDerivativePowerBound.lean) | `budget_bound`, `phase_bound` | Closed recurrence and actual generic phase estimate. |
| [UniformDirichletPowerBound](../RiemannGaussian/UniformDirichletPowerBound.lean) | `ratio_amp_le_four`, `feature_bound`, `uniform_bound` | Full literal Dirichlet estimate with uniform constants. |

## Remaining work toward a larger region

The [complete zeta line estimate](zeta-near-one-line-bound.md) is now
proved on every near-one line

\[
\sigma_k=1-(k+2)\alpha_k.
\]

The leading block term balances the real damping. The complementary
term gives the proved transition `t^(1/(k+2^(-k)))`. The actual eta tail
is controlled at an automatic logarithmic depth, with every finite block
and endpoint retained. Exact order comparisons now cover the larger
blocks and discharge the full finite budget. The resulting bound is
uniform for every order and absolute height at least two, with the
explicit eta division cost `1/(1-sigma_k)` retained.

The [vertical logarithmic package](zeta-sech-vertical-bound.md) now
controls the complete positive integral and every finite signed window,
retaining negative logarithmic mass. The full signed limiting detector
and its local zero terms remain. A resulting region of width `c*loglog(t)/log(t)`
with any fixed positive `c` would eventually improve the current
`24/(125*log(t))` width. The line estimate is proved; that larger region
is not yet claimed.

The finite terms have ordinary Dirichlet coefficients equal to one.
Prime indicators, sieves and moment weights need their own variation or
correlation estimates. In particular, this high-height bound does not
prove the independent signed prime inequality in the fixed-ordinate,
growing-moment RH contradiction.

## Validation

All seven modules pass strict direct Lean elaboration and the focused
build. The full warning-as-error build passes all 10,234 jobs. Whole-project
declaration lint and verbose lint of every new module pass. All 48 public
theorems use only `propext`, `Classical.choice` and `Quot.sound`.

The generated inventory contains 1,387 project modules, 29,895 declarations
and 26,191 theorems including generated declarations, with no project
axioms or placeholder-dependent declarations. The source scan covers all
1,530 Lean files. All 581 checked local Markdown links resolve; source
whitespace and the README regime pass. A second strict generator run
leaves both JSON and SVG byte-identical. These are local checks; work
remains uncommitted under the user's hold.

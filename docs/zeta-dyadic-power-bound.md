# Complete finite power bounds for zeta and the small-block range

The all-order Dirichlet estimates now reach the **actual zeta function**.
Lean proves a complete bound consisting only of real powers and a finite
sum of block costs. Every derivative-order selection is allowed, all
dyadic blocks and the final endpoint are included, and the existing
adjacent-ratio eta theorem controls the entire infinite tail. A canonical
logarithmic cutoff discharges the tail's scale condition.

The complete small-block prefix is controlled through the exact transition
on every balanced near-one line. The subsequent
[full line theorem](zeta-near-one-line-bound.md) now proves the remaining
order comparisons, covers every larger block and removes the entire finite
budget. The zero detector remains. The displayed zero-free region is
unchanged, and RH remains open.

## The complete bound for the actual zeta function

Let `s = sigma + i*t`, with `0 < sigma < 1` and `t > 0`. As in the
[uniform derivative estimate](uniform-dirichlet-power-bound.md), write

\[
\alpha_k=\frac1{2^{k+2}-2},\qquad
p_k=2^{-k},\qquad \beta_k=1-p_k.
\]

Define the explicit profile

\[
P_k(\sigma,t,X)=
256t^{\alpha_k}X^{1-\sigma-(k+2)\alpha_k}
+64t^{-\alpha_k}X^{\beta_k-\sigma+(k+2)\alpha_k}.
\]

For any function `r : Nat -> Nat` selecting a derivative order on each
dyadic block, put

\[
E_j=\min\{2^{j(1-\sigma)},\,P_{r(j)}(\sigma,t,2^j)\},
\qquad B_J=\sum_{j<J}E_j.
\]

These are explicit real expressions, with no unknown phase sums or zeta
values in their definitions. The first entry in the minimum preserves the
trivial bound with the full damping. The second pays for the actual
derivatives at the selected order.

Choose the canonical depth

\[
J=\left\lfloor\log_2\bigl(\lceil\lVert s\rVert\rceil+1\bigr)\right\rfloor.
\]

[ZetaDyadicPowerBound.canonical_bound](../RiemannGaussian/ZetaDyadicPowerBound.lean)
proves

\[
\boxed{
|\zeta(s)|\le
\frac{B_{J+1}+2^{1-\sigma}B_J
+(2^{J+1})^{-\sigma}+2(2^{J+1}+1)^{-\sigma}}
{2^{1-\sigma}-1}.
}
\]

The denominator is proved strictly positive throughout this open strip.
The same file's `simple_bound` proves the coarser form

\[
\boxed{\quad
|\zeta(s)|\le\frac{6(B_{J+1}+1)}{1-\sigma}.
\quad}
\]

Both theorems hold for **every** order selection. Orders can depend on the
argument and block scale; no numerical coefficient search or successful
choice is assumed. `zeta_bound` also allows any depth satisfying the
literal tail condition, rather than forcing the canonical one.

## Exact reconstruction and the tail

Write the original complete block and prefix as

\[
C_j(s)=\sum_{n<2^j}(2^j+n)^{-s},\qquad
S_J(s)=\sum_{1\le n<2^J}n^{-s}.
\]

[DirichletDyadicBlocks.prefix_pow_two](../RiemannGaussian/DirichletDyadicBlocks.lean)
proves exactly `S_J = sum_(j<J) C_j`. At the paired eta cutoff `N=2^J`,
the same module proves

\[
\eta_N(s)=S_{J+1}(s)-2\,2^{-s}S_J(s)-(2^{J+1})^{-s}.
\]

The last negative endpoint is essential: the half-open dyadic prefixes
stop one index before the inclusive finite eta sum. The exact complex
dyadic multiplier is retained, not replaced by its magnitude in this
identity.

Put `T_J(s)=eta(s)-eta_(2^J)(s)`. The exact reconstruction is

\[
(1-2\,2^{-s})\zeta(s)=
S_{J+1}(s)-2\,2^{-s}S_J(s)-(2^{J+1})^{-s}+T_J(s).
\]

[ZetaDyadicTruncation.reconstruction](../RiemannGaussian/ZetaDyadicTruncation.lean)
proves this throughout `Re(s)>0`, away from `s=1`. Its
`remainder_eq_adjacent` retains the full complex adjacent-ratio boundary
and the absolutely convergent signed variation remainder.

The [existing eta tail theorem](../RiemannGaussian/EtaUniformTailBound.lean)
then gives

\[
|T_J(s)|\le2(2^{J+1}+1)^{-\sigma}
\quad\text{if }\lVert s\rVert\le2^{J+1}+1.
\]

There is no additional height factor. The canonical depth satisfies this
condition and obeys the proved bounds

\[
2^J<\lVert s\rVert+2,\qquad
J\le\frac{\log(\lVert s\rVert+2)}{\log2}.
\]

The coupled finite expression is bounded before a separate downstream
theorem uses the triangle inequality on its two prefixes and endpoint.
The complete complex identity remains available for future cancellation.

## Uniform factorial costs and the transition range

The exact lower derivative scale is

\[
\ell_k=F_k\,tX^{-(k+2)},\qquad
F_k=\frac{(k+1)!}{2^{k+2}}.
\]

[DirichletPowerCoefficients](../RiemannGaussian/DirichletPowerCoefficients.lean)
proves `F_k^alpha_k <= 2` and `F_k^(-alpha_k) <= 2` at every order.
Before using these inequalities, `exactProfile` retains the exact factors
in the coefficients `128*F_k^alpha_k` and `32*F_k^(-alpha_k)`.
The coarser profile above therefore has constants independent of order,
height and block size, with no factorial hidden in an unspecified constant.

Set

\[
\sigma_k=1-(k+2)\alpha_k,\qquad
v_k=2(k+2)\alpha_k-p_k,\qquad
\theta_k=\frac1{k+p_k}.
\]

Lean proves `v_k>0`, `theta_k>0` and the exact identity
`theta_k*v_k=2*alpha_k`. On the balanced line,

\[
P_k(\sigma_k,t,X)
=256t^{\alpha_k}+64t^{-\alpha_k}X^{v_k}.
\]

Consequently `X <= t^theta_k` controls the whole complementary term, and
[DirichletCriticalRange.block_bound](../RiemannGaussian/DirichletCriticalRange.lean)
proves `|C_j(s)| <= 320*t^alpha_k` throughout that range. Its
`prefix_bound` controls the **entire original prefix**:

\[
\left|\sum_{1\le n<2^J}n^{-\sigma_k-it}\right|
\le320Jt^{\alpha_k}
\quad\text{if }2^J\le t^{\theta_k}.
\]

For `k>=1`, the balanced line lies in `[1/2,1)`. For example, at `k=2`
it is `sigma=5/7`, the height exponent is `1/14`, and the transition is
`t^(4/9)`. This controls a full initial range; it does not by itself bound
the larger blocks needed for the complete zeta estimate.

## Compiled entry points

The theorem names have the namespace of their linked module.

| Module | Main theorems | What is proved |
| --- | --- | --- |
| [DirichletDyadicBlocks](../RiemannGaussian/DirichletDyadicBlocks.lean) | `prefix_pow_two`, `eta_eq_prefix`, `eta_pow_two_eq_blocks` | Exact full complex block and eta reconstruction, including the endpoint. |
| [DirichletPowerParameters](../RiemannGaussian/DirichletPowerParameters.lean) | `half_le_line_succ`, `slope_eq`, `transition_balance` | Balanced near-one lines and the exact complementary transition. |
| [DirichletPowerCoefficients](../RiemannGaussian/DirichletPowerCoefficients.lean) | `factor_positive_power_le_two`, `factor_negative_power_le_two`, `scale_power` | Exact factorial factors and uniformly bounded costs. |
| [DirichletBlockPowerProfile](../RiemannGaussian/DirichletBlockPowerProfile.lean) | `exact_bound`, `bound` | Actual original dyadic blocks satisfy both the exact and uniform power profiles. |
| [DirichletCriticalRange](../RiemannGaussian/DirichletCriticalRange.lean) | `profile_le_on_range`, `block_bound`, `prefix_bound` | The whole small-block prefix has a common height-power estimate. |
| [ZetaDyadicTruncation](../RiemannGaussian/ZetaDyadicTruncation.lean) | `reconstruction`, `remainder_bound`, `zeta_norm_le`, `depth_scale`, `depth_le_log` | Exact zeta recovery, coupled finite estimate, complete tail and automatic logarithmic depth. |
| [ZetaDyadicPowerBound](../RiemannGaussian/ZetaDyadicPowerBound.lean) | `eta_prefix_bound`, `zeta_bound`, `canonical_bound`, `simple_bound` | The actual zeta function has a finite explicit power bound for every order selection. |

## Completed continuation and RH scope

The [complete near-one line bound](zeta-near-one-line-bound.md) now
proves the adjacent secant identity, all-order comparisons, coverage of
every transition window and the final blocks through `4t`. It bounds
this document's full budget by `512*(J+1)*t^alpha_k`, constructs the
needed orders and proves `J+1 <= 8*log(t)`. The result is an actual zeta
bound with coefficient `32768/(1-sigma_k)` for all `k >= 1`, `abs(t) >= 2`.

The exact reconstruction and arbitrary-order finite budget above remain
available. The full line theorem is a downstream specialization; it
retains the explicit eta cost. The [vertical logarithmic bounds](zeta-sech-vertical-bound.md)
now control the full positive mass and every finite signed window,
retaining its negative mass. The full signed limiting detector and local
zero terms are still needed for a larger region. The fixed-ordinate
signed ordinary-prime bound and RH remain open.

## Validation

All seven modules pass strict direct Lean elaboration and the focused
build. The full warning-as-error build passes all 10,234 jobs. Whole-project
declaration lint and verbose lint of every new module pass. All 54 public
theorems use only `propext`, `Classical.choice` and `Quot.sound`.

The generated inventory contains 1,387 project modules, 29,895 declarations
and 26,191 theorems including generated declarations, with no project
axioms or placeholder-dependent declarations. The source scan covers all
1,530 Lean files. All 581 checked local Markdown links resolve; source
whitespace and the README regime pass. A second strict generator run
leaves both JSON and SVG byte-identical. These are local checks; work
remains uncommitted under the user's hold.

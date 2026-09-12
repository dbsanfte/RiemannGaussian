# All-order finite derivative bounds for the original Dirichlet terms

Lean now proves an explicit finite exponential-sum bound at every
derivative order, for every adaptive cutoff rule. The complete logarithmic
derivative family discharges its analytic hypotheses. Exact conjugation
handles both derivative sign parities, and exact Abel summation preserves
the full real damping of the original Dirichlet terms.

This closes the formal induction step in the
[larger-region toolbox](zero-free-region-transport.md). The bound is an
explicit recursive expression. Its uniform quantitative simplification,
including the analytic cutoff and all lag sums, is now proved in the
[closed uniform power bound](uniform-dirichlet-power-bound.md).
The [complete near-one zeta line estimate](zeta-near-one-line-bound.md)
now pays for every block range and the eta tail. The zero detector remains.
The displayed zero-free region is unchanged, and RH remains open.

## Compiled entry points

All names below have prefix `RiemannGaussian.`.

| Module | Main theorems | What is retained or controlled |
| --- | --- | --- |
| [PhaseConjugation](../RiemannGaussian/PhaseConjugation.lean) | `weighted_sum_conj`, `norm_sum_neg_one_pow` | Exact conjugation of both complex amplitudes and phases; all alternating orientations preserve the unweighted norm. |
| [NatPhaseDifferencing](../RiemannGaussian/NatPhaseDifferencing.lean) | `overlap_eq`, `bound` | Every original natural overlap has exactly `N-h` terms, including empty large lags, with all triangular weights retained. |
| [ShiftedDerivativeFamily](../RiemannGaussian/ShiftedDerivativeFamily.lean) | `overlap_subset`, `derivative_family`, `top_bounds` | Differencing commutes with all derivatives on the original domain; the next derivative gives the exact scaled bound `h*ell`. |
| [DerivativeRecursionBudget](../RiemannGaussian/DerivativeRecursionBudget.lean) | `nonneg`, `le_length`, `base_le` | A finite recursively defined bound for every cutoff rule; the trivial fallback never exceeds the length cap and has a uniform square-root envelope. |
| [HigherDerivativeTest](../RiemannGaussian/HigherDerivativeTest.lean) | `bound` | Induction over every finite derivative order, uniformly for every original prefix below a common cap. |
| [LogarithmicDerivativeFamily](../RiemannGaussian/LogarithmicDerivativeFamily.lean) | `hasDerivAt_jet`, `hasDerivAt_oriented`, `oriented_top`, `dyadic_bounds` | Exact factorials, signs and positive-domain calculus at every logarithmic derivative order. |
| [HigherLogarithmicDerivativeBound](../RiemannGaussian/HigherLogarithmicDerivativeBound.lean) | `bound` | All analytic hypotheses discharged for the original logarithmic phase, at every order and every positive height and dyadic scale. |
| [DirichletHigherDerivativeBound](../RiemannGaussian/DirichletHigherDerivativeBound.lean) | `damped_bound`, `feature_bound` | The full original complex Dirichlet terms satisfy the recursive bound, with their initial radial factor as the exact Abel cost. |

## The explicit bound and its free parameters

Let `k` count derivative orders above two, and let `L` be a common upper
bound on the number of original summands. The cutoff rule is an arbitrary
function

\[
\kappa:\mathbb N\times\mathbb N\times\mathbb R\times\mathbb R
\longrightarrow\mathbb N.
\]

Its inputs are recursive order, length cap, positive lower derivative
scale and upper/lower derivative ratio. Set

\[
H=\kappa(k,L,\ell,A)+1.
\]

Thus every selected number of translates is positive. The theorem
does not select numerical coefficients or assume a successful choice.
It applies to every rule, including rules that adapt to the scaled
derivative size at each recursive call.

Write `D_k(L,ell,A)` for `DerivativeRecursionBudget.budget kappa k L ell A`,
and put

\[
E_0(L,\ell,A)=(3+2\pi)
\left(\frac{AL\sqrt\ell}{2\pi}+\frac2{\sqrt\ell}\right).
\]

The base is

\[
D_0(L,\ell,A)=
\begin{cases}
\min\{L,E_0(L,\ell,A)\},&0<\ell\le1,\\
L,&\text{otherwise}.
\end{cases}
\]

The successor is the literal finite expression

\[
D_{k+1}(L,\ell,A)=\min\left\{L,
\sqrt{\frac{L+H-1}{H^2}
\left(HL+2\sum_{j=0}^{H-1}(H-j-1)
D_k(L,(j+1)\ell,A)\right)}\right\}.
\]

All lags retain their individual scaled derivative size. The last lag
has coefficient zero. For `A >= 0`, every budget lies in `[0,L]`.

For `ell > 0` and `A >= 1`, `base_le` proves

\[
D_0(L,\ell,A)\le E_0(L,\ell,A)
\]

at **every** positive derivative scale. When `ell > 1`, the same envelope
dominates the trivial fallback. Subsequent analytic simplification can
therefore use this envelope without silently omitting the large-curvature
base case.

## Why the induction keeps the original domain

Suppose `F_0` is the real phase, and for `r < k+2`,

\[
F_r'=F_{r+1}\quad\text{on }[a,a+N],\qquad
\ell\le F_{k+2}\le A\ell.
\]

For every `N <= L`, `HigherDerivativeTest.bound` proves

\[
\left|\sum_{n<N}e^{iF_0(a+n)}\right|\le D_k(L,\ell,A).
\]

No monotonicity of the highest derivative is assumed. The derivative
relations and its positive bounds are genuine hypotheses on the closed
original domain, and are all proved for the actual logarithmic family.

At a positive integer lag `h <= N`, define the exact family

\[
G_r(x)=F_r(x+h)-F_r(x).
\]

The remaining overlap ends at `a+N-h`. Every interval `[x,x+h]` used
by the mean value theorem is therefore contained in `[a,a+N]`.
Differentiation preserves both endpoints, and the highest remaining
member satisfies

\[
h\ell\le G_{k+2}(x)\le A(h\ell)
\]

in the successor step. The ratio `A` is unchanged. There is no extra
extension to `a+N+h`, which could otherwise inflate the derivative ratio.
If `h > N`, the original overlap is empty and its correlation is exactly
zero; no derivative hypothesis is requested there.

The exact overlap identity remains available upstream. The common-cap
budget deliberately overestimates overlap lengths and can overpay an
empty lag. This gives one bound valid for every prefix, needed for
downstream Abel transport. It does not replace or delete the original
finite overlap information.

## All actual logarithmic derivatives and the complete damping

The proved family for `f(x)=-t*log(x)` is

\[
F_0(x)=-t\log x,\qquad
F_{r+1}(x)=\frac{(-1)^{r+1}t\,r!}{x^{r+1}},\quad x>0.
\]

At order `k+2`, multiply the whole family by `(-1)^(k+2)`. Its top
member is positive. Exact phase conjugation returns to the original
finite-sum norm after applying the generic theorem. For complex weights,
the upstream conjugation identity explicitly conjugates those weights
as well; it does not treat an arbitrary complex amplitude as real.

For `t > 0`, `X > 0` and `X <= x <= 2*X`, the actual lower scale and ratio are

\[
\ell_k=\frac{t(k+1)!}{(2X)^{k+2}},\qquad A_k=2^{k+2}.
\]

Every calculus and dyadic inequality is proved with these exact values.
There is no first-derivative resonance restriction or upper bound on `t`.
The fallback inside the recursive budget handles every base scale.

For `s=sigma+i*t`, `sigma >= 0`, a natural integer start `a >= X`, and
`a+N <= 2*X`, the terminal theorem proves

\[
\left|\sum_{n<N}(a+n)^{-s}\right|
\le a^{-\sigma}D_k(N,\ell_k,A_k)
\]

for every `k` and every cutoff rule. In Lean the terms are literally
`zetaPrimeFeature s (a+n)` and the radial factor is
`zetaPrimeExpWeight s.re a`.

The original real damping is positive and decreasing. The common cap
gives the same `D_k` for all partial sums, so the already proved exact
Abel identity keeps the full damping with only its initial value as cost.

## Remaining quantitative work and RH scope

The motivating external toolbox is the higher-derivative argument in
[Yang, *Explicit bounds on zeta(s) in the critical strip and a zero-free
region*, JMAA 2024, Section 2](https://arxiv.org/html/2301.03165v2#S2).
This is classical mathematics; the present formalization does not claim
historical novelty or the paper's optimized constants.

The [subsequent quantitative proof](uniform-dirichlet-power-bound.md)
now supplies an analytic cutoff, complete finite lag-sum estimates and
one coefficient uniform in the derivative order. With

\[
\alpha_k=\frac1{2^{k+2}-2},\qquad
p_k=2^{-k},\qquad\beta_k=1-2^{-k},
\]

Lean proves the closed bound
`32*(A^p_k * L * ell^alpha_k + L^beta_k * ell^(-alpha_k))`.
The analytic successor shift is the ceiling of
`ell^(-2*alpha_(k+1))`, equal to the proposed
`ell^(-alpha_k/(1+alpha_k))` before rounding. The proof includes the
complete positive and negative lag sums, integer rounding and cases
where the shift exceeds the length cap. For the actual logarithmic
family, `A^p_k <= 4` at every order.

The [complete zeta line estimate](zeta-near-one-line-bound.md) now pays
for every transition window, the final blocks and the whole eta tail.
The estimate is uniform in order and absolute height at least two;
its eta width cost is explicit. The [vertical logarithmic bounds](zeta-sech-vertical-bound.md)
now control the complete positive mass and finite signed windows while
retaining the negative mass. The full signed limit and local zero detector
remain before a stronger region can enter the existing
width/height-band/Cauchy-disc chain.

The terms here have ordinary Dirichlet coefficients equal to one.
Additional prime indicators, finite sieves and moment polynomials have
their own variation or correlation costs. High-height finite estimates
do not automatically give the independent signed prime lower bound in
the fixed-ordinate, growing-moment RH contradiction. That bound and RH
remain open. No new zero-free region is claimed by this slice.

## Validation

All eight modules pass strict direct Lean elaboration, the focused build
and the full 10,234-job warning-as-error build. Whole-project declaration
lint and verbose lint of all eight modules pass. All 27 public theorems
use only `propext`, `Classical.choice` and `Quot.sound`. The generated
inventory contains 1,387 project modules, 29,895 declarations and 26,191
theorems including generated declarations, with no project axioms or
placeholder-dependent declarations. The source scan covers all 1,530
Lean files. All 581 checked local Markdown links resolve, and whitespace
and README-regime checks pass. A second strict generator run leaves
both JSON and SVG byte-identical. These are local checks; work remains uncommitted
under the user's hold.

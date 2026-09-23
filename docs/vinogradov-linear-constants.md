# Finite critical-moment descent with retained constants

Lean now reaches every positive allowance above the critical high-moment
exponent by a finite iteration, starting with the proved elementary estimate.
The terminal bound applies at **every positive integer endpoint** and keeps
its accumulated coefficient in the form `A^n * k!`. The profile coefficient
also has an explicit bound independent of the number of conditioning steps.
For this arbitrary-defect theorem the coefficient remains unevaluated.
A [quantitative relative-defect continuation](vinogradov-quantitative-descent.md)
now specifies every degree cost at `u=k`, `defect=k²/q`, discharges the source
moment hypotheses, and reaches the actual damped zeta blocks. Its coefficients
are large; their improvement remains essential for uniform VK growth.

This changes neither the proved zero-free region nor the default signed
Riesz endpoint. These are refinements of the Vinogradov mean-value proof;
no historical novelty or new zeta-growth estimate is claimed.

## Actual terminal statement

Write

\[
 c=2k(u+1)-\frac{k(k+1)}2,\qquad L=k(2u+1).
\]

For every integer `k ≥ 2`, `u ≥ k`, and real `d > 0`,
[`exists_finite_critical_iteration`](../RiemannGaussian/VinogradovFiniteCritical.lean)
provides real `ε > 0`, `A ≥ 1` and an integer `n ≥ 0` such that

\[
 \varepsilon\le d/2,\qquad c\le L-n\varepsilon<c+d,\qquad
 n\varepsilon\le\max(0,L-c-d)+\varepsilon,
\]

and the original global mean value satisfies

\[
 J_{(u+1)k,k}(X)\le A^n k!\,X^{c+d}
 \qquad\text{for every integer }X\ge1.
\]

No moment-bound premise remains in this terminal theorem. Its starting
estimate is the existing elementary `k! * X^L` bound. The decrement and
multiplier are unevaluated, so this is not a numerical evaluation of the
final moment coefficient.

## Preserve the homogeneous constant

The old prime-size restriction absorbed the source constant `C` together
with the iteration coefficient `D`. The new
[`VinogradovConstantPreservation`](../RiemannGaussian/VinogradovConstantPreservation.lean)
chain requires only `D² ≤ p` and keeps `C` as an explicit multiplier.
Its complete allowance retains every original intermediate conditioned
energy, residue and colour.

The key homogeneous identity is exact:

\[
 C^{1-\theta}(CQ)^\theta=CQ^\theta
 \qquad(C>0,\ Q\ge0).
\]

Consequently the profile depth and additional multiplier can be chosen
**before** the source exponent and `C`. The actual initial allowance and
prime packet preserve this quantifier order in
[`VinogradovLinearSaving`](../RiemannGaussian/VinogradovLinearSaving.lean).

[`exists_linear_all_endpoint_improvement`](../RiemannGaussian/VinogradovLinearExponent.lean)
chooses one positive decrement `ε` and one multiplier `A` before `λ` and
`C`. Every supplied bound `J(X) ≤ C X^λ`, valid for all `X ≥ 1` with
`c+d ≤ λ ≤ L`, yields `J(X) ≤ AC X^(λ-ε)` at all the same endpoints.
The proof pays the original quotient rounding, prime packet and small
endpoints. Iterating until the first crossing of `c+d` gives the terminal
coefficient `A^n * k!` and the stated stopping-count inequality.

## One explicit profile ceiling, regardless of iteration count

Let

\[
 E=\bigl((2ku)(2ku-1)\cdots(2ku-k+1)\bigr)^{2u}.
\]

The profile update has coefficient

\[
 B_{j+1}=\max\{1,\ k!(1+2EB_j)^{1/u}\},\qquad B_0=1.
\]

[`VinogradovLinearProfile`](../RiemannGaussian/VinogradovLinearProfile.lean)
keeps the actual Hölder root and proves an invariant ceiling:

\[
 1\le B_j\le(k!)^2(1+2E)^{2/u}\le(2ku)^{7k}.
\]

The terminal `uniform_profile_degree_cost_iteration` applies this explicit
ceiling to the **original conditioned energies**, at every finite iteration
count. It keeps the source factor `C` linear. The existential depth interface
is now a corollary of `bounded_depth_profile_iteration`: if every preceding
profile satisfies `-d/2 <= defect + k*beta_j`, with `d >= k`, the actual
descendant depth is `(k+d)^n`. This pays the displayed cutoff and padded
quotient conditions. It does not yet bound the complete final coefficient
`A^n k!`.

## Evaluated depth for the actual critical high moment

[`VinogradovQuantitativeProfile`](../RiemannGaussian/VinogradovQuantitativeProfile.lean)
specializes the actual conditioning chain to `u=k`, `k>=4`, and a source
exponent at least one half above critical. Set

\[
 n_k=2k(k+1)+4,\qquad T_k=(3k)^{n_k},\qquad
 Q_k=(2k^2)^{7k},\qquad B_k=1+E Q_k.
\]

The exact profile is `beta_j=k^2-j(1-1/k)/2`. Its final value is
`-1+2/k <= -1/2`, and every preceding profile is at least `-1`.
Thus the single choice `d=2k` pays all intermediate descendant cutoffs.
`half_defect_conditioned_bound` proves, with the original homogeneous
quotient-moment budgets retained explicitly,

\[
 \frac{\text{conditionedMoment}}{\text{momentScale}}
 \le C B\,p^{\delta a-b/2},\qquad 1\le B\le Q_k,
 \qquad p^{T_k b}\le X.
\]

The theorem retains both colours, every residue and the quotient threshold
`N_0 <= floor(X/p^(T_k*b))+1`. The prime-size condition is exactly
`iterationConstant(k,k)^2 <= p`, with no dependence on `C`.
`half_defect_initial_allowance` then bounds the **complete original initial
allowance** by `C B_k p^(-1/2)`.

`half_defect_global_bound` transports this through the original prime packet:

\[
 J_{k(k+1),k}(X)\le (2R)^2 C B_k X^\lambda M^{-1/2}.
\]

This requires the displayed quotient-moment budgets, `M,R>0`,
`X^(k(k-1)) < M^R`, `4k^4 <= X`, `(2^R M)^T_k <= X`, the padded quotient
threshold at that depth, and `iterationConstant(k,k)^2 <= M`.
**These hypotheses have not been removed from this quantitative theorem.**
The older unconditional finite critical-moment theorem is still available;
its accumulated all-endpoint constant remains unevaluated.

The depth grows as `exp(O(k^2 log k))`. This is an explicit admissible cost
of this proof, not a lower bound on the best possible conditioning depth.
It reveals a serious cost to resolve before seeking degree-uniform zeta
bounds. For comparison, [Bellotti's Theorems 1.4 and 1.5](https://arxiv.org/html/2306.10680v1#S1)
use quantitative mean-value bounds to obtain an exponential-sum estimate
uniform in the height-to-length logarithmic ratio. Our new depth calculation
does not reproduce that estimate or its zero-free region. The Gaussian
resonance gain is quadratic in degree. The relative-defect continuation
below uses that margin to replace this depth by a polynomial in `k` for
fixed `q`; its resulting coefficient is still too large for the benchmark
argument.

## The extra exponent-defect saving survives upstream

[`deep_remainder_preserving_defect`](../RiemannGaussian/VinogradovDefectRemainder.lean)
retains information previously discarded in the scaled remainder. With
`δ = λ-c`, the original mixed remainder is bounded by

\[
 C\left(\frac X{p^a}\right)^{\lambda-2ku}
  \left(\frac X{p^b}\right)^{2ku}
  p^{-H/2-\delta\frac{u}{u+1}(b-a+H)}.
\]

This uses the actual two quotient moment budgets, `D² ≤ p`, `k ≥ 2`,
`u ≥ k`, `H ≥ 1`, `b-a ≤ 2H` in natural-number subtraction, and `X > 0`.
The general formula is valid for any real `λ`. At ordered scales with
`λ ≥ c`, the defect term is nonpositive and supplies an additional saving.

The named half-depth bound in `VinogradovConstantPreservation` is now a
proved downstream relaxation of this stronger theorem. **The present global
iteration still uses that relaxation and clips the initial negative profile
at `-1/2`.** Carrying the additional saving through the full allowance has
not yet been done.

## Remaining quantitative work

The [relative-defect continuation](vinogradov-quantitative-descent.md) now
completes the all-endpoint coefficient and decrement for `1<=q<=k²` and
`u=k`. It proves that the Gaussian step tolerates `q=128` and carries the
specified constants to the actual Dirichlet blocks. This does not evaluate
the sharper arbitrary fixed-defect theorem stated above.

The finite descent removes the qualitative infimum from this proof route,
and the explicit profile ceiling removes growth in that coefficient with
the profile iteration count. Descendant depth is now evaluated at `u=k`
and the half-unit defect used by the actual block-saving chain. A uniform
zeta estimate still needs substantially smaller degree costs than the
now-explicit relative-defect multiplier. Sharper bounds must then enter the existing
[actual damped Dirichlet-block saving](vinogradov-gaussian-power-saving.md)
and its all-scale analytic transport. Neither a larger universal zero-free
region nor the independent signed Riesz cancellation follows yet.

The modules are imported by the ordinary root. The exhaustive numerical
certificate stays optional; this local iteration does not rerun it.

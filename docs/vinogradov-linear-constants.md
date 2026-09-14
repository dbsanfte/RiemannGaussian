# Finite critical-moment descent with retained constants

Lean now reaches every positive allowance above the critical high-moment
exponent by a finite iteration, starting with the proved elementary estimate.
The terminal bound applies at **every positive integer endpoint** and keeps
its accumulated coefficient in the form `A^n * k!`. The profile coefficient
also has an explicit bound independent of the number of conditioning steps.
The complete degree dependence of the global coefficient is still open.

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
count. It keeps the source factor `C` linear. The descendant depth `T` is
still chosen existentially and must satisfy the displayed cutoff and padded
quotient conditions. This bound for `B_j` is not a bound for the complete
final coefficient `A^n k!`.

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

The finite descent removes the qualitative infimum from this proof route,
and the explicit profile ceiling removes growth in that coefficient with
the profile iteration count. A uniform zeta estimate still needs evaluated
bounds on descendant depth, prime-packet and rounding costs, and the final
multiplier/decrement. Those bounds must then enter the existing
[actual damped Dirichlet-block saving](vinogradov-gaussian-power-saving.md)
and its all-scale analytic transport. Neither a larger universal zero-free
region nor the independent signed Riesz cancellation follows yet.

All six modules are imported by the ordinary root. The status generator and
explorers export their actual statements, source lines, dependency paths and
transitive axiom audits. The exhaustive numerical certificate stays optional.

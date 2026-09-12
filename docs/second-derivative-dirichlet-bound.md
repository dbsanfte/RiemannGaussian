# Complete second-derivative cancellation for Dirichlet blocks

The second-derivative test now covers every resonance of the original
finite phase sum. Its analytic hypotheses are discharged for
`-t*log(x)` on positive dyadic blocks. Exact Abel summation preserves the
actual real damping, giving an explicit bound for literal complex
Dirichlet terms with coefficients equal to one.

This formalizes a classical tool used in the
[larger zero-free-region program](zero-free-region-transport.md). It does
not yet prove a larger zero-free region or the independent signed
ordinary-prime bound needed by the RH contradiction.

## Compiled entry points

All names below have prefix `RiemannGaussian.`.

| Module | Main theorems | Scope |
| --- | --- | --- |
| [FiniteKuzminLandauPeriodic](../RiemannGaussian/FiniteKuzminLandauPeriodic.lean) | `rotation_twist`, `increment_twist`, `bound_period`, `bound_Ico` | Exact integer twists leave all complex summands unchanged and move any complete nonresonant block between adjacent resonances into the basic Kuzmin test. |
| [MonotonePhaseBlocks](../RiemannGaussian/MonotonePhaseBlocks.lean) | `band_eq_Ico`, `band_card_le`, `nonresonant_band_bound` | Literal finite value bands are consecutive blocks; their endpoints and cardinalities are proved. |
| [FiniteResonancePartition](../RiemannGaussian/FiniteResonancePartition.lean) | `cellIndex_eq_iff`, `sum_eq_bands`, `cells_card_le` | Exact complex partition of every original summand, with both endpoint cells included in the cell count. |
| [DiscreteSecondDerivativeTest](../RiemannGaussian/DiscreteSecondDerivativeTest.lean) | `resonant_band_bound`, `cells_card_le_of_separation`, `bound` | Lower increment separation pays for resonances; upper separation bounds their number. |
| [SecondDerivativeIncrements](../RiemannGaussian/SecondDerivativeIncrements.lean) | `hasDerivAt_unitIncrement`, `unitIncrement_eq`, `increment_gap_bounds` | Genuine second derivatives control the full separation of exact discrete phase increments on the original closed domain. |
| [SecondDerivativeTest](../RiemannGaussian/SecondDerivativeTest.lean) | `bound`, `square_root_bound` | Complete exponential-sum estimate with either a free allowance or the exact square-root choice. |
| [LogarithmicSecondDerivativeTest](../RiemannGaussian/LogarithmicSecondDerivativeTest.lean) | `hasDerivAt_first`, `curvature_bounds`, `bound`, `square_root_bound` | All calculus and curvature conditions are discharged for the actual logarithmic phase. |
| [DirichletSecondDerivativeBound](../RiemannGaussian/DirichletSecondDerivativeBound.lean) | `damped_bound`, `feature_bound` | The full positive decreasing damping survives, giving a bound on the original finite Dirichlet sum. |

## Exact partition before estimation

Set `P = 2*pi`, and let

\[
\delta_n=\varphi(n+1)-\varphi(n),\qquad 0\le n<N.
\]

For `0 < eta <= pi`, the integer tag

\[
m(n)=\left\lfloor\frac{\delta_n+\eta}{P}\right\rfloor
\]

puts each index into exactly one half-open cell
`[m*P-eta, m*P+P-eta)`. Its near-resonant and nonresonant bands are

\[
[mP-\eta,mP+\eta),\qquad
[mP+\eta,mP+P-\eta).
\]

`sum_eq_bands` is an exact complex identity for arbitrary summands,
before any triangle inequality. Boundary points have a fixed assignment.
No index, clipped cell, winding or endpoint is omitted. Empty cells in
the complete integer range contribute zero.

The twist `phi(n) - m*P*n` changes the increments by `-m*P` while
leaving each complex exponential exactly unchanged. The existing signed
summation-by-parts identity and ordered inverse increments therefore
bound each nonresonant band by `P/eta`.

Suppose the original increments satisfy, for `i <= j < N`,

\[
\ell(j-i)\le\delta_j-\delta_i\le U(j-i),\qquad
\ell>0,\ U\ge0.
\]

A resonant band contains at most `2*eta/ell + 1` original indices.
The number of cells is at most `U*N/P + 2`. Summing the two proved
types of bound gives

\[
\left|\sum_{n<N}e^{i\varphi(n)}\right|
\le
\left(\frac{UN}{P}+2\right)
\left(\frac{2\eta}{\ell}+1+\frac{P}{\eta}\right).
\]

This is `DiscreteSecondDerivativeTest.bound`. The allowance remains a
free parameter throughout the identity and main estimate.

## The full increment separation from actual calculus

For a real phase `f`, use the real function

\[
g(x)=f(x+1)-f(x),\qquad g'(x)=f'(x+1)-f'(x).
\]

Bounds `ell <= f'' <= U` first give `ell <= g' <= U` by the mean value
theorem on `[x,x+1]`. Applying it to `g` between `a+i` and `a+j` then
gives the full factor `j-i` above. Comparing independent witnesses for
the two original increments would lose a unit of separation; this proof
avoids that loss.

Every derivative is evaluated in `[a,a+N]`. In particular, the last
auxiliary phase endpoint is included explicitly. The result does not
assume monotonicity of the second derivative; its positive lower bound
already forces the needed ordering of the increments.

If `0 < ell <= 1` and `ell <= f'' <= A*ell`, choosing
`eta = sqrt(ell)` gives the kernel-checked bound

\[
\left|\sum_{n<N}e^{if(a+n)}\right|
\le(3+2\pi)
\left(\frac{AN\sqrt\ell}{2\pi}+\frac{2}{\sqrt\ell}\right).
\]

This is `SecondDerivativeTest.square_root_bound`, the classical
second-derivative scale with a coarse explicit constant. The present
generic theorem treats positive curvature.

## The actual Dirichlet terms

For `t > 0`, `X > 0`, `X <= a` and `a+N <= 2*X`, the actual phase has

\[
f(x)=-t\log x,\quad f'(x)=-t/x,\quad f''(x)=t/x^2,
\qquad \frac{t}{4X^2}\le f''(x)\le\frac{t}{X^2}.
\]

The main logarithmic theorem allows every `0 < eta <= pi`. Its
square-root specialization assumes `t <= 4*X^2`; write
`ell = t/(4*X^2)`.

For `s = sigma+i*t`, `sigma >= 0`, and a natural integer starting point
`a >= X`, the terminal `feature_bound` proves

\[
\left|\sum_{n<N}(a+n)^{-s}\right|
\le a^{-\sigma}(3+2\pi)
\left(\frac{4N\sqrt\ell}{2\pi}+\frac{2}{\sqrt\ell}\right).
\]

In Lean the original terms are `zetaPrimeFeature s (a+n)`, defined as
`exp(-s*log(a+n))`. The positive starting point justifies this usual
Dirichlet notation. The radial factor is exactly
`zetaPrimeExpWeight sigma a = exp(-sigma*log(a))`.

All partial blocks receive the same full-block bound. Exact Abel
summation then transports the decreasing real damping with just its
initial value as cost. There is no hypothesis that the first derivative
or any increment avoids a resonance.

## Scope and next obstruction

These are classical estimates, with no claim of historical novelty.
The external reference motivating this toolbox is
[Yang, *Explicit bounds on zeta(s) in the critical strip and a zero-free
region*, JMAA 2024](https://arxiv.org/html/2301.03165v2).
The formal proof uses coarse constants established here, rather than
importing a paper's quantitative bound as an assumption.

The [all-order recurrence](all-order-dirichlet-recursion.md) is now proved
for every cutoff rule and the actual damped Dirichlet terms. Its explicit
finite budget now has a [closed power bound](uniform-dirichlet-power-bound.md)
with constants uniform in derivative order. The
[complete near-one zeta line estimate](zeta-near-one-line-bound.md)
now controls every block range and the eta tail, uniformly in order and
height. The [vertical logarithmic bounds](zeta-sech-vertical-bound.md)
now control the complete positive mass and finite signed windows. The
full signed limit and local zero detector remain before a larger width
enters the checked chain.

Extra prime, sieve and moment weights still require their own variation
or correlation estimates. The high-height finite Dirichlet bounds do
not automatically control the fixed-ordinate, growing-moment signed
prime source in the RH contradiction. That independent bound and RH
remain open. The displayed zero-free region is unchanged.

## Validation

All eight modules pass direct Lean elaboration with warnings treated as
errors, the focused build and the full 10,234-job build. Whole-project
declaration lint and verbose lint of all eight modules pass. All 33
public theorems use only `propext`, `Classical.choice` and `Quot.sound`.
The generated inventory contains 1,387 project modules, 29,895 declarations,
26,191 theorems including generated declarations, no project axioms and
no placeholder-dependent declarations. A source scan covers all 1,530
Lean files, and all 581 local Markdown links checked in the README and
related development notes resolve. Whitespace and README-regime checks
pass. These are local checks; work remains uncommitted under the user's
hold. A second strict generator run leaves both JSON and SVG artifacts
byte-identical.

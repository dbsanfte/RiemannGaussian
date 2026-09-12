# First-derivative cancellation for complete Dirichlet overlaps

The previously exposed Dirichlet correlations now have an independent
upper bound in a proved nonresonant parameter range. The result retains
the original finite support and full real damping, and feeds the actual
finite van der Corput inequality. No larger zero-free region or signed
prime-tail bound is claimed by this slice.

| Module | Compiled entry points |
| --- | --- |
| [PhaseIncrementInverse](../RiemannGaussian/PhaseIncrementInverse.lean) | `inverseStep_eq`, `inverseStep_im_monotoneOn`, `norm_inverseStep_le` |
| [FiniteKuzminLandau](../RiemannGaussian/FiniteKuzminLandau.lean) | `phase_sum_identity`, `variation_le`, `bound` |
| [FirstDerivativeTest](../RiemannGaussian/FirstDerivativeTest.lean) | `increment_witness`, `bound` |
| [LogarithmicShiftCancellation](../RiemannGaussian/LogarithmicShiftCancellation.lean) | `bound`, `log_ratio_bound`, `dirichlet_correlation_bound` |
| [FiniteAbelVariation](../RiemannGaussian/FiniteAbelVariation.lean) | `weighted_sum_eq`, `weighted_bound`, `decreasing_budget`, `decreasing_bound` |
| [DirichletOverlapCancellation](../RiemannGaussian/DirichletOverlapCancellation.lean) | `feature_pair`, `damped_block_bound`, `correlation_bound`, `vanDerCorput_bound` |

This is classical exponential-sum mathematics. The inverse-increment
argument follows the Kuzmin--Landau method discussed in
[Arias de Reyna, *On Kuzmin-Landau Lemma*](https://arxiv.org/abs/2002.05982).
Our bound uses its coarse Kuzmin constant, not Landau's sharper constant.
The larger-region motivation and derivative-test route are described in
[Yang, *Explicit bounds on zeta(s) in the critical strip and a zero-free
region*, JMAA 2024](https://arxiv.org/html/2301.03165v2).
No historical novelty or imported external axiom is claimed.

## The information that makes the variation telescope

For angles measured in radians and `0 < delta < 2*pi`, define

```text
c(delta) = 1/(exp(i*delta)-1)
         = -1/2 - (i/2)*cot(delta/2).
```

Lean proves the nonzero denominator before using the reciprocal identity.
The real part of `c` is constant, and its imaginary part is increasing
between the two resonances. For monotone or antitone increments, the
complete inverse-increment path therefore lies on one vertical line with
monotone imaginary coordinate.

Discrete summation by parts retains both complex endpoints and every
interior difference. Only then is a norm taken. The sum of the norms of
the successive inverse differences is bounded by the endpoint variation,
independently of the number of terms. Bounding every difference separately
by the same constant would lose that fact.

If all increments lie in `[eta,2*pi-eta]`, `eta > 0`, the resulting bound is

```text
norm(sum exp(i*phi(n))) <= 2*pi/eta.
```

The mean value theorem then proves the same estimate for
`sum_(0<=n<N) exp(i*f(a+n))` whenever `f` has a proved derivative on the
whole closed interval `[a,a+N]`, that derivative is monotone or antitone,
and it lies in `[eta,2*pi-eta]` throughout. Each discrete increment has a
witness in its original unit interval, so their ordering is retained.
The extra endpoint phase belongs to that derivative domain; it is not
added to the original finite sum. Empty blocks are handled explicitly.

## The actual logarithmic cancellation bound

For `t,h,X > 0`, suppose

```text
h <= X,
X <= a,
a+N <= 2*X,
t*h <= pi*X^2.
```

The already proved derivative of

```text
g_h(x) = -t*log(1+h/x)
```

is positive and decreasing. Throughout the block,

```text
t*h/(6*X^2) <= g_h'(x) <= t*h/X^2 <= pi.
```

Choosing `eta = t*h/(6*X^2)` discharges every derivative and nonresonance
condition. The terminal estimate is

```text
norm(sum_(0<=n<N) exp(-i*t*log(1+h/(a+n))))
  <= 12*pi*X^2/(t*h).
```

This improves on the term-count bound when the displayed upper bound is
smaller than the number of terms. It is not asserted to improve that bound
for every admissible parameter choice.

## Exact amplitude transport

If all original partial sums of a complex sequence `z(n)` are bounded by
`B`, finite Abel summation gives, for arbitrary complex weights `w(n)`,

```text
norm(sum_(0<=n<=M) w(n)*z(n))
  <= B*(norm(w(M)) + sum_(0<=n<M) norm(w(n)-w(n+1))).
```

The complete signed identity is retained as `weighted_sum_eq`. For
nonnegative decreasing real weights, the variation budget is proved to
equal exactly `w(0)`. No bound on the variation of arbitrary arithmetic
weights is introduced as a premise masquerading as a proved estimate.

For `s = sigma+i*t`, `sigma >= 0`, the original Dirichlet pair has the
exact damping

```text
D_sigma,h(x) = exp(-sigma*(log(x+h)+log(x))),

(x+h)^(-s) * conjugate(x^(-s))
  = D_sigma,h(x) * exp(-i*t*log(1+h/x)).
```

Lean proves that this actual damping is positive and decreasing on the
positive axis. Every prefix of an admissible block satisfies the same
logarithmic cancellation estimate, so Abel transport preserves the
complete damping with its initial value as the only cost.

## Complete original correlations and the finite block bound

For integer `a`, natural `N` and a positive integer displacement `h`, the
literal zero-extended block of `zetaPrimeFeature(s,n)` has correlation

```text
C_s(h) = sum_(a<=n<a+N-h)
  zetaPrimeFeature(s,n+h) * conjugate(zetaPrimeFeature(s,n)).
```

Under the admissibility conditions above, now for the original block
`[a,a+N)`, Lean proves

```text
norm(C_s(h)) <= (12*pi*X^2/(t*h))*D_sigma,h(a).
```

The integer-to-natural conversion is justified by `a >= X > 0`.
For shifts beyond the original block, the overlap is empty and the exact
correlation is zero. There is no periodic wrapping or boundary clipping.

`vanDerCorput_bound` applies these estimates to every positive lag of the
previously proved finite inequality. It assumes `0 < H <= X` and
`t*H <= pi*X^2`, keeps the exact `N+H-1` factor and the original diagonal
energy, and replaces only the downstream absolute correlations by their
proved bounds. All hypotheses concern the actual parameters, not a
hypothetical zero or an assumed arithmetic cancellation estimate.

## What remains toward the RH objective

The first-derivative test treats one nonresonant derivative interval.
The [complete second-derivative development](second-derivative-dirichlet-bound.md)
now covers every resonance and bounds the actual damped Dirichlet terms.
The [all-order induction](all-order-dirichlet-recursion.md) is now proved.
Its recursive bound now has a [closed uniform power estimate](uniform-dirichlet-power-bound.md).
The [complete near-one zeta line estimate](zeta-near-one-line-bound.md)
now pays for all block ranges and the eta tail, uniformly in order and
height. The [vertical logarithmic bounds](zeta-sech-vertical-bound.md)
now control the complete positive mass and finite signed windows.
The full signed limit and local zero detector remain in the
[larger-region program](zero-free-region-transport.md).

The Dirichlet correlation theorem concerns coefficients equal to one,
with their full radial damping. Prime indicators, finite sieves and
polynomial filters have additional weights. Their complex values and
explicit variation cost remain available, but their required arithmetic
control is not supplied by phase smoothness alone.

These are finite estimates with explicit joint height/scale restrictions.
They do not automatically give the independent signed ordinary-prime
lower bound in the fixed-ordinate, growing-moment RH contradiction.
That bound and RH remain open.

## Validation

All six modules pass direct Lean elaboration with warnings treated as
errors, the focused build and the full 10,234-job build. Whole-project
declaration lint and verbose lint of all six new modules pass. All 34
public theorems use only `propext`, `Classical.choice` and `Quot.sound`.
The compiled inventory contains 1,387 project modules, no project axioms
and no placeholder-dependent declarations. Repeated strict generation
leaves the JSON and SVG byte-identical. Source, local-link and whitespace
checks pass. These are local checks; work remains uncommitted under the
user's hold.

# Weighted differencing and the actual logarithmic Dirichlet phase

Five Lean modules prove finite van der Corput differencing, its exact
weighted phase identities, and its application to the repository's original
Dirichlet features. This implements the first ingredient of the
[larger-region program](zero-free-region-transport.md). The subsequent
[first-derivative development](first-derivative-dirichlet-cancellation.md)
now bounds the actual damped Dirichlet overlap correlations on admissible
blocks. Neither development yet enlarges the proved zero-free region.

| Module | Compiled entry points |
| --- | --- |
| [FiniteShiftCorrelation](../RiemannGaussian/FiniteShiftCorrelation.lean) | `shiftedSum_mass`, `shiftedSum_energy`, `norm_sum_sq_le_correlation_matrix` |
| [FiniteVanDerCorput](../RiemannGaussian/FiniteVanDerCorput.lean) | `toeplitz_sum_eq`, `signed_bound`, `absolute_bound` |
| [FiniteVanDerCorputPhase](../RiemannGaussian/FiniteVanDerCorputPhase.lean) | `correlation_windowed`, `phaseTerm_pair_re`, `signed_phase_bound`, `unit_phase_bound` |
| [LogarithmicShiftPhase](../RiemannGaussian/LogarithmicShiftPhase.lean) | `shift_eq_log_one_add`, `hasDerivAt_shift`, `hasDerivAt_slope`, `slope_antitoneOn`, `slope_dyadic_bounds` |
| [ZetaFiniteDifferencing](../RiemannGaussian/ZetaFiniteDifferencing.lean) | `phase_eq_multiplicative`, `feature_shift_pair_log`, `overlap_eq`, `signed_bound`, `absolute_bound` |

The finite inequality is classical. One source used for the unweighted
version and the exact integer-endpoint factor is
[Yang, *Explicit bounds on zeta(s) in the critical strip and a zero-free
region*, JMAA 2024, Lemma 2.3](https://arxiv.org/html/2301.03165v2).
No historical novelty is claimed for this formalization. The proof here
starts from finite Cauchy--Schwarz and justifies the complete shift sums;
the paper's statements are not introduced as axioms.

## Complete correlations before estimation

Let `f` be a complex sequence supported in the integer interval
`I = [a,a+N)`, extended by zero outside it. For any positive integer `H`,
define

```text
C(h) = sum_n f(n+h) * conjugate(f(n)),
F_H(n) = sum_(0 <= h < H) f(n+h),
E = sum_(n in I) norm(f(n))^2.
```

The full complex identities include `C(-h) = conjugate(C(h))` and
`sum_n F_H(n) = H*sum_n f(n)`. The exact energy identity is

```text
sum_n norm(F_H(n))^2
  = sum_(0 <= h,k < H) Re(C(h-k))
  = H*E + 2*sum_(1 <= h < H) (H-h)*Re(C(h)).
```

Consequently,

```text
H^2 * norm(sum_(n in I) f(n))^2
  <= (N+H-1) * (H*E + 2*sum_(1 <= h < H) (H-h)*Re(C(h))).
```

The full right-hand form is nonnegative because it is an energy. Individual
real correlations can be negative. Replacing each `Re(C(h))` by `norm(C(h))`
is a separate downstream theorem.

Lean writes the positive-lag sum using `k = 0,...,H-1`, displacement `k+1`
and coefficient `H-k-1`. Its final term has coefficient zero. There is no
assumption `H <= N`; shifts beyond the original interval have empty overlap.

The factor `N+H-1` is the size of the enclosing interval
`[a-H+1,a+N)`. It is not relaxed to `N+H`. All infinite integer sums used
in this argument are genuinely summable because the sequences have finite
support. No periodic extension or wraparound correlations are introduced.

## Phase and amplitude information retained

For arbitrary complex amplitudes `w(n)` and real phases `phi(n)`, put
`b(n) = w(n)*exp(i*phi(n))`. The exact positive-shift correlation is

```text
C(h) = sum_(a <= n < a+N-h)
  w(n+h)*conjugate(w(n))*exp(i*(phi(n+h)-phi(n))).
```

Writing `A = w(n+h)*conjugate(w(n))` and `delta = phi(n+h)-phi(n)`,
the signed summand is exactly

```text
Re(A)*cos(delta) - Im(A)*sin(delta).
```

For real weights it becomes `w(n+h)*w(n)*cos(delta)`, with both weight
signs retained. Unit amplitudes give the usual unweighted van der Corput
inequality, with diagonal mass exactly `N`.

## Application to the original zeta terms

For `s = sigma+i*t` and any arithmetic weights `w : Nat -> Complex`, the
terminal theorem bounds the literal positive-block sum of

```text
b(n) = w(n) * zetaPrimeFeature(s,n)
     = w(n) * exp(-sigma*log(n)) * exp(-i*t*log(n)).
```

Let `a_s(n) = w(n)*exp(-sigma*log(n))`. The original overlap is exactly

```text
C_s(h) = sum_(a <= n < a+N-h)
  a_s(n+h)*conjugate(a_s(n))*exp(-i*t*log(1+h/n)).
```

The implementation uses integer intervals for shifts and converts their
members to naturals. The terminal hypothesis `a > 0` proves that every
original and shifted term is a positive integer. The logarithmic ratio is
never inferred by silently evaluating a singular expression at zero.

`phase_eq_multiplicative` identifies this phase with the existing
[multiplicative matrix phase](../RiemannGaussian/ZetaMultiplicativePhase.lean).
Thus both additive differencing and multiplicative transport act on the
same original oscillation.

Prime indicators, von Mangoldt weights and finite sieve restrictions may
be encoded in `w`. Their shifted products remain in the correlations.
Smoothness of the phase alone does not bound these arithmetic products.
An unrestricted complex weight could even cancel the oscillatory factor;
any claimed saving must use actual restrictions on the weights.

## The proved logarithmic derivative scales

For `x > 0`, `h >= 0`, and real `t`, write

```text
g_h(x) = -t*log(x+h) + t*log(x) = -t*log(1+h/x).

g_h'(x)  = t*h / (x*(x+h)),
g_h''(x) = -t*h*(2*x+h) / (x^2*(x+h)^2).
```

Both derivative identities are proved. For `t,h > 0`, the first derivative
is positive; for `t,h >= 0`, it is decreasing on the positive axis.
On `X <= x <= 2*X`, with `X > 0`, `0 <= h <= X` and `t >= 0`, Lean proves

```text
t*h/(6*X^2) <= g_h'(x) <= t*h/X^2.
```

These bounds specify a genuine admissible scale. They do not by themselves
give cancellation of discrete exponentials: phase increments close to
multiples of `2*pi` require separate treatment.

## Remaining step toward larger zero-free regions

The first-derivative cancellation test and its actual damped Dirichlet
application are now proved in the
[subsequent development](first-derivative-dirichlet-cancellation.md).
The [second-derivative estimate](second-derivative-dirichlet-bound.md) now
pays for every resonant interval and bounds the full damped Dirichlet terms.
The [all-order recurrence](all-order-dirichlet-recursion.md) now retains
these ranges and controls the actual Dirichlet terms. Its finite budget
now has a [closed power bound](uniform-dirichlet-power-bound.md) with
constants uniform in order. The [complete zeta line estimate](zeta-near-one-line-bound.md)
now pays for every block range and the whole eta tail, uniformly in
order and height. The [vertical logarithmic bounds](zeta-sech-vertical-bound.md)
now control the complete positive mass and finite signed windows. The
full signed limit and local zero detection remain.
The [general width interface](zero-free-region-transport.md)
can transport the resulting larger region once it is actually proved.

For the arithmetic source, any use of these tests must also retain the
original weights or prove a suitable weighted summation-by-parts bound.
High-height Dirichlet-sum estimates are not automatically estimates in
the fixed-ordinate, growing-moment regime of the RH source. The independent
signed ordinary-prime lower bound and RH remain open.

## Validation

All five modules pass direct Lean elaboration with warnings treated as
errors. The focused build and the complete 10,234-job build pass.
Whole-project declaration lint and verbose lint of every new module pass.
All 50 public theorems use only `propext`, `Classical.choice` and `Quot.sound`.
The generated inventory contains 1,387 project modules, no project axioms
and no placeholder-dependent declarations. Repeating generation leaves
the JSON and SVG byte-identical. Source, local-link and whitespace checks
pass. These are local checks; the slice remains uncommitted under the
user's hold.

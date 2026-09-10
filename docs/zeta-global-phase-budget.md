# Global phase budget with full zero multiplicity

The global xi expansion now gives an unconditional identity between the
actual prime work and the complete zero mass for every admissible finite
or countably infinite phase family. Its regular analytic allowance is
`1 + log(sigma + |t|)`. The independent arithmetic lower bound that would
exclude every hypothetical right-half zero remains open.

## Complete identity before estimation

For `s = sigma + i*t`, define

```text
P(s,rho) = m(rho) * (sigma-Re(rho)) / |s-rho|^2,
R(s)     = 1/s - log(pi)/2 + digamma(s/2)/2.
```

Here `rho` runs over the actual distinct nontrivial zeta zeros and `m(rho)`
is the actual analytic multiplicity. For `sigma >= 1`, every Poisson term
is nonnegative and their series converges. The previously proved global
paired expansion, with its vanishing canonical remainders, gives

```text
sum_rho P(s,rho) = Re(xi'/xi(s)).
```

Functional reflection reindexes the other half of the paired sum with
multiplicity unchanged. There is no leftover entire term and no local
divisor radius. See
[`tsum_zetaGlobalPoissonSummand`](../RiemannGaussian/ZetaGlobalPoisson.lean).

On `sigma > 1`, the full complex completion identity is retained first:

```text
-zeta'/zeta(s) + xi'/xi(s) = 1/(s-1) + R(s).
```

Taking real parts gives the exact signed budget. The independent bound
on the literal Gamma correction is

```text
Re R(s) <= 1 + log(sigma + |t|),     sigma >= 1.
```

This follows from the proved Euler limit for digamma and the new
right-half-plane estimate

```text
Re digamma(z) <= log(|z|^2 / Re(z)),     Re(z) > 0.
```

The proof compares each actual reciprocal term, telescopes logarithmic
increments, and passes to that limit. See
[`re_digamma_le_log_normSq_div_re`](../RiemannGaussian/DigammaLogarithmicBound.lean)
and [`zeta_global_complex_budget`, `re_zetaGlobalRegularCorrection_le`,
`zeta_global_real_budget`](../RiemannGaussian/ZetaGlobalSignedBudget.lean).

## Every admissible phase family

Let `a_n >= 0`, with `sum a_n` finite, and let `omega_n` be arbitrary real
frequencies. At a positive shift `x`, assume the logarithmic height cost
is summable:

```text
sum_n a_n * (1 + log(1+x+|omega_n*y|)) < infinity.
```

With the actual phase kernel and prime-power work

```text
K(theta) = sum_n a_n*cos(omega_n*theta),
W        = sum_m Lambda(m)*m^(-1-x)*K(y*log(m)),
```

the exact identity is

```text
W + sum_n a_n * sum_rho P(1+x+i*omega_n*y,rho)
  = sum_n a_n*x/(x^2+(omega_n*y)^2)
      + sum_n a_n*Re R(1+x+i*omega_n*y).
```

All these series are proved convergent. In particular, convergence of
the complete zero mass follows from its sign and the actual Euler-axis
bound; convergence of the signed Gamma series follows by reassembling
the convergent channels. It is not assumed as an extra norm estimate.
No positivity of `K` is needed for this identity or its logarithmic
upper bound.

The terminals are
[`zetaPhase_primeWork_add_globalZeros_eq`,
`zetaPhase_primeWork_add_globalZeros_le`](../RiemannGaussian/ZetaGlobalPhaseBudget.lean).
When `omega_r = 1`, the selected zero contributes exactly
`a_r*m(rho)/(1+x-Re(rho))`, as recorded by
[`zetaPhase_global_multiplicity_add_primeWork_le`](../RiemannGaussian/ZetaGlobalPhaseBudget.lean).

## The smaller contradiction budget

For integer frequencies, summability of `a_n` and `a_n*log(n)` suffices.
Write

```text
d = 1-Re(rho) > 0,   y = Im(rho) != 0,   x = kappa*d,   kappa > 0,
A = sum_(n>=1) a_n,  L = sum_(n>=1) a_n*log(n),
S = a_1*m(rho)/(kappa+1) - a_0/kappa.
```

The full source inequality is

```text
S + d*W
  <= d * [a_0*(1+log(1+kappa*d))
          + A*(1+log(1+kappa*d+|y|)) + L]
       + kappa*A*d^2/y^2.
```

This is
[`phase_shifted_source_add_primeWork_le_global_split`](../RiemannGaussian/ZetaGlobalPhaseBudget.lean).
It applies to every nontrivial zero and every positive `kappa`. It does
not require the former restrictions `Re(rho) >= 3/4` and
`kappa*d <= 1/4`. On the former domain, the analytic contribution
`448*log(|t|+22)` has been replaced by `1+log(sigma+|t|)`; these are
different explicit functions, not a claimed uniform factor-448 gain.

If the phase kernel is nonnegative, any finite prime-power set `F`
contributes an independent lower bound for `W`. The full omitted tail is
nonnegative, and

```text
d * sum_(m in F) Lambda(m)*m^(-1-kappa*d)*K(y*log(m))
  <= [the displayed budget] - S.
```

See
[`phase_finite_primeWork_le_global_zero_defect`](../RiemannGaussian/ZetaGlobalPhaseBudget.lean).
This provides a direct target for an arithmetic estimate without fixing
a phase count or hunting numerical coefficients.

## Remaining obstruction

A contradiction would require an independently proved lower bound for
the retained arithmetic work that makes `S+d*W` strictly exceed the
displayed budget for each hypothetical zero with `Re(rho)>1/2`.
The exact global identity supplies an upper budget; it does not supply
that opposite inequality. The coefficient and convergence assumptions
are discharged by the stated family conditions, while the necessary
arithmetic estimate remains unproved.

The existing
[phase energy and prime-scale floors](../RiemannGaussian/ZetaPhaseBinomialScale.lean),
[balanced Suzuki criterion](../RiemannGaussian/SuzukiBalancedSubpolynomial.lean),
and [relative recovery theorem](suzuki-relative-recovery.md) remain
available. None yet closes the global arithmetic gap. This slice proves
no RH theorem and extracts no new explicit numerical zero region.

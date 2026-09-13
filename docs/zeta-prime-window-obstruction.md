# Every fixed normalized filter has large raw prime windows

Lean now proves a general obstruction to estimating the surviving prime
tail by taking norms of its separate logarithmic windows. It covers every
fixed complex polynomial normalized at the selected source, including the
repository's actual zero-isolating pole-jet filter. It does not improve the
zero-free region or prove the missing signed prime-tail floor.

## The unchanged arithmetic sum

Let `u > 1/2`, let `y` be any real ordinate, and fix a complex polynomial
`p` with `p(1/u) = 1`. For any fixed `h > 0` with `abs(y) * h <= 1`, set

```math
K_{p,N}(s,x)=x^{-s}\sum_k p_k\frac{(\log x)^{N+k}}{(N+k)!},
\qquad
W_N=\sum_{\substack{a\text{ prime}\\e^{N/u}\lt a\le e^{N/u+h}}}
 (\log a)K_{p,N}(3/2+iy,a).
```

The theorem
[`every_normalized_filter_has_large_windows`](../RiemannGaussian/ZetaPrimeWindowLocalization.lean)
proves

```math
u^{N+1}\lVert W_N\rVert\longrightarrow+\infty.
```

The polynomial is arbitrary and fixed as `N` grows. Extra pole roots,
zero-isolation roots, and complex coefficient signs are all allowed.
The starting order can depend on the polynomial. This is not a uniform
theorem over polynomials that change with `N`.

## Why normalization forces the local contribution

The exact factorization in
[`ZetaFactorialFilterLocalization`](../RiemannGaussian/ZetaFactorialFilterLocalization.lean)
is

```math
\sum_k p_k\frac{t^{N+k}}{(N+k)!}
=\frac{t^N}{N!}\,A_{p,N}(t),
\qquad
A_{p,N}(t)=\sum_k p_k t^k\frac{N!}{(N+k)!}.
```

`norm_zetaFactorialLocalAmplitude_sub_eval_le` gives an explicit endpoint
error allowance, and `tendsto_zetaFactorialLocalError` proves that it tends
to zero. Together they give uniform convergence
`A_{p,N}(t) -> p(c)` on every interval `c*N <= t <= c*N+h`, for `c >= 0`.
Choosing `c = 1/u` forces the limiting amplitude to be one. This avoids
any assumption about the polynomial's value at the absolute saddle `c=2`.

The exact prime kernel phase varies by at most one radian across the
window. Uniform localization therefore preserves a positive projection
after rotation by `exp(i*y*N/u)`. The unconditional prime number theorem
supplies the actual logarithmic prime mass in this interval; Stirling's
upper factorial bound supplies the exponential scale. No density model is
substituted for the ordinary primes.

The compiled `eventually_filteredMoment_growth_lower` and
`source_localGrowth` expose the eventual lower allowance

```math
\frac{u C_h}{6N}
 \left(e^{1-1/(2u)}\right)^N,
\qquad
C_h=\frac{e^h-1}{8}e^{-3h/2}>0,
```

for the normalized rotated real projection. Its exponential base exceeds
one for every `u > 1/2`. All other polynomial coefficients affect the
starting order, but not this displayed rate or constant.

## Connection to the original tail

For a hypothetical right-half zero `rho = beta + i*y`, use
`u = 3/2 - beta`, the unchanged pole-jet filter, and
`h = 1/(abs(y)+1)`. In
[`ZetaPrimeTailWindowObstruction`](../RiemannGaussian/ZetaPrimeTailWindowObstruction.lean):

- `source_window_primes_survive` proves that every tested prime is beyond
  the squared divisor schedule and outside the simultaneous prime sieve.
- `tailMoment_eq_filteredMoment` identifies the finite window with the
  original prime-correction coefficient, for every eligible divisor cutoff.
- `norm_normalizedTailWindow_tendsto` proves divergence for the actual
  pole-jet filter. Its proof uses normalization and actual prime counting,
  without invoking the signed source-limit theorem.
- `primeLogResponse_sub_tailMoment_eq` identifies the difference between
  the full sum and the window with the convergent sum outside that window.

Write `P_N` for the original complete normalized tail and `V_N` for this
normalized window. The earlier source theorem gives `P_N -> -m_rho`.
Combining that finite limit with the independently proved window growth,
`complementaryPrimeTail_div_window_tendsto_neg_one` proves

```math
\frac{P_N-V_N}{V_N}\longrightarrow-1.
```

The denominator is proved eventually nonzero. This retains the full
complex relative amplitude: the complement must cancel the large local
contribution. The last statement uses the hypothetical zero's source
limit; it is not a new independent cancellation estimate.

## What remains useful to try

The result eliminates raw interval norm control for **all fixed normalized
filters**, extending the earlier locally checked linear example. It does
not rule out estimates for a centered arithmetic error, estimates retaining
cancellation between windows, or filters that change with moment order.
The latter would require new uniform coefficient and analytic error bounds;
this theorem supplies none of them.

The existing [centered Abel representation](../RiemannGaussian/ZetaPrimeBandChebyshev.lean)
retains the Chebyshev error and its full complex kernel. An estimate through
that representation must be assessed at the original source scale. The
remaining sufficient target is still a fixed `epsilon > 0` and a cofinal
bound `Re(P_N) >= -1 + epsilon`. No such bound is proved here. The
[literature and rate audit](prime-tail-literature-audit-2026-09-11.md) records
why ordinary positivity, uncentered interval estimates, and generic
logarithmic savings are insufficient.

The PNT, Stirling and phase estimates are classical ingredients. No claim
of historical novelty or proximity to a proof of RH follows from this
method obstruction. All four modules are imported into the root library;
the generated proof inventory audits their declarations and axioms.

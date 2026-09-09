# A stronger arithmetic floor from weighted phase returns

`RiemannGaussian/ZetaPhaseWeightedRecurrence.lean` proves an independent,
explicit floor for the exact phase optimiser:

```text
W_sigma(y) = sum_m Lambda(m) m^(-sigma) P(y log m) >= 1/120
             for every real y and 1 < sigma <= 5/4.
```

The terminal theorem is `phaseContactExact_arithmetic_floor`. It uses
the five powers `2, 4, 8, 16, 32`, the existing exact coefficients, and
their proved enclosures. No zero hypothesis, numerical minimisation,
arithmetic cancellation assumption, or new coefficient search is used.

## The information recovered

For a summable nonnegative coefficient sequence `a`, arbitrary real
frequencies `omega`, and a zero-frequency index `r`, put
`P(t) = sum_n a_n cos(omega_n t)` and `A = sum_n a_n`.
The existing Gram inequality says that the energy of `N+1` equally
spaced phases is at least `(N+1)^2 a_r`.

The new `zetaPhase_gram_block_eq` retains its exact difference counts:

```text
sum_(0<=i,j<=N) P((j-i) theta)
  = (N+1) A + 2 sum_(k=1..N) (N+1-k) P(k theta).
```

Consequently `zetaPhase_weighted_returns_le` proves

```text
sum_(k=1..N) (N+1-k) P(k theta)
  >= (N+1) ((N+1) a_r - A) / 2.
```

This holds for finite or infinite spectra, without requiring integer
frequencies or assuming kernel nonnegativity for this intermediate step.
The identity remains available alongside the lower bound.

## Transport to actual arithmetic

For a prime `p`, `sigma >= 1`, and `1 <= k <= N`, Lean proves

```text
(N+1-k) log(p) p^(-N sigma) <= log(p) p^(-k sigma).
```

The elementary input is `j+1 <= p^j`. With `P >= 0`, every triangular
return weight is therefore paid by its own actual prime-power amplitude.
The powers are distinct, and the complete arithmetic series genuinely
converges when `sigma > 1`. Keeping their finite sum gives
`zetaPhase_weighted_primePower_floor`:

```text
W_sigma(y) >= log(p) p^(-N sigma)
             * (N+1) ((N+1) a_r - A) / 2.
```

The preceding separate-return estimate was

```text
W_sigma(y) >= log(p) p^(-N sigma) * ((N+1) a_r - A) / N.
```

For `N >= 1` and a positive mass gap, the new right side is larger by
the exact factor `N(N+1)/2`: ten at four returns, fifteen at five.
The old argument compared each individual return with the whole
arithmetic sum; it thereby lost the benefit of adding distinct terms.

`phaseContactExact_weighted_primePower_floor` discharges every phase
hypothesis for the exact optimiser at arbitrary `N`, `p`, and `y`.
`phaseContactExactFamily_six_mass_gap` proves
`6 a_0 - A >= 313/1000`. For `p=2`, `N=5`, and `sigma <= 5/4`, the
last amplitude is at least `log(2)/77`, because `2^(25/4) <= 77`.
Together with the checked logarithm bound, these inequalities yield
the stated `1/120` floor.

For orientation only, evaluating the rational coefficient centres at
`sigma=5/4`, `p=2` gives the following approximate floors. These values
are exploratory; the Lean conclusions use the formulas and rational
bound above.

| Block | Previous floor | Weighted floor |
| --- | ---: | ---: |
| Four powers | 0.000697106 | 0.006971064 |
| Five powers | 0.000570603 | 0.008559046 |

## Consequence for actual zeta zeros

Let `rho=beta+i gamma` be an actual nontrivial zero with `beta >= 15/16`,
and set `d=1-beta`. The existing zero budget uses
`sigma=1+(13/4)d`, which lies in the proved range. The new
`phaseContactExact_weighted_zero_budget` retains the exact source,
analytic multiplicity, and true height sum, with an additional `d/120`
reserve. The rational consequence is
`phaseContactExact_weighted_zero_source`:

```text
11/625 + d/120
  <= 448 d ((61/100) log(|gamma|+22) + 83/100)
       + (793/400) d^2/gamma^2.
```

`phaseContactExact_weighted_exclusion` proves zeta nonvanishing whenever
the strict reverse inequality holds, `Re(s) >= 15/16`, and `|Im(s)| >= 1`.
The improvement is explicit and reaches the actual zeta theorem.

The floor is uniform and bounded. Its contribution to the zero budget
is proportional to `d`; it does not change the leading reciprocal-log
scale of the edge exclusion. The independent signed finite-prime-band
bound for the global RH objective remains open. This slice neither
identifies the best possible arithmetic floor nor claims mathematical
priority for the Gram/weighted-return argument.

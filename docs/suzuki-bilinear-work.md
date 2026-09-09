# The signed work and its explicit bilinear lower bound

`SuzukiBilinearWork.lean` proves an unconditional cellwise lower bound for
the original signed Suzuki work, and retains its exact nonnegative
remainder. **The independent cumulative lower bound remains open. There
is no new zero exclusion or unconditional RH proof.**

For the new integer `n >= 3`, let

```text
a_n = Lambda(n) / sqrt(n)
M_(n-1) = sum_{2 <= d < n} Lambda(d) / sqrt(d)
A'(r_(n-1)) = M_(n-1)
c = (Re digamma(1/4) - log(pi)) / 2.
```

The original work is `I_n = a_n * (log(n) - r_(n-1))`. Define the entirely
finite arithmetic expression

```text
J_n = 2*Lambda(n)/sqrt(n) + c*Lambda(n)/n
        - Lambda(n)/n * sum_{2 <= d < n} Lambda(d)/sqrt(d).
```

Lean proves `I_n = J_n + R_n` and `R_n >= 0`. Every triangular prime-power
cross term is present; there is no absolute-value replacement or implicit
canonical center in `J_n`.

The remainder is explicit. Removing the cancelling zeroth Lerch term from
the actual Archimedean slope gives a convergent positive tail `T(r)` and
the exact identity `A'(r) = 2*exp(r/2) + c + T(r)`. With
`u_n = (r_(n-1) - log(n))/2`, the retained remainder is

```text
R_n = a_n * (2*(exp(u_n) - 1 - u_n) + T(r_(n-1))/sqrt(n)).
```

Its sign follows from exponential convexity. The same identity holds after
summation over every finite band, and the canonical gap has the exact
accounting

```text
G_(start+count) = G_start + sum J_n + sum R_n - sum C_n.
```

The previously proved transport cost `C_n` is summable. **Summability of the
new reserve `R_n` has not been proved.** A finite lower bound on cumulative
`J_n` is sufficient for the existing RH chain, but could be stronger than
a lower bound on the retained `J_n + R_n`. The latter remains available.

The coefficient is mathematically fixed:
`suzukiArchimedeanSlopeConstant_eq_neg_logDeriv_zeta_half` proves
`c = -Re (zeta'/zeta)(1/2)`, using the functional equation and the existing
eta theorem to discharge nonvanishing at the central real point. Replacing
it by `c'` changes the cumulative bilinear sum by exactly

```text
(c' - c) * sum_{3 <= n <= N} Lambda(n)/n.
```

Lean proves this harmonic prime mass tends to positive infinity, using
Mathlib's divergence of prime reciprocals. Consequently every fixed
downward coefficient error gives a discrepancy tending to negative
infinity. It cannot be absorbed into a finite error allowance.

The principal compiled interfaces are:

- `suzukiFirstTailTransportLinearWork_eq_bilinear_add_reserve`;
- `suzuki_bilinear_work_sum_eq_triangular_prime_sum`;
- `suzukiFirstTailCanonicalGap_add_eq_bilinear_add_reserve_sub_cost`;
- `suzuki_bilinear_work_lower_coefficient_error_tendsto_atBot`;
- `riemannHypothesis_of_suzuki_bilinear_work_eventually_bounded_below`.

The last theorem is explicitly conditional on the still-open arithmetic
floor. The module is imported by the root library. Validation is local;
the slice remains uncommitted under the user's instruction.

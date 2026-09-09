# Controlling a fixed mass shift and its exact logarithmic drift

`SuzukiMassShiftBudget.lean` proves an independent bound for removing a
fixed additive constant from the old mass in Suzuki's finite arithmetic
work. After subtracting the exact logarithmic mass drift, the remaining
error is absolutely summable and has a uniform inverse-square-root band
bound. **The lower bound for the remaining signed prime sum is still open.**

Use the actual old mass and next atom:

```text
M_j = sum_{2<=d<=j+2} Lambda(d)/sqrt(d),
a_j = Lambda(j+3)/sqrt(j+3),
M_(j+1) = M_j+a_j,
M_0 = log(2)/sqrt(2) > 0.
```

For a fixed `delta>=0`, define the finite shifted work

```text
K_delta(j) = a_j*(log(j+3)-2*log((M_j+delta)/2)).
```

The original mass-log work is exactly `K_delta` at `delta=-c`, where
`c` is the actual Archimedean slope constant. Lean proves `c<0` from the
original slope formula. The zero-shift expression `K_0` contains only
finite von-Mangoldt sums, square roots and logarithms. Every old prime
power is retained, and all logarithm arguments are proved positive.

The exact nonnegative shift cost is

```text
K_0(j)-K_delta(j) = 2*a_j*log(1+delta/M_j).
```

Its atom/mass correlation is controlled before summation. Lean proves
`a_j<=2`, and hence

```text
0 <= a_j/M_j - log(M_(j+1)/M_j)
  <= 2*(1/M_j - 1/M_(j+1)).
```

The upper bound telescopes. Together with the elementary logarithm
remainder bound it gives, for

```text
C_delta = 4*delta + 2*delta^2*(1+2/M_0),
E_delta(j) = K_0(j)-K_delta(j)
             -2*delta*(log(M_(j+1))-log(M_j)),
```

the unconditional cell estimate

```text
|E_delta(j)| <= C_delta*(1/M_j-1/M_(j+1)).
```

Thus, for every band starting at `s` with arbitrary length `k`,

```text
sum_{j=s}^{s+k-1} |E_delta(j)|
  <= C_delta*(1/M_s-1/M_(s+k))
  <= 2*C_delta/sqrt(s+2)                     (s>=3).
```

The second inequality uses the original unconditional Chebyshev lower
bound. Lean proves that `M_j` tends to infinity and that `sum |E_delta(j)|`
converges. Consequently

```text
sum_{j<count} (K_0(j)-K_delta(j))
  -2*delta*(log(M_count)-log(M_0))
```

converges to the actual sum of `E_delta`. The logarithmic drift is explicit;
it is not being treated as a bounded error. These results are checked by
`suzukiMassShiftWork_centered_error_bound`,
`sum_abs_suzukiMassShiftCenteredError_le_inv_sqrt`,
`summable_abs_suzukiMassShiftCenteredError` and
`suzukiMassShiftWork_centered_sum_tendsto`.

The earlier, simpler bound also applies when selecting only ordinary-prime
new atoms, because the uncentered shift cost is nonnegative. With
`kappa=1+2/M_0`, that complete selected discrepancy is at most

```text
2*delta*kappa*(log(12)+|log(M_0)|+log(N)/2),   N=count+2.
```

The [logarithmic-loss criterion](suzuki-logarithmic-work.md) absorbs this
allowance. Therefore an eventual lower bound

```text
sum_{j<count, j+3 prime} K_0(j) >= -(B+D*log(N)),   D>=0,
```

is sufficient for Mathlib's RH. The terminal theorem is
`riemannHypothesis_of_suzuki_unshifted_ordinaryPrime_work_eventually_log_lower_bound`.
Its arithmetic premise remains unproved. The centered telescoping theorem
above concerns the **complete** event sequence; a bounded centered remainder
for the prime-only sequence is not asserted here.

The older coefficient-sensitivity audit remains correct for a fixed
constant-floor target: a constant coefficient discrepancy accumulates.
The new target permits a logarithmic loss, and the present independent
estimate now controls that accumulation. It therefore justifies removing
the fixed mass shift for this target, without changing the original work.

The analytic background is Suzuki's pointwise-positivity criterion in
[Theorem 1.7 of his screw-function paper](https://arxiv.org/html/2206.03682).
No outside arithmetic estimate is used as a proof input in this module.

The module is root-imported and validated locally with warnings as errors,
declaration lint and transitive axiom checks. No commit is made.

# Independent bounds for complete balanced blocks

`SuzukiBalancedBlockBounds.lean` bounds the actual signed change of the
Suzuki optimum between two balanced cutoffs. It retains all intervening
prime powers and their common initial mass. **The global subpolynomial
floor remains open.** The bound requires both displayed endpoints to be
balanced; their availability at any prescribed spacing is not assumed or
proved.

Write `N = start+2`, `L = count`, and use the unchanged quantities

```text
M_N = sum_(d<=N) Lambda(d)/sqrt(d)
P_N = sum_(d<=N) Lambda(d)*log(d)/sqrt(d)
m   = M_N-c > 0
a   = M_(N+L)-M_N >= 0
r_N = 2*log(m/2)
B_N = P_N-2*m*(log(m/2)-1)+C.
```

The full centered block is

```text
W = sum_(N<n<=N+L) Lambda(n)/sqrt(n) * (log(n)-r_N).
```

The first identity is exact, without balance or asymptotic assumptions:

```text
B_(N+L)-B_N = W - 2*((m+a)*log((m+a)/m)-a).
```

Its nonlinear cost uses the entire mass `a`. It therefore includes the
mixed interactions that would disappear if each new atom were optimized
against a reset mass.

Balance means `2*sqrt(N) <= M_N-c <= 2*sqrt(N+1)`, and likewise at the
other endpoint. Every intervening prime-power location then lies between
the two mass centers, so

```text
0 <= W <= 2*a*log((m+a)/m).
```

Consequently Lean proves the signed bounds

```text
-2*((m+a)*log((m+a)/m)-a)
  <= B_(N+L)-B_N
  <= 2*(a-m*log((m+a)/m)).
```

These full relative-entropy expressions remain available upstream of the
quadratic estimate. Elementary logarithmic inequalities give

```text
abs(B_(N+L)-B_N) <= 2*a^2/m <= (L+1)^2/(N*sqrt(N)).
```

The second inequality uses both balanced masses together:
`m >= 2*sqrt(N)` and `a*sqrt(N) <= L+1`. The rounding unit is the extra
integer width of the final balanced cell.

The estimate is uniform over all such endpoints. In particular,
`L+1 <= K*N^alpha` gives

```text
abs(B_(N+L)-B_N) <= K^2*N^(2*alpha-3/2).
```

For every fixed `alpha < 3/4`, this tends uniformly to zero. At the
square-root length scale the simpler allowance is `K^2/sqrt(N)`.
The already proved comparison with the canonical Suzuki gap adds at most
`(16/75)*exp(5)*N^(-5/2)` to the corresponding gap-increment bound.

## What remains open

Vanishing local increments do not imply a global lower bound: many
decreases can accumulate, and long intervals may have no intervening
balanced cutoffs. The theorem proves neither balanced-cell density nor
monotonicity of their potentials. The exact signed centered moment is
retained for further cancellation estimates across those intervals.

The active target remains the
[one-sided subpolynomial floor on balanced cells](suzuki-balanced-subpolynomial.md).
No new zero exclusion, RH proof, or mathematical-priority claim is made.

Principal Lean declarations:

- `suzukiMassLegendrePotential_block_eq_centeredWork_sub_entropy`
- `suzukiMassBlockCenteredWork_balanced_bounds`
- `suzuki_balanced_potential_block_entropy_bounds`
- `abs_suzuki_balanced_potential_block_le_mass_square`
- `abs_suzuki_balanced_potential_block_le_cutoff_square`
- `abs_suzuki_balanced_potential_power_block_le`
- `suzuki_balanced_potential_power_blocks_uniformly_small`
- `abs_suzuki_balanced_canonical_gap_block_le`
- `suzuki_balanced_canonical_gap_power_blocks_uniformly_small`

The module is imported from the root library. Warnings-as-errors checks,
the full build, declaration lint, and terminal axiom audits have passed
locally. The slice remains uncommitted under the user's instruction.

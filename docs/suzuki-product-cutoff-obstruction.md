# The product cutoff must retain its full complement

The direct product cutoff `dn<=N` does not cover the original Suzuki
prime-pair interaction, whose support is `2<=d<n<=N`. The new Lean module
`SuzukiProductCutoffObstruction.lean` retains both regions exactly and
proves that the omitted positive interaction is too large to absorb in a
logarithmic allowance. **This is a verified obstruction to dropping terms,
not a new signed-work bound or zero exclusion.**

For event `j`, write

```text
n_j = j+3,
a_j = Lambda(n_j)/sqrt(n_j),
M_j = sum_{2<=d<=j+2} Lambda(d)/sqrt(d),
c = -Re((zeta'/zeta)(1/2)).
```

Here `c` is the real constant already identified in Lean. For `count`
events the original endpoint is `N=count+2`. Let `P_count` and `R_count`
be the triangular pair interactions on `dn<=N` and `dn>N`, respectively,
with their original weight `Lambda(n)*Lambda(d)/(n*sqrt(d))`. The initial
atom at `2` is included. Lean proves

```text
sum_{j<count} J_j = 2*sum a_j + c*sum a_j/sqrt(n_j) - (P_count+R_count),
sum_{j<count} I_j = sum_{j<count} J_j + sum_{j<count} ConvexReserve_j.
```

`I_j` is the unchanged canonical-center work, `J_j` its existing bilinear
lower bound, and the entire nonnegative convexity reserve is retained.
In particular, removing `R_count` raises the proposed lower bound. Its
nonnegativity does not justify that operation.

## A positive part of the omitted region has square-root size

Take `count=2*K`. The upper band has events `K<=j<2*K`, and mass

```text
B_K = M_(2*K)-M_K.
```

Every pair internal to that band has product greater than `2*K+2`.
Let `T_K` be its original triangular interaction. The proof keeps the
cross term between the old boundary mass `M_K` and the new band separately;
the internal interaction is only part of the complete remainder. Lean proves

```text
T_K <= R_(2*K),
T_K >= (B_K^2-2*B_K)/(2*sqrt(2*K+2)),
B_K/sqrt(K) -> 2*sqrt(2)-2.
```

The diagonal allowance `2*B_K` follows from the actual bound `0<=a_j<=2`.
The mass limit uses the already proved arithmetic cancellation theorem,
with no RH or hypothetical-zero assumption. Consequently

```text
sqrt(K)/32 <= R_(2*K)                         eventually,
B+D*log(2*K+2) < R_(2*K)                     eventually,
```

for every real `B` and every `D>=0`. The second statement is also compiled,
not merely inferred from numerical evidence.

## Scope and remaining obligation

This excludes replacing the original interaction by its smaller product
region and treating the complement as `O(log N)`. It does not exclude
Selberg identities that retain or reweight the whole complement, or a
signed estimate using its cancellation against the other original terms.
The independent logarithmic lower bound for cumulative signed work remains
open. The earlier unconditional `o(sqrt(N))` work estimate is unchanged.

Key declarations:

- `suzukiPrimeInteraction_eq_productCutoff_add_remainder`
- `suzukiBilinearWork_sum_eq_productCutoff_with_remainder`
- `suzukiSignedWork_sum_eq_productCutoff_with_remainder_and_reserve`
- `suzukiTopBandInteraction_eq_original_sub_boundary`
- `suzukiTopBandInteraction_le_productCutoffRemainder`
- `suzukiTopBandMass_div_sqrt_tendsto`
- `eventually_sqrt_le_suzukiProductCutoffRemainder`
- `eventually_log_lt_suzukiProductCutoffRemainder`

The module is imported by the root library. Validation is local under the
standing instruction to hold commits.

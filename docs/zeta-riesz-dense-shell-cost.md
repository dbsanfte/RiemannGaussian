# Dense intermediate populations: signed periods and all occupied scales

The independent whole `-79/1000` floor, `3/2` ceiling, restricted
contradiction and new zero exclusion remain open. The results here bound
a growing dense population by summing the literal signed owner-prime
period first. They also pay the number of possible cluster locations.
They do not supply an unrestricted source-normalized floor.

## Which intermediate populations remain after the sparse bound?

For the existing cofactor-prime universe `U`, the intermediate primes are

```
E = {p in U : B < log p < J/W},
B = W = 32 log(N+1).
```

The preceding `global_quarter_count_floor` covers labels with at most
`floor(log(N+1)/4)` factors in `E`, at arbitrary total count. The dense
population has more intermediate factors. Give each prime in `E` its
unique logarithmic bin

```
B*2^i < log p <= 2*B*2^i.
```

`exists_unique_log_shell` proves existence and uniqueness, including the
upper endpoints. `available_shell_count_le` bounds the entire available
grid by `2 log(N+1)+1` bins. The following priority classification avoids
charging a label in more than one case.

| Dense configuration | Cancellation or bound | Remaining obligation |
| --- | --- | --- |
| All cofactor prime logs at most `v/(128 log(N+1))` | Retained count tilt proves `O(log(N)/N^12)`, including nonempty owner clips | **Already paid:** `omega(a)>=32 log(N+1)` puts the original label inside the old spent tail; do not charge it again |
| `5 log(N+1)+2 <= omega(n) < countThreshold(N)`, at any occupied-bin number or crossing parity | **New:** keep the hard count in the signed period population price; main and actual owner clips have global relative cost `O(log^2(N)/sqrt(N))` | Same original supply pays the cost; whole literal fibre cover and final ledger placement remain |
| At most `floor(log(N+1)/16)` occupied bins, with any number of primes in each | **New:** complete signed prime periods, including ownership clips, have one global cost over all counts, bin choices, owner scales and radial periods | Original complete fibre/mask cover and a disjoint supply reserve |
| More occupied bins, but background divisor-log crossings separated by the two-prime tent width | **New:** exact two-hinge finite differences leave at most one tent at either hinge; cost is independent of background count | Total weighted population cost; see the separated-parity note |
| More occupied bins, overlapping active crossings of both parities | Existing same-label opposite-rank transport keeps the full phase and both hinges | Total matching distance, disjoint coverage and unmatched layers |
| More occupied bins, overlapping crossings of only one parity | Universal opposite-parity matching is formally impossible | Cancellation across original labels or complete prime periods, beyond the current positive budget |

Use the rows in order, so overlapping qualifications do not duplicate a
label or reserve. Inactive responses are exactly zero and are not
obstructions. This is a classification by explicit arithmetic tests, not a theorem
that the last two cases are empty. A clustered one-parity example belongs
to the few-bin case when it occupies few bins: same-label matching can
fail while signed owner-prime-period cancellation still gives a bound.
Incomplete physical fibres and previously spent supply credits are
separate ledger issues, not extra parity classes.

The small-top estimate is in
[zeta-riesz-dense-small-top-floor.md](zeta-riesz-dense-small-top-floor.md).
It retains the original count tilt rather than dropping it to the
uniform owner-scale price. The retained cofactor window forces at least
`32 log(N+1)` factors, so the original labels are already paid by the old
tail. The genuine lower-count bound and the updated unpaid enumeration
are in [zeta-riesz-unpaid-count-tilt-floor.md](zeta-riesz-unpaid-count-tilt-floor.md).

## No cap on factors inside a cluster

For a union of occupied bins `I`, the actual finite reciprocal-prime mass
satisfies

```
M_E = sum_{p in E} 1/p
    <= |I| * (log 2 + 1/B),                B >= 5000.
```

This is an estimate on the actual finite prime universe. It uses the
existing leading-one prime-interval bound; it is not a prime-density
replacement for the carrier. The all-count Euler price is

```
exp(4 M_E) <= 32^|I|.
```

`uncapped_intermediate_period_floor` retains every cofactor count,
original complex phase, factorial kernel, varying unique-owner
allocation and both hinges. The main complete period costs `123136`;
the literal ownership clips cost `98304`. Both missed sign selections
use ONE original boundary atom. Their joined price is `221440`, in the
same true supply units as before. No signed arithmetic bound is assumed
inside this theorem.

If a whole selected population uses one union of at most
`log(N+1)/8` bins, `global_dense_shell_floor` already bounds that
population with no factor-count restriction.

## Paying ALL cluster locations

Different labels need not use the same bins. `occupiedShells_mono`
shows that divisor deletion cannot add an occupied bin.
`sum_occupied_pattern_partition` assigns each original squarefree
label to its ONE exact occupied pattern. This identity holds for an
arbitrary additive weight, including the original complex phase and
allocation; no completion or averaging is involved.

For the entire grid `I` and `h <= log x/16`, `x=N+1`, Lean proves

```
sum_{K subset I, |K|<=h} 32^|K| <= exp(1) * sqrt(x),
|I| <= 2 log x + 1.
```

The number of possible patterns is included. There is no assumption
that all labels share a fixed cluster. `global_all_pattern_floor`
then derives the actual signed-period-plus-clips inequality

```
selected signed total >=
  -intermediateSupplyPrice(N) * sum_v amplitude(N,v)/v,

intermediateSupplyPrice(N)
 = 221440 * gappedHeadCost * exp(1)
   * (32 log(N+1))^8 * (1 + log(4(N+1))/log 2)
   / sqrt(N+1).
```

This sums every selected count, pattern, dyadic owner scale and radial
period. It invokes the proved signed period inequality, rather than
assuming a bilinear cancellation hypothesis. The exact pattern partition
is what prevents double spending when supplying these sets from the
current carrier.

`tendsto_intermediateSupplyPrice` gives the relative rate
`O(log^9(N)/sqrt(N))`. The ACTUAL positive supply is

```
amplitude(N,v)/v = exp(-v/2) * v^N/N!.
```

The fixed arithmetic head is finite, positive and unevaluated. This
vanishing fraction can be paid by a genuinely disjoint reserve, if one
is supplied. It is NOT an absolute source-scale `o(1)` estimate: the
whole positive factorial envelope still contains `(2u)^N`.

## Follow-up whole-carrier placements

The [dense-count cover](zeta-riesz-dense-count-cover-floor.md) now pays the
whole original upper growing-count band. The
[few-bin cover](zeta-riesz-few-bin-cover-floor.md) now pays the lower-count
class with few occupied bins of ALL large-log cofactor primes. Both keep
the original fibre masks and real ownership clips; the same supply retains
1/512 after both payments. The older owner-dependent intermediate-gap bin
test is not automatically equivalent to this stronger literal selection.
The remaining many-bin costs below are still open.

## What has not been bounded

Labels with both many intermediate factors and many occupied bins are
not covered universally. The new hard-count price handles complete
signed owner periods in the upper part of the actually unpaid count
range, independently of their crossing parity. Below that count range,
separated divisor windows have a count-free signed bound; overlapping
windows retain the matching and one-parity obstructions in the table.

The theorem premises keep the literal complete owner-prime fibres,
canonical owner inequalities, physical support and ownership boundary
sets explicit. A cover of the whole current carrier and compatibility
with the four old credits remain unproved. No global floor, ceiling,
restricted contradiction or zero exclusion is asserted.

The optional `scripts/probe_riesz_dense_populations.py` checks exact
occupied-pattern accounting on small actual squarefree populations and
the weighted pattern budget. It also tests separated-window cancellation
on actual primes and continuous large-log geometries. Continuous models
do not certify prime existence or the literal physical masks. The probe
is outside ordinary builds and CI.

Focused Lean checks and all public transitive axiom checks are recorded
in [riesz-dense-shell-cost-audit.json](riesz-dense-shell-cost-audit.json).
No novelty claim is made for dyadic grouping or finite Euler budgets.

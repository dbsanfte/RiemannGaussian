# Dense overlapping populations with a small largest cofactor log

The independent whole floor remains open. This module proves a literal
signed bound for another dense population, without a factor-count or
occupied-bin ceiling. It keeps the existing count tilt at the actual
cofactor scale rather than replacing it by its uniform inverse-owner
bound. Both original Riesz hinges, phase, factorial weight and changing
unique-owner allocation remain.

## Arithmetic conditions

For a complete owner-prime period with total-log center `v`, let `J`
bound every selected cofactor prime by

```
log q <= 4J,
512J log(N+1) <= v.
```

Thus every cofactor prime has log at most `v/(128 log(N+1))` for positive
`log(N+1)`. If the retained core cofactor has `log a >= v/4`,
`small_top_count_lower` proves

```
omega(a) >= 32 log(N+1).
```

These counts grow with the order. A dense cluster or a diffuse population
can satisfy these conditions, whether its active crossings have one or
both parities. No local opposite-parity pairing is needed.

The first variant's owner scale `H` also satisfies `4J < H`. The original near-owner
clip has a cofactor prime with `log q >= H`, while every such prime has
`log q <= 4J`. `owner_clips_empty` proves its literal support is empty.
No boundary atom is simply dropped or charged to an old reserve.

The new boundary variant removes that strict separation. Its literal
near-owner norm price retains the stronger `exp(-v/(8J))` count saving.
Both missed sign selections spend one boundary atom. The joined main
and nonempty boundary cost is

```
16136 * exp(4M - v/(32J))/H * amplitude(N,v)/v,
16136 = 3848 + 12288.
```

`global_small_top_with_boundary_floor` proves the same global
`O(log(N)/N^12)` relative supply rate with only `J<=H`.

## Keep the signed count saving

The previous uniform population price replaced
`exp(-v/(32J))/H` by `32/v`. Here `retained_count_tilt_floor` retains the
former factor and derives the actual signed complete-period bound

```
signed period total >=
  -3848 * exp(4M - v/(32J))/H * amplitude(N,v)/v,
M >= sum_{q in Q} 1/q.
```

It sums all selected count ranks first, using the proved literal
owner-period floor and squarefree factorial population bound. There is
no inserted bilinear hypothesis or assumed sign theorem.

The actual finite cofactor-prime universe has the existing leading-one
mass estimate

```
M <= C_head + log(N+1),
C_head = smallPrimeHeadMass + log 16 + 1/5000,
5000 <= J <= 4(N+1).
```

The small-top condition gives `v/(32J) >= 16 log(N+1)`. Consequently

```
3848 exp(4M - v/(32J))/H
  <= 3848 exp(4C_head - 12 log(N+1)),      H >= 1.
```

`small_top_period_floor` applies this rate directly to the literal
prime sums. `global_small_top_floor` joins ALL selected counts, dyadic
owner scales and radial periods, including the two original missed-sign
clip selections. The latter are zero by the actual support theorem.
The single relative price is

```
smallTopSupplyPrice(N)
 = 3848 exp(4C_head - 12 log(N+1))
   * (1 + log(4(N+1))/log 2).
```

Lean proves its convergence to zero; the rate is
`O(log(N)/N^12)`. The ACTUAL supply unit stays

```
amplitude(N,v)/v = exp(-v/2) * v^N/N!.
```

This is a relative supply price after signed prime-period cancellation,
not a source-normalized decay theorem. The arithmetic head is finite,
positive and unevaluated. No effective starting order is claimed.

## Ledger overlap audit

The newer `ZetaRieszUnpaidCountTiltFloor.small_top_mem_paid_tail` proves
that these original squarefree labels are ALREADY in the published
spent high-count tail: their cofactor count is at least `32 log(N+1)`,
while the old whole-label threshold is at most `16 log(N+1)` for `N>=7`.
These signed inequalities remain valid, including the new nonempty
boundary theorem. They must not be counted as new unpaid coverage or
consume the same supply reserve again.

The actual lower-count attack is now recorded in
[zeta-riesz-unpaid-count-tilt-floor.md](zeta-riesz-unpaid-count-tilt-floor.md).
It targets `5 log(N+1)+2 <= omega(n) < countThreshold(N)`.

## What is still missing

The whole original physical-prime/radial fibre cover and a fresh
disjoint reserve remain required. The theorem keeps these complete
fibre and mask premises explicit. It does not spend any of the old four
credits again.

On a separate ledger these estimates could pay a small-top population.
On the current published floor that population was paid already. Dense
lower counts with a macroscopic largest cofactor log still need joint
signed cancellation or a new population payment; see the updated
dense-shell taxonomy. The new variant also handles literal nonempty
near-owner clips when the small-top count constraint holds.
No independent `-79/1000` floor, ceiling, contradiction or zero exclusion
is asserted.

`scripts/probe_riesz_dense_small_top.py` compares the tilted count budget
with an explicit infinite-tail upper bound in a numeric budget model.
It does not approximate actual prime density or certify literal masks.
The probe is optional and outside ordinary builds and CI.

The seventeen public proofs and focused checks are recorded in
[riesz-dense-small-top-floor-audit.json](riesz-dense-small-top-floor-audit.json).

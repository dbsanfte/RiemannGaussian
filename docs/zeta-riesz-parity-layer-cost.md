# Retain the total logarithm when pricing parity layers

The independent whole floor, ceiling, RH contradiction and new zero
exclusion remain open. `ZetaRieszParityLayerCost` proves a quantitative
global cost for an explicit structured population, across all selected
counts, dyadic owner scales and radial periods. It is not a bound for
every remaining geometry or every absolute matching majorant.

## The constraint omitted by the previous count sum

Let `v` be the radial center, `H` the owner-log scale and `J <= H` a
cofactor-log scale. The original cofactor keeps at least `v/4` of the
total logarithm, and every cofactor prime has log at most `4J`.
Thus any selected count `k` obeys

```
v/4 <= 4J(k+3).
```

`literal_core_cofactor_quarter` derives the quarter from the actual
retained central lower window and owner cap. The extra three counts also
allow the original ownership boundary's deleted owner pair.
`clipped_count_constraint` proves its constraint from the actual
near-tied owner witness and total log. No arithmetic cancellation premise
is inserted into either argument.

Writing `M = sum_{p in Q} 1/p`, the count tilt gives

```
sum_{k in I} (2M)^k/k! <= 8 exp(4M - v/(32J)).
```

The earlier unconditioned price was `exp(2M)`. The tilt is applied AFTER
the signed prime period, not to an absolute source envelope. Since
`J <= H`, it also gives the uniform owner bound

```
exp(-v/(32J))/H <= 32/v.
```

The complete signed owner main therefore costs
`123136 exp(4M)/v` times `amplitude(N,v)/v`. The ACTUAL ownership clips
cost `98304 exp(4M)/v` in the same units. Both missing sign selections
spend ONE boundary atom, giving the joined constant `221440`.

The original unique-owner allocation is retained in the signed main.
`retained_owner_row_floor` uses the already proved selected-factorial
owner-fibre theorem at unrestricted count. A variable allocation family
is norm-bounded only on the ownership boundary, where it is a debit;
`allocation_family_atom_norm_le` justifies that bound pointwise.
No allocation error is multiplied by the divergent `(2u)^N` envelope.
Complete physical prime support remains an explicit premise.

## A growing spectrum class with a vanishing global price

Keep EVERY small prime. Restrict the other primes only by the log spectrum

```
log p <= B  OR  J/W <= log p <= 4J,
```

where `B >= 5000`, `W >= 1` and `J >= 10000W`. The cofactor scale may move
and shrink relative to the owner, and both count and permitted log spread
may grow. There is no fixed prime-count ceiling in the theorem.

The exact finite small-prime head and the already proved leading-one
reciprocal-prime interval estimate give

```
exp(4M) <= gappedHeadCost * B^4 * W^4,
gappedHeadCost = smallPrimeHeadCost^2 * 8^4 * exp(1).
```

The fixed arithmetic-head constant is finite, positive and unevaluated.
This is a positive cofactor-mass estimate after signed prime-period
cancellation; it is not PNT/Abel transport of the retained signed carrier.

`gapped_radial_supply_floor` joins every selected count and dyadic owner
scale before summing all radial periods. For `N+2 <= v <= G`, its single
cost is

```
221440 * gappedHeadCost * B^4 * W^4
  * (1 + log(G)/log(2))/(N+1)
  * sum_v amplitude(N,v)/v.
```

These are the ACTUAL supply units:
`amplitude(N,v)/v = exp(-v/2)*v^N/N!`. No missing radial power is hidden.
For fixed `W` and `B=32 log(N+1)` this price is `O(log^5 N/N)`. More
generally, `B=W=32 log(N+1)`, `G=4(N+1)` gives the checked
`gappedSupplyPrice = O(log^9 N/N) -> 0`.
`eventually_gappedSupplyPrice_lt` fits any fixed positive fraction.
`cost_paid_by_radial_reserve` connects it to a disjoint reserve in these
same units. It does not create a new supply credit or pay overlapping
old sectors again.

This prices reinforcing unmatched parity layers in that population even
when a local opposite-parity matching does not exist. It bounds the
assembled signed periods and their actual clips; it does NOT make an
arbitrary positive sum of transport distances source-small.

## Exact remaining gap and quantitative audit

The uncovered intermediate interval is

```
B < log p < J/W.
```

The original core does not imply this interval is empty. The optional
log-geometry probe adds one mesoscopic prime to a clustered cofactor.
At the displayed model order `10^10`, it has log `100000`, between the
head `736.8` and shell lower endpoint about `470k`. The active divisor
rank changes, but all 66 active based blocks still have the SAME parity.
Thus neither the local pairing nor the new structured-population bound
automatically covers it. This is a continuous geometry model, not a
literal prime-label or population-mass certificate.

Simply enlarging the head does not resolve that gap. Lean proves
`large_head_price_lower`: if `B^2 >= N+1`, `W >= 1` and
`0 < v <= 4(N+1)`, the positive supply-unit price is at least
`55360*gappedHeadCost*(N+1)`, even BEFORE owner multiplicity. The current
price then grows, so it cannot be used as a vanishing cost for the
intermediate scales. This audits the majorant, not impossibility of a
new signed arithmetic bound.

A whole endgame application still requires complete original fibre/mask
coverage, treatment of those intermediate scales and any small-scale
exceptions, and disjointness from previous supply credits. None of these
is assumed to be free. The current scalar `polynomialCentralRemaining`
and its original source ledger are unchanged. No `-79/1000` floor has
been proved.

## Optional numerical diagnostics and validation

`scripts/probe_riesz_parity_layer_cost.py` checks an actual small-prime
squarefree reciprocal population, exact high-precision factorial tails,
the correct supply-price units, and the spectrum coverage failure.
The large-log layouts are explicitly continuous models. The formal
arithmetic-head constant is not evaluated and no effective starting order
is certified. The probe is outside ordinary builds and CI.

Focused warning-as-error direct/build, ordinary-root-plus-explicit-module
namespace lint and every public transitive axiom check are recorded in
[riesz-parity-layer-cost-audit.json](riesz-parity-layer-cost-audit.json).
No historical novelty claim is made for factorial tilting or finite
signed prime-period pricing.

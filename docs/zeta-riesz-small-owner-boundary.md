# Preserve the least-prime saving at original ownership boundaries

The independent whole floor, ceiling, restricted contradiction and new
zero exclusion remain open. `ZetaRieszSmallOwnerBoundary` improves the
actual ownership-clip payment and audits the proposed global payment's
normalization. It makes no new carrier or prime-density replacement.

## The surviving least prime

A literal owner-period clip supplies two nearly tied large primes. If
the original least-prime log is at most `b` and both deleted prime logs
are above `b`, `least_prime_survives_pair` proves that the remaining
cofactor still has least-prime log at most `b`. The actual near-tied cover
keeps the original primes, squarefreeness, all remaining factors and the
geometric cap. `b+1 <= H` is a convenient sufficient separation condition.

The original complex atom, including its allocation and phase, now has
the fixed-count boundary bound

```
384 * b/H^2 * (2M)^k/k! * amplitude(N,v)/v.
```

The previous bound was `1536/H` times the same count and factorial units.
The new coefficient is smaller by the factor `b/(4H)`. Counts are joined
exactly before pricing; the two missed sign selections spend ONE boundary
atom. No cofactor-prime lower cutoff is required. After the finite small
prime head is included, the full boundary price is

```
384 * smallPrimeHeadCost * b * amplitude(N,v)/v.
```

Joining this with the flat-response signed prime main gives the single
`504 * smallPrimeHeadCost * b` price. Complete original fibres, original
mask cover and compatibility with prior supply credits are still needed.
This is a concrete boundary saving, not a claim that every boundary is paid.

## Exact zero-cost boundary test

The same small divisor block also controls all four cutoffs produced by
two distinct owner primes:

```
L, L-log(p), L-log(q), L-log(p)-log(q).
```

If all four miss the large-divisor intervals of width `log R`,
`owner_pair_atom_zero_of_spectrum_gaps` proves the ENTIRE original
allocated complex atom is exactly zero. Its norm is zero on any original
selected boundary population satisfying the test. This also consolidates
previous zero deletions; overlapping zero populations create no additional
supply credit. A cutoff hitting a small-block interval can still survive.

## Correct global supply units: a necessary audit

`amplitude(N,v) = exp(-v/2)*v^(N+1)/N!`. The existing positive radial-supply
theorem uses `amplitude(N,v)/v`, one degree lower. Therefore a coefficient
decaying against `amplitude` need not decay against the actual supply.

`small_flat_radial_supply_floor` joins ALL selected growing counts,
dyadic owner scales and radial periods in the CORRECT units. Its price is

```
504 * smallPrimeHeadCost * b * (1 + log(G)/log(2))
```

times the sum of `amplitude(N,v)/v`, with `v <= G`. For `b=log(N+1)` and
`G=4(N+1)`, this positive price grows. Lean proves
`tendsto_smallFlatSupplyPrice_atTop` and
`not_eventually_smallFlatSupplyPrice_le`: it cannot fit any fixed supply
fraction eventually. This audits the current majorant, not impossibility
of a sharper signed arithmetic floor.

The coefficient divided by `N+1` does tend to zero, but it is in the
wrong, one-degree-higher units. The exact identity
`smallFlatRadialPrice_mul_eq_supplyPrice` records the lost factor.
Likewise `broad_price_in_supply_units` audits the earlier broad theorem:
its coefficient `129088/a^2` against `amplitude` becomes `129088*v/a^2`
against the actual supply. Its standalone supply theorem cannot be joined
to the all-radial main without that factor. The old documentation's
purported combined `1/256` payment is withdrawn; both Lean theorems
themselves remain valid.

The next arithmetic target must keep the signed cofactor/count crossings
joined, rather than sum these positive boundary prices. Neither price may
be multiplied by the divergent `(2u)^N` source envelope.

## Probe and validation

The optional `scripts/probe_riesz_small_owner_boundary.py` keeps original
squarefree core labels, actual near-tied owners, allocation and full phase.
One four-cutoff gap case is exactly zero; two cases retaining the last
small-block hinge have response `log(2)` and a negative arithmetic
coefficient. These order-640 labels fail the current reduced-count crop
and eventual Chebyshev threshold, and their kernel underflows. They are
algebra diagnostics, not source-scale population evidence.

A separate table exposes the normalization issue: at orders 256 through
1048576 the displayed amplitude coefficient decreases while the correctly
normalized positive supply price increases. The fixed small-prime head
constant is not numerically evaluated. Focused warning-as-error direct/
build, root-plus-module namespace lint and all public transitive axiom
checks are recorded in `riesz-small-owner-boundary-audit.json`.

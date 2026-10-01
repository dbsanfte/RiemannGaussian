# Join small-prime blocks before pricing the surviving crossing

The whole `-79/1000` floor remains open. This local slice keeps each
original label, complex phase, allocation, factorial kernel and count
mask. It changes only the grouping of divisor incidences before taking a
bound. All public proofs are in `ZetaRieszSmallCofactorCancellation`.

`retained_small_orbit_eq_full` proves that an arbitrary squarefree block
containing the canonical least-prime pair may be regrouped after BOTH
existing zero deletions. The deleted incidences still sum to exactly zero
with any common original complex weight; they are not silently restored
as an unpaid carrier. Odd blocks have an exact midpoint reflection zero.
The quantitative `odd_two_hinge_bound` prices distance from that zero,
provided the other hinge really is saturated.

## The clustered mechanism

Write the cofactor as `B*R`, with a small squarefree block `R` containing
at least two primes. Each large-divisor log of `B` creates a possible
support interval of width `log R`. If the moving cutoff misses all those
intervals throughout a complete actual owner-prime phase period, the
changing Riesz hinge vanishes identically throughout that period.
`clustered_spectrum_gap` supplies explicit sufficient inequalities when
the remaining prime logarithms are close together; no numerical gap or
continuum approximation is assumed by the Lean theorem.

The other cofactor hinge remains. The full two-hinge response is exactly
constant on the period, so `flat_unallocated_fibre_floor` removes the
cutoff-variation debit while retaining the original phase and full
factorial weight. The empty allocation applies only after the already
proved hinge-allocation payment; it does not license removing allocation
on arbitrary core labels.

After summing the signed prime period, squarefree count symmetry gives
the count price `M^k/k!`. The improved row price is

```
-120 * b/H^2 * (2M)^k/k! * amplitude(N,v)/v,
```

where `log(minFac(cofactor)) <= b`. ALL selected counts may grow.
Every small cofactor prime is allowed: the exact finite prime head below
`exp(5000)` is kept in `smallPrimeHeadCost`, and the leading-one large-range
reciprocal-prime estimate gives `exp(2M) <= smallPrimeHeadCost * H^2`.
The resulting `whole_small_flat_floor` has price

```
-120 * smallPrimeHeadCost * b * amplitude(N,v)/v.
```

The head constant is fixed and finite, but not numerically evaluated.
This is an actual signed complete-period inequality on its explicit
flat-response support, not a global supply payment or a zero exclusion.
The ownership-boundary and correct radial-unit audit are in
`zeta-riesz-small-owner-boundary.md`.

## Optional quantitative probe

`scripts/probe_riesz_small_cofactor.py` is outside ordinary builds/CI.
Original squarefree core labels at order 640 compare joined small blocks
against separately priced canonical pairs. Spread examples reduce that
local price by about 85–96%; clustered examples can retain the entire
price away from the odd-block reflection midpoint. Their changing hinge
has a support gap above 36 log units throughout a phase half-width about
0.0582, so the flat-period criterion applies algebraically.

Equal-log growing-count models show the same reinforcement, but are not
actual-prime population certificates. The small literal samples fail the
later reduced-count crop; none certifies current cofinal population mass,
an effective Chebyshev start, or a fraction of the global floor deficit.
Floating kernel underflow is not cancellation. The source hashes and
focused Lean/lint/axiom checks are in `riesz-small-cofactor-audit.json`.

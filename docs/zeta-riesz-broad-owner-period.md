# Consolidating signed period payments across prime-size geometries

The independent whole floor is still open. The reusable mechanism is to
sum the exact two-hinge divisor response and the full factorial weight on
one complete original owner-prime phase period, then use squarefree count
symmetry to price its already-signed cost. Ownership clips must be joined
to the same payment, with their witness positions retained.

Earlier count-uniform payments required every cofactor prime logarithm
in `[H,4H]`. This slice replaces that comparable-size restriction by

```
a < log(q) <= 4H,     5000 <= a <= H,     H >= 10000,
```

where `H` bounds the actual owner-period lower endpoint. The cofactor
prime sizes may now span arbitrarily many logarithmic scales. There is
no upper prime-count bound. These support conditions stay explicit: the
current core does not automatically imply a lower bound on EVERY cofactor
prime merely because its allocation uses physical primes above `N^2`.

`prime_interval_mass_le` uses the already proved actual Chebyshev error
to give a positive reciprocal-prime mass bound with leading coefficient
one:

```
sum_{exp(a)<q<=exp(b), q prime} 1/q <= log(b/a) + 1/a.
```

This bounds cofactor mass after signed owner-period cancellation. It does
not replace the retained arithmetic carrier by a prime-density integral.
Exact squarefree symmetry then costs `M^k/k!`. Summing every selected count
gives `exp(2M)`, and for `M = log(4H/a) + 1/a` the exact bound is
`exp(2M) <= 32H^2/a^2`. Keeping the leading coefficient one is what prevents
the count exponential from undoing the two-power prime-period saving.

`broad_signed_period_with_boundary_floor` joins the complete signed main
and both actually missed ownership sign selections. The latter cost one
original atom, not two. `actual_clipped_witness` preserves the location
of a genuine clipped cofactor prime above the same owner-log scale.
`broad_interval_with_boundary_floor` gives the combined price

```
64544 * H/a^2 * F_N(v)/v.
```

Dyadic owner scales satisfy `sum H_j <= 2v`. Therefore
`broad_radial_supply_floor` bounds ALL selected counts, owner scales and
radial periods jointly by

```
-(129088/a^2) * sum_v F_N(v).
```

The normalization audit in `ZetaRieszSmallOwnerBoundary` identifies an
important limitation: here `F_N(v) = amplitude N v` has degree `N+1`,
whereas `eventually_broad_radial_cost_paid` pays the degree-`N` units
`F_N(v)/v`. Both theorems are valid, but they cannot be composed without
the extra factor `v`. In actual supply units the coefficient is
`129088*v/a^2`, not `129088/a^2`. The latter's convergence to zero for
`a = log(N+1)` therefore does **not** pay this all-radial bound.
No joined `1/256` payment for that main is claimed. The previous
comparable-log bound remains sharper on its own smaller support.

This is a relative signed bound, not source-normalized norm decay. Never
multiply it by the diverging `(2u)^N` envelope. A sharper signed aggregate,
the corrected supply normalization, and a compatible disjoint
complete-fibre cover of the current residual, small cofactor-prime labels,
and other physical/selector holes still require proof before this pays the
whole ledger. The exact radial endpoint and hinge-allocation payments are
separately connected to `polynomialCentralRemaining` in
`ZetaRieszRadialPeriodPayment`.

The optional probe verifies exact finite factorial symmetry on a prime
universe outside the old comparable-log geometry and checks the explicit
prices. Its tiny primes do not meet the eventual Chebyshev threshold; it
certifies neither a floor percentage nor a usable finite starting order.
Focused checks and source hashes are in `riesz-broad-owner-period-audit.json`.
No zero exclusion, RH claim, commit or wider publication checks.

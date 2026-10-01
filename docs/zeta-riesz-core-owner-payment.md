# A source-paid owner sector across the whole core

The numerical `-79/1000-o(1)` floor remains **open**. This result removes
an additional population from the actual remaining signed sum; it does
not close the funding debit, prove a zero exclusion, or measure a percentage
of the global deficit.

`ZetaRieszCoreOwnerPayment` pays every literal core label having a prime
with logarithmic share at least `751/1250 = 0.6008`. The earlier refined
payment reached `601/1000 = 0.601`. The extension uses the same factorial
allocation for all prime counts, total-log periods and phases. Arbitrary
bounded complex selections are allowed, so correlated support masks need
not be removed to spend this payment.

## Actual source-normalized payment

The two exact missing-order binomial tails on the cofactor-share interval
`[7/25,499/1250]` satisfy, for `N>=320`,

```
missingMass <= (9/4) exp(-1033 N/10000000).
```

The fixed upper tilt is `103/100`. A summable reference exponent
`sigma = 1+1/1048576` retains a strict margin over source growth. With
`M_sigma = zetaMoebiusLogMajorantMass(sigma)`, the proved allowance is

```
allowance(N) = (9/4) radiusCeiling M_sigma exp(-N/1000000).
```

`selected_sum_bound` controls the norm of the **actual** normalized sum
by this allowance. `tendsto_core_sub_cropped` then proves decay of the
difference between the full original core and its cropped version on the
original cofinal sequence. No hypothetical-zero hypothesis is used.
The reference mass is finite but has not been numerically evaluated;
the effective starting order is not certified.

## The existing ledger, with no second spend

`eventually_rejoined_floor_without_large_owners` spends the payment on
the precise unresolved population of
`ZetaRieszRejoinedPopulationFloor`. It retains the same four-prime funding
witness, both growing-population prices, signed credits, fixed epsilon
and tail debit. Only a genuinely vanishing absolute error is added.

Every nonzero label in the resulting explicit remainder satisfies

```
squarefree(n),
56 <= omega(n) < 5 log(N+1)+2,
card(cofactorBins(N,n/largestPrime(n))) > floor(log(N+1)/16),
log p < (751/1250) log n for every prime factor p.
```

This unifies the count, bin and owner restrictions in the same signed
floor. It does not imply that the remaining population has small mass
or that its phase contributions cancel. The debit of the funding supply
still cannot be paid independently by a positive polynomial allowance.

The next arithmetic target is joint cancellation across the remaining
counts, share geometries and complete phase periods, retaining both
hinges and the funding balance before taking a one-sided bound.

[Batch catalogue](riesz-growing-floor-catalogue.json) links all 28 modules'
audits and preserves supporting labels outside the active dependency chain.
[Proof audit](riesz-core-owner-payment-audit.json) records the focused
warning-as-error checks, 14 namespace linters and all 18 public transitive
axiom checks. The optional
`scripts/probe_riesz_core_owner_payment.py` diagnoses the binomial rates;
it is outside ordinary builds and CI and is not a carrier certificate.

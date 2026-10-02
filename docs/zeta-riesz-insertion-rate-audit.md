# Genuine-prime rate test for independent insertion capacity

The native floor remains open. This local audit proves that independent
ordinary-prime insertion weights cannot supply the missing geometric rate,
even when the pool contains every available prime and every insertion count
is joined. It does not prove a lower bound for the masked, allocated,
phase-weighted native carrier.

The checked module is
[`ZetaRieszInsertionRateAudit.lean`](../RiemannGaussian/ZetaRieszInsertionRateAudit.lean).
Validation, sources and probe scope are recorded in
[`riesz-insertion-rate-audit.json`](riesz-insertion-rate-audit.json).

## Exact all-count residual

For a finite pool of actual primes `Q`, retain their actual weights `1/p`,
actual logarithms and every Riesz insertion subset. The earlier proved
`response_eq_average` gives

```text
B_Q(d) = sum_{U subset Q} (-1)^|U| (prod_{p in U} 1/p) H_U(d)
       = sum_{V subset Q} BernoulliMass_Q(V) (d-log(prod V))_+.
```

Thus, for `d>0`, the empty channel alone implies

```text
B_Q(d)/d >= prod_{p in Q}(1-1/p).
```

This calculation retains the signed count sum before taking any inequality.
The empty channel is not removed or treated as a paid error.

`log_one_sub_inv_lower` and `prime_empty_mass_lower` prove

```text
log(1-1/p) >= -2/p,
prod_{p in Q}(1-1/p) >= exp(-2 sum_{p in Q} 1/p).
```

The repository's unconditional Chebyshev input
`ZetaRieszOwnerCountEnergy.primeHarmonic_le_loglog` then supplies the deliberately
coarse bound

```text
sum_{p<=X} 1/p <= 8 (1+log(4 log X+8)).
```

For **any** prime subpool `Q subset {p prime: p<=X}` with `log X<=2N+2`,
`prime_pool_empty_mass_order_lower` and `response_order_lower` prove

```text
prod_{p in Q}(1-1/p) >= exp(-16)/(8(N+2))^16,
B_Q(d)/d              >= exp(-16)/(8(N+2))^16.
```

No count ceiling, prime-density approximation, complex phase or physical mask
is silently inserted into these coefficient statements. The pool and positive
hinge may vary arbitrarily with `N`. `arithmetic_response_order_lower` gives
the same bound for the exact squarefree arithmetic cofactor sum when all old
base-prime logs lie beyond the hinge; its squarefreeness hypotheses stay explicit.

## Quantitative verdict

For every fixed `u>1/2` and every fixed polynomial discount `(N+2)^v`,
`response_source_div_pow_tendsto` proves

```text
(2u)^N * B_{Q_N}(d_N) / (d_N (N+2)^v) --> +infinity.
```

`not_frequently_response_source_div_pow_le` rules out a bounded cofinal
subsequence of this model quantity. Joining more independent prime-count
classes or increasing the independent pool cannot turn this mechanism into
a sufficient source-scale saving. Additional fixed polynomial gains do not
change that verdict.

This refutes the **independent coefficient matching** proposal. The native
floor is not refuted: its inventory, owner allocation, radial/factorial
weights, phase, funding and correlated signed remainder were never equated
to this independent model. A useful replacement must use those correlations
and bound their joint contribution, rather than assume product-weight
coverage is nearly complete.

## Genuine-prime numerical diagnostic

The optional
[`probe_riesz_prime_insertion_rate.py`](../scripts/probe_riesz_prime_insertion_rate.py)
uses every genuine prime through each specified endpoint. It has no virtual
log coordinates. At `d=log D`, every positive-hinge subset is exactly a
squarefree integer `n<D` with prime factors in the pool. Relative to empty
mass, its weight is exactly `1/phi(n)`. For `D<=X`, the finite reindex is

```text
B_Q(log D) = prod_{p<=X}(1-1/p) *
            sum_{n<D, squarefree n} log(D/n)/phi(n).
```

Subsets with product at least `D` have exactly zero hinge. All counts remain;
the implementation does not truncate at count10/11 or renormalize probability.
Integer phi and squarefreeness are computed by a sieve. Floating logs/products
are exploratory, not interval certificates or a Lean proof of the Python code.
Five small independent nested signed-subset evaluations check the Bernoulli
and sieve evaluations; these are unit regressions, not unpaid-population scans.

With all78,498 primes through one million, the empty mass is approximately
`0.0406382`. The complete coefficient residual divided by its original hinge is:

| `D` | `B_Q(log D)/log D` |
|---:|---:|
|10|0.0882828|
|100|0.141055|
|1000|0.190042|
|10000|0.237945|
|100000|0.285402|

These finite diagnostics agree with positivity; the asymptotic rate verdict
comes from Lean, not extrapolation. Separate log-domain evaluations of the
proved polynomial lower bound illustrate delayed source regrowth. Those
evaluations do not construct exponential-length prime pools or evaluate the
literal factorial carrier at the stated orders.

Reproduce from `formal/`:

```sh
../.venv/bin/python scripts/probe_riesz_prime_insertion_rate.py
```

No native unpaid records were evaluated, no new native credit was spent,
and no independent floor, ceiling, zero exclusion or RH contradiction follows.
Keep this optional audit outside ordinary builds/CI. Preserve public endpoints,
all earlier positive/no-go results and unrelated staged work; iterate locally.

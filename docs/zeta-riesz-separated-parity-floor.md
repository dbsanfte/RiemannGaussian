# Signed cancellation for widely separated intermediate configurations

The whole arithmetic floor remains open. This module proves a direct
count-free signed floor for the entire retained divisor response of
labels whose background divisor-log translations are separated. It
does not assert that the total price of these labels is source-small.

## What cancels

Let `r,s` be the canonical two least cofactor primes and write

```
a = n / largestPrime(n),
B = a / (r*s).
```

After the exact two-prime finite difference, the whole retained
divisor-antidiagonal response of the SAME original label is

```
sum_{e|B} mu(a/e) * w *
  [tent_(log r,log s)(log n - L - log e)
   -tent_(log r,log s)(log a - L - log e)].
```

Here `w` is the original complex phase/factorial/owner-allocation
weight. Both previously proved zero deletions remain. The two-prime
tent is zero outside `0 < x < log r + log s` and has height at most
`min(log r,log s)`.

If distinct background divisors obey

```
|log e - log f| >= log r + log s,
```

at most ONE background tent can contribute at either original hinge.
`retained_separated_floor` proves, before any count split,

```
Re(entire retained response)
  >= -2 * |Re w| * min(log r,log s).
```

The number of background primes and divisors is absent from the price.
The saving comes from the exact finite differences and their disjoint
support. It is not a selected-mode norm estimate, complete-prime phase
transfer or absolute matching-cost assumption.

## A checkable prime-log condition

It is enough that EVERY background prime satisfies

```
log p >= log r + log s + sum_{q|B prime, q<p} log q.
```

`superincreasing_divisor_log_gap` proves the required separation.
For two distinct squarefree divisors, choose the largest prime at which
their supports differ. Its log dominates the sum of all smaller
differences, leaving the full tent width. Squarefreeness is retained.

`retained_lacunary_floor` applies this actual prime-log certificate to
the original retained label. `global_retained_lacunary_floor` aggregates
all selected original labels, counts and radial periods with their
actual `phaseWeight`. The explicit remaining cost is

```
sum_n 2 * |Re(phaseWeight n)| * min(log(r n),log(s n)).
```

No claim is made that this cost is funded. This removes an exponential
divisor multiplicity; a population estimate or signed prime-period
payment for the remaining weighted sum is still needed.

## Relation to dense clusters

The dense-shell module covers any number of factors on at most
`floor(log(N+1)/16)` occupied logarithmic bins, including the price of
ALL bin patterns. The separated theorem can cover widely spread
configurations with many more occupied bins. Neither implies the other.

Diffuse, overlapping active crossings with both parities still need a
bound on total transport cost. Diffuse crossings with one active parity
need cancellation across labels or prime periods: a universal local
opposite-parity involution is already disproved.

The optional dense-population probe verifies the finite identities on
actual prime supports and checks a growing continuous lacunary family.
It keeps its model/core/fibre claims separate. It is not a numerical
certificate of the whole carrier. See the dense-shell note for the
priority classification of remaining populations.

Focused checks, all seven public transitive axiom checks and source hashes
are recorded in
[riesz-separated-parity-floor-audit.json](riesz-separated-parity-floor-audit.json).
No whole `-79/1000` floor, ceiling, contradiction or zero exclusion is
claimed.

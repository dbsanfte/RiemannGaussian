# Independent signed crossing payment through the cubic prime threshold

This local slice extends an existing **literal signed packet estimate**.
The canonical second-smallest cofactor prime may now be as large as
`N^3`, rather than `N^2`. The numerical whole floor remains open.

The two modules are
[ZetaRieszCubicSieveCost](../RiemannGaussian/ZetaRieszCubicSieveCost.lean)
and [ZetaRieszCubicCutoffRows](../RiemannGaussian/ZetaRieszCubicCutoffRows.lean).
Neither assumes a hypothetical zeta zero or a bilinear cancellation bound.
The radius range remains `1/2 < u <= 10001/20000`; the signed row estimate
uses fixed `|y| >= 54`.

## The actual enlarged population

Write the original label as `n=p*(B*e)`, where `p` is its canonical largest
prime. The frozen squarefree cofactor `B` contains the two smallest
cofactor primes, and the unsigned integer `e` avoids every prime through
the second one. This roughness restriction is retained as an integer
sieve mask, not replaced by a density assumption.

All existing full-row predicates remain:

* `p` is in the original intermediate-prime set; every prime of `B` is
  smaller than `p`, and `p` does not divide `B`;
* the literal core/count selection is evaluated at the same `p*(B*e)`;
* the original radial row covers `1.95N < log(n) <= 2.03N`, with the
  rounded lower endpoint included and paid;
* `log(p*B) <= (39/20-1/2016)*N`, `log(p) < 243N/200`, and
  `2.03N < log(p*B)+log(p)`;
* the canonical cutoff crossing satisfies
  `3899N/2000 < log(p*B) <= 3899N/2000+log(leastPairBlock B)`;
* the original moving Riesz length, hinge, allocation, phase, squarefree
  and physical masks are unchanged.

Only `secondPrime(B) <= N^2` changes to `secondPrime(B) <= N^3`.
There is no fixed bound on the number of cofactor primes.

`quadratic_cutoffRows_subset` proves inclusion of the old selector.
`extraRows` is its exact set difference, and `mem_extraRows_iff` identifies
the new rows by

$$
N^2<\operatorname{secondPrime}(B)\le N^3.
$$

`extraPacket_eq_sdiff` gives the literal original-prime/divisor formula
for that difference. Incidence injectivity, exclusion of the old
owner-gap rows, and non-overlap with the previously cancelled interior,
crossing and affine orbits prevent double spending. The cubic credit
**replaces** the quadratic credit.

## Why the larger cutoff is affordable

The exact sieve intersection factor is

$$
\prod_{q\in F}(1+q^{-\sigma}+q^{-2\sigma}).
$$

The earlier quadratic packet already keeps this factor at `sigma=17/32`.
This slice does not rediscover or credit that result. It uses `sigma=23/32`
and the elementary positive-power sum bound to obtain

$$
\prod_{q\le N^3}(1+q^{-23/32}+q^{-46/32})
\le \exp\!\left(\frac{64}{9}N^{27/32}\right).
$$

No prime-density approximation is used. Primes dividing the frozen
outer product remain separately accounted for by `3^omega(p*B)`; the
existing all-count Euler mass pays their summed cost.

After that outer sum and source normalization, the linear rate obeys
the exact rational inequality

$$
\frac9{64512}-\frac{203}{6553600}-\frac1{10000}
=\frac{9787}{1146880000}>\frac1{125000}.
$$

The sublinear factor is therefore absorbed eventually:

$$
e^{-N/125000}\exp\!\left(\frac{64}{9}N^{27/32}\right)
\le e^{-N/250000}.
$$

`eventually_cubic_cost_geometric` checks this in Lean. It does not certify
a practical finite starting order. The diagnostic sufficient scalar
absorption order is around `10^40`; that number excludes the other
packet constants and is not a certified whole-packet starting index.

The signed density main is joined over its full original row before
being bounded. The exact frozen cutoff multiplier remains in that main.
Only sieve discrepancies, high-count overflow and rounded endpoint errors
are normed. Counts and radial shells are not assigned separate positive
main-term allowances.

## Terminal arithmetic payment and ledger

`eventually_literalCutoffPacket_bound` proves

$$
|u^{N_j+1}\operatorname{literalCutoffPacket}_j|
\le \operatorname{cubicRowBudget}(y,N_j)
+\operatorname{cutoffEndpointBudget}(N_j)
\quad\text{eventually}.
$$

The budget is the existing signed-main saving, plus a polynomial times
`exp(-N/250000)`, the paid high-count tail, and the unchanged endpoint
price. Each tends to zero. Consequently both
`tendsto_literalCutoffPacket` and `tendsto_extraPacket` are independent
source-scale decay theorems for original finite arithmetic sums.

`cubicCentralRemaining_eq_affine_sdiff` keeps the previous exact affine
zero deletions, large-owner credit, owner rows and lower-radial payment.
It replaces only the quadratic crossing packet. The new comparison is

$$
\Re\bigl(u^{N_j+1}\operatorname{joinedPhysical}_j\bigr)
\ge u^{N_j+1}\operatorname{cubicCentralRemaining}_j
-\operatorname{cubicCentralErrorBudget}(y,N_j),
$$

with the comparison error tending to zero and every shared cost charged
once. This is an independent **comparison**, not a numerical floor for
the remaining signed term.

`eventually_cubic_crossing_paid_or_cancelled` also extends reverse
coverage: under the displayed original crossing predicates, every active
crossing with second prime at most `N^3` is either in the independently
paid packet or in a restored exact zero block. Thus an unpaid crossing
in this branch has second prime strictly above `N^3`.

## Numerical regressions and remaining gap

The manual [probe](../scripts/probe_riesz_cubic_cutoff.py) constructs
five- and seven-prime original-core labels at the original dyadic orders
`640` and `1536`. The canonical pairs are respectively
`(409609,409639)` and `(2359303,2359307)`, strictly above `N^2` and below
`N^3`. It keeps their exact integer factorization, original allocation,
full complex phase and clipped divisor block. The row multiplier is one;
the selected signed hinge coefficient is nonzero.

The early native `K/864` crop is empty, so these are regressions of the
original core selector, not tests of the cofinal native cost. The moving
length hypothesis fails at `640` and holds at `1536`; neither order is
certified by the eventual theorem. Source-sized observations are recorded
in logarithms to avoid mistaking underflow for cancellation. Large-prime
tests, logarithms and phases are numerical diagnostics, not certificates.
The probe runs only when requested manually, outside builds and CI.

The whole floor `-399/5000`, the ceiling, and zero exclusion remain open.
This slice does not certify a fraction of the global deficit and does not
bound every label with a prime below `N^3`. It pays the stated complete
crossing packet. Rougher canonical crossings, reflected Riesz-hinge
crossings and other surviving geometries still need a joint signed bound.
The existing native null/tangent credit target remains unchanged.

Validation is local: focused warning-as-error compilation/build,
ordinary-root import with scoped namespace lint, and transitive axiom
checks. No commit, push, wider CI, README or public endpoint change is
part of this iteration.

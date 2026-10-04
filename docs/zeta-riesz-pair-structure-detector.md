# Structure detection on the retained signed pair defect

Local numerical investigation, 2026-10-03. The independent cofinal bound
`Re literalPairDefect <=399/5000+o(1)` remains open. This investigation
adapts the earlier structure-detector strategy to the current two-prime
obstruction; it does not revisit the paid many-prime populations.

The optional [pair adapter](../scripts/probe_riesz_pair_structure.py)
evaluates the literal joined coefficient minus the Selberg coefficient.
It retains the rational damped cutoff, moving Riesz length, original head,
full unallocated correction, finite factorial allocation, physical and
sieve conditions, product phase, and complete-period support. Zero joined
coefficients are not used as a filter: their Selberg defect may be nonzero.
No complete-prime leg limit is transported through a share mask.

## Coverage and validation

The finite branch exhaustively enumerates distinct ordinary-prime products
in the contracted central window at orders 6, 7 and 8: respectively 12,367,
97,714 and 763,194 labels before the complete-period filter. These are
pre-asymptotic checks, not the native cofinal sequence. All their small
cofactors are retained; no eventual polynomial-cofactor payment is applied.

The larger branch uses eight disjoint share boxes at native order 256,
two seeds and 24 proven primes per marginal: 768 accepted prime samples.
Every selected smaller prime exceeds `N^16`. The boxes cover shares near
0.20, 0.255, 0.30, 0.36, 0.40, 0.43, 0.475 and 0.495. They are a small
subset of the retained population, not a cover. FLINT verifies primality;
no Lean primality certificates or certified prime counts are supplied.

Heights 54 and 65 serve as discovery controls; 100 and 142 are held out.
None is asserted to be an ordinate of a hypothetical off-critical zero.
Weights and finite period sums use floating arithmetic; sampled prime
phases are evaluated with Arb. The integer cutoff is not frozen at `2N`.
Empirical bootstraps resample prime marginals separately, and the joint
packet includes stopped-sampling count uncertainty. Cartesian pairs and
repeated height evaluations are not independent observations.

Independent finite-divisor/factorial checks, factorization-based coverage
oracles at orders 3–5, and a comparison with the previous order-6 evaluator
validate the adapter. The previous evaluator agrees at the four heights to
less than `2.5e-17`. These are numerical checks, not a correctness proof in Lean.

## Findings

The actual order-256 boxes have positive defect coefficients at low and
near-balanced shares and negative coefficients through the sampled middle
shares. After joining all eight boxes at their actual phase periods, the
estimated one-sided price falls by about 12.5–46.1% compared with charging
the two coefficient signs separately in each period. This is a finite
partial-packet diagnostic, not a payment against the whole floor.

The exhaustive small-order sums also show why joining before clipping
matters: complete-period aggregation reduces their positive atom prices
by about 98.1–99.86%. These early populations and rates cannot be spent
on the native campaign.

Across the sampled boxes, the leading singular component contains
99.735% to almost 100% of the coefficient matrix's squared Frobenius norm.
Its actual signed contribution dominates the remaining components in all
64 phase cases. Thus the observed cancellation is largely carried by the
weighted prime marginal phases, rather than by a large collection of small
matrix directions. This is an observed finite compression, not a masked
completion theorem. Its error has no proved cofinal source-scale bound.
Every sampled box lies inside complete phase periods, where the period mask
is constant. The compression therefore does not test period-edge crossings.

An initially flagged share-0.43 pattern fails the stricter replication test:
its two exceptional observations occur at different heights. No permutation
flag repeats at the same height across both seeds. The permutation reference
is a diagnostic, not a probability certificate. All 64 marginal empirical
intervals and all eight joined-packet empirical intervals include zero.

The next useful mechanism must control the leading signed contribution
with the original share/period masks, or prove a joint mass/phase comparison
between the favorable middle band and the dangerous positive bands. These
data do not justify deleting that component, completing its prime legs,
assuming orthogonality, or enlarging the samples merely to force a sign.
The detector supplies no cofinal floor credit, zero exclusion or RH claim.

The [arithmetic prime atlas](zeta-riesz-prime-atlas.md) now enriches these
same literal samples with p±1 factor profiles, residue/character colour,
proven neighbour gaps for designated anchors, structural neighbourhoods
and independently controlled feature/phase scans. Its interactive map and
audit preserve the original signed pair weights and receive no floor credit.

## Reproduction

Run from `formal/` using the existing optional analysis environment:

```sh
../.venv/bin/python scripts/probe_riesz_pair_structure.py --self-test
../.venv/bin/python scripts/probe_riesz_pair_structure.py \
  --orders 6 7 8 --sample-orders 256 --size 24 --seeds 731 732 \
  --heights 54 65 100 142 --permutations 127 \
  --output .lake/riesz-pair-structure/scan.json
```

The script resumes its matching prime cache. The adjacent `scan.html` is a
self-contained interactive view of joined boxes, individual boxes and
exhaustive sums. Source and sample hashes, uncertainty, coverage and scope
are recorded in the JSON and [audit](riesz-pair-structure-audit.json).
The probe stays outside ordinary builds/CI and public README/explorer assets.

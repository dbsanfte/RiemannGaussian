# Arithmetic and phase atlas of the unpaid prime-pair population

Local numerical investigation, 2026-10-03. This extends the
[literal pair detector](zeta-riesz-pair-structure-detector.md) with
characteristics of the primes themselves. The independent cofinal bound
`Re literalPairDefect <=399/5000+o(1)` remains open. No floor credit or
zero exclusion is inferred from the atlas.

## Actual arithmetic and retained weights

The optional [atlas script](../scripts/probe_riesz_prime_atlas.py) uses the
same 768 distinct FLINT-proved primes in 16 sampled boxes at native order
256, with seeds 731 and 732. Its 9,216 pair incidences retain the actual
joined-minus-Selberg coefficient, factorial allocation, physical cutoffs,
polynomial-cofactor restriction and complete-period/core masks. All eight
share bands are joined in each seed's partial packet. None is claimed to
cover the remaining carrier. Heights 54 and 65 are discovery controls;
100 and 142 are held-out parameters, not independent new prime samples or
ordinates of hypothetical off-critical zeros.

Each node records the actual prime, full complex phase, residues modulo
8, 30 and 210, Legendre symbols for 2, 3, 5, 7 and 11, digit features, and
exact small-prime valuations of both p-1 and p+1. Trial factorisation stops
at 257; the remaining integer is recorded without declaring it prime.
These are explicit attributes, not an intrinsic "prime quality" ranking.
The five-bit quadratic-character colour and visual phase hue are distinct
from the repository's prime-power/mixed-support arithmetic colour, which
does not distinguish these ordinary-prime legs.

One deterministic anchor in each seed/box/leg block has its previous and
next consecutive prime verified by FLINT. The other recorded spacings are
between accepted sample marks and are labelled accordingly. No Lean
primality or neighbour-gap certificates are supplied.

Every weighted complex pair atom assigns one half to each prime leg.
Summing these charges reconstructs the parent pair sums without double
counting. Relative sample charges and estimated population-scaled charges
are separate fields. The latter inherit the stopped-sampling prime-count
estimates and describe these boxes only; they are not certified whole-floor
estimates. Arithmetic weights and statistical operations use floating
arithmetic; prime logarithms and phases originate in Arb.

## Structure detection and topology

The family-balanced structural neighbour graph is constructed without
phase, signed outcome, prime size, seed or leg role. Its features comprise
the partial p±1 profiles, characters, residue indicators and digit features.
The viewer offers principal and graph projections, log position, literal
pair geometry, phase colour, signed charge colour and arithmetic colours.
Prime/pair selection exposes the underlying integers and masks; the view
supports zooming and panning.

The graph filtration records components and the cycle rank `E-V+components`.
A full-metric minimum spanning tree records single-linkage component
mergers. These are graph/0-dimensional diagnostics, not higher persistent
homology, a large-sieve theorem or evidence of independent prime phases.
Congruence and quadratic-character redundancies can produce clusters by
construction; clustering alone is not new mathematics.

Feature/phase and feature/signed-charge scans include every pairwise
interaction among the eligible scalar features. Controls remove
constant/linear/quadratic log position within each seed/box/leg block.
Permutation references shuffle primes only within the corresponding
log-position quartiles. A maximum-statistic reference adjusts for the
feature/interaction search within each seed/height/target. Candidate
replication requires the same feature and height, matching orientation,
and rank at most 0.05 on both seeds; held-out validation is recorded
separately. Shared-prime Cartesian pairs are never treated as independent
observations.

Phase is exactly determined by log p. These coarse controls do not
condition on exact log position, and the permutation references are
exploratory diagnostics, not certified significance probabilities.
A useful future pattern must explain how arithmetic affects the weighted
distribution of prime log positions, survive independent validation,
and yield an analytic estimate on the original cofinal signed sum.

## Findings and checks

The first scan has 90 nonconstant arithmetic features and 435 scalar
interactions. None passes the adjusted 0.05 diagnostic rank in any
seed/height/target case, so there is no same-height seed-replicated or
discovery/held-out candidate. Residual phase/charge agreement on the
structural graph likewise has no rank at most 0.05. These are negative
findings for this sample and these tests; they do not rule out a different
arithmetic correlation or constitute a quantitative obstruction theorem.

The visible feature bands are explainable arithmetic structure. The first
principal projection is strongly associated with the small-factor profiles
of p±1 and `v2(p-1)`; the second has absolute correlation about 0.942 with
the quadratic character `(2/p)`. For odd primes, one of p-1 and p+1 has
2-adic valuation exactly one, and residues modulo eight determine `(2/p)`.
Thus these bands primarily reflect familiar arithmetic already encoded
in the features. They do not establish phase alignment or new cancellation.
The two projections contain about 10.3% and 8.6% of the structural feature
energy, respectively; they are not a faithful view of every direction.

The ten-neighbour structural graph has 5,140 edges and one connected
component. Its filtration and full-metric MST are saved for inspection.
Thirty-two designated primes have both actual neighbours checked; their
64 consecutive-prime gaps range from 6 to 1,274. An independent replay
also checked 8,375 intervening odd composites. These gap data are not a
whole-population prime-gap estimate.

All 1,536 partial p±1 factorisations reconstruct their original integers.
The atlas reproduces the signed parent pair sums in all 64 cases, with
maximum charge-ledger roundoff below `5.6e-17`. The 128 independent
100-digit phase comparisons cover every seed/box/leg block and differ by
less than `7.4e-17` after conversion
to floating point. Arb enclosure radii are recorded separately from that
conversion error and are rounded upward if binary64 would underflow.
The desktop and narrow mobile viewer checks exercise coordinates, colours,
filters, prime/pair inspection and zoom, with no page errors or horizontal
overflow. See the [scope and validation audit](riesz-prime-atlas-audit.json).

The next arithmetic task is still to control the leading weighted prime
phase contribution with the original share and period boundaries. This
atlas provides no justification for replacing it by independent phases,
deleting a congruence class, completing a masked prime leg, or charging
these finite numerical cancellations against the `0.0798` cofinal target.

## Reproduction

First reproduce the parent detector and its prime cache as described in its
note. Then run from `formal/`:

```sh
../.venv/bin/python scripts/probe_riesz_prime_atlas.py --self-test
OPENBLAS_NUM_THREADS=2 OMP_NUM_THREADS=2 \
  ../.venv/bin/python scripts/probe_riesz_prime_atlas.py \
  --input .lake/riesz-pair-structure/scan.json \
  --output .lake/riesz-prime-atlas/atlas.json \
  --neighbours 10 --neighbour-budget 32 --permutations 255
```

Open [the local interactive atlas](../.lake/riesz-prime-atlas/atlas.html).
The adjacent JSON preserves the complete feature scan, structural graph,
prime data, literal case replays, signed community ledger and source hashes.
The neighbour cache is resumable. The script is optional and is not
imported into Lean or run by ordinary builds/CI. Policy for this workflow is
recorded in [AGENTS.md](../AGENTS.md).

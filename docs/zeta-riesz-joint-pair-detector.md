# Five joint tests of the unpaid signed prime-pair sum

The optional [joint detector](../scripts/probe_riesz_pair_joint.py) tests
the actual signed factorial-prefix weight through five coordinated views.
It retains complex phases and shared-prime correlations, with explicit
matching remainders and literal period masks at cutoff boundaries.

The independent cofinal target remains

$$
\operatorname{Re}D_{N_j}^{\rm prefix}\le399/5000+o(1).
$$

The [global prefix payment](zeta-riesz-pair-prefix-payment.md) already pays
the difference from the original literal defect. This investigation does
not spend that payment again. Its finite sample values are **not in units
of the 0.0798 floor**, and neither small coupling errors nor cancellation
on a sample supplies a bound on the unsampled population.

The [algebraic preflight](zeta-riesz-pair-prefix-convolution.md) now runs
before further statistical discovery. It retains unjoined factorial terms,
matches phase-identical products and swapped incidences exactly, and keeps
different masks and the single square diagonal explicit. The earlier five
scans below remain a snapshot of already-joined samples; they did not explain
which constituent factorial terms cancelled. No new floor credit is assigned.

## Actual-prime coverage and weights

The frozen [sampler](../scripts/sample_riesz_pair_joint.py) supplements the
earlier caches with broader share boxes at `N=640`, balanced boxes at
`N=1536`, and six transition boxes at `N=256`, on seeds 731 and 732.
The complete dataset contains 2,080 distinct primes, 50 boxes and 48,256
sampled Cartesian pair incidences. The broad-band comparisons use 10,240
of those incidences; the remaining boxes test native-order stability and
boundaries. Incidences are reused across heights and frequency offsets.
Accepted primes pass FLINT's proving `is_prime`, after a GMP probable-prime
filter. These are reproducible proven-prime samples, not Lean primality
certificates. Sampling is with replacement; Cartesian pair incidences
sharing one leg are not independent observations.

Every sampled pair is ordered `p>q>N^16`. The polynomial-small population
already paid in Lean is excluded. Exact integer cutoffs determine the
original owner/head/radial flags. The prefix weight includes both binomial
prefixes, order zero, the literal order floor, Selberg subtraction and the
damped moving Riesz length. Off the radial flag it retains the exact
completed-coefficient subtraction. No prime support or density is completed.

Within each box a common positive factorial factor is removed, and the
remaining signed weight is normalized by its sampled L1 mass. Bulk boxes
receive equal weights. This is a discovery convention, not an estimate of
the global carrier measure. Geometry and weights are floating point;
phase argument reduction and boundary period membership use ball arithmetic.
All sampled orders are below the global payment's `N>=65536` threshold.

Regression heights are 100 and 142; existing zero-free regions already
exclude the candidate strip there. Discovery uses exact integer height
`10^10000`, with `10^20000` held out. Every displayed width is below
`1/20000` at the latter heights, so those displayed regions do not exclude
the candidate lower edge there. No tested height is asserted to be a zero
ordinate, and that coverage check is not a new zero-free theorem.

## What each track measures

1. **Joined coefficient bands.** Assemble the positive and negative
   coefficient bands with their full product phases, then examine the
   complex cross term and the joined response. The same known radial
   rotation is removed from all curves for envelope analysis; relative
   phase and cancellation remain unchanged. The raw real response is
   recorded separately. Finite frequency-grid extrema are not uniform
   height bounds, and the raw radial carrier can alias on this grid.

2. **Coupled weighted prime moments.** A finite SVD resolves the sampled
   weight matrix. Each left/right weighted prime moment retains its complex
   phase, and every coupling mode is kept in the exact reconstruction.
   Leading energy and signed remaining modes are reported separately.
   No complete-leg phase limit is substituted through a hard mask.

3. **Fixed-height order stability.** Compare balanced boxes at native
   orders 256, 640 and 1536 at the same fixed height, on both seeds. Dense
   earlier samples remain labelled separately. Differing sample sizes are
   visible; three finite orders do not prove an eventual rate.

4. **Nearby opposite-weight products.** Sort actual products as integers
   and couple only their common positive/negative mass. Keep the entire
   unequal-mass remainder in the signed ledger. Log gaps are computed by
   ball `log1p` of the exact integer ratio. The phase cost is
   `min(2, |y|*|Delta log n|)`, with its trivial cap displayed. Phase-circle
   matching is also recorded, but is outcome-dependent and cannot itself
   provide an independent arithmetic transport theorem.

5. **Transition boundaries.** Sample the exact prefix transition, both
   owner transitions and both radial edges. Use full-precision period
   indices and preserve central labels lost to partial periods. Record
   which side of each actual mask a sample lies on; never fill the boundary
   or apply an eventual estimate below its proved threshold.

Band-coherence reference ranks use 255 shared-leg permutations within
marginal log quartiles. They preserve Cartesian dependence but not the
literal arithmetic characters. These are exploratory diagnostics, not
calibrated population p-values. Same-height replication requires both
seeds; a family adjustment covers the tested order/height combinations.

## Results

All five tracks ran. There is **no new independent signed estimate or floor
credit**. The complete run and independent checks are recorded in the
[scoped audit](riesz-joint-pair-detector-audit.json).

The signed-band result is inconsistent across the tested orders/heights:

| Order | Height | Band coherence, seed 731 | Seed 732 |
| --- | --- | ---: | ---: |
| 256 | `10^10000` | 0.211 | 0.432 |
| 256 | `10^20000` | -0.128 | -0.085 |
| 640 | `10^10000` | -0.252 | -0.278 |
| 640 | `10^20000` | -0.180 | 0.229 |

Negative coherence means opposition between the complex coefficient bands;
positive coherence means reinforcement. Four of the eight order/height
cases oppose on both seeds, but **none is unusual on both seeds under the
shared-leg reference diagnostic**: all family-adjusted replication values
are 1. These reference values are not population p-values. The apparent
discovery-height opposition at `N=640` does not persist on both seeds at
the held-out height.

The sampled weight matrices are locally nearly separable. Their leading
mode contains at least 99.7293% of squared matrix energy at `N=256`, and
at least 99.9999% at `N=640`. The broad-band sampled L1 remainder falls from
about `0.0114..0.0119` to `0.000120..0.000156`. All remaining modes are
retained in the complex response. This identifies coupled weighted prime
moments as a useful diagnostic object; it supplies no bound for a complete
prime moment or the source-normalized population. Balanced signed responses
at fixed height are not monotone across the three tested orders.

Exact-product transport retains common matched mass `0.375` and unmatched
absolute mass `0.25` in the equal-box convention. At both astronomical
heights its geometric phase cost is `0.75`, up to floating rounding: the
trivial cap is exhausted. Outcome-dependent phase-circle matching gives
smaller observed chord costs but retains the same unmatched remainder.
Neither the `0.25` nor `0.75` is a global carrier allowance or a fraction
of the 0.0798 target.

Boundary cases genuinely cross the original masks. For example, at height
100 the upper-radial box on seed 731 keeps 150 of 256 pairs, with 102 outside
the radial flag and four lost to partial periods; seed 732 keeps 189, with
58 outside and nine in partial periods. Independent exact-product replay
agrees on all 48 boundary cases. These losses are never silently filled.

At both astronomical heights, even neighbouring integers below the largest
sampled product cross many full phase periods. This makes the sample's
preasymptotic status explicit. A numerical finding will be promoted only
if it reproduces and yields an estimate with all unsampled labels and
boundaries retained. No cofinal saving follows from a feature flag, finite
matrix factorisation or phase matching alone.

## Precision and validation

Astronomical heights stay exact integers. Argument reduction is certified
before trigonometric evaluation, and binary64 midpoint rounding is reported
separately from the phase-ball radius. The identity for changing height by
a dyadic offset is replayed directly at full precision.

The [independent checker](../scripts/check_riesz_pair_joint.py) replays
boundary membership using `log(p*q)` and integer period endpoints rather
than the detector's sum of leg logarithms. It verifies signed matching
reconstruction, unmatched mass, source pins and all coupling modes. Selected
shifted-height product phases are independently replayed with mpmath and
compared with the Arb balls. mpmath is a regression implementation, not an
interval certificate.

All 48 exact-product boundary replays and 24 shifted-phase replays pass.
Rounded independent phase values agree exactly at binary64 precision.
A separate finite-binomial recurrence, without SciPy's CDF, replays one
coefficient per box: the maximum absolute difference is `8.53e-13`.
Signed matching reconstructs the original sample sum with maximum error
`9.17e-17`. These validate finite calculations, not asymptotic bounds.

The order/height calibration records a conservative lower bound on phase
turns between neighbouring integers. At astronomical heights these finite
orders can lie far before the eventual regime. This prevents a continuous
prime-density explanation being inferred from small-order literal samples;
it does not obstruct an eventual argument at a fixed height.

From `formal/`, run the optional suite with:

```bash
../.venv/bin/python scripts/sample_riesz_pair_joint.py
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 ../.venv/bin/python scripts/probe_riesz_pair_joint.py
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 ../.venv/bin/python scripts/check_riesz_pair_joint.py
```

Sampling is incremental and checks frozen producer/helper hashes. Do not
modify a running producer or repeat a completed primality job unnecessarily.
Artifacts and a standalone interactive five-tab viewer stay in
`.lake/riesz-pair-joint/`. The tools remain outside ordinary builds and CI.
Earlier Lean payments, multiplicity-aware sources and all no-go audits
remain unchanged; there is no new floor, ceiling, zero exclusion or RH claim.

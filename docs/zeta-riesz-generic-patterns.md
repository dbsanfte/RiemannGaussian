# Generic signed-pattern probe, restricted to unpaid support

The optional companion to `probe_riesz_structure_detector.py` accepts arbitrary
positive cofactor-log vectors. It discovers response shapes, exact local
sensitivities and changes under fixed-total interventions without assigning a
known theorem family to the input. It is numerical research, not a bound for
the native floor. The native `nativeCost <= 399/5000` target remains open.

## Spend probe time on the surviving geometry

`scripts/probe_riesz_generic_patterns.py` tests support **before** calculating
subset moments. Its default requires:

- whole-label count at least 56, including the marked owner;
- count below `5 log(N+1)+2` and both original/current native count ceilings;
- more than `floor(log(N+1)/16)` occupied **literal** cofactor bins;
- owner share below `60069/100000`, with canonical-largest ownership;
- the retained core window, phase, physical upper cutoff and allocation.

The bin head is exactly `max(5000, 32 log(N+1))`; bins are half-open in the
same direction as `ZetaRieszFewBinCoverFloor.primeBin`. Log-share spread alone
does not pass this test. The tested models also require every prime log above
`2 log N`: this is a deliberately rough subset, not a claim that the whole
core has that lower support condition. No original core label is deleted
from the mathematical endgame by this probe filter.

The default native index is 1024, where the checked near-critical count
payment applies. Smaller indices can be requested for model regressions;
their reports explicitly say they are outside that eventual regime.
Skipped records keep every failed condition and have no response value.
`--include-paid-diagnostics` is the sole opt-in for paid/out-of-support
examples; they remain excluded from discovery and candidate ranking.
This filter is not a proof that these tests exhaust the native complement.

## Complete signed computation, including uncertainty

The backend `scripts/riesz_subset_moments.py` represents **all** subsets,
both actual parities, and exact multiplicities, first/second moments and
extrema. Its grid partitions subsets; it does not replace their logs by
rounded knots. Crossing intervals use the proved Cauchy and chord bounds in
`ZetaRieszSubsetMomentBounds.lean`, with exact outward rational rounding.

The backend automatically detects a manageable common lattice or a common
lattice with a few exceptional legs; every exceptional subset is retained.
These artificial commensurate inputs are useful regressions, not prime data.
On a full lattice it computes exact coordinate sensitivities by polynomial
division, checking the homogeneous identity independently. Equal gradients
give local fixed-total invariants only up to the next **unsigned** subset
knot. A canceled signed coefficient does not erase that crossing boundary.

For unresolved inputs a second exact backend uses
`F_m(D)=F_(m-1)(D)-F_(m-1)(D-x_m)`. Entire inactive or signed-affine subtrees
can cancel before enumeration. This needs no input-family label. Budget
exhaustion never supplies a guessed sign: the complete moment enclosure
stays authoritative. Response clustering includes the actual two-hinge
target and excludes every ambiguous profile and paid diagnostic. Reported
feature correlations propose hypotheses only.

Exact rational enclosures apply to the supplied finite binary numbers.
Logarithms, phases and binomial CDFs are not interval-certified; the moving
length's separate exponentially small rounding allowance is recorded.
The density-model radial kernel and the literal atom amplitude are labeled
separately. No model score includes a proven prime-population mass or a
source-scale floor credit.

## Focused observations

The 24-case pre-asymptotic unpaid-geometry scan used cofactor counts
55,56,63,96 at native index 64, two seeds and fixed-total interventions.
All subset responses resolved. Two distinct-prime-log model splits changed
sign. A final-source regression at whole counts 57/58 gives the normalized
two-hinge coefficients about `1.4432941` and `-1.2234185`; their joined value
is about `0.2198756`. These share the same total log, owner and phase.
This is a useful signed cross-count lead, not an admissible arithmetic
matching theorem. It does not control the changed allocation or partner
capacity across the original population.

At native index 1024, four unlabelled many-bin inputs at whole counts
56/64 passed the literal masks with 48--53 occupied bins (the paid cutoff
is 45). Their target response was exactly zero for the supplied numbers.
Rather than rescan those gaps, eight stress inputs put a singleton divisor
on either side of the actual `L-log(owner)` hinge. Four responses remained
zero; four were negative, about `-3.66e-22` to `-1.13e-21` after division by
total log. Signed recursion resolved the nonzero cases in at most 143
states while retaining all `2^55` or `2^63` subsets. Three refined targets
agreed exactly at grids 1024 and 4096. This locates active crossings in
those models; it proves no density or source bound for them.

An independent arbitrary-log scan rejects seven paid/out-of-support records
before subset computation. The eight surviving nonlattice profiles remain
unresolved at the chosen budget and are not ranked. Their wide intervals
are a detector limitation, not evidence of zero response or cancellation.

## Reproduce locally

Run from `formal/`:

```sh
../.venv/bin/python scripts/probe_riesz_generic_patterns.py --self-test
../.venv/bin/python scripts/probe_riesz_generic_patterns.py \
  --counts 55 63 --grid 1024 --active-hinges \
  --output .lake/riesz-generic-pattern/eventual-crossing-final.json
```

Use `--inputs-json` for arbitrary records containing `id`, `j` and
`cofactorUnits`. Optional radius, owner-share and total-log parameters are
explicit. `--interventions` adds fixed-total redistributions and distinct-log
splits. `--active-hinges` probes both sides of the actual inner hinge.
Neither probe runs in builds or CI. Source snapshots, report hashes and
focused Lean/algorithm checks are in `riesz-generic-pattern-audit.json`.

The next mathematical step is a signed estimate for the **actual weighted
crossing aggregate**, with partner capacity, allocation/funding differences
and unmatched labels retained. The coefficient profile by itself does not
bound that aggregate, the independent floor, the ceiling or RH.

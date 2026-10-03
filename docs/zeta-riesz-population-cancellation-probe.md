# Population and phase controls for the whole-floor detector

The independent native floor is **open**. This pass improves the numerical
diagnostics; it adds no Lean theorem, native credit, cofinal estimate,
ceiling or zero exclusion. The existing compiled endpoint remains
`ZetaRieszJointNullCredit.native_floor_with_joint_credit`, with the unpaid
target

```text
nativeCost_j - nativeJointCredit_j <= 399/5000  cofinally.
```

Receipts: [numerical audit](riesz-population-cancellation-audit.json).
All previous positive results and no-go audits remain unchanged. Neither
probe runs in builds or CI, and no public endpoint changes.

## Close the prime inventory before interpreting its cancellations

The earlier quantitative-null experiments enumerated subsets of each of
two prime pools separately. They omitted products using primes from both
pools. Their largest-prime shares were at most about 0.35; this misses the
allocation transition and the larger-owner population.

[probe_riesz_closed_inventory.py](../scripts/probe_riesz_closed_inventory.py)
instead enumerates **every** subset of one sixteen-prime union. It retains
the original finite core cuts, full factorial allocation, phase, every
divisor and all complete cutoff periods. The original unit-log corrected
profile is fixed: no coefficient is fitted. Counts, owner-share classes
and pool origins are joined before the positive-part price.

At orders 256 and 640, seed 317, the retained populations have respectively
891 and 1,313 labels; 879 and 1,301 are mixed-pool products. Largest-prime
shares extend to about 0.564. The count range grows from 3–7 to 3–11.
Joining counts cancels roughly 35%–55% of their separately priced debit.
Nevertheless, **adding the mixed products increases the price of the two
pure-pool subfamilies in all six height/order comparisons**, on the same
inventory and common amplitude scale. This is a controlled comparison
inside the new union, not a comparison to the different twelve-prime pools
of the old experiment. Pool closure is not free favorable credit.

These are sparse constructed inventories. They are not density samples.
Their probable primes, floating logarithms, interpolated cutoff edges and
common amplitude rescaling are uncertified. They retain the early original
count ceiling rather than the eventual native crop. No rate or population
bound follows.

## Sample the finite integer population at its actual density

[probe_riesz_factored_population.py](../scripts/probe_riesz_factored_population.py)
uses [Kalai's rejection sampler](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/11/2003-Generating_Random_Factored_Numbers_Easily-SODA.pdf).
An inclusive decreasing integer chain supplies a prime factorization.
Exact integer rejection then gives a uniform integer in each computed
integer bin, **conditional on an exact primality oracle and ideal random
draws**. Inclusive repetitions matter: they retain nonsquarefree integers
before the original squarefree mask is applied.

The program chooses log bins uniformly, then weights each accepted draw
by the integer bin size and number of bins. This estimates the finite
literal signed sum at its population density. It does not manufacture
primes at chosen log shares or replace the prime measure by `dx/log x`.
Both complex phases, the original support and all factorial orders remain
inside the atom. Complete cutoff periods join all retained counts before
their net real contribution is clipped.

The ideal sampler law is checked separately by exact rational recursion
on ceilings 1–32. All 528 individual label probabilities have the expected
reciprocal proposal mass, equal post-rejection mass, and uniform
conditioning on every integer subinterval. Both prime and composite
self-loops are retained. This is a Python rational regression, **not** a
Lean certificate or a verification of large primality decisions.

Frozen accepted labels and factorizations are cached in `.lake`, with
integer product and interval checks, so additional phase diagnostics do
not repeat the expensive sampling. The cache is optional research data.

## Distinguish arithmetic cancellation from sampling and aggregation

Four batches use `N=32,64`, `K=16`, seeds 317 and 919, and 512 accepted
draws each. The original finite masks retain 126–170 labels per batch.
They cover counts 3–10 and largest-prime shares approximately 0.224–0.641.
These are finite library inputs, **not** canonical cofinal native points.
In particular the eventual count crop and source-limit hypotheses are
not applied at these orders.

The raw signed estimates have standard errors comparable to their size.
Their estimated joined positive-part prices are about 0.016–0.065 in
source-normalized finite-population units. These numbers are not upper
bounds or certificates. In the ideal model, convex clipping makes a
sampled price upward biased; sampling error still prevents using an
observed value as a deterministic bound.

Two controls test the proposed cancellation mechanism:

1. **Sample pooling.** Compute the price on each half sample, with its
   weights doubled, then compare their mean with the full-sample price.
   The observed convexity gaps are 15%–88% of the full-sample prices.
   This is sensitivity to sampling, not an arithmetic credit.
2. **Independent phase controls.** Preserve each label, amplitude, mask,
   divisor response and cutoff grouping, but add a separate random phase
   to each label. These altered phases are diagnostic controls only;
   they never enter the proof carrier. Each batch uses 31 phase assignments,
   shared across its three heights: 124 assignments and 372 height
   comparisons, not 372 independent arithmetic populations.

| Order, seed | Height | Observed count saving | Mean phase-control saving |
|---|---:|---:|---:|
| 32, 317 | 54 | 61.7% | 57.8% |
| 32, 317 | 65 | 63.6% | 57.2% |
| 32, 317 | 100 | 65.0% | 56.5% |
| 32, 919 | 54 | 47.1% | 57.5% |
| 32, 919 | 65 | 50.2% | 52.2% |
| 32, 919 | 100 | 46.4% | 55.9% |
| 64, 317 | 54 | 68.8% | 60.8% |
| 64, 317 | 65 | 51.2% | 61.7% |
| 64, 317 | 100 | 62.1% | 61.3% |
| 64, 919 | 54 | 59.5% | 61.7% |
| 64, 919 | 65 | 58.9% | 64.8% |
| 64, 919 | 100 | 66.4% | 63.5% |

Every observed saving lies inside its corresponding 31-control range.
The experiment therefore does **not** isolate an exceptional arithmetic
cancellation mechanism. It does not rule out such a mechanism at other
orders, heights or in the cofinal population. These are descriptive
floating comparisons, not significance tests or rigorous error bars.

## What the proof still needs

The existing signed density-prefix inequality is genuine, but it does
not pay the literal masked variation or the remaining complex moments.
Its real-weight constant-one estimate also has a compiled phase-twisted
counterexample. Neither statement supplies the missing native cost bound.

Further coefficient fitting, sparse-pool cancellation percentages and
small Monte Carlo prices cannot discharge the cofinal target. The next
useful arithmetic mechanism must control a signed correlation of the
**actual** joined prefix with its literal masks. A proof still needs its
quantitative magnitude at source scale. Numerical evidence for a special
phase correlation should be compared with these controls, rather than
identified with the generic benefit of aggregation. No generic PNT/Abel
transport, completion or independence assumption has been inserted.

## Reproduce the diagnostics

```bash
../.venv/bin/python scripts/probe_riesz_closed_inventory.py \
  --orders 256 640 --seeds 317 --heights 54 65 100

../.venv/bin/python scripts/probe_riesz_factored_population.py --regressions-only

../.venv/bin/python scripts/probe_riesz_factored_population.py \
  --orders 32 64 --count-ceiling 16 --samples 512 --seeds 317 919 \
  --phase-null-repeats 31 \
  --output .lake/riesz-factored-population/phase-control-report.json
```

Large primality decisions, bin endpoints, weights, phases, numerical zero
allocation clipping and large-period interpolation remain uncertified.
No exhaustive certification, broader publication gate or commit is part
of this local pass.

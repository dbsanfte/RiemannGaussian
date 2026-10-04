# Pair arithmetic and the unpaid factorial-prefix sum

The optional [pair detector](../scripts/probe_riesz_pair_correlations.py)
tests correlations between the two actual primes in the unpaid
[`prefixPairDefect`](../RiemannGaussian/ZetaRieszPairPrefixPayment.lean).
It found **no feature passing its exploratory maximum-statistic threshold**
on either seed at any tested height. There is no new signed upper bound,
floor credit or zero exclusion.

The independent cofinal target is still

$$
\operatorname{Re}D_{N_j}^{\rm prefix}\le399/5000+o(1).
$$

The [global prefix payment](zeta-riesz-pair-prefix-payment.md) already pays
the difference from the original literal defect. This scan tests the main
sum left unpaid; it does not spend that error payment again.

## Coverage and retained weights

The proven-prime cache has 768 distinct primes, 16 boxes, two seeds and
9,216 Cartesian pair incidences at order `N=256`. The smaller prime is
always above `N^16`, so the already-paid polynomial-small population is
excluded. All products lie in the strict interior of the original radial
band; `interiorLabels_subset_completePeriods` puts them in the retained
complete-period support for every tested height. Period edges and the full
population are not sampled.

The weight uses the exact damped moving length, both literal binomial
prefixes, the Selberg difference and the moving factorial kernel. The
complex phase is exactly `exp(-i*y*(log p+log q))` before numerical rounding.
A common positive radial factor is removed within each box. Each box is
then normalized by its sampled L1 mass and boxes receive equal weights.
These conventions compare correlations; they **do not estimate the global
carrier or its prime population**. Numerical coefficients are floating
point, not certified coefficient enclosures. `N=256` is also below the
global comparison theorem's `N>=65536` threshold.

Earlier atlas heights `54,65,100,142` already have this candidate strip
excluded by existing zero-free regions. They are now regression cases only.
The new discovery heights are the exact integers `10^10000,10^12000`;
held-out heights are `10^20000,10^24000`. Evaluating every displayed
[width formula](zero-free-regions/formulas.json) verifies that its width is
less than `1/20000` there. Thus those displayed regions do not exclude the
candidate lower edge `Re rho=99995/100000` at these heights. This is a
coverage check, not a new region or a claim that any height is a zero
ordinate. Finite tests at these heights do not establish the large-order
behavior for any fixed hypothetical zero.

## What the detector tests

The 70 nonconstant arithmetic features include partial factor profiles of
`p-q` and `p+q`, gcds between `p±1` and `q±1`, equal/opposite residue
classes, both reciprocal Legendre symbols and the Euclidean remainder.
Trial factors stop at 31. An unfactored residual is never declared prime.
Another 96 fixed random Fourier features test nonlinear combinations of
these arithmetic features. All features are constructed without the phase
or desired signed outcome.

The identities `gcd(p-q,p+q)=2` and quadratic reciprocity hold on all
sampled distinct odd primes. They are known finite arithmetic checks,
not newly discovered cancellation in the weighted sum.

Weighted least squares removes both shared-prime marginals and coarse
total-log cells **jointly**. Sequential projections could reintroduce the
first marginal, so the script checks the combined normal equations.
Permutations move leg phases inside marginal log-position quartiles and
preserve the Cartesian shared-prime dependence. Each seed/height uses 255
permutations and maximum-statistic adjustment across all 166 features.
These ranks are exploratory reference diagnostics, not calibrated
population p-values. Exact log position still determines phase, and coarse
controls do not make it independent of arithmetic features.

No adjusted rank was at most `0.05` in any of the 16 seed/height analyses.
There are consequently no same-height seed replications or candidates for
held-out confirmation. This rules out promoting a signal from **this scan**;
it does not rule out an undiscovered arithmetic identity.

Sensitivity controls use the synthetic leg phases
`chi_4(p)*chi_4(q)` in one original constant-sign box per seed. They recover
the quadratic-reciprocity feature on both seeds with adjusted rank
`1/256`, while a phase depending on only one leg leaves correlation below
`1e-14` after the joint projection. These are deliberately constructed
controls, not actual zeta phases or a cancellation theorem. They verify that
the pipeline can retain a known pair interaction rather than projecting
every possible signal away.

## Extreme-height phases and independent validation

The code never converts an astronomical height to binary64. It allocates
`bit_length(y)+1024` precision bits, certifies the integer multiple of
`2*pi`, subtracts it in ball arithmetic, and applies sine/cosine only to the
reduced angle. Direct extremely large arguments can cause Arb to return a
wide trigonometric ball; explicit reduction avoids that behavior.
See [FLINT's precision guidance](https://flintlib.org/doc/using.html).

All recorded phase-ball radii are positive and below `1e-100`; binary64
midpoint rounding is reported separately. The optional
[independent checker](../scripts/check_riesz_pair_correlations.py) replays
24 selected phases with mpmath at 420 extra decimal digits. It checks
350-digit replay values against the Arb balls as well as the rounded
complex values. mpmath supplies independent numerical regression, not an
interval or Lean certificate. The checker also verifies source pins,
coverage, support records, feature counts and projection normal equations.

From `formal/`, reproduce with:

```bash
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 ../.venv/bin/python scripts/probe_riesz_pair_correlations.py
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 ../.venv/bin/python scripts/check_riesz_pair_correlations.py
```

Artifacts stay in `.lake/riesz-pair-correlations/`; the scoped
[audit](riesz-pair-correlations-audit.json) pins them and records the negative
finding. These tools remain optional, outside ordinary builds and CI.
Previous Lean payments, source limits and no-go audits are unchanged.

## Consequence for the next investigation

The tested low-modulus pair arithmetic offers no replicated cancellation
candidate. Do not extend the feature list and count that as a signed saving.
A useful next result must control the weighted prime phase correlations
with their actual log geometry or reveal an exact identity in the joined
prefix weight. Its transport must retain the sampled-out population and
period boundaries. The source/target difference of about `0.000071797`
remains a contradiction margin, not a measured unpaid error.

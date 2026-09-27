# Ordered four/five capacity: exact signed bounds and quantitative test

The target remains an independent cofinal floor for the **whole** joint
carrier. This slice sharpens the attempted payment of its adverse
four-prime, negative-cosine population with unspent favorable five-prime
labels. It does **not** establish that population payment, the joint floor,
or a zero exclusion. The prior exponential-head payment and its signed
complement remain unchanged.

## Exact signed bounds

All theorems are in
[`ZetaRieszOrderedCapacity.lean`](../RiemannGaussian/ZetaRieszOrderedCapacity.lean).
Write `T=log n`. For squarefree `n=p*q*a*r`, `p>q>a>r`,
`positive_four_eq_cap` proves on `0<L<=T`, `2T<=3L`:

\[
(\operatorname{Re}c_L(n))_+
=\frac TL\min\!\left(\log r,
 \left[\min\{L-\log p,T-L-\log q,T+\log p-2L\}\right]_+\right).
\]

`re_four_atom_ge_cap` applies this directly to the original weighted,
phased atom. `positive_four_geometry` proves that a positive coefficient
requires `2L-T<log p<L`, `log q<T-L`, and `log a>(L-log p)/2`.
Thus the second-smallest prime stays away from zero even as the least
share approaches zero.

For squarefree `n=p*q*a*b*r`, `b>=r`, saturation of the small composite
and its three single-prime extensions leaves exactly three pair tents:

\[
\mathcal R_L(n)=
 \operatorname{tent}_{\log b,\log r}(L-\log p-\log q)
+\operatorname{tent}_{\log b,\log r}(L-\log p-\log a)
+\operatorname{tent}_{\log b,\log r}(L-\log q-\log a).
\]

`re_five_atom_eq_three_tents` gives the exact original atom identity.
`pair_tent_eq_cap` evaluates each tent as
`min(log r,max(0,min(t,log b+log r-t)))`.
`re_five_atom_ge_three_caps` gives favorable credit uniformly for an
interval `lo<=L<=hi` on the negative-cosine side. Its first cap is

\[
\min\{\log r,[\min(\mathrm{lo}-\log p-\log q,
                         T-\mathrm{hi}-\log a)]_+\}.
\]

The other caps permute the large primes. The original moment, allocation
and phase remain. Every saturation premise is explicit; no signed
prime-density estimate is assumed.

## Exact integration and relative radial cost

For `0<a<=b<S`, `c=max(a,min(m,b))`, `cap_integral_eq` proves

\[
\int_a^b\frac{\min(x,m)}{x(S-x)}\,dx
=\log\frac{S-a}{S-c}
 +\frac mS\log\frac{b(S-c)}{c(S-b)}.
\]

`cap_integral_le_log` gives the upper envelope `log((S-a)/(S-b))`.
`symmetric_pair_integral` evaluates another harmonic pair integral as
`(2/S)*log((S-a)/a)`. The cap cancellation is retained before integration.
`cap_integrable_zero` and `cap_integral_zero_eq` now also prove integrability
and the exact formula at lower endpoint zero, for positive cap. In that
case `c=min(m,b)`, and the first logarithm is `log(S/(S-c))`.
`cap_integral_le_zero_envelope` bounds every positive arithmetic lower
cutoff by this zero-completed integral. No small-prime mass is omitted.

`cap_integral_mono_parameters` proves enclosure of an entire curved fibre
by parameter and interval endpoints. `five_fibre_lower` retains the moving
large-pair boundary inside the integrand and proves the lower cap/logarithm
budget used by each supply fibre. `four_positive_in_root_box` proves the
outer support restriction for the debit, and `four_cap_density_le` supplies
the coarse-cell bound when the enclosing harmonic denominator crosses zero.

[`ZetaRieszCapacityCheck.lean`](../RiemannGaussian/ZetaRieszCapacityCheck.lean)
connects successful outward-rounded LeanCert computations to these **real
integrals**, with domain checks. Its `first_bin_fibre_credit` proves a lower
budget `11/5000` on the full fibre `2/25<=r<=9/100`, uniformly for
`11/25<=v<=4401/10000` and `27/100<=z<=2701/10000`, using cutoff enclosure
`6827/10000..3433/5000`. This checks one interior cell of the tightest bin;
it is not the complete angular certificate or an actual prime payment.

`log_rational_bounds_sharp` proves rational logarithm bounds: for
`z=(x-1)/(x+1)`, `x>=1`, twice the first `n` odd terms is a lower bound,
and its upper error is at most

\[
\frac{2z^{2n+1}}{(2n+1)(1-z^2)}.
\]

For the original `V_N(T)=exp(-T/2)*T^N/N!`, `radial_kernel_le_exp` proves
`V_N(b)<=exp(|b-a|/78)*V_N(a)` throughout the core.
`radial_kernel_le_phase_arc` proves the factor is at most **501/500** when
`|b-a|<=1/8`: a relative cost of 0.2%. This is not a source-normalized
absolute error or a completed comparison of phase-weighted prime counts.

`cutoff_ratio_variation` bounds the change of `L/T` across the same arc
by `1/(20*N)`. For the **actual moving length**, once `N>=5000`,
`moving_cutoff_stays_in_padded_bin` proves that padding a cutoff bin by
`1/100000` keeps the whole arc, including arcs crossing a bin boundary.
This prevents an unestimated phase-boundary deletion. The numerical test
below includes that padding.

## Whole-cell checks and incidence accounting

[`ZetaRieszCapacityIncidence.lean`](../RiemannGaussian/ZetaRieszCapacityIncidence.lean)
now proves the exact factor **one half** in the ordered-pair credit. The six
ordered incidences count each of the three caps twice.
`re_sum_ge_ordered_pair_credit` applies this to the original finite signed
sum, retaining every unselected label. It cannot create extra supply by
counting the same five-prime label repeatedly.

[`ZetaRieszCapacityCover.lean`](../RiemannGaussian/ZetaRieszCapacityCover.lean)
checks additive bounds over an exhaustive binary cover. Its half-open child
boxes partition the parent exactly. Every cut must lie inside its parent;
zero-credit children remain in the tree. `integrableOn_of_check` proves
integrability, and `integral_bounds_of_check` sums the actual rational leaf
budgets over the complete root.

[`ZetaRieszFourCapacityCover.lean`](../RiemannGaussian/ZetaRieszFourCapacityCover.lean)
proves measurability and bounds for the full four-prime angular density,
including empty fibres, zero caps and coarse cells crossing the apparent
harmonic singularity. `integral_le_of_checked_cover` gives a whole-region
upper bound once the finite checks and total comparison pass.

[`ZetaRieszFiveCapacityCover.lean`](../RiemannGaussian/ZetaRieszFiveCapacityCover.lean)
proves the corresponding lower checker. `pair_geometry` retains the actual
ordering, upper-share and saturation restrictions.
`fibre_eq_half_pair_integral` identifies the density with the symmetric pair
integral, cancelling its factor two with the exact incidence factor.
`fibreExpression_le` bounds each common interval throughout its outer cell;
`expression_le_density` adds all eight adjacent intervals, retaining the
nonnegative exterior pieces. `integral_ge_of_checked_cover` then gives a
whole-region lower bound from a fully accepted tree. Its coarse upper bound
is used solely to prove integrability; it is not a proposed arithmetic
allowance.

These soundness theorems do not by themselves discharge a numerical cover.
The optional generators produce **untrusted candidates**. The checker
elaborates every chunk with `decide +kernel`, then checks an assembly proving
all child-box identities and the exact total. A generator's floating-point
estimate, a passing pilot chunk, or a coarse smoke cover cannot establish
the proposed tight total. These checks run outside ordinary builds and CI.

## Numerical test and remaining proof

The optional deterministic
[`probe_riesz_ordered_capacity.py`](../scripts/probe_riesz_ordered_capacity.py)
uses eight intervals covering the proved moving ratio
`693/1015<=L/T<=139/195`. The four-prime upper model keeps largest share
at most `601/1000` and allows the least share to approach zero. The five-prime
lower model has every share at least `1/100`, largest share at most `1/2`,
and the common three-large/two-small saturated region.

Summing its three symmetric tents first leaves two outer variables: the
sum `v` of two large shares and the third large share `z`. The two-small
integral uses eight fibres and the cap antiderivative. The large-pair
integral uses the symmetric pair formula. The permutation factor `3/3!`
is cancelled by the factor two in that formula. The finite incidence factor
and exact symmetric-pair integration are now proved as described above.
The full prime-population transport is still open.

The [recorded output](riesz-ordered-capacity-probe.json) uses 30,000 active
four-prime cells and 10,000 five-prime cells per cutoff interval. It suggests
a worst supply/debit ratio around **1.0339**, after the interval and log
approximants. These are floating-point evaluations of proposed enclosures,
**not certified integral bounds** for the complete region. The cap checker
and its interior-cell theorem do not yet check this enumeration. The
calculation does not prove an actual prime-sum bound.

A second [unverified run](riesz-ordered-capacity-fast-log-probe.json) uses
only four odd-series terms for lower logarithms and six for upper ones.
Its worst model ratio is about **1.03035**, still above one over all eight
bins. This is a candidate for reducing certificate cost; it is not a second
proved surplus. The precise rational logarithm inequalities are already
proved, but their complete numerical use and angular cover remain unchecked.

The remaining proof must certify the cover and symmetry, transfer the
strict surplus to actual fixed-width prime windows on common negative-cosine
arcs, pay the radial/phase/mask losses, and spend each five-prime label once.
The existing sharp prime-window estimates provide relative population
budgets, not generic source-scale signed PNT transport. All positive-cosine
contributions and other counts remain signed even if this payment succeeds.

Generate and check a complete candidate for the tightest cutoff bin:

```sh
../.venv/bin/python scripts/generate_riesz_four_capacity_cover.py
../.venv/bin/python scripts/check_riesz_four_capacity_cover.py --jobs 2
../.venv/bin/python scripts/generate_riesz_five_capacity_cover.py
../.venv/bin/python scripts/check_riesz_four_capacity_cover.py \
  --directory .lake/riesz-five-capacity-cover --jobs 2
```

Use the pinned `ELAN_HOME` and `--lake` path if `lake` is not on `PATH`.
Each generated manifest identifies its exact rational bin, complete tree,
source hashes and untrusted proposed total. The separate check logs record
actual Lean exit codes. Other cutoff bins and the eventual signed arithmetic
comparison remain distinct obligations.

Reproduce the optional diagnostic, outside ordinary CI:

```sh
../.venv/bin/python scripts/probe_riesz_ordered_capacity.py \
  --output docs/riesz-ordered-capacity-probe.json
../.venv/bin/python scripts/probe_riesz_ordered_capacity.py \
  --log-lower-terms 4 --log-upper-terms 6 \
  --output docs/riesz-ordered-capacity-fast-log-probe.json
```

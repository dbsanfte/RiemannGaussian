# Weighted signed cutoff profiles

The investigation adds checked coefficient estimates, an independent signed
bound for an actual five-prime subfamily, and optional quantitative probes.
**The retained signed prime-sum bound and complementary
floor remain open.** The exact target stays

\[
u^{N+1}\bigl(\mathrm{lowerThresholdPacket}_{3..55}
             -\mathrm{shortOverflowPacket}_{3..13}\bigr).
\]

The [count-boundary continuation](zeta-riesz-cardinality-chamber.md) proves
exact unequal-share coefficients and records a sign transition at the
canonical source ratio. Its complete-count modal probe is diagnostic;
the retained signed bound is still open.

The [proved overflow ledger](zeta-riesz-least-order-boundary.md), earlier paid
errors and every no-go remain valid. Neither displayed term receives a
separate allowance. No zero-free frontier changes.

## Checked arithmetic information

[`four_coefficient_nonneg_lowSupport`](../RiemannGaussian/ZetaRieszCutoffProfile.lean)
proves, for `u>=1/2`, `N>=2`, and every **four-prime** label on the unchanged
`ZetaRieszLeastVariation.lowSupport`,

\[
0\le\operatorname{Re}c_{L_N}(n).
\]

The coefficient is real. Multiplication by the full phase
`exp(-iy log n)` does not preserve this real sign. Original nonnegative
factorial weights remain; no extra mask or zero hypothesis is imposed.

Extract `n=P*a`. The physical cutoff and `P>=sqrt(n)` make the composite
cofactor saturated at the original length, so `R_L(n)=-R_(L-log P)(a)`.
The existing literal length bound and core lower endpoint give

\[
L_N\le2N\log2\le\frac75N,\quad
\log n>\frac{39}{20}N,\quad
2(L_N-\log P)\le\log a.
\]

The three-prime cofactor response is nonnegative below its midpoint.
This proves the four-prime sign directly on the original retained Finset.

The file also records the exact plateau identity `R_D(br)=log r` when `r`
is prime, `br` squarefree and `log r<=D<=log p` for every prime factor `p`
of `b`. This follows from existing extreme-prime deletion at the reflected
cutoff. It is not a new saving: it shows why within-label cancellation
cannot be uniformly small, since the unit middle divisor may survive alone.

There is also a concrete opposing five-prime family.
`five_coefficient_nonpos_core` proves a nonpositive coefficient for
`n=P*r*a*b*c`, with `a<b<c`, under the current core/owner/least/physical
geometry and the additional test

\[
\log P+\log r+\log a\le L_N.
\]

In the ordered factorization, `r,a` are the two smallest primes, so this is
`P*r*a<=X_N`. No prime is completed. For middle logs `A<=B<=C`, the exact
three-prime response on `A<=t<=A+C` is

\[
R_t(abc)=A-\min\{A,(t-B)_+\}-(t-C)_+.
\]

It decreases after `A` and before its midpoint. The small-pair test places
both endpoints `D-log r,D` in that decreasing interval, proving
`R_D(rabc)=R_D(abc)-R_(D-log r)(abc)<=0`. Saturated large-prime deletion
then gives the sign of the original coefficient. The Lean theorem states
every geometric premise explicitly and discharges the midpoint and saturation
from those premises. This is a pointwise arithmetic sign, not a lower bound
for the real phased carrier or a relative population estimate.

## Quantitative two-small-prime compensation

[`ZetaRieszPrimeCompensation`](../RiemannGaussian/ZetaRieszPrimeCompensation.lean)
extends the sign investigation to a magnitude bound. Write
`n=P*r*a*b`, with `n` squarefree, `P,r,a` prime, and `D=L-log P`.
Let

\[
\mathcal T_{r,a}(t)
 =t_+-(t-\log r)_+-(t-\log a)_++(t-\log r-\log a)_+.
\]

This nonnegative tent has height at most `min(log r,log a)`. Under the
arithmetic test

\[
D\le\log p+\log q\quad(p\ne q,\ p,q\mid b\text{ prime}),
\]

every composite divisor of `b` is beyond the cutoff. Lean proves the exact
identity, **before estimating any term**,

\[
R_D(rab)=\mathcal T_{r,a}(D)
       -\sum_{p\mid b,\ p\text{ prime}}\mathcal T_{r,a}(D-\log p).
\]

It includes the three/four-prime cases `b=1` and `b` prime. If additionally
`log r+log a<=D`, the unit tent vanishes. All remaining terms then have
the same negative sign, regardless of prime-count parity. Define the
**actual finite prime set**

\[
\mathcal P=\{p\mid b:\ p\text{ prime},\quad
                   D-\log a\le\log p\le D-\log r\}.
\]

Every member supplies a full `log r` of negative response. With `L>0` and
the saturated largest-prime deletion, the original coefficient satisfies

\[
\boxed{\quad
-\frac{\log n}{L}\,\omega(b)\log r
\ \le\ \operatorname{Re}c_L(n)
\ \le\ -\frac{\log n}{L}\,|\mathcal P|\log r
\ \le\ 0.\quad}
\]

`coefficient_le_neg_plateau_count_lowSupport` proves the upper bound on
the **unchanged retained Finset**, using its canonical largest and least
primes. Saturation follows from the existing owner/physical geometry;
the small-pair and remaining-pair tests stay explicit. The bound from below
follows from `norm_coefficient_le_prime_count`. Thus the magnitude costs
one least-prime logarithm per remaining prime, rather than a separate
allowance per middle divisor. This is a quantitative arithmetic coefficient
estimate, not a bound for its real part after multiplication by
`exp(-iy log n)`.

The optional [compensation probe](../scripts/probe_riesz_prime_compensation.py)
checks the exact tent identity and measures its coverage in the same
ordinary-density model. At `u=10001/20000`, 4096 Sobol points and three
scrambles per count give these fractions of the model's **negative
coefficient mass**:

| Order | Five primes: both tests | Six primes: both tests |
| --- | ---: | ---: |
| 256 | 97.16% | 95.85% |
| 512 | 98.42% | 97.76% |
| 1024 | 99.05% | 97.93% |

The simpler integer plateau count accounts for only about half the negative
mass at order 512. The fractional tent shoulders therefore matter to a sharp
comparison; retaining the exact tents is preferable to replacing them by
plateau counts alone. These percentages do not prove arithmetic coverage.

## Proved actual opposing supply, including phase

[`eventually_retained_positive_supply`](../RiemannGaussian/ZetaRieszCompensationSupply.lean)
goes beyond the density model. Choose five **ordinary primes** in fixed-width
logarithmic intervals with slopes

\[
(\log r,\log a,\log b,\log c,\log P)
 \simeq N\left(\frac1{25},\frac1{10},\frac{11}{50},
                    \frac{27}{50},\frac{11}{10}\right).
\]

Only the largest-prime interval receives a bounded translation. The actual
integer is squarefree, its prime count is exactly five, and its total logarithm
is `2N+O_y(1)`. At the original moving length the exact coefficient is

\[
c_{L_N}(n)=-\frac{\log n}{L_N}\log r,
\qquad \operatorname{Re}c_{L_N}(n)\le-\frac{2N}{35}.
\]

The proved prime number theorem supplies at least `c exp(2N)/(N+1)^5`
**distinct actual integers** in each box, uniformly over bounded translations.
For each fixed `y!=0`, a bounded translation makes `cos(y log n)<=-1/2`
throughout the box. The phase is evaluated at the actual product; no phase
freezing or transport approximation is made. Existing factorial concentration
shows that the **original correlated rectangle weight** is at least `1/2`
eventually on every such label. Low orders are still present.

Lean discharges squarefreeness, count, physical prime thresholds, nondominant
and allocation-sector deletions, the core window, and the share interior:
the whole box is a subset of the unchanged `lowSupport` on the original
dyadic schedule. Therefore, for `1/2<u<=10001/20000` and each fixed `y!=0`,
there are `k=k(u,y)>0` and boxes `B_j` with

\[
\boxed{
\operatorname{Re}\!\left[
 u^{N_j+1}\sum_{n\in B_j}W_{N_j}(n)c_{L_{N_j}}(n)
       \frac{(\log n)^{N_j}}{N_j!}n^{-3/2-iy}
\right]
\ \ge\ k\,\frac{(2u)^{N_j}}{(N_j+1)^6}
}
\]

eventually. Here `W` is the existing `ZetaRieszJointBoundary.weight`; it
is not replaced by one. The constant and starting index are existential,
not explicit finite-order numerical certificates. No hypothetical zero is
assumed. This is an independent signed estimate for a genuine suballocation.

**What this resolves:** opposing supply exists in the actual arithmetic
population, with favorable phases and the retained factorial weight.
**What it does not resolve:** this is not the whole five-prime class, and
the remaining labels can contribute with either sign. No lower bound for
their joint sum follows by dropping them. The target remains
`lowerThresholdPacket(3..55)-shortOverflowPacket(3..13)`, followed by the
complementary carrier's independent floor. The new subfamily cannot be
counted a second time as a free reserve.

The subsequent [minimum-collision audit](zeta-riesz-minimum-collision-audit.md)
checks a specific remaining correlation. Its exact two-chamber model and
positive rate budgets do not yet prove survival or cancellation of a term in
the full joined response.

The [joined head and precision audit](zeta-riesz-joined-head-audit.md) now
proves exact cancellation of the one-cofactor head across both factorial
boundaries, including its actual two-prime arithmetic counterpart. Direct
100-digit convolution checks expose the limits of the high-order numerical
probe. The full signed estimate remains open; apparent million-order growth
from under-resolved quadrature is not accepted as a mathematical result.

The subsequent [least-prime duality applicability audit](zeta-riesz-duality-transfer-audit.md)
checks recent Alladi/Tenenbaum/Wang results and the hybrid Euler--Hadamard
formula against this same target. Lean rules out paying the source with
the stated duality allowance even with an adaptive auxiliary cutoff, and
audits every order in the displayed fixed-height hybrid error envelope.
These are limitations of those proposed inputs, not bounds or divergence
theorems for the retained signed prime sum.

The optional [actual-prime regression](../scripts/probe_riesz_compensation_supply.py)
and its [report](riesz-compensation-supply-probe.json) construct chosen Proth
prime examples at orders 1024 and 2048 and heights 54 and 100. Primality
witnesses are checked with exact integer arithmetic; logarithms, phases and
binomial weights are high-precision or floating-point regressions, not
interval certificates. Population supply comes from the Lean theorem,
not these selected examples. The probe stays outside ordinary CI.

## Weighted profile experiment

With `n=P*r*b`, `T=log n`, `D=L-log P`, `h=log r`, the finite identity from
the [anatomy audit](zeta-riesz-label-anatomy.md) is

\[
c_L(n)=\frac{T}{L}\int_{D-h}^{D}M_b(t)\,dt,
\qquad M_b(t)=\sum_{d\mid b,\ \log d\le t}\mu(d).
\]

[`probe_riesz_signed_cutoff.py`](../scripts/probe_riesz_signed_cutoff.py)
measures this staircase, its signed integral, the integral of its absolute
value, and the earlier termwise divisor allowance. It checks the integral
against the independent finite clipped-hinge sum. Every distinct marked
prime is included. Counts below 14 keep both least-order endpoints; counts
14 and above keep the lower endpoint. These are the exact finite multinomial
marginals of the current target, evaluated numerically without a normal
approximation. The old allocation factor has already been independently
paid at this target.

The [JSON report](riesz-signed-cutoff-probe.json) separates two experiments.
The first uses **ordinary-prime density** `dp/log p`, with full phase, moving
integer-floor length, core window, physical endpoints, owner/least-share
interior and exact factorial probabilities. It is not an exposed-zero model:
no factor `(-1)^omega` is inserted. It evaluates counts 3--14 at
`N=256,512,1024`, using 4096 Sobol points per count and three independent
scrambles. **It does not evaluate the Lean Finset, prove prime-density
transport, or bound the omitted counts 15--55.**

At `N=512`, the scramble averages in the nonoscillatory (`y=0`) model are:

| Operation | Approximate model mass |
| --- | ---: |
| Absolute values before the middle-divisor sum | `0.108` |
| Absolute value after the signed staircase, before integration | `0.0159` |
| Absolute value after each complete profile integral | `0.0154` |
| Signed sum of all modeled counts 3--14 | `0.00051` |

Divisor signs save a substantial factor. Further integration within each
individual profile saves only a few percent. The next large saving is
**across labels and prime counts**:

| Prime count | Mean signed model contribution, `N=512`, `y=0` |
| --- | ---: |
| 3 | `+0.002827` |
| 4 | `+0.002617` |
| 5 | `-0.002310` |
| 6 | `-0.002677` |
| 7 | `-0.000378` |
| 8 | `+0.000332` |

This is not alternation by count parity. Three/four-prime labels reinforce
when their phases agree. Counts five and six supply the principal opposing
model mass; later counts still matter to the residual.

![Signed count contributions and the joined weighted cutoff profile, ordinary-density model only](riesz-signed-cutoff-profile.svg)

The proved small-pair condition contains about 96.7%, 98.3%, and 99.0% of
the model's **negative five-prime coefficient mass** at orders 256, 512,
and 1024 respectively, averaged over the three scrambles. These are model
coverage diagnostics, not coverage estimates for actual primes. They identify
a simple sign-certified family for an arithmetic supply estimate; they do not
justify truncating the full count sum.

| Order | Signed total range across scrambles, `y=0` |
| --- | ---: |
| 256 | `0.000667..0.000673` |
| 512 | `0.000441..0.000567` |
| 1024 | `0.000321..0.000820` |

These ranges are convergence diagnostics, **not rigorous error bars** or an
asymptotic rate. Values at heights 54, 60 and 100 retain their full phase
but vary substantially between scrambles; no floor is inferred from them.
The small `y=0` residual cannot be used at a hypothetical zero's ordinate.

### Resolving the radial oscillation in the model

The [new report](riesz-prime-compensation-probe.json) also removes radial
Monte Carlo noise. For each sampled share configuration it first integrates
the full phase over

\[
\max\{1.95N,2\log(N)/r\}<T<\min\{2.03N,L_N/P\},
\]

where `P,r` here denote the largest/least **log shares**. Each signed divisor
term has physical-log profile `min(r*T,(L_N-alpha*T)_+)`; its two breakpoints
are integrated using integer incomplete-gamma antiderivatives.
At nonzero heights the finite endpoint expansion is truncated after 24 terms
with an explicit geometric series-tail bound. Eighteen independent
90-digit incomplete-gamma checks agree within `1.1e-14` absolute error.
Floating-point rounding and the remaining share quadrature are **not**
interval-certified.

All distinct marked incidences, finite factorial probabilities, moving
integer-floor length and original lower-minus-short-overflow weight remain
inside this ordinary-density integral. It does not model exposed-zero
prime phases and does not reopen the failed masked-mode radial rescue.
For modeled counts 3--14 at height 54, the source-normalized complex norms
range across three scrambles as follows:

| Order | Model norm range |
| --- | ---: |
| 256 | `6.65e-7..7.30e-7` |
| 512 | `3.77e-7..4.59e-7` |
| 1024 | `1.63e-7..2.49e-7` |

The oscillatory model is substantially smaller and better resolved than
the previous direct radial sampling suggested. These finite observations
give neither an asymptotic rate nor a bound for the actual prime measure.
The arithmetic discrepancy and counts 15--55 are still unpaid.

Reproduce the optional diagnostics with:

```sh
.lake/plot-venv/bin/python scripts/probe_riesz_prime_compensation.py \
  --orders 256 512 1024 --power 12 --seeds 3 --max-count 14 \
  --output docs/riesz-prime-compensation-probe.json
```

The second experiment constructs actual Proth primes at randomized log
targets: 96 labels over counts 3--14 at orders 256 and 512, with exact modular
primality certificates. Distinctness, products
and the explicitly listed geometric masks are checked. Transcendental
formulas use 600-digit arithmetic; factorial probabilities use floating
point. These selected integers are **not a representative prime population**;
the script does not certify membership in the original Lean Finset.

At `N=256`, certified five-prime products give `c_L(n)/log n` approximately
`+0.04707` and `-0.04151`. The positive example is a plateau with shares
about `.55364,.17172,.12608,.11714,.03142`. Thus five-prime labels do not
have a universal negative coefficient. Exact factors, certificates, full
phases and all marked weights are recorded in the report.

## Remaining arithmetic task

A useful theorem must compare the **joint weighted cutoff imbalance** of
the actual cofactor population. Keep the canonical least prime, marked
factorial weights, original support and `exp(-iy log n)` while comparing
positive three/four-prime mass with mixed-sign five/six-prime and higher-count
mass. The two-small-prime result gives a concrete negative magnitude through
actual prime windows, and identifies the fractional shoulders a comparison
must retain. It does not estimate the supply of those labels or their phased
balance against the positive unit response. Neither the new coefficient
bound nor the improved density probe proves the joint signed estimate.

Existing prime-replacement and mass-transport identities already retain the
needed phases. Their missing quantitative supply/coverage estimates remain
missing. Do not replace the profile by another unsigned divisor allowance,
assume alternating prime-count signs, truncate the unpaid tail, or invoke
generic absolute PNT/Abel transport. The earlier signed target is unchanged.

Run this optional investigation outside ordinary CI:

```sh
OPENBLAS_NUM_THREADS=1 .lake/plot-venv/bin/python \
  scripts/probe_riesz_signed_cutoff.py --orders 256 512 1024 \
  --power 12 --seeds 3 --max-count 14 --certificate-cases 4 \
  --output /tmp/riesz-signed-cutoff.json
```

`--resume` retains completed diagnostics after interruption and records
previous producer hashes. No exhaustive certification workflow is invoked.
The chart is reproduced by `scripts/plot_riesz_signed_cutoff.py --input
docs/riesz-signed-cutoff-probe.json --output docs/riesz-signed-cutoff-profile.svg`.

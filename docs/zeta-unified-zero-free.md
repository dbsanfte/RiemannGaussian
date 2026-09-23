# Complete explicit zero-free coverage

The current endpoint is
[ZetaUnifiedZeroFree.exact_strip](../RiemannGaussian/ZetaUnifiedZeroFree.lean).
It retains the earlier signed-pole and iterated-reserve exclusion alongside
both Gaussian components. Every nontrivial zero satisfies
`d(t) < Re(rho) < 1-d(t)` **at every ordinate**. Literal right-edge
nonvanishing includes the closed boundary and explicitly excludes `s=1`.

This repairs a coverage omission: the latest Gaussian curve had a better
large-height coefficient, but was smaller than an earlier proved region at
modest heights. Combining those already proved analytic bounds is a
restoration of the repository's full strength, not a newly discovered
literature result. The Gaussian component still supplies the strict
improvement over the compared benchmark envelope in its checked interval.

## Exact formula and containment

Write `L=log(abs(t)+2)`. The width is the maximum of:

| Component | Width | Analytic proof |
| --- | --- | --- |
| Signed pole | `792/(7625*L-2000)` | [Signed-pole theorem](../RiemannGaussian/ZetaSignedPoleZeroFree.lean) |
| Iterated reserve | `min(4/39,4752/(45750*max(13/10,L)-35725))` | [Reserve iteration and fixed point](../RiemannGaussian/ZetaPoleReserveBootstrap.lean) |
| Retained Gaussian cost | `min(1/450000,221/(250*(L+2052*log(L)+30240)))` | [Retained cost region](../RiemannGaussian/ZetaGaussianRetainedRegion.lean) |
| Smaller Gaussian dilation | `min(1/40500,1547/(1800*(L+1995*log(L)+29400)))` | [Expanded region](../RiemannGaussian/ZetaGaussianExpandedRegion.lean) |

The complete formula is proved by `width_eq_max`. The Gaussian analytic
proofs require `abs(t)>=1000000`. Below that height, their entire physical
cap `1/40500` is strictly smaller than the old reserve. Thus the elementary
maximum remains valid globally without pretending to extend the Gaussian
analytic estimates below their actual domain.

`gaussian_width_le` and `reserve_width_le` are explicit containment guards.
`width_eq_reserve_of_low_height` proves exact equality with the reserve
below the Gaussian threshold. On the comparison interval now extended to
`L_* < log|t| ≤ 480000`,
[`ZetaGaussianExpandedComparison.nonvanishing_and_comparison`](../RiemannGaussian/ZetaGaussianExpandedComparison.lean)
proves both literal nonvanishing on the
**entire combined edge** and strict domination of the headline envelope.
The eventual log-log component and the new
[proved Vinogradov–Korobov component](vinogradov-zero-free.md) join by
their maximum in `ZetaVinogradovSummedZeroFree.exists_eventual_union`.
Both eventual starting thresholds remain unevaluated. The explicit
region in this document retains its validity at every height.

## Original arithmetic consequence

[SquarefreeUnifiedRegion](../RiemannGaussian/ZetaSquarefreeUnifiedRegion.lean)
sets `m(y)=d(2*abs(y)+3)` and `R(y)=1+m(y)/2`. For **`abs(y)>=3`**, the
literal squarefree quotient is analytic on a neighbourhood of the complete
closed radius-`R(y)` disc at `3/2+i*y`. The same disc supplies the original
marked-response bound with the full signed two-harmonic prime envelope.

The proof checks the entire doubled window, uses the actual zero-height
floor, preserves both poles, and retains a center-dependent response
constant. `gaussian_radius_le` proves that no earlier Gaussian radius is
lost. This removes the inherited `500002` center-height requirement from
this transport; it does not prove the independent cofinal signed prime floor.

## Remaining benchmark coverage work

The target is pointwise coverage of every applicable benchmark in the
[audited literature table](zero-free-literature-frontier.md), including its
height range, strict or closed edge, source version and proof status.
Full coverage has **not** been achieved.

The restored reserve substantially improves the low-height part of the
picture. The inspected classical and Littlewood regions can still be wider
there. The [complete VK chain](vinogradov-zero-free.md) now includes
quantitative high-moment control, logarithmic exponential-sum saving,
near-one zeta growth, a paid zero detector and a joint height schedule.
Its classical-power width eventually strictly exceeds every fixed
earlier log-log coefficient, as a compiled comparison proves.
Its coefficient is still far weaker than the published VK benchmarks,
and its starting height is unevaluated. Sharpening those constants and
evaluating the coverage thresholds are the remaining quantitative tasks.

Externally verified RH up to height `3e12` is a separate substantial
certification target if the scope includes that finite-height result.
An external theorem must be formalized or verified before it can join the
kernel-checked endpoint. A comparison between formulas is insufficient.

The [evergreen picture](zero-free-regions/README.md) reflects the current
complete explicit formula. Its overview includes remaining gaps, and its
grey comparison band shows the newly proved extension through log-height
480000. This is a certified interval, not a claimed maximal comparison range.

# The full physical endgame

The unmatched saturation boundary is eliminated. The independent arithmetic
floor and ceiling remain open. The new ordinary-root modules are
[`ZetaRieszJoinedPhysical`](../RiemannGaussian/ZetaRieszJoinedPhysical.lean) and
[`ZetaRieszPhysicalCellFloor`](../RiemannGaussian/ZetaRieszPhysicalCellFloor.lean).

The existing `joinedPhysical` is unchanged. Its checked source is

\[
u^{N_j+1}\operatorname{joinedPhysical}_j
\longrightarrow -m+m^2c_{\rm ret}(u),
\qquad \tfrac12<u\le\tfrac{10001}{20000}.
\]

`tendsto_joinedPhysical_exact_source` retains the exposed-zero assumptions
and the actual analytic multiplicity. The three direct conditional endpoints
`false_of_joinedPhysical_cofinal_floor`,
`false_of_joinedPhysical_cofinal_ceiling_of_multiple` and
`false_of_joinedPhysical_cofinal_bounds` require independent arithmetic
inequalities. The floor is `-79/1000-o(1)` for simple zeros; the ceiling is
`3/2+o(1)` for higher multiplicities. Neither premise is discharged here.

## Both hinges on every original core label

Write `p = largestPrime n`, `a = n/p`, and retain the original length `L`,
prime set `A`, and allocation `boundedShare A N n`. Prime deletion proves

\[
F_N(n)=\frac{N+1}{L}(1-\operatorname{boundedShare}_N(n))
\left[R_{L-\log p}(a)-R_L(a)\right]K_{N+1}(s_0,n).
\]

`residual_atom_two_hinges` identifies this with the original residual atom.
It works at arbitrary complex `s`, without saturation or a replacement
phase. `core_eq_fullTranslated` consequently proves the exact equality

\[
\operatorname{coreResponse}_N
=\sum_{n\in\operatorname{coreBand}_N,\ n\text{ squarefree}}F_N(n).
\]

Only zero nonsquarefree coefficients are removed. Every remaining original
radial, count, allocation, ownership and physical condition stays in place.
In particular, labels outside the previous matched prime band are included;
their signed contribution is not asserted negligible.

For `L >= 11N/8`, `joined_fullTranslated_bound` gives

\[
\left\|u^{N+1}\left(\operatorname{joinedPhysical}_N-\sum_nF_N(n)\right)\right\|
\le 2(19/20)^N M(257/256).
\]

The constant is the existing summable Möbius majorant mass.
`tendsto_joined_sub_fullTranslated` proves decay with arbitrary moving
heights and counts along growing orders. Thus there is no additional
anonymous saturation/mask boundary to pay. The rectangle occurs only in
the proof of this already-paid difference, not in the full main sum.

## Signed divisor cancellation remains the arithmetic problem

`riesz_difference_eq_clipped` proves exactly

\[
R_{L-\log p}(a)-R_L(a)
=-\sum_{d\mid a}\mu(d)\min\{\log p,(L-\log d)_+\}.
\]

The interval lengths are nonnegative; their Möbius-weighted sum need not
be. The original phase must also remain correlated with this sum. Existing
complementary-divisor reflection therefore does not provide a pointwise
floor. No new sign is inferred from the clipped notation.

`all_count_two_hinges` applies the finite Euler-boundary identity to both
hinges together, including its exact empty-middle subtraction. Its weights
are Euler odds. This is not an identification with a sharply masked literal
core: the original allocation, radial cut and label-dependent support may
not be pulled through it. Such a substitution would need a separate proof.

The existing exact cancellation for at least three reflected-large primes
and at least five total primes applies to the whole full-mass atom.
`core_eq_fullTranslated_without_three_outer` removes that zero sector
exactly on the core for `u >= 1/2`, `N >= 2`. It reuses an existing saving;
it does not spend its credit twice or solve the remaining sectors.

## An explicit weaker sufficient cell saving

`physicalCellBand` groups the original squarefree core by
`k <= log n < k+1`. `physicalCell` divides the entire signed sum of
`F_N(n)` by the positive scale

\[
E_{N,k}=\frac{(k+1)^{N+1}}{(N+1)!}e^{-3k/2}.
\]

`core_eq_physicalCells` reconstructs the full core exactly. No norms or
countwise bounds enter that identity. Suppose, as an **open arithmetic
hypothesis**, that the assembled cells satisfy

\[
\Re\mathcal T_{N,k}\ge
-C(N+1)^A e^{(1-\delta)k}.
\]

`scaled_core_floor_of_cells` then proves

\[
\Re\left(u^{N+1}\operatorname{coreResponse}_N\right)
\ge -3Ce^{1/2+\delta}(N+1)^{A+1}
\left(\frac{u}{1/2+\delta}\right)^{N+1}.
\]

Any fixed `delta > u-1/2` gives a vanishing lower error.
For `delta=1/10000`, Lean checks the uniform endpoint ratio

\[
\frac{10001/20000}{1/2+1/10000}
=\frac{10001}{10002}<1.
\]

`eventually_joinedPhysical_floor_of_cells` includes the geometric boundary
error and gives the requested floor under precisely this one-sided cell
hypothesis. `false_of_physicalCell_saving` connects it directly to the simple
exposed source. The old `LocalizedTypeIIBound` is unchanged. These are
conditional reductions, not an arithmetic power saving or a zero exclusion.

The remaining task is an independent signed inequality on these full cells,
or a weaker aggregate inequality retaining their phase-period cancellations.
There is no current proof that the clipped Möbius response satisfies either.

## Local floor iteration: evaluated reflected prefixes

[`ZetaRieszSaturatedCoreFloor`](../RiemannGaussian/ZetaRieszSaturatedCoreFloor.lean)
now improves the finite independent lower estimate for the whole core and
`joinedPhysical`. The numerical `-79/1000` floor remains open.

Put `D=log n-L`, let `a` be the product of prime factors below `D`, and let
`b=n/a`. When `a` is composite and `log a<=D`, the original coefficient is
exactly zero. The new `coefficient_eq_zero_of_reflectedPrefix` also checks
the shorter cutoff `v=L-log b`: if the primes of `a` below `v` form a
composite product whose logarithm is at most `v`, the entire label again
vanishes. This second cancellation has no restriction on the original
outer-prime count and works at every phase.

For exactly two outer primes, the total-count parity cancels exactly:

\[
c_L(n)=-\frac{\log n}{L}R_v(a).
\]

If `v/2<=log(minFac a)`, no composite divisor enters below `v`, giving

\[
R_v(a)=v_+-\sum_{p\mid a}(v-\log p)_+.
\]

`coefficient_two_outer_prime_prefix` evaluates this signed expression for
every total prime count. Three actual prefix primes with
`log p<=2v/3` already exhaust the unit hinge. Thus their full physical atom
is nonnegative whenever its original cosine is nonnegative
(`fullTranslatedAtom_nonneg_of_three_prefix`). This is a geometric
all-count sign criterion, not a separate allowance for each count.

`combinedFloorCost_le_quarter` carries the earlier inner-gap saving into
the whole estimate: if `4v_+<=log(n)/omega(n)` and
`v<=log(minFac a)`, the new adverse cost is at most one quarter of the old
SignedSperner cost. This relative saving applies only on that sector; it
does not mean a quarter of the global RH budget has been paid.

`joined_floor_combined` retains every favorable real observation and
intersects the new charges with the older reflected/complementary-divisor
charges on their valid core support. Its only transfer error is the
already-proved `2*(19/20)^N*M(257/256)`. The remaining signed aggregate
still requires a cofinal numerical bound, especially across the surviving
balanced triples and other unsaturated geometries.

The optional `scripts/probe_riesz_reflected_prefix.py` checks direct divisor
enumeration against these formulas on actual distinct prime labels at
orders 512, 640 and 1027. It keeps the exact integer-dependent length and phase.
It is not a prime-population estimate, a proof of every inherited core
mask, or a source-scale certificate. Wider project/publication checks are
deferred during the current local floor iteration.

## Spending the cutoff savings only on the unpaid remainder

[`ZetaRieszJoinedPrefixFloor`](../RiemannGaussian/ZetaRieszJoinedPrefixFloor.lean)
connects the evaluated cutoff cancellations to the strongest existing
compensated floor. It starts from
`ZetaRieszSevenCountTail.eventually_core_full_floor`, preserving the balanced
triple, small-prime head, four/five/six-prime and count-tail payments and
their full radial boundary treatment. The unspent four-prime supply is
**1/64**, not the quarter retained in an earlier ledger.

For the exact unpaid remainder `E`, write `B(n)` for the already optimized
`SevenPrimeReflection.floorCost` and `F(n)` for the new prefix/saturation
cost. The additional saving is

\[
G_N=\sum_{\substack{n\in E\\\omega(n)\ge7}}
 w_N(n)\max\{B(n)-F(n),0\}\ge0.
\]

`eventually_joined_floor` proves that the old compensated observation plus
`G_N`, with its original source normalization and a vanishing boundary
error, is a lower bound for the actual `joinedPhysical`. Counts below
seven in `E` remain signed and exact. The earlier seven-prime saving is
already inside `B`; it is not spent a second time. Thus this theorem does
not replace the paid-sector ledger with a weaker whole-core majorant.

There are explicit savings against this stronger baseline:

- Either exact saturation returns the entire old adverse charge.
- A nonpositive prime-prefix response on a nonnegative cosine phase also
  returns that entire charge, while the favorable observation remains.
- On the seven-prime/two-outer inner layer, if
  `4*(L-log outerPart)_+ <= log(minFac n)`,
  `cutoffSaving_ge_three_quarters` returns at least **3/4 of the optimized
  old charge**. `weighted_saving_ge_three_quarters` sums this improvement
  with the literal allocation and factorial weights on any matching subset
  of `E`.

The regression includes three seven-prime labels outside the old
`exp(N/128)` small-prime head and below the old count tail. Two have zero
refined charge. On the adverse-phase example at `N=1027`, the optimized old
charge is approximately `34.4726`, while the new charge is `4.73158`, a
local reduction of approximately `86.27%`. These numbers are diagnostic
individual-label calculations, not certified population estimates or a
percentage of the global deficit.

Focused Lean compilation and theorem axiom checks cover this slice. The
cofinal `-79/1000` floor still requires a numerical bound for the remaining
**signed aggregate**, particularly the unpaid low-count geometries and
their correlations with the higher counts. No zero exclusion follows yet.

## Local iteration: joined unit, prime and pair cancellation

[`ZetaRieszPairChamberFloor`](../RiemannGaussian/ZetaRieszPairChamberFloor.lean)
adds a strictly new saving on balanced labels that the previous reflected
prefix test did not pay. This remains a local Lean result; wider publication
checks are deferred while the floor is being developed.

Put `T=log n`, `D=T-L` and `k=omega(n)`. For a squarefree label with

\[
\frac D3\le\log p\le\frac D2\qquad(p\mid n),
\]

all unit, prime and prime-pair hinges are active, and every higher hinge
is zero. Summing these levels **with their signs** gives exactly

\[
c_L(n)=-\frac TL(-1)^k
\left[\binom{k-1}{2}(T-L)-(k-2)T\right].
\]

`coefficient_eq_pair` has no prescribed prime count. `pair_floor_exact`
retains the original cosine, factorial weight and allocation, evaluating
the adverse charge only after this cancellation. `pairSaving` compares
that result against the minimum of the existing optimized reflection and
prefix charges, so the additional credit cannot duplicate an old one.

A quantitative benchmark is the seven-prime region

\[
\frac{2T}{15}\le\log p\le\frac{3T}{20},\qquad
\frac{2T}{3}\le L\le\frac{7T}{10}.
\]

Here `c_L(n)=-(T/L)(15L-10T)`.
`balancedSeven_old_saving_eq_zero` proves that the preceding cutoff test
gave **no** credit here. `balancedSeven_new_saving_ge_quarter` then proves
that the new cancellation removes at least **one quarter of the optimized
old charge**, at every height and phase. This comparison is against the
least-prime seven-prime bound, not the looser mean-prime allowance.
`weighted_new_saving_ge_quarter` sums it with the exact original weights
over any matching subset of the unpaid remainder.

`eventually_joined_floor` carries the additional saving into the complete
compensated `joinedPhysical` floor. All old radial payments, favorable
observations, exact signed low-count terms, and the unspent **1/64** supply
are retained. The only new term is a nonnegative charge reduction on the
same unpaid labels. The original carrier and source theorem are unchanged.

The optional `scripts/probe_riesz_pair_chamber.py` enumerates every signed
divisor of actual distinct-prime labels at orders 512, 640, 1027 and 1536.
The adverse seven-prime samples reduce the previous charge by approximately
64%, 56% and 52%; the favorable-phase sample eliminates it. An eight-prime
sample checks the count-independent formula. These are individual-label
diagnostics, not population estimates, full `coreBand` certificates, or a
percentage of the global deficit.

The unbounded task is still the signed aggregate: this theorem does not
pay labels outside its geometry, bound the remaining low-count sum, or
establish the numerical cofinal `-79/1000` floor. A fixed relative saving
on a sector is not by itself a source-scale decay estimate.

## Local iteration: signed prime periods beyond the saddle band

[`ZetaRieszSignedPeriodFloor`](../RiemannGaussian/ZetaRieszSignedPeriodFloor.lean)
now bounds whole populations using signed cancellation between actual
primes. The previous nearly constant weight argument required
`2N <= v <= 2N+sqrt N`. This one-sided argument retains the radial drift
and applies throughout the linear core, `1.95N < log n <= 2.03N`.

For the full factorial amplitude

\[
F_N(T)=\frac{e^{-T/2}T^{N+1}}{N!},
\]

the exact complete-period identity is

\[
\int_{v-\pi/y}^{v+\pi/y} F_N(T)\cos(y(T-v))\,dT
=-\frac1{y^2}\int_{v-\pi/y}^{v+\pi/y}
F_N''(T)(1+\cos(y(T-v)))\,dT.
\]

The squared radial slope in

\[
F_N''(T)=F_N(T)\left[
\left(\frac{N+1}{T}-\frac12\right)^2-\frac{N+1}{T^2}\right]
\]

is favorable for the upper bound on the centered cosine integral. Only
the negative curvature is charged. Aligning the period with the sign of
the cofactor then gives a lower bound. This alignment selects a **whole
cofactor fibre**, including both signs of the prime phase; it does not
delete individual adverse primes.

`prime_period_upper` transfers this inequality to ordinary primes with
both endpoint errors retained. `allocated_fibre_floor` keeps the actual
`1-boundedShare`, moving length, factorial kernel and unsaturated
two-cutoff cofactor response. `periodCost_le` gives an explicit
`50000/v^2` central cost. After summing literal cofactors,
`population_floor` proves

\[
\operatorname{Re}\sum_{n\in P_{N,v,k}}
\mathrm{residualCoefficient}(n)K_N(s_0,n)
\ge -C_k v^{-1/2}\frac{e^{-v/2}v^N}{N!}.
\]

Here the count is fixed, every prime period is complete, its center is a
cosine extremum, and its frozen signed cofactor coefficient is aligned
against that extremum. The explicit `populationConstant k` includes both
cutoff and allocation variation. Its dependence on the count is retained.
`eventually_core_aligned_floor` uses the original `length` and
`intermediatePrimes`; its debit is eventually less than any prescribed
positive fraction of one radial supply unit, uniformly over eligible
core centers. `sum_owned_subset` prevents incidence overcounting, and
`owned_subset_core` supplies the original core inclusion with its actual
dyadic count condition.

The optional `scripts/probe_riesz_signed_period_floor.py` checks the smooth
period identity at radial ratios 1.95, 2 and 2.03 and orders up to one
million. Away from the saddle the retained drift becomes favorable while
an absolute period cost would keep charging it. The probe is numerical
motivation, not prime-count or source-scale evidence, and stays outside CI.

This is **not** another positive bound for the whole carrier. It is a
one-sided payment for sign-aligned complete-period populations. The remaining
work is to cover the unaligned/clipped populations and coefficient-sign
transitions, matching these payments to the exact unpaid remainder without
spending the same positive supply twice. Multiplying this relative bound
by the source scale does not itself prove decay. The cofinal `-79/1000`
floor, multiplicity ceiling and RH contradiction remain open. Only focused
Lean and axiom/lint validation has been run for this local iteration.

## Local iteration: both arithmetic signs on staggered periods

[`ZetaRieszStaggeredFloor`](../RiemannGaussian/ZetaRieszStaggeredFloor.lean)
removes the frozen cofactor-sign selection from the preceding estimate.
For the literal real coefficient `c`, it uses the exact identity

\[
c=\max(c,0)-\max(-c,0).
\]

The original nonnegative allocation/factorial weight and the full cosine
multiply both terms. Positive arithmetic coefficients are summed over
complete periods centered at negative cosine peaks; negative coefficients
use the grid shifted by half a period. The phase itself is never clipped.
The inequality

\[
|\max(x,0)-\max(x',0)|\le |x-x'|
\]

pays coefficient sign changes inside a period with the existing cutoff
variation. Thus `signedPart_fibre_floor` and `signedPart_population_floor`
keep both Riesz hinges, the exact allocation, the actual ordinary primes,
and the preceding explicit count-dependent debit

\[
-C_k v^{-1/2}\,\frac{e^{-v/2}v^N}{N!}.
\]

`eventually_core_part_floor` applies to every eligible cofactor, with no
frozen-sign filter, across the original linear core. The moving physical
prime mask and Riesz length are discharged. `eventually_staggered_floor`
then sums any growing finite collection of complete periods on both grids.
It retains two explicit unmatched parts, one per arithmetic sign. Different
grids may overlap in labels: `two_cover_ledger` proves they recombine into
exactly one original atom. Within a grid, unique largest-prime ownership
and half-open period intervals prove disjointness.

`joined_two_cover_floor` carries this inequality directly to
`joinedPhysical`, subtracting only its already-proved geometric
`2*(19/20)^N*zetaMoebiusLogMajorantMass(1+1/256)` core error. It does **not**
assert that the remaining signed parts have the required numerical floor.
The arbitrary ambient set in the period inequality permits choosing the
previously unpaid set; complete-period membership must still hold after
that choice, so existing positive supply cannot be spent twice.

For total prime count at most 55, `mem_population_of_owner_margin` and
`missing_population_boundary` sharpen the geometry audit. Inside an
eligible complete period, a squarefree cofactor is included whenever

\[
\log a>\frac{203}{500}\left(\log(pa)+\frac1{16}\right),
\qquad
\log q\le\log p-\frac18\quad(q\mid a).
\]

The old upper cofactor-share cap is already redundant at these counts.
Therefore a missing interior label lies at the stated lower-share edge
or has another prime within `1/8` of the largest prime's logarithm. No
coefficient-sign condition remains. These boundaries, clipped periods,
prior-credit mask exclusions and the growing-count range still require
payment. The `C_k/sqrt(v)` estimate is a relative radial saving, not a
source-scale error. The `-79/1000` whole floor and RH contradiction remain
open. Validation for this local slice is focused Lean compilation and a
root-import declaration/axiom audit; publication checks remain deferred.

## Local iteration: paying nearly tied largest primes

[`ZetaRieszOwnerTieFloor`](../RiemannGaussian/ZetaRieszOwnerTieFloor.lean)
pays the close-owner omission isolated by the staggered-period audit.
For squarefree labels with 3 through 55 prime factors and

\[
v-\frac1{16}<\log n\le v+\frac1{16},\qquad
\log p-\frac18<\log q\le\log p,
\]

where `p` is largest and `q` is another prime factor, write `n=p*q*b`.
Both primes lie in the fixed cofactor window

\[
\frac{v-\log b}{2}-\frac18<\log p,\log q
\le\frac{v-\log b}{2}+\frac18.
\]

The count bound forces `log b <= 27v/28`. For `v >= 1000000`, the actual
prime reciprocal sum in that window is at most `60/v`. The two factors
therefore cost `3600/v^2`. Retaining the least-prime logarithm in the
coefficient and summing the remaining literal cofactor cover gives

\[
\sum_{n\in D}\left|
\mathrm{residualCoefficient}(n)K_N(s_0,n)\right|
\le \frac{C_{\rm tie}}{v}\frac{e^{-v/2}v^N}{N!}.
\]

`bounded_count_norm_bound` proves this jointly through count 55, with
`C_tie = allTieConstant` an explicit finite sum of the count-dependent
constants. It retains the original allocation and complex phase, works
for every height, and permits any additional finite mask in `D`.

`signedParts_abs_eq` checks that the absolute costs of the positive and
negative arithmetic parts add to **one** original real atom. Thus both
staggered-grid omissions on `D` cost one boundary allowance.
`joined_two_cover_floor_with_ties` removes those labels from both remaining
signed parts of `joinedPhysical`, retaining every period payment and the
same paid geometric core error. `eventually_core_grouped_tie_floor`
handles growing finite covers of such windows, including overlap, with
an arbitrarily small debit relative to their summed radial units.

This is a boundary saving, not source-normalized decay. The lower
cofactor-share edge, clipped end periods, holes from previously spent
credits, growing-count tail and aggregate comparison with unused positive
supply remain. In particular, the cofinal `-79/1000` floor is still open.
The suggested rough five-prime attack matches the checked complete-period
mechanism with a four-prime cofactor. The existing owner-weight variation
bound of 2 can preserve an independently proved partial-sum bound, but
it does not supply that bound or remove incomplete literal fibres.

## Local iteration: complete rough five-prime fibres in the unpaid sum

[`ZetaRieszRoughFivePeriodFloor`](../RiemannGaussian/ZetaRieszRoughFivePeriodFloor.lean)
checks the proposed fixed-four-prime-cofactor attack against the existing
credit ledger. For `n=a*p`, with `a` squarefree of count four, select only
cofactors whose prime factors exceed a roughness threshold `B`. The running
prime is larger than every cofactor prime, so it also exceeds `B`: this
filter creates no holes inside its complete phase period.

If `B >= max(Q,V)`, neither of the previously paid small-prime five-factor
heads can remove a label in the fibre. The other spent classes have count
three, four, six or at least seven. `rough_five_not_spent` proves exclusion
from their full union, including the radial supply. The usual dyadic core
membership theorem checks the original physical, count, radial and owner
masks as well.

`eventually_unpaid_rough_five_floor` therefore bounds the **literal unpaid
five-prime sum**, with no arithmetic cancellation hypothesis. Writing
`E5` for that sum's label set, and `P+`, `P-` for the complete rough-period
unions on the two staggered grids, it proves

\[
\sum_{n\in E5\setminus P_+}\operatorname{signedPart}_+(n)
+\sum_{n\in E5\setminus P_-}\operatorname{signedPart}_-(n)
-\varepsilon\sum_{v\text{ on both grids}}\frac{e^{-v/2}v^N}{N!}
\le \operatorname{Re}\sum_{n\in E5}\operatorname{originalAtom}(n)
\]

eventually for every fixed `epsilon > 0`, allowing growing finite grids.
Both hinges, coefficient sign changes, full phase, moving Riesz length and
the original allocation remain in the theorem. Earlier sector credits
are excluded before the estimate, so this payment does not spend them twice.

The next estimates pay this period debit. A two-unit radial slab contains
at most `floor(2y)+1` centers from each phase grid (`y >= 54`), independent
of the moment order or total number of selected slabs. Each period's radial
unit is at most `exp(2)` times the original slab unit. The existing actual
four-prime supply has a strictly positive multiple of that same unit.
Choose the fixed period precision before the moment order; then
`eventually_period_debit_paid` pays every selected period on both grids
with at most **1/128 of that slab's supply**. `exists_period_debit_supply`
proves the elementary phase selection needed for this actual supply.

`eventually_radial_rough_five_supply_floor` sums the resulting literal
inequalities over growing disjoint slabs. It retains the signed five-prime
sum outside the selected slabs and both unmatched sign parts inside them.
Their sum is a proved lower bound for the whole unpaid five-prime sum plus
**1/128 of one radial supply**. The supply phase condition remains
explicit in that theorem; it is not inferred from positivity alone.

To check compatibility with earlier payments,
`eventually_joint_slabs_floor_with_period_budget` retains the quantitative
supply scale from the original head-payment construction. It chooses ONE
supply simultaneously for the six prior charges and the new period cost,
and proves

\[
\underbrace{\mathcal C_3+\mathcal C_{3,\mathrm{head}}
+\mathcal C_{4,\mathrm{head}}+\mathcal C_{5,\mathrm{head}}
+\mathcal C_{5/6,\mathrm{head}}+\mathcal C_{7+,\mathrm{tail}}}
_{\text{the six existing literal norm charges}}
+\kappa\sum_{v\text{ on both grids}}\frac{e^{-v/2}v^N}{N!}
\le\frac{127}{128}\operatorname{Re}\sum_{n\in\mathrm{supply}}\operatorname{originalAtom}(n).
\]

Thus the old charges and complete-period debit leave **1/128 of the same
positive supply unspent**. This fraction measures supply usage, not a
percentage of the global endgame deficit. The starting order and precision
are existential and may depend on the fixed height.

The remaining terms include nonrough unspent labels, clipped radial periods
and the lower cofactor-share edge; nearly tied owners have the separate
checked payment above. These are actual sector and joint-cost inequalities,
but **not** the cofinal `-79/1000` floor or a source-normalized decay theorem.
The published proof frontier and wider gates stay unchanged.

## Local iteration: spending complete periods in the whole joined floor

[`ZetaRieszRoughFiveJoinedFloor`](../RiemannGaussian/ZetaRieszRoughFiveJoinedFloor.lean)
now incorporates the signed rough five-prime payment into a whole-carrier
inequality. The original quantitative supply selection passes through the
old radial floor and the whole-tail boundary payment. Its scale pays both
growing period grids together, so no independent supply choice or additional
phase-selection assumption is needed.

Write `E5` for the exact unpaid five-prime labels, and `Eo` for all other
unpaid labels. Let `U` be the sum of the two literal sign parts on
`E5` outside their respective complete rough-period covers. Retain the old
optimized >=7 charge in `W`, and both prefix and prime-pair savings in `G`,
now on `Eo`. `eventually_joined_floor_with_rough_periods` proves

\[
u^{N+1}\left(U+W+G+
  \sum_{\text{six old sectors}}\max(\operatorname{Re}\mathcal S,0)
  +\frac{\operatorname{Re}\mathcal Y}{128}\right)-e_j
\le \operatorname{Re}\left(u^{N+1}\operatorname{joinedPhysical}\right),
\qquad e_j\to0.
\]

The former `1/64` supply reserve funds the complete-period debit with
`1/128` remaining; none of the six old credits is removed or reused. The
error retains the proved whole-tail boundary and core/joined geometric
payments. Both hinges, every original phase and the allocation remain in
the actual arithmetic terms. No zero hypothesis or unproved arithmetic
cancellation estimate is assumed.

Radial cells assign **period centres**, rather than clipping each period
to its cell. A signed period may cross a cell boundary, and its debit is
still paid once. Full core containment remains required; repeated internal
clipping is therefore not an extra omission.

The two unmatched sign sums and the other signed unpaid sectors are still
unevaluated. In particular, the existing dominant payment already removes
cofactor shares up to `399/1000`, whereas the current period population
starts above `406/1000` (with its explicit boundary offsets). The narrow
transition, nonrough unspent labels, nearly tied owners and exterior clipped
periods must still be covered or paid. This is a concrete whole-ledger
sector saving, **not** the numerical `-79/1000` floor or a zero exclusion.
Keep local validation focused on the changed Lean modules and their
root-import axiom/lint audit; no wider publication gates are requested.

## Local iteration: the share transition and sign-specific five-prime covers

[`ZetaRieszTransitionFiveFloor`](../RiemannGaussian/ZetaRieszTransitionFiveFloor.lean)
extends the complete-period selector's lower cofactor share from `203/500`
to `199/500`. Its literal largest-prime cap is `1209/2000`, which still
discharges the original core and physical prime masks. The same two-hinge
response, allocation variation and count-dependent period cost apply.
`original_roughPeriod_subset` retains every earlier rough-period label;
`transition_mem_roughPeriod` proves that every rough five-prime label with
cofactor share in `[399/1000,407/1000]` belongs to every complete period
containing its total logarithm. There is no coefficient-sign or close-owner
condition on this transition. The enlarged cover therefore overlaps the
independently paid dominant region; the old `0.399`–`0.406` separation is
not an intrinsic limitation of the period estimate.

[`ZetaRieszFiveSignCoverFloor`](../RiemannGaussian/ZetaRieszFiveSignCoverFloor.lean)
also removes the unnecessary common roughness threshold `max(Q,V)`.
The positive arithmetic part uses the original positive-head threshold
`Q`, and the negative part uses the original negative-head threshold `V`.
`positive_part_zero_of_spent` and `negative_part_zero_of_spent` prove that
the only possible intersections with the opposite paid head have exactly
zero contribution to the selected sign part. Restricting a complete period
to the unpaid set therefore retains its signed floor without charging the
already-paid head again.

Let `X+` be the enlarged `Q`-cover on the negative-peak grid and `X-` the
enlarged `V`-cover on the positive-peak grid. Define the literal unmatched
parts by

\[
 U=\sum_{n\in E5\setminus X+}\operatorname{signedPart}_{+}(n)
   +\sum_{n\in E5\setminus X-}\operatorname{signedPart}_{-}(n).
\]

`eventually_joined_floor_with_signed_rough_periods` gives the same
whole-carrier inequality above with this larger, sign-specific cover. It
retains every earlier favorable credit, the higher-count prefix/pair
savings, the original geometric errors and the remaining `1/128` supply.
The enlarged coverage has **no additional period debit**.

`unpaid_positive_rough` and `unpaid_negative_rough` establish the separate
roughness conditions on nonzero unpaid sign parts in the retained radial
interior `244N/125 < log n <= 2029N/1000`. The two
`transition_*_zero_or_covered` theorems consequently remove the transition
omission even when a label is not rough above `max(Q,V)`: its selected
part is zero or is in its own threshold's cover. This is a literal signed
coverage result, not a numerical prime-density approximation.

Exterior clipped periods, close owners outside the transition and the
remaining signed unpaid sectors still need their aggregate bounds.
Neither the cofinal `-79/1000` floor nor a new zero exclusion is proved.
Continue local floor iteration with focused Lean and root-import axiom
checks; keep the published endpoints and wider gates unchanged.


## Local milestone: the entire unpaid five-prime sector is paid

The stronger checked endpoint
`ZetaRieszFiveSignCoverFloor.eventually_joined_floor_without_fives`
removes the **entire original unpaid five-prime sector** from the main
signed remainder. It does not require user-supplied phase grids or an
unproved prime cancellation hypothesis.

The proof covers all separated owners beyond the independently paid
`399/1000` cofactor cutoff, not only the narrow share transition.
`completeGrid` and `slabGrid` select both staggered half-open grids
explicitly. Every total logarithm in the retained radial interior is in a
complete period, and centre assignment retains periods crossing internal
slab boundaries. The positive part keeps threshold `Q`, and the negative
part keeps `V`. Neither uses `max(Q,V)`.

`interior_parts_covered` isolates precisely three remaining causes of
missing coverage. The already-proved dominant allocation pays the eligible
owner share at least `601/1000`; the complete close-owner estimate pays
owner logarithms less than `1/8` apart; and the existing deviation theorem
pays both outer radial strips. The latter two source errors and the dominant
error retain the original allocation, phase and every finite support mask.
No prime cofactor is completed.

For the exact unpaid five-prime set `E5`, `exists_unpaid_five_floor` proves,
with `U_N` the sum of both grids' radial units and suitable `0 <= r < 1`,

\[
 \Re\left(u^{N+1}\sum_{n\in E5}f_N(n)\right)
 \ge -u^{N+1}\epsilon U_N
       -4M(1+1/262144)e^{-N/1000000}-2Cr^N.
\]

Here `epsilon` can be any positive fixed number; the starting order depends
on that choice and the fixed height. This is a **signed lower bound**, not
source-scale norm decay. Choosing the debit from the same original
quantitative supply selection spends at most `Y_N/128`. The resulting
whole-carrier ledger is

\[
 \Re\left(u^{N+1}\operatorname{joinedPhysical}_N\right)
 \ge u^{N+1}
       \left(W_N+G_N+\sum_{i=1}^{6}\mathrm{credit}_{i,N}
                    +Y_N/128\right)-e_N,
 \qquad e_N\to0.
\]

The remaining `W_N` is over `E \ E5` only. All six earlier favorable
credits, optimized higher-count charges, prefix/pair savings and the
remaining `1/128` of the actual positive supply are retained. The period
and tie costs share one budget; no previous credit is spent twice.

**Still open:** the signed aggregate at the other unpaid counts, chiefly
three, four and six and the remaining charge at counts at least seven.
This theorem does not establish the cofinal `-79/1000` floor, the ceiling,
a contradiction or any new zero-free region. Keep this milestone local;
published diagrams and explorer endpoints remain unchanged.

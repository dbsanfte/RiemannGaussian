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

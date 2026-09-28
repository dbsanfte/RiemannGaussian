# Ordered four/five capacity: exact signed bounds and quantitative test

The target remains an independent cofinal floor for the **whole** joint
carrier. Literal five-prime labels now pay one concrete interior
four-prime, negative-cosine population and leave a proved positive surplus.
Whole ordered-region arithmetic bounds now include their boundary costs.
The exact certificate-domain comparison is proved, and the checked first
bin gives a literal five-prime credit. The [complete-period payment](zeta-riesz-capacity-phase-payment.md)
now combines the two populations with disjoint spending and full phase
costs in that bin. The remaining bins, signed complement, whole floor
and zero exclusion remain open. Opposite-phase component ceilings are
also proved; the whole ceiling needed for multiple zeros remains open.
The prior exponential-head payment and its signed complement remain
unchanged; their supplies are not added to this payment without a combined
disjoint ledger.
The [extra owner-credit theorem](zeta-riesz-five-owner-credit.md) now adds
`1/800` to the angular credit of the **same** five-prime family for cutoff
bins inside `69/100..7/10`, with an explicit relative calibration factor
for the upper comparison. Its checked cubes lie beyond the old one-half
owner cap. They strengthen the integral bound, not a second overlapping
prime supply; the complete signed complement remains open.
The [central comparison](zeta-riesz-capacity-phase-payment.md#checked-central-payment-for-the-broader-triple-band)
is now also checked: 85 four-prime chunks, 447 five-prime chunks, both
assemblies, and the literal signed transfer. Owner-enhanced credit
`1309/10000` pays debit `1261/10000`, including the broader triple band,
over a complete phase period in both directions. The margin
`g*V0*h/500` is a component comparison, not a whole-sum bound.

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

The first padded-bin debit cover has now passed locally: all 30,128 leaves
in 274 chunks, the complete assembly, and its terminal axiom audit. The
generated `RieszFourCapacityBin0.Assembly.whole_debit_upper` proves the exact
upper bound **133011/1000000** throughout
`1979971/2900000 <= L/T <= 77646131/113100000`. Reproduce it with the optional
commands below; the generated proof is outside the default root. This is
the complete angular debit, now transferred to an actual adverse-prime
floor below. The matching first-bin five-prime cover has also passed:
10,131 leaves in 713 chunks and the complete assembly prove
`RieszFiveCapacityBin0.Assembly.whole_supply_lower`, with exact lower bound
**34261/250000 = 0.137044**. The optional
[`CheckRieszCapacitySurplus.lean`](../scripts/CheckRieszCapacitySurplus.lean)
combines both checked assemblies and audits the terminal axioms. Its
`first_bin_angular_surplus` leaves **two percent** angular surplus after
one `1/1250` ordering cost and one aggregate `1/2000` approximation budget.
The other cutoff bins and the complete favorable prime-population transfer
remain unfinished; this is not a whole arithmetic floor.

## A proved common phase and population budget

[`ZetaRieszPhaseBudget.lean`](../RiemannGaussian/ZetaRieszPhaseBudget.lean)
now pays two explicit costs in the proposed transfer. Its
`original_radial_phase_budget` keeps the exact original factorial kernel
and cosine over a complete phase period inside the core, for `abs(y)>=54`.
If angular supply is at least `103/100` times debit, a one-percent aggregate
population/allocation loss, radial oscillation `501/500`, and phase
uncertainty at most `1/10000` still leave a strictly positive joint budget.
`weighted_joint_phase_budget` gives the quantitative lower bound
`(3/100)*D*V0`, where `D` is the angular debit and `V0>0` the radial minimum.
The full period is retained, including neighborhoods of cosine zeros.

`tuple_negative_phase_enclosure` bounds the phase uncertainty of a literal
prime tuple by `abs(y)*k*h`, where each logarithmic prime window has fixed
width `h`. Such a width can be chosen once for the fixed height. It does not
shrink with the moment order. `eventually_phase_window_mass` proves the
actual harmonic prime mass lies between `9999/10000` and `10001/10000`
times `h/a`, uniformly over `a>=alpha*N`, for fixed `0<h<=1/100000` and
`alpha>0`. `eventually_phase_tuple_mass` combines up to five legs with
relative bounds `999/1000` and `1001/1000`.

These are relative counting and signed phase budgets. They do not assert
source-scale prime-density approximation. The angular cells still have to
be transferred to disjoint actual prime populations, with their original
masks and unspent supply. The one-percent budget is not a proof that those
remaining costs have been paid. No whole-carrier floor follows yet.

## Proved signed transfer for literal five-prime cells

[`ZetaRieszCoupledWindow`](../RiemannGaussian/ZetaRieszCoupledWindow.lean)
puts the final prime in the exact interval
` t-log(m) < log(p) <= t+h-log(m) `, where `m` is the actual four-prime
cofactor. Every product therefore has `t<log(m*p)<=t+h`. Its cosine is
retained. Strict largest-prime ownership makes the resulting products
unique, and the original core masks are proved from the cell geometry.
`eventually_owned_five_core_lower` bounds any finite collection of these
ordered cofactor windows inside `coreResponse`, retaining the entire signed
complement.

[`ZetaRieszMacroPrimeWindows`](../RiemannGaussian/ZetaRieszMacroPrimeWindows.lean)
now allows the four outer log intervals to have widths proportional to `N`.
Exact unions of fixed-width windows prove relative harmonic bounds
`(4999/5000)*H/(a+H)` and `(5001/5000)*H/a`, uniformly for
`a>=alpha*N`, `H>=beta*N`, with fixed positive `alpha,beta`.
For up to four outer legs the combined constants are `999/1000` and
`1001/1000`. Ordered windows enumerate cofactors once. These are relative
positive population bounds, not signed PNT errors multiplied by a growing
source envelope.

[`ZetaRieszFivePrimeCells.eventually_five_cell_core_floor`](../RiemannGaussian/ZetaRieszFivePrimeCells.lean)
combines those bounds into an explicit arithmetic credit. For ordered outer
endpoints `a_i`, widths `H_i`, let `K` be its three common hinge caps,
`v=t-sum a_i`, and `phi=-cos(y*t)-abs(y)*h>=0`. The selected actual five-prime
sum has real part at least

```math
\frac{997}{1000}\,\frac{t}{L}\,K\,\phi\,
\frac{e^{-(t+h)/2}t^N}{N!}\,
\frac{h}{v}\prod_{i=0}^{3}\frac{H_i}{a_i+H_i}.
```

The theorem pays the old allocation and all five prime-population errors
within this **0.3% relative allowance**. The original moment, moving length,
core edges, physical upper cutoff, coefficient and phase remain unchanged.
There is no hypothetical-zero, signed-score or unproved counting premise.
The explicit cell inequalities enforce ordering, saturation and largest
share at most `9/16`. Starting indices remain unevaluated.

The matching upper transfer is now proved in
[`ZetaRieszFourPrimeCells.eventually_four_cell_core_floor`](../RiemannGaussian/ZetaRieszFourPrimeCells.lean).
Its cost is `501/500` times an explicit upper cell debit, retaining all three
positive-coefficient caps. Only labels satisfying the original support,
positive coefficient and negative cosine are charged. Every unselected
label stays signed.

[`ZetaRieszJointPrimeCells.eventually_joint_cell_family_floor`](../RiemannGaussian/ZetaRieszJointPrimeCells.lean)
combines **arbitrary finite families** of those literal cells. Ordered
coordinate separation proves that five-prime credit cells are disjoint.
Four-prime debit cells may overlap: their actual atoms are nonpositive, so
duplicates overcharge the debit. Counts four and five are disjoint. A phase
window without a favorable lower margin supplies zero credit; its adverse
debit and cosine-zero neighborhoods remain in the inequality.

Recovering the complete angular integrals from the cell budgets and paying
angular grid/edge losses still remain. The 0.3% and 0.2% factors pay counting
and allocation, not those open approximation costs. All unselected phases
and counts remain signed, and the joint `-79/1000-o(1)` floor remains open.

## Proved interior four/five payment

[`ZetaRieszCellCompensation.eventually_fixed_height_payment`](../RiemannGaussian/ZetaRieszCellCompensation.lean)
now discharges an actual comparison, with **no assumed numerical surplus**.
For every fixed `y != 0` and `1/2<u<=10001/20000`, there are fixed `h>0`
and `C>=0` such that eventually, at each original dyadic order `N`, some
`t=2N+v`, `0<=v<=C`, lies in the core and supplies the following cells.
The table gives `log(prime)/t`, not `log(prime)/log(n)`:

| Population | Ordered cofactor-prime intervals, least first |
| --- | --- |
| Four-prime debit | `(0.060,0.061]`, `(0.230,0.231]`, `(0.240,0.241]` |
| Five-prime credit | `(0.060,0.064]`, `(0.070,0.074]`, `(0.220,0.224]`, `(0.245,0.249]` |

The largest prime follows the exact cofactor: `t<log(n)<=t+h`.
The four-prime selection retains its positive-coefficient, negative-cosine
and original support masks. The five-prime cell satisfies all original
core masks, with its exact allocation factor. The moving length is proved
to obey `17t/25 <= L <= 18t/25`; no saddle or cutoff is frozen.

Lean proves a five-prime angular credit of at least `1/6000000` and a
four-prime debit of at most `1/16000000`, already including the population
and allocation costs. The deliberately conservative phase and radial
comparisons still leave, with
`V=exp(-(t+h)/2)*t^N/N!`,

```math
\operatorname{Re}(\mathrm{coreResponse})
\ge
\operatorname{Re}\!\sum_{n\in\mathrm{core}\setminus(D_4\cup D_5)}a_N(n)
+\frac{hV}{100000000},
\qquad \frac{hV}{100000000}>0.
```

Here `a_N` is the unchanged residual-coefficient/factorial-kernel atom.
The fixed-height theorem supplies a favorable phase by a bounded radial
translation and keeps the original moment and full complex phase. Its
starting index is existential, not numerically evaluated.

This pays **one interior four-prime population**. It does not establish the
three-percent whole angular surplus, pay all four-prime labels, or bound
the signed complement. It is a concrete test that the exact correlated
prime-window transfer gives an arithmetic payment, rather than only a
continuum comparison. The finite-family theorem is available for expanding
that payment with disjoint supplies.

## Ordering boundaries and a complete adverse grid

[`ZetaRieszFourPrimeCells.lean`](../RiemannGaussian/ZetaRieszFourPrimeCells.lean)
now retains exact ordering predicates inside **overlapping** cofactor-prime
intervals. `eventually_boundary_cell_floor` gives the same explicit debit
with factor **501/500**, without assuming separated interval endpoints.
The largest prime is selected by its actual comparison with every cofactor
prime. Dropping ordering enlarges only the nonnegative counting budget;
it does not replace the signed arithmetic selection.

The exact coefficient also proves a useful zero-cost boundary region.
On the actual cutoff chamber, `positive_four_top_gap` gives

\[
\operatorname{Re}c_L(pqar)>0
\quad\Longrightarrow\quad
\log p-\log q>\frac7{145}\log(pqar).
\]

Consequently `re_four_nonneg_of_top_gap` proves the entire atom is
nonnegative on the negative-cosine side when that gap is at most the stated
threshold. The two middle ordering boundaries can still contain adverse
atoms and are covered, not deleted.

[`ZetaRieszFourBoundaryCover.lean`](../RiemannGaussian/ZetaRieszFourBoundaryCover.lean)
then covers **every** squarefree adverse four-prime label in `(t,t+h]`
whose prime logs exceed `delta*N`, for any fixed `0<delta<=1/128`. Its grid
has origins `a=delta*N`, width `b=delta*N/1000`, and fixed size
`M=ceil(3000/delta)` along each cofactor coordinate. Cells are ordered by
index but may share intervals; half-open endpoints leave no missed labels.
Only cells with final-prime window start at least `t/4` are needed. The
positive coefficient itself proves that this restriction misses no adverse
label. No grid is evaluated by enumerating its potentially enormous size.

`eventually_exponential_threshold_floor` proves, on the unchanged cofinal
schedule and throughout the core window,

\[
\operatorname{Re}\,\mathrm{coreResponse}
\ge \operatorname{Re}\!\sum_{n\in\mathrm{coreBand}\setminus Q} f_N(n)
 -\sum_{v\in\mathrm{gridCover}}\mathrm{cellDebit}(v),
\]

where `Q` is the **entire** positive-coefficient, negative-cosine
four-prime population above the threshold in that total-log interval and
`f_N` is the unchanged residual atom. The signed rest remains explicit.
The threshold matches the form already available after exponential-head
compensation; that earlier credit has not been spent a second time.
`eventually_joint_boundary_family_floor` also connects arbitrary collections
of these cells to disjoint five-prime supplies in the original core.

This is a proved finite population debit, **not** a bound making that debit
small at source scale. Its total still needs a sufficiently sharp angular
comparison and a combined spending ledger. In particular, the optional
four-prime integral certificate has largest-share cutoff `601/1000`; one
must retain that restriction and its previously paid exterior when linking
it to a grid. The new general grid theorem does not silently identify a
larger domain with that certificate. Favorable five-prime boundary losses,
positive-cosine populations and other counts remain open.

## A numerical budget for the literal ordering boundaries

[`ZetaRieszFourOrderingBudget.lean`](../RiemannGaussian/ZetaRieszFourOrderingBudget.lean)
now gives a quantitative bound on the actual boundary prime population.
The exact largest-share mask is `601/1000`; its exterior stays signed.
A nonempty adverse cell forces its middle and second-largest cofactor
origins above `t/25` and `13*t/100`, and its final-prime interval starts
above `9*t/25`. The least-prime coefficient cancels its own harmonic
factor. Including the relative counting cost, `cell_angular_le` proves
an upper density **800** per unit three-dimensional grid volume.

Ordering faces occur only when adjacent cofactor grid indices agree.
`repeated_index_card` and `edgeIndices_card` prove that at most
`2*ceil(t/(3*b))^2` such nonempty cells occur, independently of the
ambient grid size. Each costs at most `800*(b/t)^3` times the common
radial/phase factor. On `b=delta*N/1000`, `delta<=1/128`, and
`t>=39*N/20`, this gives the proved bound

\[
\frac{1}{1250}\,V_N^+(t)\,\Phi_y^+(t)\,h,
\qquad
V_N^+(t)=e^{-t/2}\frac{(t+h)^N}{N!},
\qquad
\Phi_y^+(t)=\max(0,-\cos(yt))+|y|h.
\]

`eventually_edge_population_floor` applies its negative directly to the
**literal signed prime sum**, retaining the original allocation, phase,
count four, squarefreeness, physical support and largest-share restriction.
`grid_ordered_or_edge` proves that the uncharged nonempty cells have
separated cofactor intervals: no ordering face is omitted.
`eventually_core_interior_floor` therefore gives the whole clipped
adverse population's cost as the explicit interior-cell debit plus this
**0.0008** boundary allowance, inside the unchanged core ledger.
The full complement remains signed. This is a relative angular budget;
it is not a source-normalized constant or a separate boundary-decay claim.

`original_two_percent_budget` sharpens the previous phase comparison:
**2% angular surplus** suffices after the same one-percent aggregate loss,
radial oscillation `501/500` and phase uncertainty `1/10000`. Its weighted
version retains a positive `D*V0/100` full-period budget.
The exact rational `first_bin_budget_room` verifies

\[
\frac{102}{100}\left(
\frac{133011}{1000000}+\frac1{1250}+\frac1{2000}\right)
\le\frac{137044}{1000000}.
\]

The complete first-bin five-prime cover now verifies that supply, and
`CheckRieszCapacitySurplus.lean` proves this inequality for the actual angular
integrals. The adverse domain transfer and favorable ordered-region
boundary estimate are proved below. The favorable certificate-domain
comparison and combined disjoint spending remain open, as do other
phases/counts and the joint numerical floor.

## The entire adverse population now has an exact-integral floor

[`ZetaRieszFourInteriorBudget.eventually_core_integral_floor`](../RiemannGaussian/ZetaRieszFourInteriorBudget.lean)
now controls every adverse four-prime label above the existing exponential
prime threshold and below the literal largest-share cutoff `601/1000`.
Here the adverse sector has a positive arithmetic coefficient and
nonpositive cosine; the other sign/phase sector stays in the signed rest.
Write `Omega` for the union of its nonempty cofactor-share grid cells and
`D_Omega` for the integral of the exact capped coefficient density there.
The retained debit is at most

```math
\left(\frac{1003}{1000}D_{\Omega}+\frac{1}{100000}\right)
\frac{e^{-t/2}(t+h)^N}{N!}
\bigl(\max(0,-\cos(yt))+|y|h\bigr)h.
```

This is a bound for the **literal signed prime sum**, with the whole
complement kept signed. The `0.3%` factor includes upper prime counts.
The additive `1/100000` pays the **whole cell family**, through disjoint
angular volume; it is not one charge per cell. The original moment,
moving length, allocation, physical support and phase remain unchanged.
All ordering faces are covered. Refining to log-cell width
`delta*N/1000000000` changes only the cover; its size is the fixed finite
`M=ceil(3000000000/delta)`. Eventual starting indices remain unevaluated.

The density is exactly the earlier ordered cap integrand before the least
share is integrated (`density_eq_ordered`). Its denominators are controlled
by actual positive-coefficient geometry. No signed PNT error is multiplied
by the source envelope.

## The complete adverse angular domain is now paid

[`ZetaRieszFourAngularDomain.eventually_core_capacity_floor`](../RiemannGaussian/ZetaRieszFourAngularDomain.lean)
closes that domain comparison. Write `D` for the complete two-dimensional
ordered cap integral on `outerBox lo`, with `17/25 <= lo <= L/t`. The literal
debit is now at most

```math
\left[\frac{1003}{1000}
\left(D+\frac{1}{1000000000}+\frac{1}{78000000}\right)
+\frac{1}{100000}\right]
\frac{e^{-t/2}(t+h)^N}{N!}
\bigl(\max(0,-\cos(yt))+|y|h\bigr)h.
```

The affine map `(r,a,q) -> (1-r-a-q,q,r)` has unit absolute Jacobian.
`ordered_integral_eq` proves integrability and the exact Fubini identity
with the certificate density. The refined mesh sharpens the earlier ordering budget: `fine_face_budget`
bounds both repeated-index families together by **one billionth**. Literal largest-share clipping bounds the covering
excess by four normalized cell widths. Its volume is at most that thickness,
and the exact capped density is at most `800`; on the refined mesh this
costs at most `1/78000000`. No label or grid endpoint is dropped.

`eventually_population_capacity_floor` applies to the actual finite prime
population. The dyadic theorem places it in the unchanged core, retaining
the entire signed complement. All original factorial, moving length,
allocation, physical and phase information remains. These are **relative
angular costs**, not small source-normalized constants.

The optional checked first-bin upper value `D <= 133011/1000000` therefore
fits the concrete debit `133421/1000000` times the original radial/phase
factor. Its exact Lean application is
[`CheckRieszFourCapacityTransfer.lean`](../scripts/CheckRieszFourCapacityTransfer.lean),
which imports the separately checked cover assembly and audits the terminal
theorem's axioms. It is deliberately outside ordinary builds and CI. Run it
only after generating and checking the four-prime cover, with that directory
on `LEAN_PATH`; it does not trust the manifest as a proof.

This applies only inside the certificate's exact padded cutoff bin. The
favorable five-prime ordered-region transfer, boundary budget and exact
comparison with its certificate's pair integral are now proved below.
The mesh and largest-share costs use part of
the **single aggregate `1/2000` approximation allowance**; each later error
cannot spend that allowance again. Other sign/phase/count sectors and the
independent whole joint floor remain open.

## The favorable five-prime region has a literal lower bound

[`ZetaRieszFiveAngularBoundary.eventually_ordered_region_core_floor`](../RiemannGaussian/ZetaRieszFiveAngularBoundary.lean)
now transfers the complete ordered three-large/two-small region into the
original finite arithmetic sum. For `1/2<u<=10001/20000`, fixed
`0<h<=1/100000`, sufficiently large original dyadic orders, and
`39N/20<=t<t+h<=203N/100`, write `lambda=L_N/t` and require the padded bin
`lo<=lambda<=hi`. The result is

```math
\operatorname{Re}(\mathrm{coreResponse})\ge
\operatorname{Re}(\mathrm{signedRest})+
\left(\frac{996}{1000}D_5(\lambda;lo,hi)-\frac1{50000}\right)
\frac{e^{-(t+h)/2}t^N}{N!}
\max(0,-\cos(yt)-|y|h)h.
```

Here `D_5` is the four-dimensional integral of the exact three-cap density
`ZetaRieszFiveInteriorBudget.density`. Its cofactor coordinates are
`x=(r,b,a,q)`, normalized by `t`, with `p=1-sum x`. The region has
`1/100<=r<=b<=a<=q<=p<=1/2`, `1-q-a<=lo`, and `hi<=1-b-r`.
`signedRest` contains every original core label outside the explicitly
selected union of disjoint literal five-prime cells. The original moving
length, factorial kernel, prime and allocation masks, phase and cofinal
schedule are unchanged. No hypothetical-zero premise enters this estimate.

[`ZetaRieszFiveInteriorBudget.angular_family_lower`](../RiemannGaussian/ZetaRieszFiveInteriorBudget.lean)
pays the approximation over the **entire** half-open grid with one
`1/100000` angular allowance, retaining `996/1000` after the earlier
prime-count and allocation costs. The error is proportional to cell volume
before summing; it is not charged once per cell or prime label.

Every uncovered point lies within ten mesh widths of one of six faces:
the four successive ordering gaps, including the owner gap, and the two
saturation boundaries. Their combined volume is at most `60*b_mesh`.
The exact density is bounded by `10^12` on the relevant positive-share
region. Thus a fixed mesh `0<b_mesh<=10^(-20)`, with `M*b_mesh>=1`, pays all
these faces with one further `1/100000`. This includes equality boundaries.
All selected cells satisfy the actual arithmetic transfer conditions, and
their prime populations are disjoint. The final combined cost is
`1/50000`. The very fine grid is finite and used symbolically; no grid
enumeration is needed. The eventual starting order remains unevaluated.

The comparison with the optional certificate's two-dimensional pair integral
is now proved in the next two sections, and the checked first-bin application
substitutes `34261/250000`. Both errors above multiply the original
radial/phase factor; they are not small source-normalized constants.
Complete-period aggregation with one disjoint ledger is now checked for
the first and central bins. The other six bins, unselected signs/counts
and the independent whole joint floor and ceiling remain open. No zero
exclusion follows from these comparisons.

## The six incidences fit the literal supply

[`ZetaRieszFiveAngularIncidence.half_integral_pairDensity_le`](../RiemannGaussian/ZetaRieszFiveAngularIncidence.lean)
now pays the incidence part of that comparison. Keep `x=(r,b,a,q)` and
`p=1-r-b-a-q`. The unordered chamber fixes `1/100<=r<=b`, puts each of
`a,q,p` between `b` and `1/2`, and imposes both padded saturation conditions
on every large-prime incidence. For any measurable subset `E` of this
chamber, define the paired budget

```math
I_E=\frac12\int_E
\frac{\min\{r,\max(0,\min(lo-(a+q),1-hi-p))\}}
{hi\,rbaqp}\,dx.
```

Lean proves `I_E <= D_5(lambda;lo,hi)` whenever
`17/25<=lambda` and `lo<=lambda<=hi`. The six label permutations of
`a,q,p` have unit absolute Jacobian and preserve the denominator. Their
cap sum is exactly twice the three-cap numerator, so the factor `1/2`
is retained before integration. Sorting covers equality faces as well.
The proof uses a nonnegative covering inequality and does not assume the
six preimages are disjoint. All integrability conditions are proved, with
no extra angular error or removed boundary.

[`eventually_pair_integral_core_floor`](../RiemannGaussian/ZetaRieszFiveAngularIncidence.lean)
substitutes this comparison into the literal prime-sum estimate:

```math
\operatorname{Re}(\mathrm{coreResponse})\ge
\operatorname{Re}(\mathrm{signedRest})+
\left(\frac{996}{1000}I_E-\frac1{50000}\right)F.
```

Here `F` and every arithmetic mask are exactly those in the preceding
ordered-region theorem. This corollary requires `17/25<=lo`, retains the
same disjoint five-prime supply and the full signed complement, and uses
no zero hypothesis. It does not spend a second copy of the supply.

The exact Fubini and certificate-domain comparison is now proved below.
It retains the literal least-share and large-pair fibres, including their
endpoints. Common phase aggregation, other bins and the independent joint
floor remain open.

## The first-bin certificate now reaches the prime sum

[`ZetaRieszFiveAngularDomain.half_integral_fibre_eq`](../RiemannGaussian/ZetaRieszFiveAngularDomain.lean)
identifies the certificate's two-dimensional integral exactly with `I_E`.
The coordinates send `(r,b,a,q)` to `(a+q,1-r-b-a-q,r,a)` with determinant
`-1`. Both scalar fibres remain half-open, their curved endpoints and the
admissibility condition are unchanged, and bounded integrability justifies
both Fubini exchanges. The exact half factor cancels the factor two in the
symmetric pair integral. There is no additional angular loss.

`supply_integral_le_ordered` therefore compares the certificate integral
with `D_5`. `eventually_core_capacity_floor` applies it directly to the
actual finite prime sum. For the certificate's outer domain, the pair sum
is at most one and the third large share is at most one half; those
comparison premises are proved explicitly in the optional application.

[`CheckRieszFiveCapacityTransfer.lean`](../scripts/CheckRieszFiveCapacityTransfer.lean)
imports the cached, kernel-checked first-bin assembly and proves

```math
\operatorname{Re}(\mathrm{coreResponse})\ge
\operatorname{Re}(\mathrm{signedRest})+
\frac{8529739}{62500000}\,F,
\qquad
\frac{8529739}{62500000}
=\frac{996}{1000}\frac{34261}{250000}-\frac1{50000}.
```

The constant is exactly `0.136475824`. The theorem keeps the full original
radial/phase factor `F`, all arithmetic masks, and every label outside the
selected disjoint five-prime population in `signedRest`. It has no
hypothetical-zero premise. The first-bin range is exactly
`1979971/2900000 <= L/t <= 77646131/113100000`.

Lean also checks the remaining room between the literal constants:

```math
\frac{8529739}{62500000}
-\frac{102}{100}\frac{133421}{1000000}
=\frac{96601}{250000000}>0.
```

This constant comparison is now promoted to a literal complete-period
payment in
[`CheckRieszJointCapacityTransfer.lean`](../scripts/CheckRieszJointCapacityTransfer.lean).
Its `eventually_exists_first_bin_payment` pays the different factors `F`
and `E` together, with one disjoint union and one unchanged signed
complement. See the [exact statement and scope](zeta-riesz-capacity-phase-payment.md).
Previously spent interior supply is not added a second time. The other
six bins and all unselected sign/count sectors remain open; the central
bin's subsequent comparison is recorded above. This is not
the source-normalized `-79/1000-o(1)` whole floor and gives no zero exclusion.

The optional application prints its terminal axiom dependencies. Only
`propext`, `Classical.choice` and `Quot.sound` occur. Neither exhaustive
cover assembly is imported by the ordinary project root or normal CI.

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
The exact certificate-to-prime-population transport is now proved above.

The [recorded output](riesz-ordered-capacity-probe.json) uses 30,000 active
four-prime cells and 10,000 five-prime cells per cutoff interval. It suggests
a worst supply/debit ratio around **1.0339**, after the interval and log
approximants. These are floating-point evaluations of proposed enclosures,
**not certified integral bounds** for the complete eight-bin comparison.
The first-bin pair of complete Lean covers now certifies that bin's
angular surplus, and the central bin now has its own checked covers and
literal transfer. The other six bins remain unverified. The calculation
alone does not prove a joint prime-sum floor: the adverse whole-domain
transfer and favorable ordered-region transfer are now proved, including
their boundary costs and the exact favorable certificate-domain comparison.

A second [unverified run](riesz-ordered-capacity-fast-log-probe.json) uses
only four odd-series terms for lower logarithms and six for upper ones.
Its worst model ratio is about **1.03035**, still above one over all eight
bins. This is a candidate for reducing certificate cost; it is not a second
proved surplus. The precise rational logarithm inequalities are already
proved, but their complete numerical use and angular cover remain unchecked.

The remaining proof must finish the other numerical bins and extend the
proved first-bin complete-period payment. Both cell
transfers, their finite-family aggregation and their complete ordered-region
boundary budgets are proved, as is the concrete interior payment above.
Those positive supplies must be spent together in one disjoint ledger.
The upper debit cover now includes labels close to prime-order equalities
through exact ordered subselections; its repeated-index cells now cost
at most 1/1250 of the common radial/phase factor. The finite sum is now
related to its exact covering-region angular integral with the numerical
cost above. The adverse comparison with the certified ordered domain is now proved,
including its largest-share excess. The favorable five-prime estimate
retains 99.6% of its integral with total angular cost 1/50000. A certified
whole comparison must include these proved losses once.
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

After both assemblies pass, check the literal first-bin debit, credit and
angular surplus without rerunning the exhaustive covers:

```sh
lake env bash -c 'LEAN_PATH="$PWD/.lake/riesz-four-capacity-cover:$LEAN_PATH" lean -DwarningAsError=true scripts/CheckRieszFourCapacityTransfer.lean'
lake env bash -c 'LEAN_PATH="$PWD/.lake/riesz-five-capacity-cover:$LEAN_PATH" lean -DwarningAsError=true scripts/CheckRieszFiveCapacityTransfer.lean'
lake env bash -c 'LEAN_PATH="$PWD/.lake/riesz-four-capacity-cover:$PWD/.lake/riesz-five-capacity-cover:$LEAN_PATH" lean -DwarningAsError=true scripts/CheckRieszCapacitySurplus.lean'
lake env bash -c 'LEAN_PATH="$PWD/.lake/riesz-four-capacity-cover:$PWD/.lake/riesz-five-capacity-cover:$LEAN_PATH" lean -DwarningAsError=true scripts/CheckRieszJointCapacityTransfer.lean'
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

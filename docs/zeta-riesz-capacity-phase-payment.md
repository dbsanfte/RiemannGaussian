# Literal period payment and opposite-phase component bounds

The first and central checked angular bins now give both lower and upper
payments over a complete original phase period. In the central bin, the
same five-prime supply pays every triple whose prime shares lie in
`0.31..0.35`, together with the selected four-prime population. The signed
complement remains explicit in both inequalities.
These are component estimates, not a whole-carrier floor, ceiling or zero
exclusion. Neither payment assumes simplicity or a hypothetical zero.

## Balanced triples paid from the same five-prime credit

[`ZetaRieszBalancedTripleBudget.lean`](../RiemannGaussian/ZetaRieszBalancedTripleBudget.lean)
selects **every** squarefree triple in the original support and log window
whose three prime shares satisfy

```math
\frac{997}{3000}\le\frac{\log p}{\log n}\le\frac{1003}{3000}.
```

The actual-prime theorem `eventually_reciprocal_mass` bounds the reciprocal
mass of this population by `h/(8000*t)`. It covers two prime legs by literal
log intervals and retains the exact product-dependent interval for the
third leg. Together with the original Riesz coefficient, factorial kernel
and allocation, this gives the following **two signed bounds**, for fixed
`0<h<=1/100000`, eventually uniformly in the eligible original windows:

```math
-\frac{1}{10000}V_N^+(t)\bigl(\max(0,-\cos(yt))+|y|h\bigr)h
\le \operatorname{Re}\sum_{n\in B_t}a_N(n)
\le \frac{1}{10000}V_N^+(t)\bigl(\max(0,\cos(yt))+|y|h\bigr)h.
```

Here `V_N^+(t)=exp(-t/2)*(t+h)^N/N!`. This is a bound for literal primes,
with the original phase and masks, not a continuum density comparison.
The count-three population is disjoint from both the count-four debit and
count-five credit. No earlier four-prime compensation is added again.

The optional checked transfer now proves
`eventually_first_bin_three_four_five_floor` and
`eventually_first_bin_three_four_five_all_phase_ceiling`. Their enlarged
debit constants are respectively `133521/1000000` and `133655/1000000`;
the old five-prime credits are unchanged. At each favorable cosine peak
there remains a margin `V_N(t)*h/1000`, where
`V_N(t)=exp(-t/2)*t^N/N!`.

The stronger terminal theorems
`eventually_exists_first_bin_three_four_five_period` and
`eventually_exists_first_bin_three_four_five_upper_period` pay **complete
phase periods** on every sufficiently large original dyadic order, at each
fixed `abs(y)>=54`. Both include all phase-boundary costs and the original
moving length. Writing `g` for the positive phase-mesh integer, each
inequality retains margin `g*V0*h/2000`, with `V0>0`. The lower and upper
theorems use their respective favorable five-prime selections and each
keeps its one exact signed complement. They are alternative bounds, not
credits to be added together. `mem_full_period_iff` proves that no eligible
balanced triple in the full half-open period is omitted.

The triples outside this narrow share band, other count/sign sectors,
small-prime and physical complements, and the remaining cutoff bins are
not paid by these theorems. No fixed positive source-normalized margin is
claimed. The whole-sum floor and ceiling needed for the multiplicity-aware
contradiction remain open.

## A broader triple band with the six orderings accounted for

[`ZetaRieszBroadTripleBudget.lean`](../RiemannGaussian/ZetaRieszBroadTripleBudget.lean)
now proves a literal two-sided estimate for the much wider band

```math
\frac{31}{100}\le\frac{\log p}{\log n}\le\frac7{20}
\quad\text{for every prime }p\mid n.
```

The crucial improvement is exact finite counting. Every selected
squarefree triple has six distinct ordered prime representations in the
same covering domain. `six_le_representation_count` retains all six with
the exact product and moving last-prime window; `six_mul_reciprocal_mass_le`
therefore proves six times the original reciprocal mass is at most the
ordered cover mass. No favorable population is multiplied by this factor.

The two outer prime windows each have reciprocal mass at most `13/100`.
The exact last-prime window costs at most `(67/20)*h/t`. Division by the
proved incidence gives

```math
\sum_{n\in B_t^{\rm broad}}\frac1n
\le\frac{19}{2000}\frac ht,
\qquad
\sum_{n\in B_t^{\rm broad}}
 \operatorname{weight}(A,N,n)\operatorname{Re}c_L(n)
\le\frac1{200}V_N^+(t)h.
```

`eventually_signed_bounds` retains the two distinct original phase
factors, giving lower debit
`(1/200)*Vplus*(max(0,-cos(y*t))+abs(y)*h)*h` and upper debit
`(1/200)*Vplus*(max(0,cos(y*t))+abs(y)*h)*h`.
`eventually_core_bounds` preserves the entire ambient signed complement.
These theorems hold eventually for fixed `0<h<=1/100000`, with `N<=t`,
`0<L`, and `t+h<=2L`, uniformly in the observation height. They use the
actual primes, original coefficient and allocation; no zero hypothesis or
prime-density approximation appears.

The optional central-bin transfer now proves
`eventually_central_window_three_four_floor` and
`eventually_central_window_three_four_ceiling` on every eligible actual
short window inside `1.999N..2.001N`. Their combined debit constants are
respectively **125882/1000000** and **126003/1000000**, with one complement
of the triple/four-prime union. The lower estimate uses the original
adverse four-prime selection; the upper estimate retains all eligible
calibrated positive-coefficient four-prime labels. The original clipped
support and small-prime threshold `log(p)>delta*N` for that four-prime
selection are unchanged. The moving cutoff hypotheses are discharged.

The broader selection contains the old narrow band (`narrow_subset`),
so it **replaces** that debit rather than being added to it. Its payment
from central five-prime credit is now checked below. All these estimates
preserve their signed rests; none bounds the whole joint carrier.

The optional [quantitative probe](riesz-broad-triple-probe.json), reproduced
by `../.venv/bin/python scripts/probe_riesz_broad_triple.py`, compares the
continuous coefficient density on the two triple bands. It also records
an exact rational budget test with an earlier **proposed** central
credit `2593/20000`: after the broad debit, both radial comparisons and all
phase uncertainties, the conservative period margin would exceed
`1/1000`. Neither the quadrature nor that conditional scalar test verifies
a prime-sum credit, phase transport or source-scale bound. The Lean triple
estimate is independent of the probe.

## Checked central payment for the broader triple band

The central four-prime cover passed **85/85 chunks and assembly**, and the
five-prime cover passed **447/447 chunks and assembly**. The exact padded bin is

```math
\frac{78068869}{113100000}\le\frac{L_N}{t}
\le\frac{26165377}{37700000}.
```

`RieszFiveCapacityBin2.Assembly.whole_supply_lower` proves angular credit
at least `13021/100000`. The [additional owner cubes](zeta-riesz-five-owner-credit.md)
increase the credit of the same literal five-prime family by `1/800`.
After the existing angular loss and the upper observation calibration,
`eventually_central_bin_five_floor` and `..._five_ceiling` both retain the
common coefficient `1309/10000`. Every original support, allocation and
phase condition remains. The calibration changes the counting comparison,
not the height in the resulting arithmetic sum.

The optional, compiled
[`CheckRieszCentralCapacityTransfer.lean`](../scripts/CheckRieszCentralCapacityTransfer.lean)
then proves the joint lower and upper comparisons with

```math
C_5=\frac{1309}{10000},\qquad
D_{3,4}=\frac{1261}{10000}.
```

The latter safely bounds both `125882/1000000` and `126003/1000000`.
The populations are disjoint by prime count. Each inequality removes their
union once and retains **the entire original signed complement**. It does
not add either an older four-prime supply or a second copy of the enlarged
five-prime family.

`eventually_central_bin_three_four_five_period_payment` and its upper
counterpart pay the different radial factors and every cosine-boundary
cost over a complete original phase period. Writing `g` for the positive
mesh integer, the strict margin is

```math
\frac{g}{500}V_0h>0,
\qquad V_0>0,\qquad h=\frac{\pi}{4g|y|}.
```

The two `eventually_exists_central_bin_three_four_five_...period`
theorems discharge the moving-bin geometry and construct a suitable period
on every sufficiently large original dyadic order, for fixed `|y|>=54`
and `1/2<u<=10001/20000`. They use no zero or simplicity hypothesis.
The lower and upper selections are alternative comparisons; their credits
must not be added. The subsequent [source-scale theorem](zeta-riesz-central-reserve.md)
retains the radial witness and proves an explicit growing normalized
component credit. The whole `-79/1000` floor, whole `3/2` ceiling and zero
exclusion remain open because the exact opposing complements remain.

The [audit record](riesz-central-capacity-audit.json) identifies the exact
checked source hashes, counts and terminal transfer. The covers remain
optional and outside ordinary CI. Once cached, only the application is run:

```sh
lake env bash -c 'LEAN_PATH="$PWD/.lake/riesz-four-capacity-bin2:$PWD/.lake/riesz-five-capacity-bin2:$LEAN_PATH" lean -DwarningAsError=true scripts/CheckRieszCentralCapacityTransfer.lean'
```

For a fresh reproduction, first generate the four cover with `--bin 2
--cells 8000 --output .lake/riesz-four-capacity-bin2` and the five cover with
`--bin 2 --cells 6000 --output .lake/riesz-five-capacity-bin2`, using their
respective `generate_riesz_*_capacity_cover.py` scripts and default chunk
sizes. Run `check_riesz_four_capacity_cover.py --directory <directory>
--jobs 2` for each generated directory. The generator's proposed total is
untrusted until the chunks and assembly pass Lean.

## Complete-period payment

The optional
[`CheckRieszJointCapacityTransfer.lean`](../scripts/CheckRieszJointCapacityTransfer.lean)
imports the already checked four- and five-prime assemblies. It introduces
no numerical assumptions. The constants are

```math
D=\frac{133421}{1000000},\qquad
S=\frac{8529739}{62500000}.
```

`eventually_first_bin_family_floor` spends their literal populations in
disjoint half-open total-log intervals. Count four and count five prove
the two populations disjoint before their bounds are combined. The
complement is the original core minus their union; no earlier supply is
added to this credit.

`eventually_first_bin_period_payment` retains all `8*m` cells of a full
period, including neighborhoods of cosine zeros. With
`h=pi/(4*m*abs(y))`, it proves

```math
\operatorname{Re}(\mathrm{coreResponse})
\ge \operatorname{Re}\sum_{n\in\mathrm{core}\setminus\bigcup_i P_i}a_N(n)
  +\frac{m}{1000}V_0h,\qquad V_0>0.
```

The original factorial radial weight, moving length, allocation, phase,
prime-count and physical masks remain. The finite phase budget pays the
different radial envelopes and the Lipschitz cosine errors together.

[`ZetaRieszCapacityPhaseBudget.eventually_exists_first_bin_period`](../RiemannGaussian/ZetaRieszCapacityPhaseBudget.lean)
discharges the geometry: for every `1/2<u<=10001/20000`, every sufficiently
large original dyadic order admits a full period in the core for each
fixed `abs(y)>=54`, entirely in the certified ratio interval

```math
\frac{1979971}{2900000}\le\frac{L_N}{t}
\le\frac{77646131}{113100000}.
```

`eventually_exists_first_bin_payment` combines that geometry with the
arithmetic estimates. The surplus is strictly positive on every such
order; it is not asserted bounded below by a fixed positive constant after
source normalization. The first bin sits to the right of the factorial
saddle; the subsequent central-bin payment is documented above. The other
six bins remain unchecked. Starting indices are existential.

## Upper estimates with unchanged arithmetic weights

[`ZetaRieszOppositePhase.lean`](../RiemannGaussian/ZetaRieszOppositePhase.lean)
uses a calibration height `z=pi/t` on a short total-log interval
`t<log(n)<=t+h`. For `t>=1` and `0<h<=1/100000`, Lean proves
`cos(z*t)=-1` and `abs(z)*h<=1/10000`.

The coefficient, allocation and factorial amplitude do not depend on the
height. A lower bound at the calibration height therefore bounds the
same signed coefficient mass at the original height. This is a relative
local comparison; it never multiplies a vanishing error by the absolute
whole-carrier envelope.

`eventually_five_cell_core_ceiling` gives, on
`phi=cos(y*t)-abs(y)*h>=0`,

```math
\operatorname{Re}(\mathrm{coreResponse})
\le \operatorname{Re}\sum_{n\in\mathrm{core}\setminus D_5}a_N(n)
-\frac{996}{1000}\frac{t}{L}K\,\phi\,
 \frac{e^{-(t+h)/2}t^N}{N!}
 \frac{h}{t-\sum_i a_i}\prod_i\frac{H_i}{a_i+H_i}.
```

Here `D_5` is the same literal ordered five-prime cell, and `K` is its
three-hinge `boxCap`. The proof of its nonpositive arithmetic coefficient
is independent of any phase or zero hypothesis.

`eventually_four_core_ceiling` gives the complete clipped
positive-coefficient four-prime population with every `log(p)>delta*N`
an upper budget using the same angular integral as the existing lower
theorem. The exact additional factor is

```math
\frac{10000}{9999}\left(1+\left|\frac\pi t\right|h\right)
\le\frac{1001}{1000}.
```

`mem_calibrated_population_iff` proves that calibration retains every
eligible positive-coefficient label in the interval. It does not delete
labels according to their original phase. The original height is arbitrary,
and the unselected terms remain signed.

The optional `eventually_first_bin_four_ceiling` discharges the angular
integral using the cached first-bin certificate. Including calibration,
its constant is exactly `133555/1000000`, multiplying
`exp(-t/2)*(t+h)^N/N! * (max(0,cos(y*t))+abs(y)*h)*h`.
It has no assumed numerical bound, zero or simplicity premise.

## Joint upper payment

[`ZetaRieszJointCapacityCeiling.eventually_five_core_ceiling`](../RiemannGaussian/ZetaRieszJointCapacityCeiling.lean)
calibrates the entire existing five-prime angular population as one finite
sum. Its lower certificate supplies an upper credit after only the exact
factor `1-abs(pi/t)*h`. All angular losses, incidence normalization, prime
masks, allocation and original phases are retained. Low counts or phase
boundary labels are not discarded in this transfer.

The optional `eventually_first_bin_joint_ceiling` combines that result
with the checked four-prime ceiling. Write `phi=cos(y*t)-abs(y)*h>=0`
and let `Q,D` be the unchanged calibrated four- and five-prime populations.
Lean proves

```math
\begin{aligned}
\operatorname{Re}(\mathrm{coreResponse})
&\le \operatorname{Re}\sum_{n\in\mathrm{core}\setminus(Q\cup D)}a_N(n)\\
&\quad +\frac{133555}{1000000}V_N^+(t)
        \bigl(\max(0,\cos(yt))+|y|h\bigr)h
-\frac{6823}{50000}V_N^-(t)\,\phi h,
\end{aligned}
```

where `V_N^+(t)=exp(-t/2)*(t+h)^N/N!` and
`V_N^-(t)=exp(-(t+h)/2)*t^N/N!`. The selected populations are disjoint
because their prime counts differ. Previous supplies are not added again.

`eventually_first_bin_positive_peak_payment` pays both radial factors
and the original phase error. At `cos(y*t)=1`, `abs(y)*h<=1/10000`,

```math
\operatorname{Re}(\mathrm{coreResponse})
\le \operatorname{Re}\sum_{n\in\mathrm{core}\setminus(Q\cup D)}a_N(n)
-\frac{h}{1000}\frac{e^{-t/2}t^N}{N!}.
```

`eventually_exists_first_bin_upper_payment` supplies such a window at
every sufficiently large original dyadic order for every fixed
`abs(y)>=54`, throughout `1/2<u<=10001/20000`. The same actual moving
length stays in the certified bin. This is a strictly negative literal
component with all geometric hypotheses discharged, independent of any
zero or simplicity assumption. It is not an upper bound for its signed
complement or a fixed source-normalized allowance.

## Upper payment over a complete period

`eventually_first_bin_all_phase_ceiling` extends the upper inequality to
every phase cell. It retains the full calibrated four-prime debit `Q_i`.
The five-prime population `D_i` is spent when
`cos(y*t_i)-abs(y)*h>=0`; otherwise it remains entirely in the original
signed complement. Thus no unfavorable five-prime term is dropped.

For the same complete grid `t_i=v+periodAngle(m,i)/abs(y)`, `i<8*m`,
with `cos(y*v)=-1`, the new finite budget is

```math
\sum_{i<8m}\left[
 \frac{133555}{1000000}V_N^+(t_i)
   \bigl(\max(0,\cos(yt_i))+|y|h\bigr)h
-\frac{6823}{50000}V_N^-(t_i)
   \max(0,\cos(yt_i)-|y|h)h\right]
\le-\frac{m}{2000}V_0h,\qquad V_0>0.
```

Here `m` is the phase-grid parameter, not the analytic multiplicity of a zero.

`original_finite_upper_period_budget` proves this using the original
radial factors. Every cell, including those next to cosine zeros, pays its
phase uncertainty. `mem_full_period_calibrated_iff` proves that the union
of calibrated debits contains exactly all eligible positive-coefficient
four-prime labels in the full half-open period, with every prime logarithm
above `delta*N`. It imposes no original-phase restriction on those labels.

`eventually_first_bin_family_ceiling` combines the disjoint literal
populations. Consequently `eventually_first_bin_upper_period_payment`
proves

```math
\operatorname{Re}(\mathrm{coreResponse})
\le \operatorname{Re}\sum_{n\in\mathrm{core}\setminus\bigcup_i(Q_i\cup D_i)}a_N(n)
-\frac{m}{2000}V_0h.
```

`eventually_exists_first_bin_upper_period` supplies such a complete
period at every sufficiently large original dyadic order. All angular,
arithmetic, moving-length and phase premises are discharged. The upper
and lower payments have different selected populations; they cannot be
added as independent reserves. The displayed signed complement, including
the unspent five-prime terms, remains unbounded.

## Central-bin verification

The next region is the bin containing the factorial saddle.
`eventually_central_bin_ratio` proves that the literal
band `1999N/1000<=t<=2001N/1000` lies in
`78068869/113100000<=L_N/t<=26165377/37700000` eventually, and
`eventually_exists_central_bin_period` constructs a full phase period
there, throughout the same radius interval.

The optional central four-prime cover has now passed all 85 chunks and
its final assembly. It proves the complete angular debit at most
`12051/100000`. The checked
[`CheckRieszCentralCapacityTransfer.lean`](../scripts/CheckRieszCentralCapacityTransfer.lean)
pays the arithmetic and calibration costs and proves
`eventually_central_window_four_ceiling`: for every actual window inside
that central band,

```math
\operatorname{Re}(\mathrm{coreResponse})
\le\operatorname{Re}\sum_{n\in\mathrm{core}\setminus Q}a_N(n)
+\frac{121003}{1000000}V_N^+(t)
 \bigl(\max(0,\cos(yt))+|y|h\bigr)h.
```

The moving-length bin premises are discharged. `Q` retains every eligible
positive-coefficient four-prime label in the window with all prime logs
above `delta*N`; the complementary sum is still signed. This is an actual
upper estimate around the saddle, not merely a continuum angular result.

The corresponding five-prime cover is still being verified separately.
No central-bin **joint payment** is claimed before its complete assembly
passes and the literal five-prime transfer is checked. Partial chunk
success is not a completed certificate.

## Endgame scope and remaining arithmetic

The [multiplicity audit](zeta-riesz-joint-floor.md) gives source
`-m+m^2*c_ret(u)`, with `9/10<c_ret(u)<921/1000`. The simple-zero endgame
needs a whole-joint-sum cofinal floor `-79/1000-o(1)`. Multiple zeros require
a different obstruction; a cofinal ceiling `3/2+o(1)` for the same sum is
one checked sufficient condition. Both independent whole-sum estimates
remain open.

The period and peak payments each control a specified union of populations.
They do not control the whole carrier. Other bins, other signs and prime
counts, remaining small-prime terms, and the signed complement still need
joint control. Balanced triples outside the earlier compensated band
remain a major unresolved contribution; the existing allowance-divergence
audits still rule out bounding them by a fixed absolute charge.
Nothing here assumes simplicity, a zero, or the desired arithmetic floor.

## Local validation

The ordinary root imports the mathematical modules, but neither
exhaustive angular certificate assembly. Recheck the optional application
against the existing cached assemblies with:

```sh
lake env bash -c 'LEAN_PATH="$PWD/.lake/riesz-four-capacity-cover:$PWD/.lake/riesz-five-capacity-cover:$LEAN_PATH" lean -DwarningAsError=true scripts/CheckRieszJointCapacityTransfer.lean'
```

This checks the transfer and terminal axioms without rerunning the
exhaustive covers. Use the repository's pinned `ELAN_HOME` and `lake` path.

The central application uses the separate four- and five-prime cached
assemblies:

```sh
lake env bash -c 'LEAN_PATH="$PWD/.lake/riesz-four-capacity-bin2:$PWD/.lake/riesz-five-capacity-bin2:$LEAN_PATH" lean -DwarningAsError=true scripts/CheckRieszCentralCapacityTransfer.lean'
```

For a fresh checkout, use the exact generation and check commands for both
optional assemblies in
[`riesz-central-capacity-audit.json`](riesz-central-capacity-audit.json).
The generator's manifest is explicitly untrusted; only successful chunk
checks, assembly, and transfer establish the bounds. None runs as part of
an ordinary build.

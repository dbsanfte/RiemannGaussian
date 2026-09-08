# Signed inverse-energy normalization and product-cut audit

This slice checks the repository-root
`RiemannGaussian_signed_current_inverse_energy_steer.md`, whose reference
head is `6b00386e24ad1f24951502b6c4406a3fb0325790`.
It implements the signed transport and quantitative normalization, and
tests the suggested complete low-product split against the actual inverse
definitions. The independent signed upper estimate remains open. No new
zero exclusion, zero-proportion certificate, or RH proof is obtained.

## The normalized arithmetic target

Write `rho#` for the conjugate partner, `sigma=Re(rho)`, and
`e=|2*sigma-1|`. Put

\[
 V_\rho(N)=\operatorname{pairedEtaFiniteCompletedMoment}(\rho,N+2,0),
 \qquad a_\rho=\Re\operatorname{pairedEtaCurrentZeroEnergyCoefficient}(\rho)>0.
\]

Each `V` is exactly the complete inverse region at physical cutoff
`M=2*(N+2)` and center `log(M+1)`. Define

\[
 B_\rho(N)=a_{\rho^\#}|V_{\rho^\#}(N)|^2-a_\rho|V_\rho(N)|^2,
 \qquad S_\rho(K)=\sum_{N<K}B_\rho(N).
\]

The normalized sum is
`pairedEtaNormalizedReflectedEnergyPartialSum`. The actual full inverse
energy is exactly `I_rho(N)=2*Delta_(N+1)*B_rho(N)`.

The compiled
`pairedEtaLeadingFluxSignedPartialSum_fullInverse_error_le` bounds

\[
 |W_\rho(K)-W^{\rm inv}_\rho(K)|\le Z_\rho,
 \qquad
 Z_\rho=\sum_{N\ge0}\operatorname{pairedEtaCurrentZeroEnergyErrorEnvelope}(\rho,N).
\]

This envelope was already proved summable. The new signed difference also
converges to its actual signed correction series, rather than only
satisfying an absolute budget.

The compiled
`pairedEtaCurrent_abs_odd_weight_mul_shift_sub_two_le` gives, for every
`N>=0`,

\[
 |(2N+1)\Delta_{N+1}-2|\le\frac4{N+1}.
\]

It uses the existing elementary bounds
`2/(2*N+5)<=Delta_(N+1)` and `(2*N+1)*Delta_(N+1)<=2`.
The exact signed pointwise normalization correction is

\[
 (2N+1)I_\rho(N)-4B_\rho(N)
 =2\big((2N+1)\Delta_{N+1}-2\big)B_\rho(N).
\]

For the error estimate only, put
`Q_rho=pairedEtaCurrentMomentConstant rho` and
`D_rho(N)=(2*N+3)^(-sigma)`. The full error is at most

\[
 H_\rho(N)=\frac8{N+1}
 \left(a_{\rho^\#}Q_{\rho^\#}^2D_{\rho^\#}(N)
       +a_\rho Q_\rho^2D_\rho(N)\right).
\]

`summable_pairedEtaCurrentStepNormalizationErrorEnvelope` proves this
envelope summable for every actual zero, including both multiplicity
branches. Separate channel norms are used only to pay this summable error;
the main signed bracket is unchanged.

The compiled `pairedEtaLeadingFluxSignedPartialSum_normalized_error_le`
therefore proves

\[
 |W_\rho(K)-4S_\rho(K)|\le Z_\rho+\sum_{N\ge0}H_\rho(N).
\]

The signed normalization correction also converges to its actual series.
The terminal
`pairedEtaNormalizedReflectedEnergyPartialSum_power_lower_eventually`
transports the already established off-critical lower power:

\[
 \operatorname{side}(\rho)S_\rho(K)
 \ge \frac{c_\rho}{8}(K+1)^{e_\rho}
 \quad\text{eventually},\qquad c_\rho>0,\ e_\rho>0.
\]

An independent relative vanishing upper factor for this signed sum would
contradict an off-critical zero. A saving on a cofinal sequence of cutoffs
is sufficient, because the lower bound holds eventually at every cutoff.
Neither the transport nor the normalization proves such a saving.

## The complete low-product split is already the whole carrier

The actual inverse cell has the exact complex identity

\[
 d^{-\rho}\,\operatorname{MoebiusTerm}_\rho
       (k,a-\log d,\lfloor M/d\rfloor,e)
 =\mu(e)\,\operatorname{Atom}_\rho(k,a,M,de).
\]

For a complete product region `H_T={(d,e):d,e>=1,de<=T}`, the coefficient
at an included product `n` is

\[
 \sum_{de=n}\mu(e)=\begin{cases}1,&n=1,\\0,&n>1.\end{cases}
\]

This is formalized as `pairedEtaInverseRegionCoefficient_full_product`,
using Mathlib's classical Möbius convolution identity. It is an audit of
the actual representation, not a claim of novel Möbius cancellation.

The compiled `pairedEtaCompletedMomentInverseRegion_lowProduct_eq_full`
consequently gives, for every `1<=T<=M`, every center, and every moment order,

\[
 V_\rho(k,a,M;\,de\le T)=V_\rho(k,a,M;\,de\le M).
\]

The physical prefix inside each atom still has cutoff `M`. At `T=1`,
the single cell `(1,1)` already contains that entire physical prefix.
Decreasing the product cutoff does not shorten that prefix.

`pairedEtaCompletedMomentInverseRegion_highProduct_eq_zero` proves that
the complete high-product complement is exactly zero as a complex number.
Thus its two ordered cross terms vanish exactly for this particular split.
This does not apply to arbitrary regions that cut through product fibers;
their mixed complement terms remain essential.

The stronger complex identity
`pairedEtaCompletedMomentInverseRegion_productWeight_eq_prefix` states
that arbitrary product weights `w(de)` on any positive complete product
region leave precisely `w(1)` times the full physical prefix. A product
taper with `w(1)=1` leaves the carrier unchanged; one with `w(1)=0`
annihilates it and cannot reconstruct the original current.

Finally,
`pairedEtaCurrentLowProductInverseEnergy_signed_sum_power_lower_eventually`
checks the implication at the actual signed-energy level: every admissible
moving schedule `1<=T(N)<=2*(N+2)` retains the entire off-critical lower
power. A relative saving on this low-product part would still solve the
whole arithmetic problem. There is no smaller surviving complement to
attack after such a saving.

## Corrections to the proposed block estimates

Direct substitution into the existing region estimate gives, schematically,

\[
 \operatorname{MeanAbsolute}_{A,L}\le
 T(1+\log T)^5
 \left(C_{\rho^\#}A^{-2(1-\sigma)}+C_\rho A^{-2\sigma}\right),
 \qquad T^2\le L.
\]

At `L=A`, multiplying the average by the block length returns
`A^e` times the product/logarithmic budget. The rectangle estimate similarly
retains its `ED*(1+log E)^2*(1+log(ED))^2` budget. These upper expressions
do not have a vanishing factor relative to `A^e`, even at fixed positive
product range. This audits the available estimates; it does not prove
that every sharper signed estimate must fail. Their proofs currently
pass through separate channel bounds, despite preserving a richer signed
object upstream.

A bound on complete dyadic increments can be aimed directly at the cofinal
dyadic endpoints. A generic passage from endpoint control to every natural
cutoff additionally requires control between those endpoints; it is not
automatic for arbitrary signed sequences. The contradiction itself does
not require that stronger conclusion.

The next arithmetic experiment must use the complete normalized signed
correlation. If divisor regions are introduced, their choice must cut
through product fibers to produce a nontrivial split, and all complementary
and mixed terms must be retained. The existing top-prefix hyperbolic form
represents a different energy; applying that language here requires an
exact bridge retaining the zeroth-moment coefficients. No independent
relative upper estimate is currently supplied by that change of coordinates.

## Verification

The three new modules are imported by the root library:

- `EtaLeadingFluxSignedInversePartialSum.lean`;
- `EtaInverseProductShellCollapse.lean`;
- `EtaCurrentOddWeightStepAsymptotic.lean`.

Direct warning-as-error elaboration of all three modules passed, as did
the focused build (4327 jobs), full build (9735 jobs), whole-project
declaration lint, and all 14 verbose root linters. The 14 selected terminal
axiom audits use only `propext`, `Classical.choice`, and `Quot.sound`.
The compiled status audit reports 888 project modules, 18895 declarations,
16250 theorems, no project axioms, and no placeholder dependencies.
The staged hook repeats the build, lint, integrity, freshness, and
whitespace gates before commit; the exact commit must also pass CI.
The dashboard remains an inventory of proved transport and normalization
theorems, with the arithmetic frontier open and `rhImplied:false`.

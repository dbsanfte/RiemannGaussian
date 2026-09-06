# Applying the eta heat results to the completed signed current

Review outcome, 2026-09-06: the overnight heat and matrix targets are proved,
including the joint cubic-phase/moving-tilt limit. No quantitative estimate
for the completed signed leading flux follows from the identities inspected.
The missing connection is an arithmetic kernel identity and estimate, with
cutoff and multiplicity dependence retained. This review completes the
application assessment in the [overnight plan](rh-overnight-theorem-plan.md);
it does not claim a new RH implication or an improved certificate.

## The literal target and its two branches

For an actual nontrivial zero `rho`, let `m` be its analytic multiplicity
and let `F_rho(N)` be `pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N`.
Lean already proves

\[
\sum_N (2N+1)|F_\rho(N)|<\infty
\quad\Longleftrightarrow\quad \operatorname{Re}\rho=\tfrac12.
\]

The terminal declaration is
[summable_oddEndpoint_mul_abs_topPrefixFiniteEnergyLeadingFlux_iff_re_eq_half](../RiemannGaussian/EtaEnergyLeadingFlux.lean#L598).
The preceding theorem proves the remainder flux has an unconditionally
summable first absolute moment. Thus moving work into that remainder cannot
remove the leading-current obligation.

| Multiplicity | Checked exact carrier | Data that a heat connection must preserve |
| --- | --- | --- |
| `m = 1` | [Head kernel integral](../RiemannGaussian/EtaEnergyLeadingFluxKernel.lean#L543), on the translated new-head measure times the successor finite eta measure. | The negative new head, its translation, the two completion factors, and its pairing with the successor top term. |
| `m >= 2` | [Factored adjacent-moment integral](../RiemannGaussian/EtaEnergyLeadingFluxKernelFactorization.lean#L461), on the finite eta measure at `N+2` squared. | The positive factor `2(m-1) delta_(N+1)`, adjacent centered powers of degrees `m-2` and `m-1`, the actual ordinate cosine, and the completed horizontal difference. |

In the second row, with `L = pairedEtaLogTailCutoff (N+2)`, the integrand is

\[
2(m-1)\delta_{N+1}(t-L)^{m-2}(u-L)^{m-1}
\cos(\operatorname{Im}\rho\,(u-t))
\left[w(1-\bar\rho)e^{-(1-\operatorname{Re}\rho)(t+u)}
      -w(\rho)e^{-\operatorname{Re}\rho(t+u)}\right].
\]

[The factorization](../RiemannGaussian/EtaEnergyLeadingFluxKernelFactorization.lean#L238)
is pointwise and its integral is genuinely integrable. The centered monomial
is strictly negative almost everywhere. The horizontal bracket has exactly
one crossover off the critical line, with its sign characterized by
[the oriented-crossover theorem](../RiemannGaussian/EtaEnergyLeadingFluxKernelFactorization.lean#L393).
Taking absolute values before using this difference loses its cancellation.
The multiplicity-one head is not covered by this factorization.

## What the new estimates control

The new carrier is the actual support/gap transition
`(chi(t)-chi(u))^2`, with Gaussian convolution and positive horizontal tilt.
Its exact eta spectral interpretation is proved for linear phases. It also
has independent finite-cutoff errors and exact continuous commutator kernel
identities. The nonlinear extension now proves

\[
\frac{\Lambda_{1/2+\lambda/\ell_h,\,
    \kappa t/h+\alpha t^3/(h\ell_h^2)}(h)}{h\ell_h}
\longrightarrow \mathcal K_\lambda(\kappa,\alpha),
\qquad \ell_h=\log(1/h),
\]

for fixed real parameters, together with every fixed mixed matrix entry and
an integral-of-squares formula for the limiting matrix. The complex
displacement is retained upstream. The proved Gaussian majorant is
`exp(4|lambda|) (12+11v^2)` after normalization, once
`R >= max(1,4|lambda|)` and `h=exp(-R)`.

These statements appear in
[EtaCubicHeatLimit](../RiemannGaussian/EtaCubicHeatLimit.lean),
[EtaMovingTiltGaussianBound](../RiemannGaussian/EtaMovingTiltGaussianBound.lean),
and [EtaCubicHeatGram](../RiemannGaussian/Hybrid/EtaCubicHeatGram.lean).

## Why the direct application does not close

1. **The integration carriers differ.** The higher-multiplicity current
   lives on finite support times finite support. The new leakage factor
   vanishes on that set, since both indicators equal one. Inserting it
   directly therefore does not represent the leading current. A product
   of two support/gap transition kernels could return to support, but its
   equality to the completed adjacent-moment current has not been proved.
   The translated head branch requires its own connection as well.
2. **The relevant weights vary with cutoff and multiplicity.** The bounded
   Lipschitz boundary theorem gives explicit dependence on the test bounds
   `B` and `K`. Centered moment multipliers depend on `N` and `m`; treating
   these as fixed constants would discard precisely the dependence needed
   for a summable `(2N+1)`-weighted error.
3. **Fixed moving tilt is not fixed off-axis location.** At a fixed
   horizontal coordinate `beta`, the scaling parameter would be
   `lambda_R = (beta-1/2)R`. The proved limit fixes `lambda`. Its majorant
   contains `exp(4|lambda|)`, so it does not supply the required uniform
   control for this growing parameter.
4. **The zero condition and completion remain essential.** Cubic modulation
   does not preserve eta's zeros. The linear eta spectral identity averages
   a support/gap correlation along a vertical line; it does not identify
   that positive correlation with the signed completed current at an
   individual zero. The two completion weights cannot be replaced by the
   raw positive Gram.

The proposed insertion was therefore not turned into a new triangle-bound
lemma or a restatement of first-moment summability. Neither would discharge
the missing arithmetic estimate.

## A concrete next obligation

A future heat application should first prove an exact finite-cutoff
decomposition of the **literal** head or adjacent-moment current into a
specified continuous heat-kernel pairing plus its signed error. Its statement
must retain `rho`, analytic multiplicity, the centered moment degrees,
both completion weights, the finite cutoff, and the independent heat width.
The subsequent error estimate must be strong enough for the existing
`(2N+1)`-weighted summability criterion; the main signed term still needs an
arithmetic estimate. This is a proposed research obligation, not a theorem
or an assumed premise added to Lean.

The completed overnight contribution is the quantitative boundary, heat,
spectral, commutator, and mixed-matrix mathematics. The signed connection
to RH remains open.

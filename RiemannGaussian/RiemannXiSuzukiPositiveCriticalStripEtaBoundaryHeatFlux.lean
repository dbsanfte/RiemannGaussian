import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaFlux

/-!
# Heat-weighted divisor flux for the convergent paired-eta field

The preceding module proves that the literal convergent paired-eta quotient
retains analytic multiplicity as an `L¹` radial flux. This module inserts the
actual non-holomorphic Gaussian boundary-heat kernel used by the live RH
detector.

Lean proves that the heat-weighted eta quotient is circle integrable near
every nontrivial zero and that its shrinking-circle flux returns the heat
kernel at that zero times its genuine analytic multiplicity. The complex
quotient flux is then rewritten pointwise through the normalized bilinear eta
numerators and their squared denominator.

For every finite upper-spectral divisor window, a common shrinking radius
therefore recovers exactly `2 * pi` times the existing positive heat-residue
window. These finite limiting values converge at positive heat time to
`2 * pi` times the complete RH-equivalent boundary-heat detector. The terminal
theorem packages this as a checked two-stage limit of literal convergent eta
fluxes. No interchange of the two limits and no global cancellation estimate
is assumed.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The actual Gaussian boundary-heat kernel times the literal convergent
paired-eta logarithmic quotient, written in the original zeta coordinate. -/
def pairedEtaBoundaryHeatWeightedArithmeticQuotient
    (x tau : ℝ) (s : ℂ) : ℂ :=
  suzukiChebyshevLaplaceBoundaryHeatKernel x tau (s - 1 / 2) *
    (pairedEtaArithmeticDerivativeValue s / pairedEtaCore s)

/-- The boundary-heat kernel is complex-valued only by embedding a real
function, so its imaginary part vanishes identically. -/
@[simp] theorem suzukiChebyshevLaplaceBoundaryHeatKernel_im
    (x tau : ℝ) (p : ℂ) :
    (suzukiChebyshevLaplaceBoundaryHeatKernel x tau p).im = 0 := rfl

/-- Multiplying the paired-eta quotient by the moving Gaussian heat kernel
preserves its local residue, scaled by the kernel value at the zero. -/
theorem tendsto_sub_mul_pairedEtaBoundaryHeatWeightedArithmeticQuotient
    (x tau : ℝ) (rho : NontrivialZetaZero) :
    Tendsto
      (fun s : ℂ => (s - rho.1) *
        pairedEtaBoundaryHeatWeightedArithmeticQuotient x tau s)
      (𝓝[≠] rho.1)
      (𝓝 (suzukiChebyshevLaplaceBoundaryHeatKernel x tau
          (suzukiChebyshevLaplaceZeroCoordinate rho) *
        (analyticZetaZeroMultiplicity rho : ℂ))) := by
  have hkernelFull : Tendsto
      (fun s : ℂ =>
        suzukiChebyshevLaplaceBoundaryHeatKernel x tau (s - 1 / 2))
      (𝓝 rho.1)
      (𝓝 (suzukiChebyshevLaplaceBoundaryHeatKernel x tau
        (suzukiChebyshevLaplaceZeroCoordinate rho))) := by
    have hcontinuous : Continuous (fun s : ℂ =>
        suzukiChebyshevLaplaceBoundaryHeatKernel x tau (s - 1 / 2)) :=
      (differentiable_real_suzukiChebyshevLaplaceBoundaryHeatKernel
        x tau).continuous.comp (by fun_prop)
    simpa [suzukiChebyshevLaplaceZeroCoordinate] using
      hcontinuous.tendsto rho.1
  have hkernel : Tendsto
      (fun s : ℂ =>
        suzukiChebyshevLaplaceBoundaryHeatKernel x tau (s - 1 / 2))
      (𝓝[≠] rho.1)
      (𝓝 (suzukiChebyshevLaplaceBoundaryHeatKernel x tau
        (suzukiChebyshevLaplaceZeroCoordinate rho))) :=
    hkernelFull.mono_left nhdsWithin_le_nhds
  have hquotient := tendsto_sub_mul_pairedEtaArithmeticQuotient rho
  have hproduct := hkernel.mul hquotient
  apply hproduct.congr'
  filter_upwards with s
  unfold pairedEtaBoundaryHeatWeightedArithmeticQuotient
  ring

/-- The heat-weighted convergent eta quotient is circle integrable on every
sufficiently small positive circle about a nontrivial zero. -/
theorem eventually_circleIntegrable_pairedEtaBoundaryHeatWeightedArithmeticQuotient
    (x tau : ℝ) (rho : NontrivialZetaZero) :
    ∀ᶠ r : ℝ in 𝓝[>] 0,
      CircleIntegrable
        (pairedEtaBoundaryHeatWeightedArithmeticQuotient x tau)
        rho.1 r := by
  have hquotient :=
    eventually_circleIntegrable_pairedEtaArithmeticQuotient rho
  have hkernel : Continuous (fun s : ℂ =>
      suzukiChebyshevLaplaceBoundaryHeatKernel x tau (s - 1 / 2)) :=
    (differentiable_real_suzukiChebyshevLaplaceBoundaryHeatKernel
      x tau).continuous.comp (by fun_prop)
  filter_upwards [hquotient] with r hr
  unfold pairedEtaBoundaryHeatWeightedArithmeticQuotient
  exact hr.continuousOn_mul hkernel.continuousOn

/-- The complex small-circle integral of the literal heat-weighted eta
quotient converges to `2 * pi * I` times its heat-weighted multiplicity. -/
theorem tendsto_circleIntegral_pairedEtaBoundaryHeatWeightedArithmeticQuotient
    (x tau : ℝ) (rho : NontrivialZetaZero) :
    Tendsto
      (fun r : ℝ =>
        ∮ s in C(rho.1, r),
          pairedEtaBoundaryHeatWeightedArithmeticQuotient x tau s)
      (𝓝[>] 0)
      (𝓝 ((2 * Real.pi * Complex.I) *
        (suzukiChebyshevLaplaceBoundaryHeatKernel x tau
            (suzukiChebyshevLaplaceZeroCoordinate rho) *
          (analyticZetaZeroMultiplicity rho : ℂ)))) := by
  exact tendsto_circleIntegral_nhdsGT_zero_of_tendsto_sub_mul
    (eventually_circleIntegrable_pairedEtaBoundaryHeatWeightedArithmeticQuotient
      x tau rho)
    (tendsto_sub_mul_pairedEtaBoundaryHeatWeightedArithmeticQuotient
      x tau rho)

/-- The real radial flux of the literal heat-weighted eta quotient on a
circle about one nontrivial zero. -/
def pairedEtaBoundaryHeatArithmeticRadialFlux
    (x tau : ℝ) (rho : NontrivialZetaZero) (r : ℝ) : ℝ :=
  ∫ theta : ℝ in 0..2 * Real.pi,
    (circleMap 0 r theta *
      pairedEtaBoundaryHeatWeightedArithmeticQuotient x tau
        (circleMap rho.1 r theta)).re

/-- Whenever the weighted quotient is circle integrable, its real radial
flux is the imaginary part of its complex contour integral. -/
theorem pairedEtaBoundaryHeatArithmeticRadialFlux_eq_circleIntegral_im
    (x tau : ℝ) (rho : NontrivialZetaZero) {r : ℝ}
    (hintegrable : CircleIntegrable
      (pairedEtaBoundaryHeatWeightedArithmeticQuotient x tau)
      rho.1 r) :
    pairedEtaBoundaryHeatArithmeticRadialFlux x tau rho r =
      (∮ s in C(rho.1, r),
        pairedEtaBoundaryHeatWeightedArithmeticQuotient x tau s).im := by
  exact (circleIntegral_im_eq_intervalIntegral_radialProjection
    hintegrable).symm

/-- The real heat-weighted arithmetic radial flux tends to `2 * pi` times
the real heat coefficient multiplied by genuine analytic multiplicity. -/
theorem tendsto_pairedEtaBoundaryHeatArithmeticRadialFlux
    (x tau : ℝ) (rho : NontrivialZetaZero) :
    Tendsto (pairedEtaBoundaryHeatArithmeticRadialFlux x tau rho)
      (𝓝[>] 0)
      (𝓝 (2 * Real.pi *
        (suzukiChebyshevLaplaceBoundaryHeatKernel x tau
            (suzukiChebyshevLaplaceZeroCoordinate rho)).re *
          (analyticZetaZeroMultiplicity rho : ℝ))) := by
  have hcircle :=
    tendsto_circleIntegral_pairedEtaBoundaryHeatWeightedArithmeticQuotient
      x tau rho
  have him := Complex.continuous_im.continuousAt.tendsto.comp hcircle
  have hintegrable :=
    eventually_circleIntegrable_pairedEtaBoundaryHeatWeightedArithmeticQuotient
      x tau rho
  have hflux : Tendsto
      (pairedEtaBoundaryHeatArithmeticRadialFlux x tau rho)
      (𝓝[>] 0)
      (𝓝 (((2 * Real.pi * Complex.I) *
        (suzukiChebyshevLaplaceBoundaryHeatKernel x tau
            (suzukiChebyshevLaplaceZeroCoordinate rho) *
          (analyticZetaZeroMultiplicity rho : ℂ))).im)) := by
    apply him.congr'
    filter_upwards [hintegrable] with r hr
    change
      (∮ s in C(rho.1, r),
        pairedEtaBoundaryHeatWeightedArithmeticQuotient x tau s).im =
          pairedEtaBoundaryHeatArithmeticRadialFlux x tau rho r
    exact
      (pairedEtaBoundaryHeatArithmeticRadialFlux_eq_circleIntegral_im
        x tau rho hr).symm
  convert hflux using 1
  rw [suzukiChebyshevLaplaceBoundaryHeatKernel_apply]
  norm_num
  ring

/-- The heat-weighted radial flux written directly through the normalized
bilinear eta numerators and the squared eta denominator. -/
def pairedEtaBoundaryHeatNormalizedNumeratorRadialFlux
    (x tau : ℝ) (rho : NontrivialZetaZero) (r : ℝ) : ℝ :=
  ∫ theta : ℝ in 0..2 * Real.pi,
    let s := circleMap rho.1 r theta
    (suzukiChebyshevLaplaceBoundaryHeatKernel x tau (s - 1 / 2)).re *
      ((circleMap 0 r theta).re *
          (pairedEtaLogDerivativeRealNumerator s /
            pairedEtaCoreNormSq s) -
        (circleMap 0 r theta).im *
          (pairedEtaLogDerivativeImaginaryNumerator s /
            pairedEtaCoreNormSq s))

/-- The normalized-numerator heat flux is pointwise identical to the literal
arithmetic quotient heat flux. -/
theorem pairedEtaBoundaryHeatNormalizedNumeratorRadialFlux_eq_arithmetic
    (x tau : ℝ) (rho : NontrivialZetaZero) (r : ℝ) :
    pairedEtaBoundaryHeatNormalizedNumeratorRadialFlux x tau rho r =
      pairedEtaBoundaryHeatArithmeticRadialFlux x tau rho r := by
  unfold pairedEtaBoundaryHeatNormalizedNumeratorRadialFlux
    pairedEtaBoundaryHeatArithmeticRadialFlux
  apply intervalIntegral.integral_congr
  intro theta _
  dsimp only
  rw [← pairedEtaArithmeticQuotient_re,
    ← pairedEtaArithmeticQuotient_im]
  unfold pairedEtaBoundaryHeatWeightedArithmeticQuotient
  rw [Complex.mul_re, Complex.mul_re, Complex.mul_im]
  rw [suzukiChebyshevLaplaceBoundaryHeatKernel_im]
  ring

/-- The normalized-numerator heat-flux integrand is genuinely `L¹` on every
sufficiently small positive circle about a nontrivial zero. -/
theorem eventually_intervalIntegrable_pairedEtaBoundaryHeatNormalizedNumeratorRadialFlux
    (x tau : ℝ) (rho : NontrivialZetaZero) :
    ∀ᶠ r : ℝ in 𝓝[>] 0,
      IntervalIntegrable
        (fun theta : ℝ =>
          let s := circleMap rho.1 r theta
          (suzukiChebyshevLaplaceBoundaryHeatKernel x tau
              (s - 1 / 2)).re *
            ((circleMap 0 r theta).re *
                (pairedEtaLogDerivativeRealNumerator s /
                  pairedEtaCoreNormSq s) -
              (circleMap 0 r theta).im *
                (pairedEtaLogDerivativeImaginaryNumerator s /
                  pairedEtaCoreNormSq s)))
        volume 0 (2 * Real.pi) := by
  have hcircle :=
    eventually_circleIntegrable_pairedEtaBoundaryHeatWeightedArithmeticQuotient
      x tau rho
  filter_upwards [hcircle] with r hr
  have hradial :=
    CircleIntegrable.intervalIntegrable_radialProjection hr
  apply hradial.congr
  intro theta _
  dsimp only
  rw [← pairedEtaArithmeticQuotient_re,
    ← pairedEtaArithmeticQuotient_im]
  unfold pairedEtaBoundaryHeatWeightedArithmeticQuotient
  rw [Complex.mul_re, Complex.mul_re, Complex.mul_im]
  rw [suzukiChebyshevLaplaceBoundaryHeatKernel_im]
  ring

/-- The normalized bilinear eta heat flux has the exact heat-weighted
multiplicity limit at every nontrivial zero. -/
theorem tendsto_pairedEtaBoundaryHeatNormalizedNumeratorRadialFlux
    (x tau : ℝ) (rho : NontrivialZetaZero) :
    Tendsto
      (pairedEtaBoundaryHeatNormalizedNumeratorRadialFlux x tau rho)
      (𝓝[>] 0)
      (𝓝 (2 * Real.pi *
        (suzukiChebyshevLaplaceBoundaryHeatKernel x tau
            (suzukiChebyshevLaplaceZeroCoordinate rho)).re *
          (analyticZetaZeroMultiplicity rho : ℝ))) := by
  have h := tendsto_pairedEtaBoundaryHeatArithmeticRadialFlux x tau rho
  apply h.congr'
  exact Filter.Eventually.of_forall fun r =>
    (pairedEtaBoundaryHeatNormalizedNumeratorRadialFlux_eq_arithmetic
      x tau rho r).symm

/-- At a selected upper-spectral zero, the normalized eta heat flux tends
exactly to `2 * pi` times the existing positive boundary-heat residue. -/
theorem tendsto_pairedEtaBoundaryHeatNormalizedNumeratorRadialFlux_selected
    (x tau : ℝ) (rho : NontrivialZetaZero)
    (hp : (suzukiChebyshevLaplaceZeroCoordinate rho).re < 0) :
    Tendsto
      (pairedEtaBoundaryHeatNormalizedNumeratorRadialFlux x tau rho)
      (𝓝[>] 0)
      (𝓝 (2 * Real.pi *
        (suzukiChebyshevLaplaceBoundaryHeatResidue x tau rho).re)) := by
  have h :=
    tendsto_pairedEtaBoundaryHeatNormalizedNumeratorRadialFlux
      x tau rho
  convert h using 1
  rw [suzukiChebyshevLaplaceBoundaryHeatResidue, if_pos hp,
    Complex.mul_re,
    suzukiChebyshevLaplaceBoundaryHeatKernel_im]
  norm_num
  ring

/-- The common-radius normalized eta heat flux summed over the genuine finite
upper-spectral divisor window. -/
def pairedEtaBoundaryHeatNormalizedNumeratorRadialFluxWindow
    (x tau T r : ℝ) : ℝ :=
  ∑ rho ∈ spectralUpperZetaZeroWindow T,
    pairedEtaBoundaryHeatNormalizedNumeratorRadialFlux
      x tau rho r

/-- Shrinking a common radius around every zero in one finite selected window
recovers exactly `2 * pi` times that window's positive heat-residue total. -/
theorem tendsto_pairedEtaBoundaryHeatNormalizedNumeratorRadialFluxWindow
    (x tau T : ℝ) :
    Tendsto
      (pairedEtaBoundaryHeatNormalizedNumeratorRadialFluxWindow
        x tau T)
      (𝓝[>] 0)
      (𝓝 (2 * Real.pi *
        (suzukiChebyshevLaplaceBoundaryHeatResidueWindow x tau T).re)) := by
  have hsum := tendsto_finsetSum (spectralUpperZetaZeroWindow T) fun rho hrho =>
    tendsto_pairedEtaBoundaryHeatNormalizedNumeratorRadialFlux_selected
      x tau rho
        ((suzukiChebyshevLaplaceZeroCoordinate_re_neg_iff_upper rho).mpr
          (mem_spectralUpperZetaZeroWindow.mp hrho).2)
  change Tendsto
    (fun r : ℝ => ∑ rho ∈ spectralUpperZetaZeroWindow T,
      pairedEtaBoundaryHeatNormalizedNumeratorRadialFlux
        x tau rho r) (𝓝[>] 0) _ at hsum
  have hwindow :
      suzukiChebyshevLaplaceBoundaryHeatResidueWindow x tau T =
        ∑ rho ∈ spectralUpperZetaZeroWindow T,
          suzukiChebyshevLaplaceBoundaryHeatResidue x tau rho := by
    rw [suzukiChebyshevLaplaceBoundaryHeatResidueWindow_eq_selected]
    apply Finset.sum_congr rfl
    intro rho hrho
    rw [suzukiChebyshevLaplaceBoundaryHeatResidue,
      if_pos
        ((suzukiChebyshevLaplaceZeroCoordinate_re_neg_iff_upper rho).mpr
          (mem_spectralUpperZetaZeroWindow.mp hrho).2)]
  convert hsum using 1
  · rfl
  · rw [hwindow, Complex.re_sum, Finset.mul_sum]

/-- If a finite window contains a selected zero, its normalized eta heat flux
is strictly positive on all sufficiently small common positive radii. -/
theorem eventually_pairedEtaBoundaryHeatNormalizedNumeratorRadialFluxWindow_pos
    (x tau T : ℝ) {rho : NontrivialZetaZero}
    (hrho : rho ∈ spectralUpperZetaZeroWindow T) :
    ∀ᶠ r : ℝ in 𝓝[>] 0,
      0 < pairedEtaBoundaryHeatNormalizedNumeratorRadialFluxWindow
        x tau T r := by
  have hlimit :=
    tendsto_pairedEtaBoundaryHeatNormalizedNumeratorRadialFluxWindow
      x tau T
  have htarget : 0 < 2 * Real.pi *
      (suzukiChebyshevLaplaceBoundaryHeatResidueWindow x tau T).re := by
    exact mul_pos (by positivity)
      (suzukiChebyshevLaplaceBoundaryHeatResidueWindow_re_pos_of_mem_upper
        x tau T hrho)
  exact hlimit.eventually (eventually_gt_nhds htarget)

/-- At positive heat time, the exact finite-window flux limits converge to
`2 * pi` times the complete nonnegative boundary-heat detector. -/
theorem tendsto_pairedEtaBoundaryHeatNormalizedNumeratorRadialFluxWindowLimit
    (x : ℝ) {tau : ℝ} (htau : 0 < tau) :
    Tendsto
      (fun T : ℝ => 2 * Real.pi *
        (suzukiChebyshevLaplaceBoundaryHeatResidueWindow x tau T).re)
      atTop
      (𝓝 (2 * Real.pi *
        riemannXiUpperHyperbolicBoundaryHeatTotal x tau)) := by
  have hwindow :=
    tendsto_suzukiChebyshevLaplaceBoundaryHeatResidueWindow x htau
  have hre := Complex.continuous_re.continuousAt.tendsto.comp hwindow
  have hscaled := hre.const_mul (2 * Real.pi)
  convert hscaled using 1 <;> norm_num

/-- The complete fixed-time RH detector is a checked two-stage limit of
literal, convergent, normalized-bilinear paired-eta `L¹` fluxes: first shrink
the common puncture radius in each finite divisor window, then expand the
window. This theorem does not interchange those limits. -/
theorem exists_pairedEtaBoundaryHeatNormalizedNumeratorRadialFlux_twoStageLimit
    (x : ℝ) {tau : ℝ} (htau : 0 < tau) :
    ∃ L : ℝ → ℝ,
      (∀ T : ℝ,
        Tendsto
          (pairedEtaBoundaryHeatNormalizedNumeratorRadialFluxWindow
            x tau T)
          (𝓝[>] 0) (𝓝 (L T))) ∧
      Tendsto L atTop
        (𝓝 (2 * Real.pi *
          riemannXiUpperHyperbolicBoundaryHeatTotal x tau)) := by
  refine ⟨fun T => 2 * Real.pi *
      (suzukiChebyshevLaplaceBoundaryHeatResidueWindow x tau T).re,
    ?_, ?_⟩
  · exact fun T =>
      tendsto_pairedEtaBoundaryHeatNormalizedNumeratorRadialFluxWindow
        x tau T
  · exact
      tendsto_pairedEtaBoundaryHeatNormalizedNumeratorRadialFluxWindowLimit
        x htau

end
end RiemannGaussian

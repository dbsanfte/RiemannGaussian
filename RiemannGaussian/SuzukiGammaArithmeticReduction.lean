/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiCompanionHeatDecay
import RiemannGaussian.SuzukiReflectionMassConcentration

/-!
# The remaining normalized arithmetic reflection density

Both the shifted Gamma curvature and original companion heat have global
L1 decay. The exact source therefore reduces to the weighted arithmetic
quartic with its full variable denominator. Its source limit is retained;
the independent arithmetic ceiling is not assumed or proved here.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Interval
namespace RiemannGaussian
noncomputable section

/-- The remaining quartic density retains the full original reflection
weight, Gaussian and variable arithmetic carrier denominator. -/
def suzukiGammaShiftWeightedArithmeticSource (rho : NontrivialZetaZero)
    (r c tau : ℝ) (z : ℂ) : ℂ :=
  suzukiXiReflectionWeight rho z * suzukiSmoothSpectralBoundaryHeat c tau z *
    suzukiGammaShiftArithmeticSource r (suzukiArithmeticZetaArgument z)

/-- The sum of the two independently controlled actual errors. -/
def suzukiGammaShiftSourceError (rho : NontrivialZetaZero) (r c tau : ℝ) (z : ℂ) : ℂ :=
  suzukiGammaShiftReflectionError rho r c tau z + suzukiXiReflectionCompanionHeat rho r c tau z

/-- The full original source is exactly the normalized weighted quartic
plus the two complete errors, with all phases and central values retained. -/
theorem suzukiXiSmoothReflectionSource_eq_weightedArithmetic_add_error
    (rho : NontrivialZetaZero) (r c tau : ℝ) (z : ℂ) :
    suzukiXiSmoothReflectionSource rho r c tau z =
      suzukiGammaShiftWeightedArithmeticSource rho r c tau z + suzukiGammaShiftSourceError rho r c tau z := by
  unfold suzukiXiSmoothReflectionSource suzukiXiSmoothBoundaryHeatBulk
    suzukiGammaShiftWeightedArithmeticSource suzukiGammaShiftSourceError
    suzukiGammaShiftReflectionError suzukiXiReflectionCompanionHeat
  ring

/-- Both exact errors together are integrable on the full upper half-plane. -/
theorem integrableOn_suzukiGammaShiftSourceError (rho : NontrivialZetaZero) {r tau : ℝ}
    (hr : 1 ≤ r) (htau : 0 < tau) (c : ℝ) :
    IntegrableOn (suzukiGammaShiftSourceError rho r c tau) {z : ℂ | 0 ≤ z.im} :=
  (integrableOn_suzukiGammaShiftReflectionError rho hr htau c).add
    (integrable_suzukiXiReflectionCompanionHeat rho hr htau c).integrableOn

/-- The difference between the complete actual source and the remaining
normalized arithmetic quartic tends to zero in L1 over the entire upper
half-plane at each fixed positive Gaussian time. -/
theorem tendsto_integral_norm_suzukiGammaShiftSourceError (rho : NontrivialZetaZero)
    {tau : ℝ} (htau : 0 < tau) (c : ℝ) :
    Tendsto (fun r : ℝ => ∫ z in {z : ℂ | 0 ≤ z.im},
      ‖suzukiGammaShiftSourceError rho r c tau z‖) atTop (𝓝 0) := by
  have hB := (tendsto_integral_norm_suzukiGammaShiftReflectionError rho htau c).add
    (tendsto_integral_norm_suzukiXiReflectionCompanionHeat rho htau c)
  rw [zero_add] at hB
  apply squeeze_zero' (Eventually.of_forall fun _ => integral_nonneg fun _ => norm_nonneg _) _ hB
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
  have hG := integrableOn_suzukiGammaShiftReflectionError rho hr htau c
  have hH := integrable_suzukiXiReflectionCompanionHeat rho hr htau c
  have hE := integrableOn_suzukiGammaShiftSourceError rho hr htau c
  calc
    _ ≤ ∫ z in {z : ℂ | 0 ≤ z.im}, (‖suzukiGammaShiftReflectionError rho r c tau z‖ +
        ‖suzukiXiReflectionCompanionHeat rho r c tau z‖) :=
      integral_mono hE.norm (hG.norm.add hH.norm.integrableOn) (fun _ => norm_add_le _ _)
    _ = (∫ z in {z : ℂ | 0 ≤ z.im}, ‖suzukiGammaShiftReflectionError rho r c tau z‖) +
        ∫ z in {z : ℂ | 0 ≤ z.im}, ‖suzukiXiReflectionCompanionHeat rho r c tau z‖ :=
      integral_add hG.norm hH.norm.integrableOn
    _ ≤ _ := add_le_add le_rfl (setIntegral_le_integral hH.norm (ae_of_all _ fun _ => norm_nonneg _))

/-- Both complete errors vanish on arbitrary moving cutoffs inside the
upper half-plane. This estimate is uniform in the spatial cutoff. -/
theorem tendsto_setIntegral_suzukiGammaShiftSourceError (rho : NontrivialZetaZero)
    {tau : ℝ} (htau : 0 < tau) (c : ℝ) (K : ℝ → Set ℂ)
    (hK : ∀ r : ℝ, K r ⊆ {z : ℂ | 0 ≤ z.im}) :
    Tendsto (fun r : ℝ => ∫ z in K r, suzukiGammaShiftSourceError rho r c tau z)
      atTop (𝓝 0) := by
  apply squeeze_zero_norm' _ (tendsto_integral_norm_suzukiGammaShiftSourceError rho htau c)
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
  apply (norm_integral_le_integral_norm _).trans
  exact setIntegral_mono_set (integrableOn_suzukiGammaShiftSourceError rho hr htau c).norm
    (ae_of_all _ fun _ => norm_nonneg _) (ae_of_all _ fun _ hz => hK r hz)

/-- The actual remaining weighted arithmetic density is integrable on
every compact upper region, including through its reflected node. -/
theorem integrableOn_suzukiGammaShiftWeightedArithmeticSource (rho : NontrivialZetaZero)
    {r tau : ℝ} (hr : 1 ≤ r) (htau : 0 < tau) (c : ℝ) {K : Set ℂ}
    (hK : IsCompact K) (hupper : K ⊆ {z : ℂ | 0 ≤ z.im}) :
    IntegrableOn (suzukiGammaShiftWeightedArithmeticSource rho r c tau) K := by
  have hG := (locallyIntegrable_suzukiXiSmoothReflectionSource rho
    (lt_of_lt_of_le zero_lt_one hr) c tau).integrableOn_isCompact hK
  have hE := (integrableOn_suzukiGammaShiftSourceError rho hr htau c).mono_set hupper
  convert! hG.sub hE using 1
  funext z
  simp only [Pi.sub_apply]
  rw [suzukiXiSmoothReflectionSource_eq_weightedArithmetic_add_error]
  simp

/-- Removing the two globally negligible errors retains the full
positive reflected-node source in the normalized arithmetic quartic on
each eligible rectangle. No independent arithmetic ceiling is inferred. -/
theorem tendsto_suzukiGammaShiftWeightedArithmeticSource_rectangle
    (rho : NontrivialZetaZero) (hzero : 1 / 2 < rho.1.re) {tau R : ℝ}
    (htau : 0 < tau) (hR : 1 ≤ R) (c : ℝ) (hc : 2 * |c| ≤ R)
    (hRe : 2 * |(zetaSpectralCoordinate rho.1).re| ≤ R) :
    Tendsto (fun r : ℝ => ∫ z in [[-R,R]] ×ℂ [[0,R]],
      suzukiGammaShiftWeightedArithmeticSource rho r c tau z) atTop
      (𝓝 ((2 * Real.pi * I) * ((analyticZetaZeroMultiplicity rho : ℂ)⁻¹ *
        suzukiSmoothSpectralBoundaryHeat c tau (starRingEnd ℂ (zetaSpectralCoordinate rho.1))))) := by
  let K : Set ℂ := [[-R,R]] ×ℂ [[0,R]]
  have hK : IsCompact K := isCompact_uIcc.reProdIm isCompact_uIcc
  have hupper : K ⊆ {z : ℂ | 0 ≤ z.im} := by
    intro z hz
    have hy := hz.2
    rw [uIcc_of_le (show 0 ≤ R by linarith)] at hy
    exact hy.1
  have hG := tendsto_suzukiXiSmoothReflectionSource_smoothing_area rho hzero htau hR c hc hRe
  have hE := tendsto_setIntegral_suzukiGammaShiftSourceError rho htau c (fun _ => K) (fun _ => hupper)
  have h := hG.sub hE
  rw [sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
  have hAint := integrableOn_suzukiGammaShiftWeightedArithmeticSource rho hr htau c hK hupper
  have hEint := (integrableOn_suzukiGammaShiftSourceError rho hr htau c).mono_set hupper
  change (∫ z in K, suzukiXiSmoothReflectionSource rho r c tau z) -
      (∫ z in K, suzukiGammaShiftSourceError rho r c tau z) = _
  simp_rw [suzukiXiSmoothReflectionSource_eq_weightedArithmetic_add_error]
  rw [integral_add hAint hEint, add_sub_cancel_right]

end
end RiemannGaussian

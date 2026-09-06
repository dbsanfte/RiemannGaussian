import RiemannGaussian.EtaPolynomialHeatFinitePart

/-!
# Signed second-order heat reflection on the actual eta carrier

The reflected logarithmic phase stays in the polynomial family. Its leading
Gaussian profile cancels exactly, leaving a signed difference of the two
endpoint profiles. This logarithmic tilt reflection does not introduce a
xi completion weight or a positivity assertion.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ENNReal NNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The signed endpoint profile combines the difference of arithmetic
constants with the logarithmic Gaussian moment. -/
def pairedEtaSignedEndpointHeatProfile (kappa : ℝ) : ℝ :=
  (Real.eulerMascheroniConstant - 1 - (1 - Real.log (Real.pi / 2))) * pairedEtaHeatPhaseProfile kappa +
    pairedEtaLogHeatPhaseProfile kappa

/-- Exact reflection of the second-order coefficient leaves a signed
difference of the lower and upper endpoint profiles. -/
theorem pairedEtaPolynomialHeatFinitePart_reflection (lambda kappa beta alpha : ℝ) :
    pairedEtaPolynomialHeatFinitePart lambda kappa beta alpha - Real.exp (-2 * lambda) *
      pairedEtaPolynomialHeatFinitePart (-lambda) (kappa + beta + 3 * alpha) (-beta - 6 * alpha) alpha =
      pairedEtaSignedEndpointHeatProfile kappa - Real.exp (-2 * lambda) *
        pairedEtaSignedEndpointHeatProfile (kappa + beta + 3 * alpha) := by
  have hi : Real.exp (-2 * lambda) * Real.exp (-2 * (-lambda)) = 1 := by
    rw [← Real.exp_add, show -2 * lambda + -2 * (-lambda) = 0 by ring, Real.exp_zero]
  unfold pairedEtaPolynomialHeatFinitePart pairedEtaSignedEndpointHeatProfile
  rw [show kappa + beta + 3 * alpha + (-beta - 6 * alpha) + 3 * alpha = kappa by ring]
  simp only [mul_add, mul_sub, ← mul_assoc, hi, one_mul]
  ring

/-- The signed reflected combination of the two literal eta support/gap
heat integrals at logarithmic scale `R`. -/
def pairedEtaSignedPolynomialHeat (lambda kappa beta alpha R : ℝ) : ℝ :=
  pairedEtaSupportGapGaussianLeakage (pairedEtaMovingCriticalTilt lambda R) (Real.exp (-R))
    (pairedEtaCriticalPolynomialPhase kappa beta alpha (Real.exp (-R)) R) -
  Real.exp (-2 * lambda) *
    pairedEtaSupportGapGaussianLeakage (pairedEtaMovingCriticalTilt (-lambda) R) (Real.exp (-R))
      (pairedEtaCriticalPolynomialPhase (kappa + beta + 3 * alpha) (-beta - 6 * alpha) alpha (Real.exp (-R)) R)

/-- The leading profiles cancel at every finite scale before taking a
limit; the full actual signed heat is retained in this identity. -/
theorem pairedEtaSignedPolynomialHeat_eq_finite_part_difference (lambda kappa beta alpha R : ℝ) :
    pairedEtaSignedPolynomialHeat lambda kappa beta alpha R / Real.exp (-R) =
      (pairedEtaSupportGapGaussianLeakage (pairedEtaMovingCriticalTilt lambda R) (Real.exp (-R))
        (pairedEtaCriticalPolynomialPhase kappa beta alpha (Real.exp (-R)) R) / Real.exp (-R) -
          R * pairedEtaPolynomialHeatProfile lambda kappa beta alpha) - Real.exp (-2 * lambda) *
      (pairedEtaSupportGapGaussianLeakage (pairedEtaMovingCriticalTilt (-lambda) R) (Real.exp (-R))
        (pairedEtaCriticalPolynomialPhase (kappa + beta + 3 * alpha) (-beta - 6 * alpha) alpha (Real.exp (-R)) R) /
          Real.exp (-R) - R * pairedEtaPolynomialHeatProfile (-lambda)
            (kappa + beta + 3 * alpha) (-beta - 6 * alpha) alpha) := by
  rw [pairedEtaPolynomialHeatProfile_reflection lambda kappa beta alpha]
  unfold pairedEtaSignedPolynomialHeat
  ring

/-- The signed reflection law for the actual continuous eta heat: after
the exact leading cancellation only the signed endpoint difference remains. -/
theorem pairedEtaSignedPolynomialHeat_exp_tendsto (lambda kappa beta alpha : ℝ) :
    Tendsto (fun R : ℝ ↦ pairedEtaSignedPolynomialHeat lambda kappa beta alpha R / Real.exp (-R)) atTop
      (𝓝 (pairedEtaSignedEndpointHeatProfile kappa - Real.exp (-2 * lambda) *
        pairedEtaSignedEndpointHeatProfile (kappa + beta + 3 * alpha))) := by
  have h := (pairedEtaSupportGapGaussianLeakage_polynomial_finite_part_exp_tendsto lambda kappa beta alpha).sub
    ((pairedEtaSupportGapGaussianLeakage_polynomial_finite_part_exp_tendsto (-lambda)
      (kappa + beta + 3 * alpha) (-beta - 6 * alpha) alpha).const_mul (Real.exp (-2 * lambda)))
  rw [pairedEtaPolynomialHeatFinitePart_reflection] at h
  simpa only [pairedEtaSignedPolynomialHeat_eq_finite_part_difference] using h

/-- The signed heat reflection law in the original positive heat width. -/
theorem pairedEtaSignedPolynomialHeat_tendsto (lambda kappa beta alpha : ℝ) :
    Tendsto (fun h : ℝ ↦ pairedEtaSignedPolynomialHeat lambda kappa beta alpha (Real.log (1 / h)) / h)
      (𝓝[>] 0) (𝓝 (pairedEtaSignedEndpointHeatProfile kappa - Real.exp (-2 * lambda) *
        pairedEtaSignedEndpointHeatProfile (kappa + beta + 3 * alpha))) := by
  have h := (pairedEtaSignedPolynomialHeat_exp_tendsto lambda kappa beta alpha).comp tendsto_etaHeatLogScale_atTop
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh0 : 0 < h := hh
  have he : Real.exp (-Real.log (1 / h)) = h := by
    rw [one_div, Real.log_inv, neg_neg, Real.exp_log hh0]
  simp only [Function.comp_def, he]

end

end RiemannGaussian

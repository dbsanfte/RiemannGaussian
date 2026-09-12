/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.AnalyticStripBoundary
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.CircleAverage

/-!
# The exact vertical change of variables for circle averages

Both semicircles are covered by their complete real height parameters.
The positive Jacobian is the hyperbolic secant. Integrability is transported
by the actual change-of-variables theorem before either arc is combined
with the other. No truncation in height is introduced.
-/

namespace RiemannGaussian.AnalyticStripBoundaryIntegral
noncomputable section
open Complex Function MeasureTheory Metric Set
open AnalyticStripBoundary
open scoped Topology

/-- The oppositely oriented angular map covers precisely the left semicircle. -/
theorem range_pi_sub_angle :
    range (fun u : ℝ => Real.pi - angle u) = Ioo (Real.pi / 2) (3 * Real.pi / 2) := by
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    have h : angle u ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) := range_angle ▸ mem_range_self u
    constructor <;> linarith [h.1, h.2]
  · rintro ⟨hx, hy⟩
    have h : Real.pi - x ∈ range angle := by
      rw [range_angle]
      constructor <;> linarith
    obtain ⟨u, hu⟩ := h
    exact ⟨u, by linarith⟩

/-- Integrability on the right angular arc transports to the full height line. -/
theorem integrable_angle_iff (g : ℝ → ℝ) :
    IntegrableOn g (Ioo (-(Real.pi / 2)) (Real.pi / 2)) ↔
      Integrable (fun u => (1 / Real.cosh u) * g (angle u)) := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
    (fun u _ => (hasDerivAt_angle u).hasDerivWithinAt) angle_strictMono.injective.injOn g
  simpa only [image_univ, range_angle, abs_of_pos (one_div_pos.mpr (Real.cosh_pos _)),
    smul_eq_mul, integrableOn_univ] using h

/-- The right arc's change of variables retains the complete signed integrand. -/
theorem integral_angle (g : ℝ → ℝ) :
    (∫ θ in -(Real.pi / 2)..Real.pi / 2, g θ) =
      ∫ u : ℝ, (1 / Real.cosh u) * g (angle u) := by
  have h := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun u _ => (hasDerivAt_angle u).hasDerivWithinAt) angle_strictMono.injective.injOn g
  rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), integral_Ioc_eq_integral_Ioo]
  simpa only [image_univ, range_angle, abs_of_pos (one_div_pos.mpr (Real.cosh_pos _)),
    smul_eq_mul, Measure.restrict_univ] using h

/-- Integrability on the left angular arc transports with the positive absolute Jacobian. -/
theorem integrable_pi_sub_angle_iff (g : ℝ → ℝ) :
    IntegrableOn g (Ioo (Real.pi / 2) (3 * Real.pi / 2)) ↔
      Integrable (fun u => (1 / Real.cosh u) * g (Real.pi - angle u)) := by
  have hi : Injective (fun u : ℝ => Real.pi - angle u) := by
    intro x y h
    apply angle_strictMono.injective
    linarith
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
    (fun u _ => ((hasDerivAt_angle u).const_sub Real.pi).hasDerivWithinAt) hi.injOn g
  simpa only [image_univ, range_pi_sub_angle, abs_neg,
    abs_of_pos (one_div_pos.mpr (Real.cosh_pos _)), smul_eq_mul, integrableOn_univ] using h

/-- Reversing the left angular orientation keeps the vertical integral upward. -/
theorem integral_pi_sub_angle (g : ℝ → ℝ) :
    (∫ θ in Real.pi / 2..3 * Real.pi / 2, g θ) =
      ∫ u : ℝ, (1 / Real.cosh u) * g (Real.pi - angle u) := by
  have hi : Injective (fun u : ℝ => Real.pi - angle u) := by
    intro x y h
    apply angle_strictMono.injective
    linarith
  have h := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun u _ => ((hasDerivAt_angle u).const_sub Real.pi).hasDerivWithinAt) hi.injOn g
  rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), integral_Ioc_eq_integral_Ioo]
  simpa only [image_univ, range_pi_sub_angle, abs_neg,
    abs_of_pos (one_div_pos.mpr (Real.cosh_pos _)), smul_eq_mul, Measure.restrict_univ] using h

/-- The angular Jacobian is genuinely integrable over the entire height line. -/
theorem integrable_sech : Integrable (fun u : ℝ => 1 / Real.cosh u) := by
  simpa using (integrable_angle_iff (fun _ => 1)).mp
    (continuous_const.integrableOn_Icc.mono_set Ioo_subset_Icc_self)

/-- The exact total angular Jacobian equals the length of one semicircle. -/
theorem integral_sech : (∫ u : ℝ, 1 / Real.cosh u) = Real.pi := by
  have h := integral_angle (fun _ => 1)
  simp only [mul_one, intervalIntegral.integral_const, smul_eq_mul] at h
  linarith

private theorem continuous_circle {f : ℂ → ℝ} {r : ℝ}
    (hf : ContinuousOn f (sphere 0 |r|)) : Continuous (fun θ => f (circleMap 0 r θ)) := by
  exact hf.comp_continuous (continuous_circleMap 0 r) (circleMap_mem_sphere' 0 r)

/-- Each complete positive arc integral is genuinely integrable. -/
theorem integrable_right {f : ℂ → ℝ} {r : ℝ}
    (hf : ContinuousOn f (sphere 0 |r|)) :
    Integrable (fun u => (1 / Real.cosh u) * f ((r : ℂ) * right u)) := by
  have h := (integrable_angle_iff (fun θ => f (circleMap 0 r θ))).mp
    ((continuous_circle hf).integrableOn_Icc.mono_set Ioo_subset_Icc_self)
  simpa only [circleMap_angle] using h

/-- Each complete negative arc integral is genuinely integrable. -/
theorem integrable_left {f : ℂ → ℝ} {r : ℝ}
    (hf : ContinuousOn f (sphere 0 |r|)) :
    Integrable (fun u => (1 / Real.cosh u) * f ((r : ℂ) * left u)) := by
  have h := (integrable_pi_sub_angle_iff (fun θ => f (circleMap 0 r θ))).mp
    ((continuous_circle hf).integrableOn_Icc.mono_set Ioo_subset_Icc_self)
  simpa only [circleMap_pi_sub_angle] using h

/-- The exact circle average splits into its two full height integrals.
The signed input function remains unchanged on both arcs. -/
theorem circleAverage_eq_vertical {f : ℂ → ℝ} {r : ℝ}
    (hf : ContinuousOn f (sphere 0 |r|)) :
    Real.circleAverage f 0 r = (2 * Real.pi)⁻¹ *
      ((∫ u : ℝ, (1 / Real.cosh u) * f ((r : ℂ) * right u)) +
       (∫ u : ℝ, (1 / Real.cosh u) * f ((r : ℂ) * left u))) := by
  rw [Real.circleAverage_eq_integral_add (η := -(Real.pi / 2)),
    intervalIntegral.integral_comp_add_right (fun θ => f (circleMap 0 r θ))]
  simp only [zero_add, smul_eq_mul]
  rw [show 2 * Real.pi + -(Real.pi / 2) = 3 * Real.pi / 2 by ring]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (b := Real.pi / 2) ((continuous_circle hf).intervalIntegrable _ _)
    ((continuous_circle hf).intervalIntegrable _ _)]
  rw [integral_angle, integral_pi_sub_angle]
  simp only [circleMap_angle, circleMap_pi_sub_angle]

end
end RiemannGaussian.AnalyticStripBoundaryIntegral

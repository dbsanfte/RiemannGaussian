import RiemannGaussian.EtaTranslatedLaplace
import RiemannGaussian.EtaPhaseProjectionKernel

/-!
# A compact eta projection target sharing the elementary factor

The target is the actual first logarithmic eta interval, weighted by
`exp t`. Its transform shares eta's elementary factor, so those additional
boundary zeros do not impose the obstruction they create for a plain
exponential target. At every actual nontrivial zeta zero the target
transform remains nonzero. Its critical weighted square mass is exactly one.
-/

open Complex Filter MeasureTheory Set
open scoped Classical

namespace RiemannGaussian

noncomputable section

/-- The compact first-interval target, retaining its full exponential weight. -/
def pairedEtaProjectionHead (t : ℝ) : ℂ :=
  (Ioc 0 (Real.log 2)).indicator (fun u : ℝ ↦ (Real.exp u : ℂ)) t

/-- The actual finite Laplace integral of the compact target, including at the removable point `s=1`. -/
def pairedEtaProjectionHeadTransform (s : ℂ) : ℂ :=
  ∫ t : ℝ in (0 : ℝ)..Real.log 2, Complex.exp ((1 - s) * t)

/-- The compact target is measurable. -/
theorem measurable_pairedEtaProjectionHead : Measurable pairedEtaProjectionHead :=
  (Real.measurable_exp.complex_ofReal).indicator measurableSet_Ioc

/-- The target's pointwise norm is at most two on its entire support. -/
theorem norm_pairedEtaProjectionHead_le (t : ℝ) : ‖pairedEtaProjectionHead t‖ ≤ 2 := by
  by_cases ht : t ∈ Ioc 0 (Real.log 2)
  · simp only [pairedEtaProjectionHead, indicator_of_mem ht, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos t)]
    exact (Real.exp_le_exp.mpr ht.2).trans_eq (Real.exp_log (by norm_num))
  · simp [pairedEtaProjectionHead, ht]

/-- Multiplying by the Laplace kernel retains the exact compact exponential. -/
theorem pairedEtaProjectionHead_mul_exp (s : ℂ) (t : ℝ) :
    pairedEtaProjectionHead t * Complex.exp (-s * t) =
      (Ioc 0 (Real.log 2)).indicator (fun u : ℝ ↦ Complex.exp ((1 - s) * u)) t := by
  by_cases ht : t ∈ Ioc 0 (Real.log 2)
  · simp only [pairedEtaProjectionHead, indicator_of_mem ht, Complex.ofReal_exp]
    rw [← Complex.exp_add]
    congr 1
    ring
  · simp [pairedEtaProjectionHead, ht]

/-- The full compact Laplace kernel is integrable at every complex parameter. -/
theorem integrable_pairedEtaProjectionHead_mul_exp (s : ℂ) :
    Integrable (fun t : ℝ ↦ pairedEtaProjectionHead t * Complex.exp (-s * t)) := by
  simp_rw [pairedEtaProjectionHead_mul_exp]
  apply (integrable_indicator_iff measurableSet_Ioc).mpr
  exact (show Continuous (fun t : ℝ ↦ Complex.exp ((1 - s) * t)) by fun_prop).integrableOn_Icc.mono_set Ioc_subset_Icc_self

/-- The whole-line transform is the literal first-interval integral. -/
theorem integral_pairedEtaProjectionHead_mul_exp (s : ℂ) :
    (∫ t : ℝ, pairedEtaProjectionHead t * Complex.exp (-s * t)) = pairedEtaProjectionHeadTransform s := by
  simp_rw [pairedEtaProjectionHead_mul_exp]
  rw [integral_indicator measurableSet_Ioc, pairedEtaProjectionHeadTransform,
    intervalIntegral.integral_of_le (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))]

/-- The target has exactly the same elementary factor as eta, with its sole removable denominator retained. -/
theorem pairedEtaProjectionHeadTransform_eq_factor {s : ℂ} (hs : s ≠ 1) :
    pairedEtaProjectionHeadTransform s = pairedEtaFactor s / (s - 1) := by
  have h1 : 1 - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs)
  have he : Complex.exp ((1 - s) * (Real.log 2 : ℝ)) = 2 * (2 : ℂ) ^ (-s) := by
    have hlog : Complex.log (2 : ℂ) = (Real.log (2 : ℝ) : ℂ) := by
      norm_num
    rw [Complex.cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0), hlog]
    have htwo : (2 : ℂ) = Complex.exp (Real.log 2 : ℝ) := by
      rw [← Complex.ofReal_exp, Real.exp_log (by norm_num)]
      norm_num
    rw [htwo, ← Complex.exp_add]
    congr 1
    ring
  rw [pairedEtaProjectionHeadTransform, integral_exp_mul_complex h1, Complex.ofReal_zero, mul_zero,
    Complex.exp_zero, he, pairedEtaFactor]
  rw [show 1 - s = -(s - 1) by ring, div_neg]
  ring

/-- The target shares every nonremovable elementary eta-factor zero. -/
theorem pairedEtaProjectionHeadTransform_eq_zero_of_factor {s : ℂ}
    (hs : s ≠ 1) (hfactor : pairedEtaFactor s = 0) : pairedEtaProjectionHeadTransform s = 0 := by
  rw [pairedEtaProjectionHeadTransform_eq_factor hs, hfactor, zero_div]

/-- The shared factor never loses an actual nontrivial zeta zero from the target's test. -/
theorem pairedEtaProjectionHeadTransform_ne_zero (rho : NontrivialZetaZero) :
    pairedEtaProjectionHeadTransform rho.1 ≠ 0 := by
  have hs : rho.1 ≠ 1 := by
    intro h
    have hr := NontrivialZetaZero.re_lt_one rho
    simp [h] at hr
  rw [pairedEtaProjectionHeadTransform_eq_factor hs]
  exact div_ne_zero (pairedEtaFactor_ne_zero_of_re_lt_one (NontrivialZetaZero.re_lt_one rho)) (sub_ne_zero.mpr hs)

/-- The target's critical weighted square is exactly the first-interval exponential mass. -/
theorem pairedEtaProjectionHead_weighted_sq (t : ℝ) :
    Real.exp (-t) * ‖pairedEtaProjectionHead t‖ ^ 2 =
      (Ioc 0 (Real.log 2)).indicator Real.exp t := by
  by_cases ht : t ∈ Ioc 0 (Real.log 2)
  · simp only [pairedEtaProjectionHead, indicator_of_mem ht, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos t)]
    rw [sq, ← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
  · simp [pairedEtaProjectionHead, ht]

/-- The exact complete critical square mass of the compact target is one. -/
theorem integral_pairedEtaProjectionHead_weighted_sq :
    (∫ t : ℝ, Real.exp (-t) * ‖pairedEtaProjectionHead t‖ ^ 2) = 1 := by
  simp_rw [pairedEtaProjectionHead_weighted_sq]
  rw [integral_indicator measurableSet_Ioc,
    ← intervalIntegral.integral_of_le (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)), integral_exp]
  norm_num [Real.exp_log (by norm_num : (0 : ℝ) < 2)]

end

end RiemannGaussian

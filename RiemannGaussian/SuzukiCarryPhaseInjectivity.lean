/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiCarryPhaseContinuation
import Mathlib.MeasureTheory.VectorMeasure.WithDensity
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-!
# Injectivity of the joined logarithmic cosine spectrum

The two signs of the exponential coordinate are joined before using
characteristic-function uniqueness. The diagonal is not discarded by a norm.
-/

namespace RiemannGaussian.SuzukiCarryPhaseInjectivity
noncomputable section
open Complex MeasureTheory Set Filter
open scoped BigOperators Topology

/-- Symmetric pushforward under the two disjoint exponential branches. -/
def symmetricExp (μ : Measure ℝ) : Measure ℝ :=
  μ.map Real.exp+μ.map (fun t => -Real.exp t)

instance (μ : Measure ℝ) [IsFiniteMeasure μ] : IsFiniteMeasure (symmetricExp μ) := by
  unfold symmetricExp
  infer_instance

private theorem integrable_unitExp (μ : Measure ℝ) [IsFiniteMeasure μ] (tau : ℝ) :
    Integrable (fun t : ℝ => Complex.exp ((tau*t : ℝ)*I)) μ := by
  apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
  filter_upwards with t
  simp [Complex.norm_exp]

theorem charFun_symmetricExp (μ : Measure ℝ) [IsFiniteMeasure μ] (tau : ℝ) :
    charFun (symmetricExp μ) tau = 2*(∫ t : ℝ, (Real.cos (tau*Real.exp t) : ℂ) ∂μ) := by
  unfold symmetricExp
  rw [charFun_apply_real]
  simp only [← Complex.ofReal_mul]
  rw [integral_add_measure
    (integrable_unitExp _ tau) (integrable_unitExp _ tau),
    integral_map (by fun_prop) (by fun_prop), integral_map (by fun_prop) (by fun_prop)]
  have hi (sgn : ℝ) : Integrable (fun t : ℝ => Complex.exp ((tau*(sgn*Real.exp t) : ℝ)*I)) μ := by
    apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
    filter_upwards with t
    simp [Complex.norm_exp]
  rw [← integral_add (by simpa using hi 1) (by simpa using hi (-1)), ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  have he : Complex.exp ((tau*Real.exp t : ℝ)*I)+
      Complex.exp ((tau*(-Real.exp t) : ℝ)*I) = 2*(Real.cos (tau*Real.exp t) : ℂ) := by
    rw [Complex.exp_mul_I, Complex.exp_mul_I]
    simp [Complex.ofReal_mul]
    ring
  exact he

theorem symmetricExp_injective : Function.Injective symmetricExp := by
  intro μ ν he
  apply Real.isOpenEmbedding_exp.measurableEmbedding.map_injective
  apply Measure.ext
  intro S hS
  have hh := congrArg (fun m : Measure ℝ => m (S ∩ Ioi 0)) he
  have hp : Real.exp ⁻¹' (S ∩ Ioi 0) = Real.exp ⁻¹' S := by
    ext t
    simp [Real.exp_pos]
  have hm : (fun t : ℝ => -Real.exp t) ⁻¹' (S ∩ Ioi 0) = ∅ := by
    ext t
    simp [not_lt.mpr (le_of_lt (neg_neg_of_pos (Real.exp_pos t)))]
  unfold symmetricExp at hh
  rw [Measure.add_apply, Measure.add_apply,
    Measure.map_apply Real.measurable_exp (hS.inter measurableSet_Ioi),
    Measure.map_apply (show Measurable (fun t : ℝ => -Real.exp t) by fun_prop)
      (hS.inter measurableSet_Ioi),
    Measure.map_apply Real.measurable_exp (hS.inter measurableSet_Ioi),
    Measure.map_apply (show Measurable (fun t : ℝ => -Real.exp t) by fun_prop)
      (hS.inter measurableSet_Ioi), hp, hm, measure_empty, measure_empty, add_zero, add_zero] at hh
  simpa only [Measure.map_apply Real.measurable_exp hS] using hh

/-- A real integrable logarithmic density cannot be invisible at every
cosine modulation. The positive exponential coordinate is injective. -/
theorem ae_eq_zero_of_cosineExp_eq_zero {f : ℝ → ℝ} (hf : Measurable f)
    (hi : Integrable f) (hz : ∀ tau : ℝ, ∫ t : ℝ, Real.cos (tau*Real.exp t)*f t = 0) :
    f =ᵐ[volume] 0 := by
  let μ : Measure ℝ := volume.withDensity (fun t => ENNReal.ofReal (f t))
  let ν : Measure ℝ := volume.withDensity (fun t => ENNReal.ofReal (-f t))
  let : IsFiniteMeasure μ := isFiniteMeasure_withDensity_ofReal hi.2
  let : IsFiniteMeasure ν := isFiniteMeasure_withDensity_ofReal hi.neg.2
  have hc (tau : ℝ) : (∫ t : ℝ, (Real.cos (tau*Real.exp t) : ℂ) ∂μ) =
      ∫ t : ℝ, (Real.cos (tau*Real.exp t) : ℂ) ∂ν := by
    have hp : Integrable (fun t => Real.cos (tau*Real.exp t)*max (f t) 0) := by
      apply hi.norm.mono' (by fun_prop)
      filter_upwards with t
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (show 0 ≤ max (f t) 0 from le_max_right _ _)]
      exact (mul_le_of_le_one_left (le_max_right _ _) (Real.abs_cos_le_one _)).trans
        (by rw [Real.norm_eq_abs]; exact max_le (le_abs_self _) (abs_nonneg _))
    have hn : Integrable (fun t => Real.cos (tau*Real.exp t)*max (-f t) 0) := by
      apply hi.norm.mono' (by fun_prop)
      filter_upwards with t
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (show 0 ≤ max (-f t) 0 from le_max_right _ _)]
      exact (mul_le_of_le_one_left (le_max_right _ _) (Real.abs_cos_le_one _)).trans
        (by rw [Real.norm_eq_abs]; exact max_le (neg_le_abs _) (abs_nonneg _))
    have hre : (∫ t : ℝ, Real.cos (tau*Real.exp t)*max (f t) 0) =
        ∫ t : ℝ, Real.cos (tau*Real.exp t)*max (-f t) 0 := by
      apply sub_eq_zero.mp
      rw [← integral_sub hp hn]
      have he (t : ℝ) : Real.cos (tau*Real.exp t)*max (f t) 0-
          Real.cos (tau*Real.exp t)*max (-f t) 0 = Real.cos (tau*Real.exp t)*f t := by
        rw [← mul_sub]
        by_cases ht : 0 ≤ f t
        · rw [max_eq_left ht, max_eq_right (by linarith), sub_zero]
        · rw [max_eq_right (by linarith), max_eq_left (by linarith)]
          ring
      simp_rw [he]
      exact hz tau
    unfold μ ν
    rw [integral_withDensity_eq_integral_toReal_smul (hf.ennreal_ofReal)
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top),
      integral_withDensity_eq_integral_toReal_smul ((show Measurable (fun t => -f t) by fun_prop).ennreal_ofReal)
        (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_ofReal', Complex.real_smul]
    norm_cast
    simpa [mul_comm] using hre
  have hs : symmetricExp μ = symmetricExp ν :=
    Measure.ext_of_charFun (funext fun tau => by rw [charFun_symmetricExp, charFun_symmetricExp, hc tau])
  have he : μ = ν := symmetricExp_injective hs
  have hd : volume.withDensityᵥ f = 0 := by
    rw [withDensityᵥ_eq_withDensity_pos_part_sub_withDensity_neg_part hi]
    change μ.toSignedMeasure-ν.toSignedMeasure = 0
    simp [he]
  apply hi.ae_eq_of_withDensityᵥ_eq (integrable_zero ℝ ℝ volume)
  rwa [withDensityᵥ_zero]

theorem integrable_cosineExp_mul {f : ℝ → ℂ} (hi : Integrable f) (tau : ℝ) :
    Integrable (fun t : ℝ => (Real.cos (tau*Real.exp t) : ℂ)*f t) := by
  apply hi.norm.mono' (by fun_prop)
  filter_upwards with t
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_of_le_one_left (norm_nonneg _) (Real.abs_cos_le_one _)

theorem ae_eq_zero_of_complex_cosineExp_eq_zero {f : ℝ → ℂ} (hf : Measurable f)
    (hi : Integrable f) (hz : ∀ tau : ℝ, ∫ t : ℝ, (Real.cos (tau*Real.exp t) : ℂ)*f t = 0) :
    f =ᵐ[volume] 0 := by
  have hr : (fun t => (f t).re) =ᵐ[volume] 0 := by
    apply ae_eq_zero_of_cosineExp_eq_zero (f := fun t => (f t).re)
      (Complex.continuous_re.measurable.comp hf)
      (by simpa only [Function.comp_def, RCLike.re_eq_complex_re] using hi.re)
    intro tau
    have hh := congrArg Complex.re (hz tau)
    change RCLike.re (∫ t : ℝ, (Real.cos (tau*Real.exp t) : ℂ)*f t) = 0 at hh
    rw [← integral_re (integrable_cosineExp_mul hi tau)] at hh
    change (∫ t : ℝ, ((Real.cos (tau*Real.exp t) : ℂ)*f t).re) = 0 at hh
    simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using hh
  have him : (fun t => (f t).im) =ᵐ[volume] 0 := by
    apply ae_eq_zero_of_cosineExp_eq_zero (f := fun t => (f t).im)
      (Complex.continuous_im.measurable.comp hf)
      (by simpa only [Function.comp_def, RCLike.im_eq_complex_im] using hi.im)
    intro tau
    have hh := congrArg Complex.im (hz tau)
    change RCLike.im (∫ t : ℝ, (Real.cos (tau*Real.exp t) : ℂ)*f t) = 0 at hh
    rw [← integral_im (integrable_cosineExp_mul hi tau)] at hh
    change (∫ t : ℝ, ((Real.cos (tau*Real.exp t) : ℂ)*f t).im) = 0 at hh
    simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero] using hh
  filter_upwards [hr,him] with t ht hi'
  exact Complex.ext ht hi'

end
end RiemannGaussian.SuzukiCarryPhaseInjectivity

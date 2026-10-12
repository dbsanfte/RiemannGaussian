/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiCarryPhaseCosine

/-! The integrable second-derivative density of the literal contrast. -/

namespace RiemannGaussian.SuzukiCarryPhaseDensity
noncomputable section
open Complex MeasureTheory Set Filter
open SuzukiCarryPhaseQuadrature SuzukiCarryPhaseSpectrum SuzukiCarryPhaseTransform
open SuzukiCarryPhaseContinuation SuzukiCarryPhaseCosine
open scoped BigOperators Topology

/-- Integrable logarithmic density of the literal phase-contrast source. -/
def sourceDensity (s : ℂ) (t : ℝ) : ℂ :=
  Complex.exp ((s+2)*t)*bracket s (Real.exp t)

/-- Exponential coordinate clipped only beyond the density's zero support. -/
def boundedCoordinate (t : ℝ) : ℝ := min 2 (Real.exp t)

theorem measurable_boundedCoordinate : Measurable boundedCoordinate := by
  unfold boundedCoordinate
  fun_prop

theorem boundedCoordinate_bounds (t : ℝ) : 0 < boundedCoordinate t ∧ boundedCoordinate t ≤ 2 :=
  ⟨lt_min (by norm_num) (Real.exp_pos t), min_le_left _ _⟩

theorem measurable_lagTerm_log (s : ℂ) (h : ℕ) :
    Measurable (fun t : ℝ => lagTerm s (Real.exp t) h) := by
  unfold lagTerm lagRemainder
  have hm : Measurable (fun t : ℝ =>
      overlapSum (Real.exp t) (Real.exp t/((h+1 : ℕ) : ℝ))-
        ((h+1 : ℕ) : ℝ)/Real.exp t*overlapIntegral (Real.exp t)) :=
    (measurable_overlapSum_log h).sub ((measurable_const.div Real.measurable_exp).mul
      (measurable_overlapIntegral.comp Real.measurable_exp))
  exact measurable_const.mul (Complex.measurable_ofReal.comp hm)

theorem measurable_bracket_log (s : ℂ) : Measurable (fun t : ℝ => bracket s (Real.exp t)) := by
  unfold bracket errorSpectrum
  exact ((measurable_const.mul (Complex.measurable_ofReal.comp
    (measurable_overlapIntegral.comp Real.measurable_exp))).div
      (Complex.measurable_ofReal.comp Real.measurable_exp)).add
        (Measurable.tsum (measurable_lagTerm_log s))

theorem measurable_sourceDensity (s : ℂ) : Measurable (sourceDensity s) := by
  unfold sourceDensity
  have he : Measurable (fun t : ℝ => Complex.exp ((s+2)*t)) := by fun_prop
  exact he.mul (measurable_bracket_log s)

theorem bracket_zero {v : ℝ} (hv : 2 ≤ v) (s : ℂ) : bracket s v = 0 := by
  unfold bracket errorSpectrum
  rw [overlapIntegral_zero hv, Complex.ofReal_zero, mul_zero, zero_div, zero_add]
  simp only [lagTerm, lagRemainder_zero hv, Complex.ofReal_zero, mul_zero, tsum_zero]

theorem sourceDensity_zero {t : ℝ} (ht : Real.log 2 < t) (s : ℂ) : sourceDensity s t = 0 := by
  unfold sourceDensity
  rw [bracket_zero (((Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 2)).mp ht).le), mul_zero]

theorem sourceDensity_norm_le {s : ℂ} (hs : 0 < s.re) {t : ℝ} (ht : t ≤ Real.log 2) :
    ‖sourceDensity s t‖ ≤
      (3*‖SuzukiCarryPhaseEta.eta (s-1)‖+8*powerBudget s)*Real.exp ((s.re+1)*t) := by
  have hv := Real.exp_pos t
  have hv2 : Real.exp t ≤ 2 := by
    calc
      Real.exp t ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr ht
      _ = 2 := Real.exp_log (by norm_num)
  have hb : ‖bracket s (Real.exp t)‖ ≤
      3*‖SuzukiCarryPhaseEta.eta (s-1)‖/Real.exp t+2*Real.exp t*powerBudget s := by
    unfold bracket
    apply (norm_add_le _ _).trans
    simp only [norm_div, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hv]
    exact add_le_add
      (div_le_div_of_nonneg_right
        (by nlinarith [overlapIntegral_abs_le hv.le, norm_nonneg (SuzukiCarryPhaseEta.eta (s-1))]) hv.le)
      (errorSpectrum_norm_le hs hv)
  unfold sourceDensity
  rw [norm_mul, Complex.norm_exp]
  have he : ((s+2)*(t : ℂ)).re = (s.re+2)*t := by simp [Complex.mul_re]
  rw [he]
  calc
    _ ≤ Real.exp ((s.re+2)*t)*(3*‖SuzukiCarryPhaseEta.eta (s-1)‖/Real.exp t+
        2*Real.exp t*powerBudget s) := mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
    _ = (3*‖SuzukiCarryPhaseEta.eta (s-1)‖+2*(Real.exp t)^2*powerBudget s)*
        Real.exp ((s.re+1)*t) := by
      rw [show (s.re+2)*t = (s.re+1)*t+t by ring, Real.exp_add]
      field_simp
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      have hsq : (Real.exp t)^2 ≤ 4 := by nlinarith
      have hm := mul_le_mul_of_nonneg_right hsq (powerBudget_nonneg s)
      linarith

theorem integrable_sourceDensity {s : ℂ} (hs : 0 < s.re) : Integrable (sourceDensity s) := by
  have hp : 0 < s.re+1 := by linarith
  let B : ℝ := 3*‖SuzukiCarryPhaseEta.eta (s-1)‖+8*powerBudget s
  have hi : Integrable ((Iic (Real.log 2)).indicator (fun t : ℝ => B*Real.exp ((s.re+1)*t))) :=
    (integrable_indicator_iff measurableSet_Iic).mpr
      ((integrableOn_exp_mul_Iic hp (Real.log 2)).const_mul B)
  apply hi.mono' (measurable_sourceDensity s).aestronglyMeasurable
  filter_upwards with t
  by_cases ht : t ≤ Real.log 2
  · rw [Set.indicator_of_mem (show t ∈ Iic (Real.log 2) from ht)]
    exact sourceDensity_norm_le hs ht
  · rw [sourceDensity_zero (lt_of_not_ge ht), norm_zero,
      Set.indicator_of_notMem (show t ∉ Iic (Real.log 2) from ht)]

theorem sourceDensity_not_ae_zero {y : ℝ} (hy : y ≠ 0) :
    ¬ sourceDensity (1-I*y) =ᵐ[volume] 0 := by
  have hb := Real.tendsto_exp_atBot_nhdsGT.eventually (eventually_bracket_ne_zero hy)
  have he : ∀ᶠ t : ℝ in atBot, sourceDensity (1-I*y) t ≠ 0 := by
    filter_upwards [hb] with t ht
    exact mul_ne_zero (Complex.exp_ne_zero _) ht
  obtain ⟨T, hT⟩ := eventually_atBot.mp he
  intro hz
  have hnull : volume {t : ℝ | sourceDensity (1-I*y) t ≠ 0} = 0 := by
    simpa only [Pi.zero_apply] using (ae_iff.mp hz)
  have hin : Ioo (T-1) T ⊆ {t : ℝ | sourceDensity (1-I*y) t ≠ 0} :=
    fun t ht => hT t ht.2.le
  have hn := measure_mono_null hin hnull
  simp [Real.volume_Ioo] at hn

theorem contrast_eq_sourceDensity {s : ℂ} (hs : 0 < s.re) (tau : ℝ) :
    SuzukiCarryMellinRate.continuumResponse s tau-SuzukiCarryMellinRate.continuumResponse s 0 =
      Complex.exp ((s+1)*(Real.log 2 : ℂ))*contrastResponse boundedCoordinate (sourceDensity s) tau := by
  rw [contrast_eq_spectrum_integral hs]
  unfold contrastResponse
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  by_cases ht : t ≤ Real.log 2
  · have hv : Real.exp t ≤ 2 := by
      calc
        Real.exp t ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr ht
        _ = 2 := Real.exp_log (by norm_num)
    rw [boundedCoordinate, min_eq_right hv, sourceDensity]
    have he : Complex.exp ((s+2)*(t : ℂ)) =
        Complex.exp (s*t)*(Real.exp t : ℂ)^2 := by
      rw [show (s+2)*(t : ℂ) = s*t+(t : ℂ)+(t : ℂ) by ring,
        Complex.exp_add, Complex.exp_add, ← Complex.ofReal_exp]
      ring
    rw [he]
    push_cast
    field_simp
  · rw [sourceDensity_zero (lt_of_not_ge ht), mul_zero,
      bracket_zero (((Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 2)).mp (lt_of_not_ge ht)).le),
      mul_zero]

end
end RiemannGaussian.SuzukiCarryPhaseDensity

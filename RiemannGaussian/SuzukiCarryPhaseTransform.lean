/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiCarryPhaseLag
import RiemannGaussian.SuzukiCarryPhaseSpectrum
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Signed lag transform

The ordinary overlap quadrature is substituted before the alternating
bulk is continued. All identities refer to the original tent and phase.
-/

namespace RiemannGaussian.SuzukiCarryPhaseTransform
noncomputable section
open Complex MeasureTheory Set Filter
open SuzukiCarryMellinLimit SuzukiCarryMellinRate SuzukiCarryPhaseQuadrature
open SuzukiCarryPhaseHolomorphy SuzukiCarryPhaseLag SuzukiCarryPhaseSpectrum
open scoped BigOperators Topology

/-- Logarithmic density of the overlap-integral phase contrast. -/
def bulkDensity (tau t : ℝ) : ℝ :=
  (Real.cos (tau*Real.exp t)-1)*overlapIntegral (Real.exp t)/Real.exp t

/-- Logarithmic density of one exact lag quadrature correction. -/
def remainderDensity (tau : ℝ) (h : ℕ) (t : ℝ) : ℝ :=
  (Real.cos (tau*Real.exp t)-1)*lagRemainder (Real.exp t) (h+1)

/-- Unregularized density of one literal lag overlap. -/
def ordinaryDensity (tau : ℝ) (h : ℕ) (t : ℝ) : ℝ :=
  (Real.cos (tau*Real.exp t)-1)*
    overlapSum (Real.exp t) (Real.exp t/((h+1 : ℕ) : ℝ))

theorem measurable_overlapIntegral : Measurable overlapIntegral := by
  unfold overlapIntegral smallOverlapIntegral largeOverlapIntegral
  apply Measurable.ite (measurableSet_le measurable_id measurable_const) (by fun_prop)
  exact Measurable.ite (measurableSet_le measurable_id measurable_const)
    (by fun_prop) measurable_const

theorem measurable_overlapSum_log (h : ℕ) :
    Measurable (fun t : ℝ => overlapSum (Real.exp t) (Real.exp t/((h+1 : ℕ) : ℝ))) := by
  classical
  let count : ℝ → ℕ := fun t => ⌊3/(Real.exp t/((h+1 : ℕ) : ℝ))⌋₊+1
  have mc : Measurable count :=
    (Nat.measurable_floor.comp (measurable_const.div (Real.measurable_exp.div_const _))).add_const 1
  have he : (fun t : ℝ => overlapSum (Real.exp t) (Real.exp t/((h+1 : ℕ) : ℝ))) =
      fun t => ∑' n : ℕ, if n < count t then
        tent ((n : ℝ)*(Real.exp t/((h+1 : ℕ) : ℝ)))*
          tent ((n : ℝ)*(Real.exp t/((h+1 : ℕ) : ℝ))+Real.exp t) else 0 := by
    funext t
    rw [tsum_eq_sum (s := Finset.range (count t))
      (fun n hn => by rw [ite_eq_right (by simpa only [Finset.mem_range] using hn)])]
    apply Finset.sum_congr rfl
    intro n hn
    split_ifs with hn'
    · rfl
    · exact (hn' (Finset.mem_range.mp hn)).elim
  rw [he]
  apply Measurable.tsum
  intro n
  apply Measurable.ite (measurableSet_lt measurable_const mc) _ measurable_const
  unfold tent
  fun_prop

theorem measurable_bulkDensity (tau : ℝ) : Measurable (bulkDensity tau) := by
  unfold bulkDensity
  exact ((Real.continuous_cos.measurable.comp (measurable_const.mul Real.measurable_exp)).sub
    measurable_const).mul (measurable_overlapIntegral.comp Real.measurable_exp) |>.div
      Real.measurable_exp

theorem measurable_remainderDensity (tau : ℝ) (h : ℕ) :
    Measurable (remainderDensity tau h) := by
  unfold remainderDensity lagRemainder
  exact ((Real.continuous_cos.measurable.comp (measurable_const.mul Real.measurable_exp)).sub
    measurable_const).mul ((measurable_overlapSum_log h).sub
      ((measurable_const.div Real.measurable_exp).mul
        (measurable_overlapIntegral.comp Real.measurable_exp)))

theorem overlapIntegral_abs_le {v : ℝ} (hv : 0 ≤ v) : |overlapIntegral v| ≤ 3 := by
  unfold overlapIntegral
  split_ifs with h1 h2
  · have hsq : v^2 ≤ 1 := by nlinarith
    have hcu : v^3 ≤ 1 := by nlinarith [mul_nonneg hv (sub_nonneg.mpr h1)]
    rw [abs_le]
    unfold smallOverlapIntegral
    constructor <;> nlinarith [pow_nonneg hv 3]
  · have hb : 0 ≤ 2-v ∧ 2-v ≤ 1 := by constructor <;> linarith
    have he : (2-v)^3 ≤ 1 := by nlinarith [mul_nonneg hb.1 (sub_nonneg.mpr hb.2)]
    unfold largeOverlapIntegral
    rw [abs_of_nonneg (by positivity)]
    nlinarith
  · norm_num

theorem overlapIntegral_zero {v : ℝ} (hv : 2 ≤ v) : overlapIntegral v = 0 := by
  unfold overlapIntegral
  rw [ite_eq_right (by linarith : ¬v ≤ 1)]
  split_ifs with h2
  · have he : v = 2 := by linarith
    simp [he, largeOverlapIntegral]
  · rfl

theorem lagRemainder_zero {v : ℝ} (hv : 2 ≤ v) (h : ℕ) : lagRemainder v h = 0 := by
  rw [lagRemainder, overlapSum_eq_zero hv, overlapIntegral_zero hv, mul_zero, sub_self]

private theorem cos_contrast_abs_le (v : ℝ) : |Real.cos v-1| ≤ v^2/2 := by
  rw [abs_of_nonpos (sub_nonpos.mpr (Real.cos_le_one v))]
  linarith [Real.one_sub_sq_div_two_le_cos (x := v)]

theorem bulkDensity_abs_le (tau t : ℝ) : |bulkDensity tau t| ≤ 3*tau^2 := by
  by_cases ht : Real.exp t ≤ 2
  · have hv := Real.exp_pos t
    unfold bulkDensity
    rw [abs_div, abs_mul, abs_of_pos hv]
    calc
      _ ≤ ((tau*Real.exp t)^2/2)*3/Real.exp t := by
        gcongr
        · exact cos_contrast_abs_le _
        · exact overlapIntegral_abs_le hv.le
      _ ≤ _ := by
        have he : ((tau*Real.exp t)^2/2)*3/Real.exp t = 3/2*tau^2*Real.exp t := by
          field_simp
        rw [he]
        nlinarith [sq_nonneg tau]
  · rw [bulkDensity, overlapIntegral_zero (by linarith), mul_zero, zero_div, abs_zero]
    positivity

theorem bulkDensity_zero (tau : ℝ) {t : ℝ} (ht : Real.log 2 < t) : bulkDensity tau t = 0 := by
  have hv : 2 ≤ Real.exp t := ((Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 2)).mp ht).le
  rw [bulkDensity, overlapIntegral_zero hv, mul_zero, zero_div]

theorem remainderDensity_abs_le (tau : ℝ) (h : ℕ) (t : ℝ) :
    |remainderDensity tau h t| ≤ 8/((h+1 : ℕ) : ℝ) := by
  by_cases ht : Real.exp t ≤ 2
  · unfold remainderDensity
    rw [abs_mul]
    have hc : |Real.cos (tau*Real.exp t)-1| ≤ 2 := by
      rw [abs_le]
      constructor <;> linarith [Real.neg_one_le_cos (tau*Real.exp t), Real.cos_le_one (tau*Real.exp t)]
    calc
      _ ≤ 2*(2*Real.exp t/((h+1 : ℕ) : ℝ)) :=
        mul_le_mul hc (lagRemainder_abs_le (Real.exp_pos t) (by omega))
          (abs_nonneg _) (by norm_num)
      _ = 4*Real.exp t/((h+1 : ℕ) : ℝ) := by ring
      _ ≤ _ := div_le_div_of_nonneg_right (by linarith) (by positivity)
  · rw [remainderDensity, lagRemainder_zero (by linarith), mul_zero, abs_zero]
    positivity

theorem remainderDensity_zero (tau : ℝ) (h : ℕ) {t : ℝ} (ht : Real.log 2 < t) :
    remainderDensity tau h t = 0 := by
  have hv : 2 ≤ Real.exp t := ((Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 2)).mp ht).le
  rw [remainderDensity, lagRemainder_zero hv, mul_zero]

theorem ordinaryDensity_eq (tau : ℝ) (h : ℕ) (t : ℝ) :
    ordinaryDensity tau h t = ((h+1 : ℕ) : ℝ)*bulkDensity tau t+remainderDensity tau h t := by
  unfold ordinaryDensity bulkDensity remainderDensity lagRemainder
  ring

theorem analytic_bulkMellin (tau : ℝ) :
    AnalyticOnNhd ℂ (logMellin (bulkDensity tau)) {s : ℂ | 0 < s.re} :=
  analytic_logMellin (measurable_bulkDensity tau) (by positivity)
    (bulkDensity_abs_le tau) (fun _ ht => bulkDensity_zero tau ht)

theorem analytic_remainderMellin (tau : ℝ) (h : ℕ) :
    AnalyticOnNhd ℂ (logMellin (remainderDensity tau h)) {s : ℂ | 0 < s.re} :=
  analytic_logMellin (measurable_remainderDensity tau h) (by positivity)
    (remainderDensity_abs_le tau h) (fun _ ht => remainderDensity_zero tau h ht)

theorem measurable_ordinaryDensity (tau : ℝ) (h : ℕ) :
    Measurable (ordinaryDensity tau h) := by
  have he : ordinaryDensity tau h = fun t =>
      ((h+1 : ℕ) : ℝ)*bulkDensity tau t+remainderDensity tau h t :=
    funext (ordinaryDensity_eq tau h)
  rw [he]
  exact (measurable_const.mul (measurable_bulkDensity tau)).add
    (measurable_remainderDensity tau h)

theorem ordinaryDensity_abs_le (tau : ℝ) (h : ℕ) (t : ℝ) :
    |ordinaryDensity tau h t| ≤ (3*tau^2+8)*((h+1 : ℕ) : ℝ) := by
  have hp : (0 : ℝ) < (h+1 : ℕ) := by positivity
  have h1 : (1 : ℝ) ≤ (h+1 : ℕ) := by exact_mod_cast (show 1 ≤ h+1 by omega)
  rw [ordinaryDensity_eq]
  apply (abs_add_le _ _).trans
  rw [abs_mul, abs_of_pos hp]
  calc
    _ ≤ ((h+1 : ℕ) : ℝ)*(3*tau^2)+8/((h+1 : ℕ) : ℝ) :=
      add_le_add (mul_le_mul_of_nonneg_left (bulkDensity_abs_le tau t) hp.le)
        (remainderDensity_abs_le tau h t)
    _ ≤ _ := by
      have hh : 8/((h+1 : ℕ) : ℝ) ≤ 8*((h+1 : ℕ) : ℝ) := by
        apply (div_le_iff₀ hp).mpr
        nlinarith
      nlinarith

theorem ordinaryDensity_zero (tau : ℝ) (h : ℕ) {t : ℝ} (ht : Real.log 2 < t) :
    ordinaryDensity tau h t = 0 := by
  rw [ordinaryDensity_eq, bulkDensity_zero tau ht, remainderDensity_zero tau h ht,
    mul_zero, add_zero]

theorem ordinaryMellin_eq {s : ℂ} (hs : 0 < s.re) (tau : ℝ) (h : ℕ) :
    logMellin (ordinaryDensity tau h) s =
      ((h+1 : ℕ) : ℂ)*logMellin (bulkDensity tau) s+
        logMellin (remainderDensity tau h) s := by
  have ib := integrable_logWeight (measurable_bulkDensity tau) (by positivity)
    (bulkDensity_abs_le tau) (fun _ ht => bulkDensity_zero tau ht) hs
  have ir := integrable_logWeight (measurable_remainderDensity tau h) (by positivity)
    (remainderDensity_abs_le tau h) (fun _ ht => remainderDensity_zero tau h ht) hs
  have he : (fun t : ℝ => Complex.exp (s*t)*(ordinaryDensity tau h t : ℂ)) =
      fun t : ℝ => ((h+1 : ℕ) : ℂ)*(Complex.exp (s*t)*(bulkDensity tau t : ℂ))+
        Complex.exp (s*t)*(remainderDensity tau h t : ℂ) := by
    funext t
    rw [ordinaryDensity_eq]
    push_cast
    ring
  unfold logMellin
  rw [he, integral_add (ib.const_mul _) ir, integral_const_mul]

/-- Mellin coefficient of one signed lag correction. -/
def remainderCoefficient (tau : ℝ) (h : ℕ) (s : ℂ) : ℂ :=
  (-1 : ℂ)^(h+1)*Complex.exp (-s*(Real.log (h+1) : ℂ))*
    logMellin (remainderDensity tau h) s

theorem remainderCoefficient_norm_le {s : ℂ} (hs : 0 < s.re) (tau : ℝ) (h : ℕ) :
    ‖remainderCoefficient tau h s‖ ≤
      (8*Real.exp (s.re*Real.log 2)/s.re)*((h+1 : ℕ) : ℝ)^(-s.re-1) := by
  have hh : (0 : ℝ) < (h+1 : ℕ) := by positivity
  have hn : ‖Complex.exp (-s*(Real.log (h+1) : ℂ))‖ =
      ((h+1 : ℕ) : ℝ)^(-s.re) := by
    rw [Complex.norm_exp, Real.rpow_def_of_pos hh]
    congr 1
    simp [Complex.mul_re, mul_comm]
  unfold remainderCoefficient
  rw [norm_mul, norm_mul, norm_pow]
  norm_num only [norm_neg, norm_one, one_pow, one_mul]
  rw [hn]
  calc
    _ ≤ ((h+1 : ℕ) : ℝ)^(-s.re)*
        ((8/((h+1 : ℕ) : ℝ))*Real.exp (s.re*Real.log 2)/s.re) :=
      mul_le_mul_of_nonneg_left
        (norm_logMellin_le (by positivity) (remainderDensity_abs_le tau h)
          (fun _ ht => remainderDensity_zero tau h ht) hs) (by positivity)
    _ = _ := by
      rw [show -s.re-1 = -s.re+(-1) by ring, Real.rpow_add hh, Real.rpow_neg_one]
      ring

theorem summable_remainderCoefficient {s : ℂ} (hs : 0 < s.re) (tau : ℝ) :
    Summable (fun h => remainderCoefficient tau h s) :=
  ((summable_powerBudget hs).mul_left (8*Real.exp (s.re*Real.log 2)/s.re)).of_norm_bounded
    (remainderCoefficient_norm_le hs tau)

theorem analytic_remainderCoefficient (tau : ℝ) (h : ℕ) :
    AnalyticOnNhd ℂ (remainderCoefficient tau h) {s : ℂ | 0 < s.re} := by
  intro s hs
  unfold remainderCoefficient
  exact (analyticAt_const.mul
    ((analyticAt_id.neg.mul analyticAt_const).cexp)).mul
      (analytic_remainderMellin tau h s hs)

/-- Analytic lag response with the eta channel and all corrections joined. -/
def regularizedResponse (s : ℂ) (tau : ℝ) : ℂ :=
  Complex.exp ((s+1)*(Real.log 2 : ℂ))*
    (-SuzukiCarryPhaseEta.eta (s-1)*logMellin (bulkDensity tau) s+
      ∑' h : ℕ, remainderCoefficient tau h s)

theorem analytic_remainderSum (tau : ℝ) :
    AnalyticOnNhd ℂ (fun s => ∑' h : ℕ, remainderCoefficient tau h s)
      {s : ℂ | 0 < s.re} := by
  intro s hs
  change 0 < s.re at hs
  let a : ℝ := s.re/2
  let b : ℝ := s.re+1
  let U : Set ℂ := {w | a < w.re ∧ w.re < b}
  have ha : 0 < a := by dsimp [a]; linarith
  have hU : IsOpen U := (isOpen_lt continuous_const continuous_re).inter
    (isOpen_lt continuous_re continuous_const)
  have hmem : s ∈ U := by dsimp [U, a, b]; constructor <;> linarith
  have hp : Summable (fun h : ℕ => ((h+1 : ℕ) : ℝ)^(-a-1)) := by
    have hp : Summable (fun h : ℕ => (h : ℝ)^(-a-1)) :=
      Real.summable_nat_rpow.mpr (by linarith)
    exact (summable_nat_add_iff 1).mpr hp
  have hdiff : DifferentiableOn ℂ
      (fun w => ∑' h : ℕ, remainderCoefficient tau h w) U := by
    refine Complex.differentiableOn_tsum_of_summable_norm
      (hp.mul_left (8*Real.exp (b*Real.log 2)/a)) ?_ hU ?_
    · intro h w hw
      exact (analytic_remainderCoefficient tau h w (ha.trans hw.1)).differentiableAt.differentiableWithinAt
    · intro h w hw
      have hwpos := ha.trans hw.1
      apply (remainderCoefficient_norm_le hwpos tau h).trans
      apply mul_le_mul _ _ (by positivity) (by positivity)
      · apply div_le_div₀ (by positivity) _ ha hw.1.le
        gcongr
        exact hw.2.le
      · exact Real.rpow_le_rpow_of_exponent_le
          (by exact_mod_cast (show 1 ≤ h+1 by omega)) (by linarith [hw.1])
  exact hdiff.analyticAt (hU.mem_nhds hmem)

theorem analytic_regularizedResponse (tau : ℝ) :
    AnalyticOnNhd ℂ (fun s => regularizedResponse s tau) {s : ℂ | 0 < s.re} := by
  intro s hs
  unfold regularizedResponse
  apply ((analyticAt_id.add analyticAt_const).mul analyticAt_const).cexp.mul
  apply AnalyticAt.add _ (analytic_remainderSum tau s hs)
  have hshift : AnalyticAt ℂ (fun z : ℂ => z-1) s := by fun_prop
  have heta : AnalyticAt ℂ (fun z : ℂ => SuzukiCarryPhaseEta.eta (z-1)) s :=
    (SuzukiCarryPhaseEta.analytic_eta (s-1) (mem_univ _)).comp
      (f := fun z : ℂ => z-1) (x := s) hshift
  exact heta.neg.mul (analytic_bulkMellin tau s hs)

end
end RiemannGaussian.SuzukiCarryPhaseTransform

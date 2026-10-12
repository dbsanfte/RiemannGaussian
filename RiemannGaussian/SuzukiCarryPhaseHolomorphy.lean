/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiCarryMellinRate
import Mathlib.Probability.Moments.ComplexMGF

/-!
# Holomorphic logarithmic Mellin integrals

This leaf supplies analytic continuation for the literal signed lag
response. Signed densities are joined before continuation; no prime
measure or source-smallness estimate is asserted.
-/

namespace RiemannGaussian.SuzukiCarryPhaseHolomorphy
noncomputable section
open Complex MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology ENNReal

/-- Mellin integral written in the logarithmic coordinate. -/
def logMellin (f : ℝ → ℝ) (s : ℂ) : ℂ :=
  ∫ t : ℝ, Complex.exp (s*t)*(f t : ℂ)

theorem integrable_logWeight {f : ℝ → ℝ} (hf : Measurable f)
    {B U : ℝ} (_hB : 0 ≤ B) (hb : ∀ t, |f t| ≤ B)
    (hz : ∀ t, U < t → f t = 0) {s : ℂ} (hs : 0 < s.re) :
    Integrable (fun t : ℝ => Complex.exp (s*t)*(f t : ℂ)) := by
  have hm : Integrable ((Iic U).indicator (fun t : ℝ => B*Real.exp (s.re*t))) :=
    (integrable_indicator_iff measurableSet_Iic).mpr
      ((integrableOn_exp_mul_Iic hs U).const_mul B)
  apply hm.mono' (by fun_prop)
  filter_upwards with t
  by_cases ht : t ≤ U
  · rw [Set.indicator_of_mem (show t ∈ Iic U from ht), norm_mul, Complex.norm_exp, Complex.norm_real,
      Real.norm_eq_abs]
    have he : (s*(t : ℂ)).re = s.re*t := by simp [Complex.mul_re]
    rw [he]
    nlinarith [hb t, Real.exp_pos (s.re*t)]
  · rw [hz t (lt_of_not_ge ht), Complex.ofReal_zero, mul_zero, norm_zero,
      Set.indicator_of_notMem (show t ∉ Iic U from ht)]

theorem norm_logMellin_le {f : ℝ → ℝ} {B U : ℝ} (_hB : 0 ≤ B)
    (hb : ∀ t, |f t| ≤ B) (hz : ∀ t, U < t → f t = 0)
    {s : ℂ} (hs : 0 < s.re) :
    ‖logMellin f s‖ ≤ B*Real.exp (s.re*U)/s.re := by
  have hm : Integrable ((Iic U).indicator (fun t : ℝ => B*Real.exp (s.re*t))) :=
    (integrable_indicator_iff measurableSet_Iic).mpr
      ((integrableOn_exp_mul_Iic hs U).const_mul B)
  unfold logMellin
  calc
    _ ≤ ∫ t : ℝ, (Iic U).indicator (fun t : ℝ => B*Real.exp (s.re*t)) t := by
      apply norm_integral_le_of_norm_le hm
      filter_upwards with t
      by_cases ht : t ≤ U
      · rw [Set.indicator_of_mem (show t ∈ Iic U from ht), norm_mul, Complex.norm_exp, Complex.norm_real,
          Real.norm_eq_abs]
        have he : (s*(t : ℂ)).re = s.re*t := by simp [Complex.mul_re]
        rw [he]
        nlinarith [hb t, Real.exp_pos (s.re*t)]
      · rw [hz t (lt_of_not_ge ht), Complex.ofReal_zero, mul_zero, norm_zero,
          Set.indicator_of_notMem (show t ∉ Iic U from ht)]
    _ = _ := by
      rw [integral_indicator measurableSet_Iic, integral_const_mul,
        integral_exp_mul_Iic hs]
      ring

theorem integral_norm_logWeight_le {f : ℝ → ℝ} (hf : Measurable f)
    {B U : ℝ} (hB : 0 ≤ B) (hb : ∀ t, |f t| ≤ B)
    (hz : ∀ t, U < t → f t = 0) {s : ℂ} (hs : 0 < s.re) :
    (∫ t : ℝ, ‖Complex.exp (s*t)*(f t : ℂ)‖) ≤
      B*Real.exp (s.re*U)/s.re := by
  have hm : Integrable ((Iic U).indicator (fun t : ℝ => B*Real.exp (s.re*t))) :=
    (integrable_indicator_iff measurableSet_Iic).mpr
      ((integrableOn_exp_mul_Iic hs U).const_mul B)
  calc
    _ ≤ ∫ t : ℝ, (Iic U).indicator (fun t : ℝ => B*Real.exp (s.re*t)) t := by
      apply integral_mono (integrable_logWeight hf hB hb hz hs).norm hm
      intro t
      change ‖Complex.exp (s*t)*(f t : ℂ)‖ ≤
        (Iic U).indicator (fun t : ℝ => B*Real.exp (s.re*t)) t
      by_cases ht : t ≤ U
      · rw [Set.indicator_of_mem (show t ∈ Iic U from ht), norm_mul, Complex.norm_exp,
          Complex.norm_real, Real.norm_eq_abs]
        have he : (s*(t : ℂ)).re = s.re*t := by simp [Complex.mul_re]
        rw [he]
        nlinarith [hb t, Real.exp_pos (s.re*t)]
      · rw [hz t (lt_of_not_ge ht), Complex.ofReal_zero, mul_zero, norm_zero,
          Set.indicator_of_notMem (show t ∉ Iic U from ht)]
    _ = _ := by
      rw [integral_indicator measurableSet_Iic, integral_const_mul,
        integral_exp_mul_Iic hs]
      ring

private def density (f : ℝ → ℝ) : Measure ℝ :=
  volume.withDensity (fun t => ENNReal.ofReal (f t))

private theorem analytic_positive {f : ℝ → ℝ} (hf : Measurable f)
    (hp : ∀ t, 0 ≤ f t)
    (hi : ∀ a : ℝ, 0 < a → Integrable (fun t : ℝ => Real.exp (a*t)*f t)) :
    AnalyticOnNhd ℂ (logMellin f) {s : ℂ | 0 < s.re} := by
  have hm (a : ℝ) (ha : 0 < a) : a ∈ integrableExpSet id (density f) := by
    change Integrable (fun t : ℝ => Real.exp (a*t)) _
    rw [density, integrable_withDensity_iff_integrable_smul₀' hf.aemeasurable.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    apply (hi a ha).congr
    filter_upwards with t
    rw [ENNReal.toReal_ofReal (hp t), smul_eq_mul]
    ring
  have he (s : ℂ) : logMellin f s = complexMGF id (density f) s := by
    rw [logMellin, complexMGF, density,
      integral_withDensity_eq_integral_toReal_smul₀ hf.aemeasurable.ennreal_ofReal
        (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    apply integral_congr_ae
    filter_upwards with t
    rw [ENNReal.toReal_ofReal (hp t), Complex.real_smul]
    simp only [id_eq]
    ring
  have hd : Ioi (0 : ℝ) ⊆ interior (integrableExpSet id (density f)) :=
    isOpen_Ioi.subset_interior_iff.mpr hm
  have heq : logMellin f = complexMGF id (density f) := funext he
  rw [heq]
  exact fun s hs => analyticAt_complexMGF (hd hs)

/-- Arbitrary signed bounded densities with a finite upper support endpoint
have a holomorphic logarithmic Mellin transform on Re(s)>0. -/
theorem analytic_logMellin {f : ℝ → ℝ} (hf : Measurable f)
    {B U : ℝ} (hB : 0 ≤ B) (hb : ∀ t, |f t| ≤ B)
    (hz : ∀ t, U < t → f t = 0) :
    AnalyticOnNhd ℂ (logMellin f) {s : ℂ | 0 < s.re} := by
  let fp : ℝ → ℝ := fun t => max 0 (f t)
  let fm : ℝ → ℝ := fun t => max 0 (-f t)
  have hp (t : ℝ) : 0 ≤ fp t := le_max_left _ _
  have hn (t : ℝ) : 0 ≤ fm t := le_max_left _ _
  have bp (t : ℝ) : |fp t| ≤ B := by
    rw [abs_of_nonneg (hp t)]
    exact max_le hB ((le_abs_self _).trans (hb t))
  have bn (t : ℝ) : |fm t| ≤ B := by
    rw [abs_of_nonneg (hn t)]
    exact max_le hB ((neg_le_abs _).trans (hb t))
  have zp (t : ℝ) (ht : U < t) : fp t = 0 := by simp [fp, hz t ht]
  have zn (t : ℝ) (ht : U < t) : fm t = 0 := by simp [fm, hz t ht]
  have mp : Measurable fp := measurable_const.max hf
  have mn : Measurable fm := measurable_const.max hf.neg
  have ip (s : ℂ) (hs : 0 < s.re) := integrable_logWeight mp hB bp zp hs
  have im (s : ℂ) (hs : 0 < s.re) := integrable_logWeight mn hB bn zn hs
  have ap := analytic_positive mp hp (fun a ha => by
    have hi := (ip (a : ℂ) ha).re
    simpa [Complex.exp_re, Complex.mul_re, Complex.mul_im] using hi)
  have am := analytic_positive mn hn (fun a ha => by
    have hi := (im (a : ℂ) ha).re
    simpa [Complex.exp_re, Complex.mul_re, Complex.mul_im] using hi)
  have he : ∀ s : ℂ, 0 < s.re → logMellin f s = logMellin fp s-logMellin fm s := by
    intro s hs
    rw [logMellin, logMellin, logMellin, ← integral_sub (ip s hs) (im s hs)]
    apply integral_congr_ae
    filter_upwards with t
    have hpm : fp t-fm t = f t := by
      dsimp [fp,fm]
      by_cases ht : 0 ≤ f t
      · rw [max_eq_right ht, max_eq_left (by linarith : -f t ≤ 0)]; ring
      · rw [max_eq_left (by linarith : f t ≤ 0), max_eq_right (by linarith : 0 ≤ -f t)]; ring
    rw [← mul_sub, ← Complex.ofReal_sub, hpm]
  exact (ap.sub am).congr (isOpen_lt continuous_const Complex.continuous_re)
    (fun s hs => (he s hs).symm)

open SuzukiCarryMellinLimit SuzukiCarryMellinRate

/-- Public measurability of the unchanged finite alternating jump profile. -/
theorem measurable_profile (tau : ℝ) :
    Measurable (fun t : ℝ => profile tau (Real.exp t)) := by
  classical
  have mc : Measurable (fun t : ℝ => jumpCount (Real.exp t)) :=
    Nat.measurable_ceil.comp (measurable_const.div Real.measurable_exp)
  have ma : Continuous (amplitude tau) := by unfold amplitude tent; fun_prop
  have he : (fun t : ℝ => profile tau (Real.exp t)) =
      fun t : ℝ => ∑' k : ℕ, if k < jumpCount (Real.exp t) then
        (-1 : ℂ)^k*amplitude tau (((k+1 : ℕ) : ℝ)*Real.exp t/2) else 0 := by
    funext t
    rw [tsum_eq_sum (s := Finset.range (jumpCount (Real.exp t)))
      (fun k hk => by rw [ite_eq_right (by simpa only [Finset.mem_range] using hk)])]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [ite_eq_left (Finset.mem_range.mp hk)]
  rw [he]
  apply Measurable.tsum
  intro k
  exact Measurable.ite (measurableSet_lt measurable_const mc)
    (measurable_const.mul (ma.measurable.comp
      ((measurable_const.mul Real.measurable_exp).div_const 2))) measurable_const

/-- The literal response, not the exploratory boundary series, is
holomorphic in the Mellin exponent throughout Re(s)>0. -/
theorem analytic_continuumResponse (tau : ℝ) :
    AnalyticOnNhd ℂ (fun s => continuumResponse s tau) {s : ℂ | 0 < s.re} := by
  apply analytic_logMellin ((measurable_profile tau).norm.pow_const 2)
    (B := (3*(1+|tau|))^2) (U := Real.log 6) (by positivity)
  · intro t
    rw [abs_of_nonneg (sq_nonneg _)]
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr
      (profile_norm_le tau (Real.exp_pos t))
  · intro t ht
    rw [profile_eq_zero_above (tau := tau)
      (((Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 6)).mp ht).le),
      norm_zero, zero_pow (by decide)]

end
end RiemannGaussian.SuzukiCarryPhaseHolomorphy

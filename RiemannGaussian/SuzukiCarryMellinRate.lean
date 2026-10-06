/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiCarryMellinLimit
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Quantitative scaled Mellin convergence

Only the sampling error is norm-bounded. The limiting source response is
retained, and determinant nonvanishing is a separate analytic gate.
-/

namespace RiemannGaussian.SuzukiCarryMellinRate
noncomputable section
open Complex MeasureTheory Set Filter
open SuzukiCarryGramSource SuzukiCarryPhaseCode SuzukiCarryMellinLimit
open scoped BigOperators Topology

/-- The requested exact normalization of the literal finite packet. -/
def scaledResponse (H : ℕ) (s : ℂ) (tau : ℝ) : ℂ :=
  Complex.exp (-s*(Real.log H : ℂ))*Cmod H (tau/(H : ℝ)) s

/-- Mellin response of the limiting alternating tent profile. -/
def continuumResponse (s : ℂ) (tau : ℝ) : ℂ :=
  ∫ t : ℝ, Complex.exp (s*t)*(‖profile tau (Real.exp t)‖^2 : ℝ)

private def roundedResponse (H : ℕ) (s : ℂ) (tau : ℝ) : ℂ :=
  ∫ t : ℝ, Complex.exp (s*t)*(‖roundedProfile H tau (Real.exp t)‖^2 : ℝ)

private theorem continuous_amplitude (tau : ℝ) : Continuous (amplitude tau) := by
  unfold amplitude tent
  fun_prop

private theorem measurable_roundUp (H : ℕ) : Measurable (roundUp H) :=
  (measurable_of_countable (fun n : ℕ => (n : ℝ)/(H : ℝ))).comp
    (Nat.measurable_ceil.comp (measurable_const.mul measurable_id))

private theorem measurable_jumpCount_exp : Measurable (fun t : ℝ => jumpCount (Real.exp t)) :=
  Nat.measurable_ceil.comp (measurable_const.div Real.measurable_exp)

private theorem measurable_profile (tau : ℝ) :
    Measurable (fun t : ℝ => profile tau (Real.exp t)) := by
  classical
  have he : (fun t : ℝ => profile tau (Real.exp t)) =
      (fun t : ℝ => ∑' k : ℕ, if k < jumpCount (Real.exp t) then
        (-1 : ℂ)^k*amplitude tau (((k+1 : ℕ) : ℝ)*Real.exp t/2) else 0) := by
    funext t
    rw [tsum_eq_sum (s := Finset.range (jumpCount (Real.exp t)))
      (fun k hk => by simpa only [Finset.mem_range, ite_eq_right_iff] using
        (fun h => (hk (Finset.mem_range.mpr h)).elim :
          k < jumpCount (Real.exp t) →
            (-1 : ℂ)^k*amplitude tau (((k+1 : ℕ) : ℝ)*Real.exp t/2) = 0))]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [if_pos (Finset.mem_range.mp hk)]
  rw [he]
  apply Measurable.tsum
  intro k
  apply Measurable.ite (measurableSet_lt measurable_const measurable_jumpCount_exp)
    _ measurable_const
  exact measurable_const.mul ((continuous_amplitude tau).measurable.comp
    ((measurable_const.mul Real.measurable_exp).div_const 2))

private theorem measurable_roundedProfile (H : ℕ) (tau : ℝ) :
    Measurable (fun t : ℝ => roundedProfile H tau (Real.exp t)) := by
  classical
  have he : (fun t : ℝ => roundedProfile H tau (Real.exp t)) =
      (fun t : ℝ => ∑' k : ℕ, if k < jumpCount (Real.exp t) then
        (-1 : ℂ)^k*amplitude tau (roundUp H (((k+1 : ℕ) : ℝ)*Real.exp t/2)) else 0) := by
    funext t
    rw [tsum_eq_sum (s := Finset.range (jumpCount (Real.exp t)))
      (fun k hk => by rw [if_neg (by simpa only [Finset.mem_range] using hk)])]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [if_pos (Finset.mem_range.mp hk)]
  rw [he]
  apply Measurable.tsum
  intro k
  apply Measurable.ite (measurableSet_lt measurable_const measurable_jumpCount_exp)
    _ measurable_const
  exact measurable_const.mul ((continuous_amplitude tau).measurable.comp
    ((measurable_roundUp H).comp ((measurable_const.mul Real.measurable_exp).div_const 2)))

private theorem integrable_bounded_kernel {s : ℂ} (hs : 0 < s.re)
    {g : ℝ → ℂ} (hg : Measurable g) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ t, ‖g t‖ ≤ B) {U : ℝ} (hz : ∀ t, U < t → g t = 0) :
    Integrable (fun t : ℝ => Complex.exp (s*t)*(‖g t‖^2 : ℝ)) := by
  have hm : Integrable ((Iic U).indicator (fun t : ℝ => B^2*Real.exp (s.re*t))) :=
    (integrable_indicator_iff measurableSet_Iic).mpr
      ((integrableOn_exp_mul_Iic hs U).const_mul (B^2))
  apply hm.mono' (((Complex.continuous_exp.measurable.comp
    (measurable_const.mul Complex.measurable_ofReal))).mul
      (Complex.measurable_ofReal.comp (hg.norm.pow_const 2))).aestronglyMeasurable
  filter_upwards with t
  change ‖Complex.exp (s*t)*((‖g t‖^2 : ℝ) : ℂ)‖ ≤
    (Iic U).indicator (fun t : ℝ => B^2*Real.exp (s.re*t)) t
  by_cases ht : t ≤ U
  · rw [Set.indicator_of_mem (show t ∈ Iic U from ht), norm_mul, Complex.norm_exp, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have he : (s*(t : ℂ)).re = s.re*t := by simp [Complex.mul_re]
    rw [he]
    have hsq := (sq_le_sq₀ (norm_nonneg _) hB).mpr (hb t)
    nlinarith [Real.exp_pos (s.re*t)]
  · rw [hz t (lt_of_not_ge ht), norm_zero, zero_pow (by decide), Complex.ofReal_zero,
      mul_zero, norm_zero, Set.indicator_of_notMem (show t ∉ Iic U from ht)]

theorem integrable_continuumResponse {s : ℂ} (hs : 0 < s.re) (tau : ℝ) :
    Integrable (fun t : ℝ => Complex.exp (s*t)*(‖profile tau (Real.exp t)‖^2 : ℝ)) := by
  apply integrable_bounded_kernel hs (measurable_profile tau) (by positivity)
    (fun t => profile_norm_le tau (Real.exp_pos t)) (U := Real.log 6)
  intro t ht
  apply profile_eq_zero_above
  exact ((Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 6)).mp ht).le

private theorem integrable_roundedResponse {H : ℕ} (hH : 0 < H) {s : ℂ}
    (hs : 0 < s.re) (tau : ℝ) :
    Integrable (fun t : ℝ => Complex.exp (s*t)*(‖roundedProfile H tau (Real.exp t)‖^2 : ℝ)) := by
  apply integrable_bounded_kernel hs (measurable_roundedProfile H tau) (by positivity)
    (fun t => roundedProfile_norm_le hH tau (Real.exp_pos t)) (U := Real.log 6)
  intro t ht
  apply roundedProfile_eq_zero_above hH
  exact ((Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 6)).mp ht).le

/-- The scaled response is exactly the rounded-profile Mellin integral. -/
theorem scaledResponse_eq_rounded {H : ℕ} (hH : 0 < H) (s : ℂ) (tau : ℝ) :
    scaledResponse H s tau = roundedResponse H s tau := by
  unfold scaledResponse Cmod SuzukiCarryPoleCenter.mellin
  have hi := integral_add_right_eq_self (μ := (volume : Measure ℝ))
    (fun t : ℝ => Complex.exp (s*t)*
      (realMass (Finset.range (H+2*H)) (modulate (SuzukiCarryFejer.coefficient H H)
        (tau/(H : ℝ))) t : ℂ)) (Real.log H)
  rw [← hi]
  simp_rw [realMass_eq_roundedProfile hH]
  rw [← integral_const_mul]
  unfold roundedResponse
  congr 1
  funext t
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

private theorem mass_error_sampling {H : ℕ} (hH : 0 < H) (tau : ℝ)
    {x : ℝ} (hx : 0 < x) :
    |‖roundedProfile H tau x‖^2-‖profile tau x‖^2| ≤
      7*(1+|tau|)^2*(6/x+1)/(H : ℝ) := by
  have ha := roundedProfile_norm_le hH tau hx
  have hb := profile_norm_le tau hx
  have hd := roundedProfile_sub_profile_norm hH tau hx
  calc
    _ = |‖roundedProfile H tau x‖-‖profile tau x‖| *
        (‖roundedProfile H tau x‖+‖profile tau x‖) := by
      rw [sq_sub_sq, abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
      ring
    _ ≤ ‖roundedProfile H tau x-profile tau x‖*
        (‖roundedProfile H tau x‖+‖profile tau x‖) := by
      exact mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le _ _)
        (add_nonneg (norm_nonneg _) (norm_nonneg _))
    _ ≤ ((1+|tau|)*(6/x+1)/(H : ℝ))*(7*(1+|tau|)) := by
      apply mul_le_mul hd (by linarith) (add_nonneg (norm_nonneg _) (norm_nonneg _))
        (by positivity)
    _ = _ := by ring

private theorem mass_error_uniform {H : ℕ} (hH : 0 < H) (tau : ℝ)
    {x : ℝ} (hx : 0 < x) :
    |‖roundedProfile H tau x‖^2-‖profile tau x‖^2| ≤ 25*(1+|tau|)^2 := by
  have ha := roundedProfile_norm_le hH tau hx
  have hb := profile_norm_le tau hx
  have han := norm_nonneg (roundedProfile H tau x)
  have hbn := norm_nonneg (profile tau x)
  have hc : 0 ≤ 1+|tau| := by positivity
  have ha2 := (sq_le_sq₀ han (by positivity : 0 ≤ 4*(1+|tau|))).mpr ha
  have hb2 := (sq_le_sq₀ hbn (by positivity : 0 ≤ 3*(1+|tau|))).mpr hb
  rw [abs_le]
  constructor <;> nlinarith

/-- A two-cutoff estimate: the small-denominator tail and the grid error
are paid separately, without taking a norm of the source response. -/
theorem scaledResponse_error_two_cutoffs {H : ℕ} (hH : 0 < H) {s : ℂ}
    (hs : 0 < s.re) (tau T : ℝ) :
    ‖scaledResponse H s tau-continuumResponse s tau‖ ≤
      25*(1+|tau|)^2*Real.exp (s.re*T)/s.re +
      (7*(1+|tau|)^2*(6*Real.exp (-T)+1)/(H : ℝ))*
        Real.exp (s.re*Real.log 6)/s.re := by
  let c := 1+|tau|
  let b := 7*c^2*(6*Real.exp (-T)+1)/(H : ℝ)
  let major : ℝ → ℝ := fun t =>
    (Iic T).indicator (fun t => 25*c^2*Real.exp (s.re*t)) t +
    (Iic (Real.log 6)).indicator (fun t => b*Real.exp (s.re*t)) t
  have hb : 0 ≤ b := by dsimp [b, c]; positivity
  have hi1 : Integrable ((Iic T).indicator (fun t => 25*c^2*Real.exp (s.re*t))) :=
    (integrable_indicator_iff measurableSet_Iic).mpr
      ((integrableOn_exp_mul_Iic hs T).const_mul (25*c^2))
  have hi2 : Integrable ((Iic (Real.log 6)).indicator (fun t => b*Real.exp (s.re*t))) :=
    (integrable_indicator_iff measurableSet_Iic).mpr
      ((integrableOn_exp_mul_Iic hs (Real.log 6)).const_mul b)
  have hm : Integrable major := hi1.add hi2
  have hm2 : ∀ t, 0 ≤ (Iic (Real.log 6)).indicator
      (fun t => b*Real.exp (s.re*t)) t := by
    intro t
    apply indicator_nonneg
    intro _ _
    positivity
  rw [scaledResponse_eq_rounded hH, roundedResponse, continuumResponse,
    ← integral_sub (integrable_roundedResponse hH hs tau) (integrable_continuumResponse hs tau)]
  calc
    _ ≤ ∫ t : ℝ, major t := norm_integral_le_of_norm_le hm (by
      filter_upwards with t
      have he : ‖Complex.exp (s*t)*(‖roundedProfile H tau (Real.exp t)‖^2 : ℝ)-
          Complex.exp (s*t)*(‖profile tau (Real.exp t)‖^2 : ℝ)‖ =
          Real.exp (s.re*t)*
            |‖roundedProfile H tau (Real.exp t)‖^2-‖profile tau (Real.exp t)‖^2| := by
        rw [← mul_sub, norm_mul, Complex.norm_exp]
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
        rw [← Complex.ofReal_sub,
          Complex.norm_real, Real.norm_eq_abs]
      rw [he]
      change _ ≤ (Iic T).indicator _ t + (Iic (Real.log 6)).indicator _ t
      by_cases ht : t ≤ T
      · rw [indicator_of_mem (show t ∈ Iic T from ht)]
        have he := mul_le_mul_of_nonneg_left
          (mass_error_uniform hH tau (Real.exp_pos t)) (Real.exp_pos (s.re*t)).le
        dsimp [c] at *
        nlinarith [hm2 t]
      · rw [indicator_of_notMem (show t ∉ Iic T from ht), zero_add]
        by_cases hu : t ≤ Real.log 6
        · rw [indicator_of_mem (show t ∈ Iic (Real.log 6) from hu)]
          have hx : 6/Real.exp t+1 ≤ 6*Real.exp (-T)+1 := by
            rw [div_eq_mul_inv, ← Real.exp_neg]
            have h := Real.exp_le_exp.mpr (by linarith : -t ≤ -T)
            linarith
          have hB : 7*c^2*(6/Real.exp t+1)/(H : ℝ) ≤ b := by
            apply div_le_div_of_nonneg_right _ (by positivity)
            exact mul_le_mul_of_nonneg_left hx (by positivity)
          have he := (mass_error_sampling hH tau (Real.exp_pos t)).trans hB
          simpa only [mul_comm] using mul_le_mul_of_nonneg_left he
            (Real.exp_pos (s.re*t)).le
        · have hx : 6 ≤ Real.exp t :=
            ((Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 6)).mp (lt_of_not_ge hu)).le
          rw [profile_eq_zero_above (tau := tau) hx,
            roundedProfile_eq_zero_above hH (tau := tau) hx,
            norm_zero, sub_self, abs_zero, mul_zero,
            indicator_of_notMem (show t ∉ Iic (Real.log 6) from hu)])
    _ = _ := by
      rw [integral_add hi1 hi2, integral_indicator measurableSet_Iic,
        integral_indicator measurableSet_Iic, integral_const_mul, integral_const_mul,
        integral_exp_mul_Iic hs, integral_exp_mul_Iic hs]
      dsimp [c, b]
      ring

/-- Explicit convergence rate, uniform over the entire bounded real-part
strip. The imaginary part of the Mellin parameter costs nothing. -/
theorem scaledResponse_error_uniform {H : ℕ} (hH : 0 < H) {s : ℂ}
    {a b : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (has : a ≤ s.re) (hsb : s.re ≤ b)
    (tau : ℝ) :
    ‖scaledResponse H s tau-continuumResponse s tau‖ ≤
      ((25+49*Real.exp (b*Real.log 6))*(1+|tau|)^2/a)*
        Real.exp (-a*Real.log H/2) := by
  have hHp : (0 : ℝ) < H := by exact_mod_cast hH
  have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hL : 0 ≤ Real.log H := Real.log_nonneg hH1
  have hs : 0 < s.re := ha.trans_le has
  have hl6 : 0 ≤ Real.log 6 := Real.log_nonneg (by norm_num)
  have he1 : Real.exp (s.re*(-Real.log H/2)) ≤ Real.exp (-a*Real.log H/2) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have he2 : Real.exp (s.re*Real.log 6) ≤ Real.exp (b*Real.log 6) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hsb hl6)
  have hsample : (6*Real.exp (Real.log H/2)+1)/(H : ℝ) ≤
      7*Real.exp (-a*Real.log H/2) := by
    have he : Real.exp (-Real.log H/2)*(H : ℝ) = Real.exp (Real.log H/2) := by
      calc
        _ = Real.exp (-Real.log H/2)*Real.exp (Real.log H) := by rw [Real.exp_log hHp]
        _ = _ := by rw [← Real.exp_add]; congr 1; ring
    have h0 : 1 ≤ Real.exp (Real.log H/2) := Real.one_le_exp (by positivity)
    have h1 : Real.exp (-Real.log H/2) ≤ Real.exp (-a*Real.log H/2) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    apply (div_le_iff₀ hHp).mpr
    have hmul := mul_le_mul_of_nonneg_right h1 hHp.le
    rw [he] at hmul
    nlinarith
  have h := scaledResponse_error_two_cutoffs hH hs tau (-Real.log H/2)
  have h25 : 0 ≤ 25*(1+|tau|)^2 := by positivity
  have h7 : 0 ≤ 7*(1+|tau|)^2 := by positivity
  have ht1 : 25*(1+|tau|)^2*Real.exp (s.re*(-Real.log H/2))/s.re ≤
      25*(1+|tau|)^2*Real.exp (-a*Real.log H/2)/a := by
    exact div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left he1 h25) ha has
  have ht2 : (7*(1+|tau|)^2*(6*Real.exp (-(-Real.log H/2))+1)/(H : ℝ))*
      Real.exp (s.re*Real.log 6)/s.re ≤
      49*(1+|tau|)^2*Real.exp (-a*Real.log H/2)*Real.exp (b*Real.log 6)/a := by
    have h0 : 7*(1+|tau|)^2*(6*Real.exp (-(-Real.log H/2))+1)/(H : ℝ) ≤
        49*(1+|tau|)^2*Real.exp (-a*Real.log H/2) := by
      have hm := mul_le_mul_of_nonneg_left hsample h7
      calc
        _ = 7*(1+|tau|)^2*((6*Real.exp (Real.log H/2)+1)/(H : ℝ)) := by
          rw [show -(-Real.log H/2) = Real.log H/2 by ring]
          ring
        _ ≤ 7*(1+|tau|)^2*(7*Real.exp (-a*Real.log H/2)) := hm
        _ = _ := by ring
    apply div_le_div₀ (by positivity) _ ha has
    exact mul_le_mul h0 he2 (Real.exp_pos _).le (by positivity)
  calc
    _ ≤ _ := h
    _ ≤ _ := add_le_add ht1 ht2
    _ = _ := by ring

/-- Convergence of the literal packet, rather than of a substituted model. -/
theorem tendsto_scaledResponse {s : ℂ} (hs : 0 < s.re) (tau : ℝ) :
    Tendsto (fun H : ℕ => scaledResponse H s tau) atTop (𝓝 (continuumResponse s tau)) := by
  let a := min s.re 1
  have ha : 0 < a := lt_min hs (by norm_num)
  have hr : Tendsto (fun H : ℕ => (H : ℝ)^(-(a/2))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by positivity : 0 < a/2)).comp tendsto_natCast_atTop_atTop
  have he : Tendsto (fun H : ℕ => Real.exp (-a*Real.log H/2)) atTop (𝓝 0) := by
    apply hr.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with H hH
    rw [Real.rpow_def_of_pos (by exact_mod_cast hH : (0 : ℝ) < H)]
    congr 1
    ring
  have hm := he.const_mul (((25+49*Real.exp (s.re*Real.log 6))*(1+|tau|)^2/a))
  simp only [mul_zero] at hm
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hm
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with H hH
  exact scaledResponse_error_uniform hH ha (min_le_right _ _) (min_le_left _ _) le_rfl tau

/-- Joint uniform convergence on a real-part strip and a bounded
modulation interval. In particular this gives the requested locally
uniform Mellin limit near either campaign exponent. -/
theorem tendstoUniformlyOn_scaledResponse {a b T : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) :
    TendstoUniformlyOn (fun H : ℕ => fun v : ℂ × ℝ => scaledResponse H v.1 v.2)
      (fun v => continuumResponse v.1 v.2) atTop
      {v : ℂ × ℝ | a ≤ v.1.re ∧ v.1.re ≤ b ∧ |v.2| ≤ T} := by
  have hr : Tendsto (fun H : ℕ => (H : ℝ)^(-(a/2))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by positivity : 0 < a/2)).comp tendsto_natCast_atTop_atTop
  have he : Tendsto (fun H : ℕ => Real.exp (-a*Real.log H/2)) atTop (𝓝 0) := by
    apply hr.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with H hH
    rw [Real.rpow_def_of_pos (by exact_mod_cast hH : (0 : ℝ) < H)]
    congr 1
    ring
  have hm := he.const_mul ((25+49*Real.exp (b*Real.log 6))*(1+T)^2/a)
  simp only [mul_zero] at hm
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro epsilon hepsilon
  filter_upwards [eventually_gt_atTop (0 : ℕ), hm.eventually (gt_mem_nhds hepsilon)]
    with H hH hsmall
  rintro ⟨s, tau⟩ ⟨has, hsb, ht⟩
  rw [dist_eq_norm_sub, norm_sub_rev]
  calc
    _ ≤ ((25+49*Real.exp (b*Real.log 6))*(1+|tau|)^2/a)*
        Real.exp (-a*Real.log H/2) := scaledResponse_error_uniform hH ha ha1 has hsb tau
    _ ≤ ((25+49*Real.exp (b*Real.log 6))*(1+T)^2/a)*
        Real.exp (-a*Real.log H/2) := by
      gcongr
    _ < epsilon := hsmall

/-- Evenness survives the exact finite-to-continuum passage. -/
theorem continuumResponse_neg {s : ℂ} (hs : 0 < s.re) (tau : ℝ) :
    continuumResponse s (-tau) = continuumResponse s tau := by
  have he : (fun H : ℕ => scaledResponse H s (-tau)) =
      (fun H : ℕ => scaledResponse H s tau) := by
    funext H
    simp only [scaledResponse, neg_div, Cmod_neg]
  exact tendsto_nhds_unique (by simpa only [he] using tendsto_scaledResponse hs (-tau))
    (tendsto_scaledResponse hs tau)

/-- The continuum gate for the asymmetric, same-amplitude phase code. -/
def continuumDet (p s : ℂ) (tau : ℝ) : ℂ :=
  sourceDet (fun j : Fin 3 => continuumResponse p ((j : ℕ)*tau))
    (fun j : Fin 3 => continuumResponse s ((j : ℕ)*tau))

/-- The literal determinant with the same fixed modulation scale tau/H. -/
def nativeDet (H : ℕ) (p s : ℂ) (tau : ℝ) : ℂ :=
  sourceDet (fun j : Fin 3 => Cmod H (((j : ℕ)*tau)/(H : ℝ)) p)
    (fun j : Fin 3 => Cmod H (((j : ℕ)*tau)/(H : ℝ)) s)

theorem sourceDet_scale (c b : Fin 3 → ℂ) (A B : ℂ) :
    sourceDet (fun j => A*c j) (fun j => B*b j) = A*B*sourceDet c b := by
  simp only [sourceDet_eq_contrasts]
  ring

/-- No finite determinant is replaced by its limit inside the arithmetic
code. This is an exact identity for the diagnostic source normalization. -/
theorem normalized_nativeDet_eq (H : ℕ) (p s : ℂ) (tau : ℝ) :
    Complex.exp (-(p+s)*(Real.log H : ℂ))*nativeDet H p s tau =
      sourceDet (fun j : Fin 3 => scaledResponse H p ((j : ℕ)*tau))
        (fun j : Fin 3 => scaledResponse H s ((j : ℕ)*tau)) := by
  unfold scaledResponse nativeDet
  rw [sourceDet_scale, ← Complex.exp_add]
  congr 1
  congr 1
  ring

/-- The normalized matched-source determinant converges for every fixed
complex pole exponent and every fixed positive-real-part matched exponent. -/
theorem tendsto_normalized_nativeDet {p s : ℂ} (hp : 0 < p.re) (hs : 0 < s.re)
    (tau : ℝ) :
    Tendsto (fun H : ℕ => Complex.exp (-(p+s)*(Real.log H : ℂ))*nativeDet H p s tau)
      atTop (𝓝 (continuumDet p s tau)) := by
  simp_rw [normalized_nativeDet_eq, continuumDet, sourceDet_eq_contrasts]
  exact ((tendsto_scaledResponse hp _).sub (tendsto_scaledResponse hp _)).mul
    ((tendsto_scaledResponse hs _).sub (tendsto_scaledResponse hs _)) |>.sub
      (((tendsto_scaledResponse hp _).sub (tendsto_scaledResponse hp _)).mul
        ((tendsto_scaledResponse hs _).sub (tendsto_scaledResponse hs _)))

/-- A nonzero continuum gate gives a cofinal source-sized lower bound for
the actual finite determinant. Nonvanishing is an explicit remaining premise. -/
theorem eventually_nativeDet_source_lower {p s : ℂ} (hp : 0 < p.re) (hs : 0 < s.re)
    {tau : ℝ} (hdet : continuumDet p s tau ≠ 0) :
    ∀ᶠ H : ℕ in atTop,
      (‖continuumDet p s tau‖/2)*Real.exp ((p.re+s.re)*Real.log H) ≤
        ‖nativeDet H p s tau‖ := by
  have he := (tendsto_normalized_nativeDet hp hs tau).norm
  have hd : 0 < ‖continuumDet p s tau‖ := norm_pos_iff.mpr hdet
  filter_upwards [he.eventually (lt_mem_nhds (by linarith :
    ‖continuumDet p s tau‖/2 < ‖continuumDet p s tau‖))] with H hH
  rw [norm_mul, Complex.norm_exp] at hH
  have hre : (-(p+s)*(Real.log H : ℂ)).re = -(p.re+s.re)*Real.log H := by
    simp only [Complex.mul_re, Complex.neg_re, Complex.add_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
  rw [hre] at hH
  have hexp : Real.exp ((p.re+s.re)*Real.log H)*
      Real.exp (-(p.re+s.re)*Real.log H) = 1 := by
    rw [← Real.exp_add]
    rw [show (p.re+s.re)*Real.log H+ -(p.re+s.re)*Real.log H = 0 by ring, Real.exp_zero]
  have hm := mul_le_mul_of_nonneg_left hH.le
    (Real.exp_pos ((p.re+s.re)*Real.log H)).le
  calc
    _ = Real.exp ((p.re+s.re)*Real.log H)*(‖continuumDet p s tau‖/2) := by ring
    _ ≤ _ := hm
    _ = _ := by rw [← mul_assoc, hexp, one_mul]

/-- Exact equivalence of continuum nonvanishing and a positive cofinal
native source margin. Convergence alone does not supply this margin. -/
theorem continuumDet_ne_zero_iff_cofinal_source {p s : ℂ}
    (hp : 0 < p.re) (hs : 0 < s.re) (tau : ℝ) :
    continuumDet p s tau ≠ 0 ↔
      ∃ c : ℝ, 0 < c ∧ ∀ᶠ H : ℕ in atTop,
        c*Real.exp ((p.re+s.re)*Real.log H) ≤ ‖nativeDet H p s tau‖ := by
  constructor
  · intro hd
    exact ⟨‖continuumDet p s tau‖/2, by positivity,
      eventually_nativeDet_source_lower hp hs hd⟩
  · rintro ⟨c, hc, hbound⟩ hz
    have he := (tendsto_normalized_nativeDet hp hs tau).norm
    rw [hz, norm_zero] at he
    have hsmall := he.eventually (gt_mem_nhds hc)
    obtain ⟨H, hH, hS⟩ := (hbound.and hsmall).exists
    have hre : (-(p+s)*(Real.log H : ℂ)).re = -(p.re+s.re)*Real.log H := by
      simp only [Complex.mul_re, Complex.neg_re, Complex.add_re, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, sub_zero]
    rw [norm_mul, Complex.norm_exp, hre] at hS
    have hmul := mul_le_mul_of_nonneg_left hH
      (Real.exp_pos (-(p.re+s.re)*Real.log H)).le
    have hcancel : Real.exp (-(p.re+s.re)*Real.log H)*
        Real.exp ((p.re+s.re)*Real.log H) = 1 := by
      rw [← Real.exp_add]
      rw [show -(p.re+s.re)*Real.log H+(p.re+s.re)*Real.log H = 0 by ring, Real.exp_zero]
    have hlow : c ≤ Real.exp (-(p.re+s.re)*Real.log H)*‖nativeDet H p s tau‖ := by
      calc
        c = c*(Real.exp (-(p.re+s.re)*Real.log H)*
            Real.exp ((p.re+s.re)*Real.log H)) := by rw [hcancel, mul_one]
        _ = Real.exp (-(p.re+s.re)*Real.log H)*
            (c*Real.exp ((p.re+s.re)*Real.log H)) := by ring
        _ ≤ _ := hmul
    linarith

end
end RiemannGaussian.SuzukiCarryMellinRate

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiCarryPhaseTransform
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Literal contrast and its continued lag spectrum

The identity is first justified by absolute integration on Re(s)>2, then
continued as a joined signed identity to Re(s)>0. No prime estimate is used.
-/

namespace RiemannGaussian.SuzukiCarryPhaseContinuation
noncomputable section
open Complex MeasureTheory Set Filter
open SuzukiCarryMellinLimit SuzukiCarryMellinRate SuzukiCarryPhaseQuadrature
open SuzukiCarryPhaseHolomorphy SuzukiCarryPhaseLag SuzukiCarryPhaseSpectrum
open SuzukiCarryPhaseTransform
open scoped BigOperators Topology

private theorem integrable_complex_tsum {F : ℕ → ℝ → ℂ}
    (hi : ∀ i, Integrable (F i)) (hs : Summable (fun i => ∫ t, ‖F i t‖)) :
    Integrable (fun t => ∑' i, F i t) := by
  refine ⟨(AEMeasurable.tsum (fun i => (hi i).aestronglyMeasurable.aemeasurable)).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  apply lt_of_le_of_lt (lintegral_mono (fun _ => enorm_tsum_le_tsum_enorm))
  rw [lintegral_tsum (fun i => (hi i).aestronglyMeasurable.enorm)]
  have he (i : ℕ) : ∫⁻ t, ‖F i t‖ₑ = ‖∫ t, ‖F i t‖‖ₑ := by
    dsimp [enorm]
    rw [lintegral_coe_eq_integral _ (hi i).norm, ENNReal.coe_nnreal_eq, coe_nnnorm,
      Real.norm_of_nonneg (integral_nonneg (fun t => norm_nonneg (F i t)))]
    simp only [coe_nnnorm]
  simp_rw [he]
  exact (ENNReal.tsum_coe_ne_top_iff_summable.2 <| NNReal.summable_coe.1 hs.abs).lt_top

/-- Logarithmic change of scale for the positive lag h+1. -/
def lagOffset (h : ℕ) : ℝ := Real.log 2-Real.log (h+1)

theorem exp_lagOffset (h : ℕ) : Real.exp (lagOffset h) = 2/((h+1 : ℕ) : ℝ) := by
  rw [lagOffset, Real.exp_sub, Real.exp_log (by norm_num), Real.exp_log (by positivity)]
  norm_cast

theorem literalLag_translate (tau t : ℝ) (h : ℕ) :
    literalLag tau (Real.exp (t+lagOffset h)) h =
      (-1 : ℝ)^(h+1)*ordinaryDensity tau h t := by
  have hh : ((h+1 : ℕ) : ℝ) ≠ 0 := by positivity
  rw [Real.exp_add, exp_lagOffset]
  unfold literalLag ordinaryDensity
  have hv : ((h+1 : ℕ) : ℝ)*(Real.exp t*(2/((h+1 : ℕ) : ℝ)))/2 = Real.exp t := by
    field_simp
  rw [hv]
  have he : Real.exp t*(2/((h+1 : ℕ) : ℝ))/2 = Real.exp t/((h+1 : ℕ) : ℝ) := by ring
  have hc : tau*((h+1 : ℕ) : ℝ)*(Real.exp t*(2/((h+1 : ℕ) : ℝ)))/2 = tau*Real.exp t := by
    field_simp
  rw [he, hc]
  ring

theorem weightedLag_translate (s : ℂ) (tau t : ℝ) (h : ℕ) :
    Complex.exp (s*((t+lagOffset h : ℝ) : ℂ))*(literalLag tau (Real.exp (t+lagOffset h)) h : ℂ) =
      (Complex.exp (s*lagOffset h)*(-1 : ℂ)^(h+1))*
        (Complex.exp (s*t)*(ordinaryDensity tau h t : ℂ)) := by
  rw [literalLag_translate]
  push_cast
  rw [mul_add, Complex.exp_add]
  ring

theorem integral_weightedLag (s : ℂ) (tau : ℝ) (h : ℕ) :
    (∫ t : ℝ, Complex.exp (s*t)*(literalLag tau (Real.exp t) h : ℂ)) =
      (Complex.exp (s*lagOffset h)*(-1 : ℂ)^(h+1))*logMellin (ordinaryDensity tau h) s := by
  rw [← integral_add_right_eq_self
    (fun t : ℝ => Complex.exp (s*t)*(literalLag tau (Real.exp t) h : ℂ)) (lagOffset h)]
  simp_rw [weightedLag_translate]
  rw [integral_const_mul]
  rfl

theorem integrable_weightedLag {s : ℂ} (hs : 0 < s.re) (tau : ℝ) (h : ℕ) :
    Integrable (fun t : ℝ => Complex.exp (s*t)*(literalLag tau (Real.exp t) h : ℂ)) := by
  have hi := integrable_logWeight (measurable_ordinaryDensity tau h) (by positivity)
    (ordinaryDensity_abs_le tau h) (fun _ ht => ordinaryDensity_zero tau h ht) hs
  have htrans : Integrable (fun t : ℝ =>
      Complex.exp (s*lagOffset h)*(-1 : ℂ)^(h+1)*
        (Complex.exp (s*((t-lagOffset h : ℝ) : ℂ))*(ordinaryDensity tau h (t-lagOffset h) : ℂ))) := by
    simpa only [Function.comp_def, sub_eq_add_neg] using
      (measurePreserving_add_right (volume : Measure ℝ) (-lagOffset h)).integrable_comp_of_integrable
        (hi.const_mul (Complex.exp (s*lagOffset h)*(-1 : ℂ)^(h+1)))
  apply htrans.congr
  filter_upwards with t
  have he := weightedLag_translate s tau (t-lagOffset h) h
  simpa only [sub_add_cancel] using he.symm

theorem integral_norm_weightedLag_le {s : ℂ} (hs : 0 < s.re) (tau : ℝ) (h : ℕ) :
    (∫ t : ℝ, ‖Complex.exp (s*t)*(literalLag tau (Real.exp t) h : ℂ)‖) ≤
      ((3*tau^2+8)*Real.exp (2*s.re*Real.log 2)/s.re)*
        ((h+1 : ℕ) : ℝ)^(1-s.re) := by
  rw [← integral_add_right_eq_self
    (fun t : ℝ => ‖Complex.exp (s*t)*(literalLag tau (Real.exp t) h : ℂ)‖) (lagOffset h)]
  simp_rw [weightedLag_translate]
  have he (t : ℝ) :
      ‖(Complex.exp (s*lagOffset h)*(-1 : ℂ)^(h+1))*
        (Complex.exp (s*t)*(ordinaryDensity tau h t : ℂ))‖ =
      ‖Complex.exp (s*lagOffset h)*(-1 : ℂ)^(h+1)‖*
        ‖Complex.exp (s*t)*(ordinaryDensity tau h t : ℂ)‖ := norm_mul _ _
  simp_rw [he]
  rw [integral_const_mul]
  have hn : ‖Complex.exp (s*lagOffset h)*(-1 : ℂ)^(h+1)‖ =
      Real.exp (s.re*lagOffset h) := by
    rw [norm_mul]
    simp [norm_pow, Complex.norm_exp, Complex.mul_re]
  rw [hn]
  calc
    _ ≤ Real.exp (s.re*lagOffset h)*
        (((3*tau^2+8)*((h+1 : ℕ) : ℝ))*Real.exp (s.re*Real.log 2)/s.re) :=
      mul_le_mul_of_nonneg_left
        (integral_norm_logWeight_le (measurable_ordinaryDensity tau h) (by positivity)
          (ordinaryDensity_abs_le tau h) (fun _ ht => ordinaryDensity_zero tau h ht) hs)
        (Real.exp_pos _).le
    _ = _ := by
      rw [lagOffset, mul_sub, Real.exp_sub, Real.rpow_def_of_pos (by positivity),
        show Real.log ((h+1 : ℕ) : ℝ)*(1-s.re) =
          Real.log ((h+1 : ℕ) : ℝ)-s.re*Real.log ((h+1 : ℕ) : ℝ) by ring,
        Real.exp_sub, Real.exp_log (by positivity)]
      rw [show 2*s.re*Real.log 2 = s.re*Real.log 2+s.re*Real.log 2 by ring, Real.exp_add]
      simp only [Nat.cast_add, Nat.cast_one]
      field_simp

theorem summable_integral_norm_weightedLag {s : ℂ} (hs : 2 < s.re) (tau : ℝ) :
    Summable (fun h : ℕ => ∫ t : ℝ, ‖Complex.exp (s*t)*(literalLag tau (Real.exp t) h : ℂ)‖) := by
  have hp : Summable (fun h : ℕ => (h : ℝ)^(1-s.re)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  exact (((summable_nat_add_iff 1).mpr hp).mul_left
    ((3*tau^2+8)*Real.exp (2*s.re*Real.log 2)/s.re)).of_nonneg_of_le
      (fun _ => integral_nonneg (fun _ => norm_nonneg _))
      (integral_norm_weightedLag_le (by linarith) tau)

theorem hasSum_negative_eta {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun h : ℕ => (-1 : ℂ)^(h+1)*Complex.exp (-s*(Real.log (h+1) : ℂ)))
      (-SuzukiCarryPhaseEta.eta s) := by
  let f : ℕ → ℂ := fun n => (-1 : ℂ)^n/(n : ℂ)^s
  have hf : HasSum f (HurwitzZeta.cosZeta ((1/2 : ℝ) : UnitAddCircle) s) := by
    convert HurwitzZeta.hasSum_nat_cosZeta (1/2 : ℝ) hs using 1
    funext n
    rw [show 2*Real.pi*(1/2 : ℝ)*(n : ℝ) = (n : ℝ)*Real.pi by ring,
      Real.cos_nat_mul_pi]
    simp only [f, Complex.ofReal_pow, Complex.ofReal_neg, Complex.ofReal_one]
  have h0 : f 0 = 0 := by simp [f, Complex.zero_cpow (ne_zero_of_one_lt_re hs)]
  have hshift : HasSum (fun n : ℕ => f (n+1))
      (HurwitzZeta.cosZeta ((1/2 : ℝ) : UnitAddCircle) s) := by
    simpa [h0] using (hasSum_nat_add_iff' 1).mpr hf
  convert hshift using 1
  · funext n
    dsimp only [f]
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (show n+1 ≠ 0 by omega)),
      ← Complex.natCast_log, div_eq_mul_inv, ← Complex.exp_neg]
    simp only [Nat.cast_add, Nat.cast_one]
    congr 2
    ring
  · simp [SuzukiCarryPhaseEta.eta]

theorem contrast_eq_lagIntegrals {s : ℂ} (hs : 2 < s.re) (tau : ℝ) :
    continuumResponse s tau-continuumResponse s 0 =
      2*(∑' h : ℕ, ∫ t : ℝ, Complex.exp (s*t)*(literalLag tau (Real.exp t) h : ℂ)) := by
  have hp : 0 < s.re := by linarith
  rw [integral_tsum_of_summable_integral_norm
    (integrable_weightedLag hp tau) (summable_integral_norm_weightedLag hs tau),
    ← integral_const_mul]
  unfold continuumResponse
  rw [← integral_sub (integrable_continuumResponse hp tau) (integrable_continuumResponse hp 0)]
  apply integral_congr_ae
  filter_upwards with t
  rw [← mul_sub, ← Complex.ofReal_sub, profile_contrast_eq_lags (Real.exp_pos t) tau,
    Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_tsum, tsum_mul_left]
  ring

theorem exp_order_weight (s : ℂ) (h : ℕ) :
    Complex.exp (-s*(Real.log (h+1) : ℂ))*((h+1 : ℕ) : ℂ) =
      Complex.exp (-(s-1)*(Real.log (h+1) : ℂ)) := by
  have he : Complex.exp (Real.log (h+1) : ℂ) = ((h+1 : ℕ) : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log (by positivity)]
    norm_cast
  rw [← he, ← Complex.exp_add]
  congr 1
  ring

theorem contrast_eq_regularized_high {s : ℂ} (hs : 2 < s.re) (tau : ℝ) :
    continuumResponse s tau-continuumResponse s 0 = regularizedResponse s tau := by
  have hp : 0 < s.re := by linarith
  have hb := (hasSum_negative_eta (s := s-1) (by simp only [Complex.sub_re, Complex.one_re]; linarith)).mul_right
    (logMellin (bulkDensity tau) s)
  have hr := (summable_remainderCoefficient hp tau).hasSum
  have hsum : HasSum (fun h : ℕ => (-1 : ℂ)^(h+1)*
      Complex.exp (-s*(Real.log (h+1) : ℂ))*logMellin (ordinaryDensity tau h) s)
      (-SuzukiCarryPhaseEta.eta (s-1)*logMellin (bulkDensity tau) s+
        ∑' h : ℕ, remainderCoefficient tau h s) := by
    apply (hb.add hr).congr_fun
    intro h
    rw [ordinaryMellin_eq hp, mul_add, remainderCoefficient]
    congr 1
    rw [show (-1 : ℂ)^(h+1)*Complex.exp (-s*(Real.log (h+1) : ℂ))*
        (((h+1 : ℕ) : ℂ)*logMellin (bulkDensity tau) s) =
        (-1 : ℂ)^(h+1)*(Complex.exp (-s*(Real.log (h+1) : ℂ))*((h+1 : ℕ) : ℂ))*
          logMellin (bulkDensity tau) s by ring, exp_order_weight]
  have ht (h : ℕ) :
      (∫ t : ℝ, Complex.exp (s*t)*(literalLag tau (Real.exp t) h : ℂ)) =
        Complex.exp (s*(Real.log 2 : ℂ))*
          ((-1 : ℂ)^(h+1)*Complex.exp (-s*(Real.log (h+1) : ℂ))*
            logMellin (ordinaryDensity tau h) s) := by
    rw [integral_weightedLag, lagOffset]
    push_cast
    rw [mul_sub, sub_eq_add_neg, Complex.exp_add]
    ring
  rw [contrast_eq_lagIntegrals hs, tsum_congr ht, tsum_mul_left, hsum.tsum_eq]
  unfold regularizedResponse
  rw [add_mul, Complex.exp_add]
  have h2 : Complex.exp (Real.log 2 : ℂ) = 2 := by
    rw [← Complex.ofReal_exp, Real.exp_log (by norm_num)]
    norm_num
  simp only [one_mul, h2]
  ring

theorem contrast_eq_regularized {s : ℂ} (hs : 0 < s.re) (tau : ℝ) :
    continuumResponse s tau-continuumResponse s 0 = regularizedResponse s tau := by
  let U : Set ℂ := {s | 0 < s.re}
  have hf : AnalyticOnNhd ℂ (fun s => continuumResponse s tau-continuumResponse s 0) U :=
    (analytic_continuumResponse tau).sub (analytic_continuumResponse 0)
  have hg : AnalyticOnNhd ℂ (fun s => regularizedResponse s tau) U :=
    analytic_regularizedResponse tau
  have hconn : IsPreconnected U := by
    exact (convex_halfSpace_re_gt 0).isPreconnected
  have he := hf.eqOn_of_preconnected_of_eventuallyEq hg hconn
    (by norm_num [U] : (3 : ℂ) ∈ U)
    (eventuallyEq_of_mem
      ((isOpen_lt continuous_const continuous_re).mem_nhds (by norm_num : 2 < (3 : ℂ).re))
      (fun z hz => contrast_eq_regularized_high hz tau))
  exact he hs

theorem remainderCoefficient_eq_integral (s : ℂ) (tau : ℝ) (h : ℕ) :
    remainderCoefficient tau h s =
      ∫ t : ℝ, Complex.exp (s*t)*(Real.cos (tau*Real.exp t)-1 : ℝ)*
        lagTerm s (Real.exp t) h := by
  unfold remainderCoefficient logMellin remainderDensity lagTerm
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  push_cast
  ring

theorem regularized_eq_spectrum_integral {s : ℂ} (hs : 0 < s.re) (tau : ℝ) :
    regularizedResponse s tau = Complex.exp ((s+1)*(Real.log 2 : ℂ))*
      ∫ t : ℝ, Complex.exp (s*t)*(Real.cos (tau*Real.exp t)-1 : ℝ)*bracket s (Real.exp t) := by
  let F : ℕ → ℝ → ℂ := fun h t =>
    (-1 : ℂ)^(h+1)*Complex.exp (-s*(Real.log (h+1) : ℂ))*
      (Complex.exp (s*t)*(remainderDensity tau h t : ℂ))
  have hi (h : ℕ) : Integrable (F h) :=
    (integrable_logWeight (measurable_remainderDensity tau h) (by positivity)
      (remainderDensity_abs_le tau h) (fun _ ht => remainderDensity_zero tau h ht) hs).const_mul _
  have hn (h : ℕ) : (∫ t : ℝ, ‖F h t‖) ≤
      (8*Real.exp (s.re*Real.log 2)/s.re)*((h+1 : ℕ) : ℝ)^(-s.re-1) := by
    unfold F
    have he (t : ℝ) : ‖(-1 : ℂ)^(h+1)*Complex.exp (-s*(Real.log (h+1) : ℂ))*
        (Complex.exp (s*t)*(remainderDensity tau h t : ℂ))‖ =
        ‖(-1 : ℂ)^(h+1)*Complex.exp (-s*(Real.log (h+1) : ℂ))‖*
          ‖Complex.exp (s*t)*(remainderDensity tau h t : ℂ)‖ := norm_mul _ _
    simp_rw [he]
    rw [integral_const_mul]
    have hh : (0 : ℝ) < (h+1 : ℕ) := by positivity
    have hx : ‖(-1 : ℂ)^(h+1)*Complex.exp (-s*(Real.log (h+1) : ℂ))‖ =
        ((h+1 : ℕ) : ℝ)^(-s.re) := by
      simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
      rw [Complex.norm_exp, Real.rpow_def_of_pos hh]
      congr 1
      simp [Complex.mul_re, mul_comm]
    rw [hx]
    calc
      _ ≤ ((h+1 : ℕ) : ℝ)^(-s.re)*
          ((8/((h+1 : ℕ) : ℝ))*Real.exp (s.re*Real.log 2)/s.re) :=
        mul_le_mul_of_nonneg_left
          (integral_norm_logWeight_le (measurable_remainderDensity tau h) (by positivity)
            (remainderDensity_abs_le tau h) (fun _ ht => remainderDensity_zero tau h ht) hs)
          (by positivity)
      _ = _ := by
        rw [show -s.re-1 = -s.re+(-1) by ring, Real.rpow_add hh, Real.rpow_neg_one]
        ring
  have hsum : Summable (fun h : ℕ => ∫ t : ℝ, ‖F h t‖) :=
    ((summable_powerBudget hs).mul_left (8*Real.exp (s.re*Real.log 2)/s.re)).of_nonneg_of_le
      (fun _ => integral_nonneg (fun _ => norm_nonneg _)) hn
  have hrem : (∑' h : ℕ, remainderCoefficient tau h s) =
      ∫ t : ℝ, Complex.exp (s*t)*(Real.cos (tau*Real.exp t)-1 : ℝ)*errorSpectrum s (Real.exp t) := by
    have he (h : ℕ) : remainderCoefficient tau h s = ∫ t : ℝ, F h t := by
      unfold F remainderCoefficient logMellin
      rw [integral_const_mul]
    rw [tsum_congr he, integral_tsum_of_summable_integral_norm hi hsum]
    apply integral_congr_ae
    filter_upwards with t
    unfold errorSpectrum
    rw [← tsum_mul_left]
    apply tsum_congr
    intro h
    unfold F remainderDensity lagTerm
    push_cast
    ring
  have ib := integrable_logWeight (measurable_bulkDensity tau) (by positivity)
    (bulkDensity_abs_le tau) (fun _ ht => bulkDensity_zero tau ht) hs
  have ir : Integrable (fun t : ℝ => Complex.exp (s*t)*
      (Real.cos (tau*Real.exp t)-1 : ℝ)*errorSpectrum s (Real.exp t)) := by
    have ht := integrable_complex_tsum hi hsum
    apply ht.congr
    filter_upwards with t
    unfold errorSpectrum
    rw [← tsum_mul_left]
    apply tsum_congr
    intro h
    unfold F remainderDensity lagTerm
    push_cast
    ring
  unfold regularizedResponse
  rw [hrem, logMellin, ← integral_const_mul, ← integral_add (ib.const_mul _) ir]
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  unfold bulkDensity bracket
  push_cast
  ring

/-- Exact all-height literal spectral bridge. -/
theorem contrast_eq_spectrum_integral {s : ℂ} (hs : 0 < s.re) (tau : ℝ) :
    continuumResponse s tau-continuumResponse s 0 =
      Complex.exp ((s+1)*(Real.log 2 : ℂ))*
        ∫ t : ℝ, Complex.exp (s*t)*(Real.cos (tau*Real.exp t)-1 : ℝ)*bracket s (Real.exp t) :=
  (contrast_eq_regularized hs tau).trans (regularized_eq_spectrum_integral hs tau)

end
end RiemannGaussian.SuzukiCarryPhaseContinuation

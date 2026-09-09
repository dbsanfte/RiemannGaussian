/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaCanonicalMoments
import Mathlib.Probability.Moments.ComplexMGF

/-!
# Exact factorial moments of a signed real Laplace integral

Exponential integrability in an open half-plane justifies every complex
derivative under the integral. The positive and negative density measures
are used only to obtain domination; their difference is reassembled before
any conclusion. The final identity retains the original signed signal.
-/

namespace RiemannGaussian
noncomputable section
open Complex Filter MeasureTheory ProbabilityTheory Set
open scoped Topology ENNReal

private theorem sign_cancel (n : ℕ) (z : ℂ) (t : ℝ) :
    (-1 : ℂ) ^ n * (((-t : ℝ) : ℂ) ^ n * Complex.exp (z * ((-t : ℝ) : ℂ))) =
      (t : ℂ) ^ n * Complex.exp (-z * (t : ℂ)) := by
  have hs : (-1 : ℂ) ^ n * (-1) ^ n = 1 := by rw [← mul_pow]; norm_num
  simp only [Complex.ofReal_neg, neg_pow (t : ℂ), mul_neg, neg_mul]
  calc
    _ = ((-1 : ℂ) ^ n * (-1) ^ n) *
        ((t : ℂ) ^ n * Complex.exp (-(z * (t : ℂ)))) := by ring
    _ = _ := by rw [hs, one_mul]

private theorem nonnegative_laplace_moments {μ : Measure ℝ} {f : ℝ → ℝ} {b : ℝ}
    (hf : AEMeasurable f μ) (hp : ∀ t, 0 ≤ f t)
    (hi : ∀ x : ℝ, b < x → Integrable (fun t : ℝ => f t * Real.exp (-x * t)) μ)
    {z : ℂ} (hz : b < z.re) :
    AnalyticAt ℂ (fun w : ℂ => ∫ t, (f t : ℂ) * Complex.exp (-w * (t : ℂ)) ∂μ) z ∧
    ∀ n : ℕ,
      Integrable (fun t : ℝ => (f t : ℂ) * (t : ℂ) ^ n *
        Complex.exp (-z * (t : ℂ))) μ ∧
      signedTaylorMoment n (fun w : ℂ =>
        ∫ t, (f t : ℂ) * Complex.exp (-w * (t : ℂ)) ∂μ) z =
        ∫ t, ((f t : ℂ) * (t : ℂ) ^ n * Complex.exp (-z * (t : ℂ))) /
          (n.factorial : ℂ) ∂μ := by
  let ν := μ.withDensity (fun t => ENNReal.ofReal (f t))
  have hdom : Ioi b ⊆ interior (integrableExpSet (fun t : ℝ => -t) ν) := by
    apply isOpen_Ioi.subset_interior_iff.mpr
    intro x hx
    change Integrable (fun t : ℝ => Real.exp (x * -t)) ν
    dsimp only [ν]
    rw [integrable_withDensity_iff_integrable_smul₀' hf.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    simpa only [ENNReal.toReal_ofReal (hp _), smul_eq_mul, mul_neg, neg_mul] using hi x hx
  have he (w : ℂ) : (∫ t, (f t : ℂ) * Complex.exp (-w * (t : ℂ)) ∂μ) =
      complexMGF (fun t : ℝ => -t) ν w := by
    rw [complexMGF]
    dsimp only [ν]
    rw [integral_withDensity_eq_integral_toReal_smul₀ hf.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_ofReal (hp _), Complex.real_smul, Complex.ofReal_neg,
      mul_neg, neg_mul]
  have hfun := funext he
  rw [hfun]
  refine ⟨analyticAt_complexMGF (hdom hz), fun n => ?_⟩
  have hn := integrable_pow_mul_cexp_of_re_mem_interior_integrableExpSet (hdom hz) n
  dsimp only [ν] at hn
  rw [integrable_withDensity_iff_integrable_smul₀' hf.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)] at hn
  simp only [ENNReal.toReal_ofReal (hp _), Complex.real_smul] at hn
  have hint : Integrable (fun t : ℝ => (f t : ℂ) * (t : ℂ) ^ n *
      Complex.exp (-z * (t : ℂ))) μ := by
    apply (hn.const_mul ((-1 : ℂ) ^ n)).congr
    filter_upwards with t
    calc
      _ = (f t : ℂ) * ((-1 : ℂ) ^ n *
          (((-t : ℝ) : ℂ) ^ n * Complex.exp (z * ((-t : ℝ) : ℂ)))) := by ring
      _ = _ := by rw [sign_cancel]; ring
  refine ⟨hint, ?_⟩
  rw [signedTaylorMoment, iteratedDeriv_complexMGF (hdom hz) n]
  dsimp only [ν]
  rw [integral_withDensity_eq_integral_toReal_smul₀ hf.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top), ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  simp only [ENNReal.toReal_ofReal (hp _), Complex.real_smul]
  calc
    _ = (f t : ℂ) * ((-1 : ℂ) ^ n *
        (((-t : ℝ) : ℂ) ^ n * Complex.exp (z * ((-t : ℝ) : ℂ)))) /
        (n.factorial : ℂ) := by ring
    _ = _ := by rw [sign_cancel]; ring

private theorem positive_part_integrable {μ : Measure ℝ} {f : ℝ → ℝ} {x : ℝ}
    (hf : AEMeasurable f μ)
    (hi : Integrable (fun t : ℝ => f t * Real.exp (-x * t)) μ) :
    Integrable (fun t : ℝ => max (f t) 0 * Real.exp (-x * t)) μ := by
  apply hi.norm.mono' (by fun_prop)
  filter_upwards with t
  simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _),
    abs_of_nonneg (le_max_right (f t) 0)]
  exact mul_le_mul_of_nonneg_right
    (max_le (le_abs_self _) (abs_nonneg _)) (Real.exp_pos _).le

/-- Every order of the complete signed Laplace moment is integrable, and
its normalized derivative is the literal factorial-weighted time integral.
Only actual exponential integrability on an open half-plane is required. -/
theorem signed_real_laplace_moments {μ : Measure ℝ} {f : ℝ → ℝ} {b : ℝ}
    (hf : AEMeasurable f μ)
    (hi : ∀ x : ℝ, b < x → Integrable (fun t : ℝ => f t * Real.exp (-x * t)) μ)
    {z : ℂ} (hz : b < z.re) :
    AnalyticAt ℂ (fun w : ℂ => ∫ t, (f t : ℂ) * Complex.exp (-w * (t : ℂ)) ∂μ) z ∧
    ∀ n : ℕ,
      Integrable (fun t : ℝ => (f t : ℂ) * (t : ℂ) ^ n *
        Complex.exp (-z * (t : ℂ))) μ ∧
      signedTaylorMoment n (fun w : ℂ =>
        ∫ t, (f t : ℂ) * Complex.exp (-w * (t : ℂ)) ∂μ) z =
        ∫ t, ((f t : ℂ) * (t : ℂ) ^ n * Complex.exp (-z * (t : ℂ))) /
          (n.factorial : ℂ) ∂μ := by
  have hp (w : ℂ) (hw : b < w.re) :=
    nonnegative_laplace_moments (hf.max aemeasurable_const) (fun t => le_max_right (f t) 0)
      (fun x hx => positive_part_integrable hf (hi x hx)) hw
  have hneg (x : ℝ) (hx : b < x) :
      Integrable (fun t : ℝ => (-f t) * Real.exp (-x * t)) μ := by
    apply (hi x hx).neg.congr
    filter_upwards with t
    exact (neg_mul (f t) _).symm
  have hm (w : ℂ) (hw : b < w.re) :=
    nonnegative_laplace_moments (f := fun t => max (-f t) 0)
      (hf.neg.max aemeasurable_const) (fun t => le_max_right (-f t) 0)
      (fun x hx => positive_part_integrable (f := fun t => -f t) hf.neg (hneg x hx)) hw
  have hsplit (t : ℝ) : ((max (f t) 0 : ℝ) : ℂ) - ((max (-f t) 0 : ℝ) : ℂ) = (f t : ℂ) := by
    have hr : max (f t) 0 - max (-f t) 0 = f t := by
      rcases le_total (f t) 0 with h | h
      · rw [max_eq_right h, max_eq_left (by linarith : 0 ≤ -f t)]
        ring
      · rw [max_eq_left h, max_eq_right (by linarith : -f t ≤ 0)]
        ring
    exact_mod_cast hr
  have he : (fun w : ℂ => ∫ t, (f t : ℂ) * Complex.exp (-w * (t : ℂ)) ∂μ) =ᶠ[𝓝 z]
      (fun w => (∫ t, ((max (f t) 0 : ℝ) : ℂ) * Complex.exp (-w * (t : ℂ)) ∂μ) -
        ∫ t, ((max (-f t) 0 : ℝ) : ℂ) * Complex.exp (-w * (t : ℂ)) ∂μ) := by
    have hopen : IsOpen {w : ℂ | b < w.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.eventually_mem hz] with w hw
    have hp0 := ((hp w hw).2 0).1
    have hm0 := ((hm w hw).2 0).1
    simp only [pow_zero, mul_one] at hp0 hm0
    rw [← integral_sub hp0 hm0]
    apply integral_congr_ae
    filter_upwards with t
    rw [← sub_mul, hsplit]
  refine ⟨((hp z hz).1.sub (hm z hz).1).congr he.symm, fun n => ?_⟩
  have hpn := (hp z hz).2 n
  have hmn := (hm z hz).2 n
  constructor
  · apply (hpn.1.sub hmn.1).congr
    filter_upwards with t
    simp only [Pi.sub_apply]
    rw [← sub_mul, ← sub_mul, hsplit]
  · rw [signedTaylorMoment_congr n he, signedTaylorMoment_sub n (hp z hz).1 (hm z hz).1,
      hpn.2, hmn.2, ← integral_sub (hpn.1.div_const _) (hmn.1.div_const _)]
    apply integral_congr_ae
    filter_upwards with t
    rw [← sub_div, ← sub_mul, ← sub_mul, hsplit]

end
end RiemannGaussian

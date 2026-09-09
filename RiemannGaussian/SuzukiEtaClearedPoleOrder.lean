/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiEtaClearedDenominator

/-!
# Exact multiplicities after clearing the eta denominator

Clearing the dyadic factor preserves every zero of the actual Suzuki
denominator and adds exactly two to the order at a dyadic exception.
These are analytic orders, so the statement retains higher-order
denominator zeros rather than imposing simplicity or pole separation.
-/

open Complex Filter Set Topology
namespace RiemannGaussian
noncomputable section

/-- The actual spectral denominator in the reflected arithmetic
coordinate, with no zero-avoidance or completion-domain assumptions. -/
theorem suzukiXiEValue_eq_xi_add_deriv (z : ℂ) :
    suzukiXiEValue z = riemannXi (suzukiArithmeticZetaArgument z) +
      deriv riemannXi (suzukiArithmeticZetaArgument z) := by
  rw [suzukiArithmeticZetaArgument_eq_one_sub_completedSpectralCoordinate,
    riemannXi_one_sub, deriv_riemannXi_one_sub, suzukiXiEValue_eq, deriv_riemannXiSpectral]
  change riemannXi (completedSpectralCoordinate z) + I *
    (I * deriv riemannXi (completedSpectralCoordinate z)) = _
  rw [← mul_assoc, I_mul_I]
  ring

private lemma arithmeticArgument_inverse (s : ℂ) :
    suzukiArithmeticZetaArgument (I * (s - 1 / 2)) = s := by
  unfold suzukiArithmeticZetaArgument
  simp only [mul_sub, ← mul_assoc, I_mul_I]
  ring

/-- Rotation and translation to the spectral coordinate preserve the
exact order of `xi+xi'`. -/
theorem analyticOrderAt_xi_add_deriv_eq_suzukiXiEValue (s : ℂ) :
    analyticOrderAt (fun w => riemannXi w + deriv riemannXi w) s =
      analyticOrderAt suzukiXiEValue (I * (s - 1 / 2)) := by
  have he : (fun w => riemannXi w + deriv riemannXi w) =
      suzukiXiEValue ∘ (fun w => I * (w - 1 / 2)) := by
    funext w
    simp only [Function.comp_apply, suzukiXiEValue_eq_xi_add_deriv, arithmeticArgument_inverse]
  rw [he]
  have hd : HasDerivAt (fun w : ℂ => I * (w - 1 / 2)) I s := by
    simpa only [id_eq, mul_one] using ((hasDerivAt_id s).sub_const (1 / 2 : ℂ)).const_mul I
  exact analyticOrderAt_comp_of_deriv_ne_zero (by fun_prop)
    (by rw [hd.deriv]; exact I_ne_zero)

private lemma analyticAt_factor (s : ℂ) : AnalyticAt ℂ pairedEtaFactor s :=
  (show Differentiable ℂ pairedEtaFactor from
    fun w => (hasDerivAt_pairedEtaFactor w).differentiableAt).analyticAt s

/-- Every dyadic zero is simple; the factor's exact order is zero or one. -/
theorem analyticOrderAt_pairedEtaFactor_eq (s : ℂ) :
    analyticOrderAt pairedEtaFactor s = if pairedEtaFactor s = 0 then 1 else 0 := by
  split_ifs with hs
  · apply (analyticAt_factor s).analyticOrderAt_eq_one_of_zero_deriv_ne_zero hs
    rw [(hasDerivAt_pairedEtaFactor s).deriv]
    apply mul_ne_zero
    · apply mul_ne_zero (by norm_num)
      have h : (Real.log 2 : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
      simpa only [Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2), ofReal_ofNat] using h
    · exact Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  · exact (analyticAt_factor s).analyticOrderAt_eq_zero.mpr hs

/-- The complete cleared denominator has exactly the genuine
denominator order plus twice the elementary dyadic order. -/
theorem analyticOrderAt_suzukiEtaClearedCarrierDenominator {s : ℂ}
    (hs : 0 < s.re) (h1 : s ≠ 1) :
    analyticOrderAt suzukiEtaClearedCarrierDenominator s =
      2 • analyticOrderAt pairedEtaFactor s +
        analyticOrderAt suzukiXiEValue (I * (s - 1 / 2)) := by
  have hG : AnalyticAt ℂ pairedEtaXiCompletionNumerator s := by
    apply DifferentiableOn.analyticAt (s := {w : ℂ | 0 < w.re})
    · intro w hw
      exact (differentiableAt_pairedEtaXiCompletionNumerator hw).differentiableWithinAt
    · exact (Complex.isOpen_re_gt 0).mem_nhds hs
  have hJ := analyticAt_suzukiEtaClearedCarrierDenominator hs h1
  have hQ : AnalyticAt ℂ (fun w => riemannXi w + deriv riemannXi w) s :=
    (differentiable_riemannXi.analyticAt s).add (differentiable_riemannXi.analyticAt s).deriv
  have he : (pairedEtaXiCompletionNumerator * suzukiEtaClearedCarrierDenominator) =ᶠ[𝓝 s]
      pairedEtaFactor ^ 2 * (fun w => riemannXi w + deriv riemannXi w) := by
    filter_upwards [(Complex.isOpen_re_gt 0).mem_nhds hs,
      (isOpen_ne_fun continuous_id continuous_const).mem_nhds h1] with w hw hw1
    exact pairedEtaXiCompletionNumerator_mul_clearedCarrierDenominator hw hw1
  have ho := analyticOrderAt_congr he
  rw [analyticOrderAt_mul hG hJ,
    hG.analyticOrderAt_eq_zero.mpr (pairedEtaXiCompletionNumerator_ne_zero_of_re_pos hs h1),
    zero_add, analyticOrderAt_mul ((analyticAt_factor s).pow 2) hQ,
    analyticOrderAt_pow (analyticAt_factor s), analyticOrderAt_xi_add_deriv_eq_suzukiXiEValue] at ho
  exact ho

/-- All orders of the cleared denominator are finite on its analytic
domain, including the added double dyadic zeros. -/
theorem analyticOrderAt_suzukiEtaClearedCarrierDenominator_ne_top {s : ℂ}
    (hs : 0 < s.re) (h1 : s ≠ 1) :
    analyticOrderAt suzukiEtaClearedCarrierDenominator s ≠ ⊤ := by
  rw [analyticOrderAt_suzukiEtaClearedCarrierDenominator hs h1,
    analyticOrderAt_pairedEtaFactor_eq]
  split_ifs <;> simp [analyticOrderAt_suzukiXiEValue_ne_top]

/-- The finite multiplicity identity separates the two spurious
dyadic orders from every genuine denominator order exactly. -/
theorem analyticOrderNatAt_suzukiEtaClearedCarrierDenominator {s : ℂ}
    (hs : 0 < s.re) (h1 : s ≠ 1) :
    analyticOrderNatAt suzukiEtaClearedCarrierDenominator s =
      (if pairedEtaFactor s = 0 then 2 else 0) +
        analyticOrderNatAt suzukiXiEValue (I * (s - 1 / 2)) := by
  unfold analyticOrderNatAt
  rw [analyticOrderAt_suzukiEtaClearedCarrierDenominator hs h1,
    analyticOrderAt_pairedEtaFactor_eq]
  split_ifs <;> simp [ENat.toNat_add, analyticOrderAt_suzukiXiEValue_ne_top]

end
end RiemannGaussian

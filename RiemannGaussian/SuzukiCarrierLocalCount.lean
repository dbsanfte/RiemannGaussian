/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiEtaLocalPoleCount
import RiemannGaussian.SuzukiCarrierPoleWindowGap

/-!
# Local denominator counts on both sides of the spectral strip

Complex conjugation preserves the arithmetic denominator's orders.
It therefore transfers the translated Jensen estimate to both signs
of the spectral abscissa. The bounds below apply to the actual
denominator and retain analytic multiplicities.
-/

open Complex Filter MeromorphicOn Metric Set Topology
open scoped ComplexConjugate
namespace RiemannGaussian
noncomputable section

/-- Conjugation preserves the exact analytic order of `xi+xi'`. -/
theorem analyticOrderAt_xi_add_deriv_conj (s : ℂ) :
    analyticOrderAt (fun w => riemannXi w + deriv riemannXi w) (conj s) =
      analyticOrderAt (fun w => riemannXi w + deriv riemannXi w) s := by
  let f : ℂ → ℂ := fun w => riemannXi w + deriv riemannXi w
  have ha (w : ℂ) : AnalyticAt ℂ f w :=
    (analyticAt_riemannXi w).add (analyticAt_riemannXi w).deriv
  have hf : conj ∘ f ∘ conj = f := by
    funext w
    simp [f, Function.comp_apply, riemannXi_conj, deriv_riemannXi_conj]
  have hi (n : ℕ) : iteratedDeriv n f (conj s) = conj (iteratedDeriv n f s) := by
    have he := iteratedDeriv_conj_conj f n
    rw [hf] at he
    simpa [Function.comp_apply] using congrFun he (conj s)
  apply ENat.eq_of_forall_natCast_le_iff
  intro n
  rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (ha (conj s)),
    natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (ha s)]
  simp [hi]

/-- Reflection between the two moving disks preserves every actual
denominator multiplicity. -/
theorem analyticOrderAt_suzukiXiLocalDenominator_neg (T : ℝ) (w : ℂ) :
    analyticOrderAt (suzukiXiLocalDenominator (-T)) w =
      analyticOrderAt (suzukiXiLocalDenominator T) (conj w) := by
  rw [analyticOrderAt_suzukiXiLocalDenominator, analyticOrderAt_suzukiXiLocalDenominator,
    ← analyticOrderAt_xi_add_deriv_eq_suzukiXiEValue,
    ← analyticOrderAt_xi_add_deriv_eq_suzukiXiEValue]
  have he : staticContourSafeEndpoint (-T) + w = conj (staticContourSafeEndpoint T + conj w) := by
    norm_num [staticContourSafeEndpoint, map_ofNat]
  rw [he, analyticOrderAt_xi_add_deriv_conj]

/-- The full local divisor mass agrees at opposite ordinates; this
is an exact symmetry, before applying the logarithmic majorant. -/
theorem sum_divisor_suzukiXiLocalDenominator_neg (T : ℝ) :
    (∑ᶠ w, divisor (suzukiXiLocalDenominator (-T)) (closedBall 0 (17 / 16)) w : ℤ) =
      ∑ᶠ w, divisor (suzukiXiLocalDenominator T) (closedBall 0 (17 / 16)) w := by
  apply finsum_eq_of_bijective conj (star_involutive.bijective)
  intro w
  have ha (U : ℝ) : AnalyticOnNhd ℂ (suzukiXiLocalDenominator U) (closedBall 0 (17 / 16)) :=
    fun z _ => analyticAt_suzukiXiLocalDenominator U z
  have hmem : conj w ∈ closedBall (0 : ℂ) (17 / 16) ↔ w ∈ closedBall (0 : ℂ) (17 / 16) := by
    simp only [mem_closedBall, dist_zero_right, norm_conj]
  by_cases hw : w ∈ closedBall (0 : ℂ) (17 / 16)
  · rw [(ha (-T)).divisor_apply hw, (ha T).divisor_apply (hmem.mpr hw),
      analyticOrderAt_suzukiXiLocalDenominator_neg]
  · simp [hw, hmem]

/-- A uniform logarithmic count for the actual denominator at both
signs of the ordinate, with no zero or multiplicity hypothesis. -/
theorem sum_divisor_suzukiXiLocalDenominator_le_log_abs {T : ℝ} (hT : 2 ≤ |T|) :
    (∑ᶠ w, divisor (suzukiXiLocalDenominator T) (closedBall 0 (17 / 16)) w : ℤ) ≤
      Real.log (suzukiEtaLocalPoleJensenConstant * (|T| + 4) ^ 2) / Real.log (18 / 17 : ℝ) := by
  by_cases ht : 0 ≤ T
  · rw [abs_of_nonneg ht] at hT ⊢
    exact sum_divisor_suzukiXiLocalDenominator_le_log hT
  · have hn : |T| = -T := abs_of_neg (lt_of_not_ge ht)
    rw [hn] at hT ⊢
    rw [← sum_divisor_suzukiXiLocalDenominator_neg T]
    exact sum_divisor_suzukiXiLocalDenominator_le_log hT

private lemma local_coordinate_inverse (T : ℝ) (z : ℂ) :
    I * (staticContourSafeEndpoint T + (suzukiArithmeticZetaArgument z -
      staticContourSafeEndpoint T) - 1 / 2) = z := by
  calc
    _ = I * (-I * z) := by unfold suzukiArithmeticZetaArgument; congr 1; ring
    _ = z := by simp [← mul_assoc]

/-- Any finite collection in the local disk has bounded total actual
denominator order. The collection need not consist of simple zeros. -/
theorem sum_suzukiXiEValue_order_le_log_of_mem_local_disk {T : ℝ} (hT : 2 ≤ |T|)
    (C : Finset ℂ) (hC : ∀ z ∈ C, suzukiArithmeticZetaArgument z - staticContourSafeEndpoint T ∈
      closedBall 0 (17 / 16)) :
    ((∑ z ∈ C, analyticOrderNatAt suzukiXiEValue z : ℕ) : ℝ) ≤
      Real.log (suzukiEtaLocalPoleJensenConstant * (|T| + 4) ^ 2) / Real.log (18 / 17 : ℝ) := by
  classical
  let g : ℂ → ℂ := fun z => suzukiArithmeticZetaArgument z - staticContourSafeEndpoint T
  let d := divisor (suzukiXiLocalDenominator T) (closedBall 0 (17 / 16))
  have ha : AnalyticOnNhd ℂ (suzukiXiLocalDenominator T) (closedBall 0 (17 / 16)) :=
    fun z _ => analyticAt_suzukiXiLocalDenominator T z
  have hg : Function.Injective g := by
    intro z v he
    have hh := congrArg (fun w => I * (staticContourSafeEndpoint T + w - 1 / 2)) he
    simpa only [g, local_coordinate_inverse] using hh
  have hd (z : ℂ) (hz : z ∈ C) : d (g z) = (analyticOrderNatAt suzukiXiEValue z : ℤ) := by
    dsimp only [d]
    rw [ha.divisor_apply (hC z hz), analyticOrderAt_suzukiXiLocalDenominator]
    rw [local_coordinate_inverse, ← Nat.cast_analyticOrderNatAt (analyticOrderAt_suzukiXiEValue_ne_top z)]
    simp
  have he : (∑ z ∈ C, (analyticOrderNatAt suzukiXiEValue z : ℤ)) = ∑ w ∈ C.image g, d w := by
    rw [Finset.sum_image (fun _ _ _ _ he => hg he)]
    exact Finset.sum_congr rfl fun z hz => (hd z hz).symm
  have hf := d.finiteSupport (isCompact_closedBall (0 : ℂ) (17 / 16))
  let K := C.image g ∪ hf.toFinset
  have hsupp : Function.support d ⊆ (K : Set ℂ) := by
    intro w hw
    exact Finset.mem_union_right _ (hf.mem_toFinset.mpr hw)
  have hs : (∑ w ∈ C.image g, d w) ≤ ∑ᶠ w, d w := by
    rw [finsum_eq_sum_of_support_subset _ hsupp]
    exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
      (fun w _ _ => ha.divisor_nonneg w)
  have hz : ((∑ z ∈ C, analyticOrderNatAt suzukiXiEValue z : ℕ) : ℝ) ≤ ((∑ᶠ w, d w : ℤ) : ℝ) := by
    rw [← he] at hs
    exact_mod_cast hs
  exact hz.trans (sum_divisor_suzukiXiLocalDenominator_le_log_abs hT)

/-- A fixed window contains the full spectral strip from height zero
to one half and fits inside the moving Jensen disk. -/
theorem suzukiArithmeticZetaArgument_mem_local_disk {T : ℝ} {z : ℂ}
    (hx : |z.re + T| ≤ 1 / 4) (hy : z.im ∈ Icc 0 (1 / 2)) :
    suzukiArithmeticZetaArgument z - staticContourSafeEndpoint T ∈ closedBall 0 (17 / 16) := by
  let w := suzukiArithmeticZetaArgument z - staticContourSafeEndpoint T
  have hr : w.re = z.im - 1 := by
    simp [w, suzukiArithmeticZetaArgument, staticContourSafeEndpoint]
    ring
  have hi : w.im = -(z.re + T) := by
    simp [w, suzukiArithmeticZetaArgument, staticContourSafeEndpoint]
    ring
  have hx2 : (z.re + T) ^ 2 ≤ (1 / 4 : ℝ) ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by norm_num)).mpr hx
  have hnorm := Complex.sq_norm w
  rw [Complex.normSq_apply, hr, hi] at hnorm
  have hw : ‖w‖ ≤ 17 / 16 := by nlinarith [hy.1, hy.2, norm_nonneg w]
  simpa only [mem_closedBall, dist_zero_right] using hw

/-- The actual retained genuine pole group in a fixed strip window
has logarithmically bounded total multiplicity on both sides of the
spectral plane. No pole order is truncated. -/
theorem sum_suzukiXiCarrierGenuinePoleWindow_orders_le_log {T : ℝ} (hT : 2 ≤ |T|) :
    ((∑ z ∈ suzukiXiCarrierGenuinePoleWindow (-T - 1 / 4) (-T + 1 / 4) 0 (1 / 2),
      analyticOrderNatAt suzukiXiEValue z : ℕ) : ℝ) ≤
      Real.log (suzukiEtaLocalPoleJensenConstant * (|T| + 4) ^ 2) / Real.log (18 / 17 : ℝ) := by
  apply sum_suzukiXiEValue_order_le_log_of_mem_local_disk hT
  intro z hz
  have hm := (mem_suzukiXiCarrierPoleWindow.mp (Finset.mem_filter.mp hz).1).1
  have hrect : (-T - 1 / 4 ≤ z.re ∧ z.re ≤ -T + 1 / 4) ∧ (0 ≤ z.im ∧ z.im ≤ 1 / 2) := by
    simpa only [Complex.Rectangle, Complex.mem_reProdIm, ofReal_re, ofReal_im, add_re, add_im,
      mul_re, mul_im, I_re, I_im, mul_zero, mul_one, add_zero, zero_add, sub_zero,
      uIcc_of_le (by linarith : -T - 1 / 4 ≤ -T + 1 / 4),
      uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2), mem_Icc] using hm
  exact suzukiArithmeticZetaArgument_mem_local_disk (abs_le.mpr ⟨by linarith [hrect.1.1],
    by linarith [hrect.1.2]⟩) hrect.2

end
end RiemannGaussian

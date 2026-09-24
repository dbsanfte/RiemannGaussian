/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.RosserSchoenfeldLargeChebyshev
import RiemannGaussian.RosserSchoenfeldComparison

/-!
# Actual prime-count bounds from the large-range Chebyshev error

The proved 41/100 theta error and exact Abel summation give the original
strict count bounds for every real x >= exp(5100). Explicit comparison
primitives pay the large-range integral, and a Taylor bound for exp pays
the entire unknown prefix below exp(5000). No estimate on the intermediate
prime range or additional zero table is assumed.
-/

namespace RiemannGaussian.RosserSchoenfeldLargePrimeCounting
noncomputable section
open Real MeasureTheory RosserSchoenfeldComparison
set_option maxHeartbeats 800000

private def upperPrimitive (x : ℝ) : ℝ := x/log x^2+(5/2)*x/log x^3

private theorem upperPrimitive_hasDerivAt {x : ℝ} (hx : 1 < x) :
    HasDerivAt upperPrimitive (1/log x^2+(1/2)/log x^3-(15/2)/log x^4) x := by
  have hd := (logTerm_hasDerivAt 1 hx).add ((logTerm_hasDerivAt 2 hx).const_mul (5/2))
  convert! hd using 1
  · ext t
    simp only [upperPrimitive, Pi.add_apply, Nat.reduceAdd]
    ring
  · norm_num only [Nat.cast_one, Nat.cast_ofNat, Nat.reduceAdd]
    field_simp [(log_pos hx).ne']
    ring

private theorem early_cost {t : ℝ} (ht : 5100 ≤ t) : exp 5000 < (1/50)*exp t/t^2 := by
  let z := t-5000
  have hz : 100 ≤ z := by dsimp [z]; linarith
  have hz0 : 0 < z := by linarith
  have ht0 : 0 < t := by linarith
  have he := Real.pow_div_factorial_le_exp z hz0.le 6
  norm_num only [Nat.factorial_succ, Nat.factorial_zero, Nat.reduceMul, Nat.cast_ofNat] at he
  have hz4 : (100 : ℝ)^4 ≤ z^4 := pow_le_pow_left₀ (by norm_num) hz 4
  have hz6 : 100000000*z^2 ≤ z^6 := by
    have hh := mul_le_mul_of_nonneg_right hz4 (sq_nonneg z)
    nlinarith [hh]
  have htz : t ≤ 51*z := by dsimp [z]; linarith
  have ht2 : t^2 ≤ 2601*z^2 := by nlinarith [sq_nonneg (51*z-t)]
  have hmain : t^2 < (1/50)*exp z := by nlinarith [sq_pos_of_pos hz0]
  have hh := mul_lt_mul_of_pos_left hmain (exp_pos 5000)
  rw [show t = 5000+z by dsimp [z]; ring, exp_add]
  apply (lt_div_iff₀ (sq_pos_of_pos (show 0 < 5000+z by linarith))).mpr
  convert! hh using 1 <;> dsimp [z] <;> ring

private theorem theta_range {x : ℝ} (hx : exp 5000 ≤ x) :
    x-(41/100)*x/log x ≤ Chebyshev.theta x ∧
      Chebyshev.theta x ≤ x+(41/100)*x/log x := by
  have hx0 := (exp_pos 5000).trans_le hx
  have hh := RosserSchoenfeldLargeChebyshev.abs_theta_sub_exp_le
    ((le_log_iff_exp_le hx0).mpr hx)
  rw [exp_log hx0, abs_le] at hh
  constructor <;> linarith [hh.1, hh.2]

private theorem theta_kernel_bounds {x : ℝ} (hx : exp 5000 ≤ x) :
    1/log x^2-2/log x^3 ≤ Chebyshev.theta x/(x*log x^2) ∧
      Chebyshev.theta x/(x*log x^2) ≤ 1/log x^2+(1/2)/log x^3-(15/2)/log x^4 := by
  have hx0 := (exp_pos 5000).trans_le hx
  have hl : 5000 ≤ log x := (le_log_iff_exp_le hx0).mpr hx
  have hl0 : 0 < log x := by linarith
  have hd0 : 0 < x*log x^2 := by positivity
  obtain ⟨hL,hU⟩ := theta_range hx
  have hLL : 1/log x^2-(41/100)/log x^3 ≤ Chebyshev.theta x/(x*log x^2) := by
    convert! div_le_div_of_nonneg_right hL hd0.le using 1
    field_simp
  have hUU : Chebyshev.theta x/(x*log x^2) ≤ 1/log x^2+(41/100)/log x^3 := by
    convert! div_le_div_of_nonneg_right hU hd0.le using 1
    field_simp
  constructor
  · apply le_trans _ hLL
    have hh : (41/100 : ℝ)/log x^3 ≤ 2/log x^3 := by gcongr; norm_num
    linarith
  · apply hUU.trans
    have hh : 0 ≤ ((9/100)*log x-15/2)/log x^4 :=
      div_nonneg (by linarith) (pow_nonneg hl0.le _)
    apply sub_nonneg.mp
    convert! hh using 1
    field_simp
    ring

private theorem base_gt_two : (2 : ℝ) < exp 5000 := by
  have hh := Real.add_one_le_exp (5000 : ℝ)
  linarith

private def lowerPrimitive (x : ℝ) : ℝ := x/log x^2

private theorem lowerPrimitive_hasDerivAt {x : ℝ} (hx : 1 < x) :
    HasDerivAt lowerPrimitive (1/log x^2-2/log x^3) x := by
  have hd := logTerm_hasDerivAt 1 hx
  convert! hd using 1
  norm_num only [Nat.cast_one, Nat.reduceAdd]
  field_simp [(log_pos hx).ne']

private theorem integral_upper {x : ℝ} (hx : exp 5000 ≤ x) :
    (∫ t in exp 5000..x, Chebyshev.theta t/(t*log t^2)) ≤
      upperPrimitive x-upperPrimitive (exp 5000) := by
  apply intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le hx
  · intro t ht
    exact (upperPrimitive_hasDerivAt (by linarith [ht.1, base_gt_two])).continuousAt.continuousWithinAt
  · intro t ht
    exact (upperPrimitive_hasDerivAt (by linarith [ht.1, base_gt_two])).hasDerivWithinAt
  · exact (Chebyshev.integrableOn_theta_div_id_mul_log_sq x).mono_set
      (Set.Icc_subset_Icc_left base_gt_two.le)
  · intro t ht
    exact (theta_kernel_bounds ht.1.le).2

private theorem integral_lower {x : ℝ} (hx : exp 5000 ≤ x) :
    lowerPrimitive x-lowerPrimitive (exp 5000) ≤
      (∫ t in exp 5000..x, Chebyshev.theta t/(t*log t^2)) := by
  apply intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le hx
  · intro t ht
    exact (lowerPrimitive_hasDerivAt (by linarith [ht.1, base_gt_two])).continuousAt.continuousWithinAt
  · intro t ht
    exact (lowerPrimitive_hasDerivAt (by linarith [ht.1, base_gt_two])).hasDerivWithinAt
  · exact (Chebyshev.integrableOn_theta_div_id_mul_log_sq x).mono_set
      (Set.Icc_subset_Icc_left base_gt_two.le)
  · intro t ht
    exact (theta_kernel_bounds ht.1.le).1

private theorem primeCounting_anchored {x : ℝ} (hx : exp 5000 ≤ x) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) =
      (Nat.primeCounting ⌊exp 5000⌋₊ : ℝ)-Chebyshev.theta (exp 5000)/log (exp 5000)+
        Chebyshev.theta x/log x+
          ∫ t in exp 5000..x, Chebyshev.theta t/(t*log t^2) := by
  have h1 := Chebyshev.primeCounting_eq_theta_div_log_add_integral (base_gt_two.le.trans hx)
  have h0 := Chebyshev.primeCounting_eq_theta_div_log_add_integral base_gt_two.le
  have hi : IntervalIntegrable (fun t => Chebyshev.theta t/(t*log t^2)) volume 2 x := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (base_gt_two.le.trans hx)]
    exact Chebyshev.integrableOn_theta_div_id_mul_log_sq x
  have hi0 : IntervalIntegrable (fun t => Chebyshev.theta t/(t*log t^2)) volume 2 (exp 5000) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le base_gt_two.le]
    exact Chebyshev.integrableOn_theta_div_id_mul_log_sq (exp 5000)
  have hh := intervalIntegral.integral_add_adjacent_intervals hi0 (hi0.symm.trans hi)
  linarith

private theorem primeCounting_bounds {x : ℝ} (hx : exp 5000 ≤ x) :
    x/log x+(59/100)*x/log x^2-2*exp 5000 ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧
      (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤
        2*exp 5000+x/log x+(141/100)*x/log x^2+(5/2)*x/log x^3 := by
  have hx1 : 1 < x := by linarith [base_gt_two]
  have hl0 := log_pos hx1
  have hθ := theta_range hx
  have hθL : x/log x-(41/100)*x/log x^2 ≤ Chebyshev.theta x/log x := by
    convert! div_le_div_of_nonneg_right hθ.1 hl0.le using 1
    field_simp
  have hθU : Chebyshev.theta x/log x ≤ x/log x+(41/100)*x/log x^2 := by
    convert! div_le_div_of_nonneg_right hθ.2 hl0.le using 1
    field_simp
  have hcountA : (Nat.primeCounting ⌊exp 5000⌋₊ : ℝ) ≤ 2*exp 5000 := by
    have hn : Nat.primeCounting ⌊exp 5000⌋₊ ≤ ⌊exp 5000⌋₊+1 := Nat.count_le Nat.Prime
    have hnR : (Nat.primeCounting ⌊exp 5000⌋₊ : ℝ) ≤ (⌊exp 5000⌋₊ : ℝ)+1 := by exact_mod_cast hn
    have hf := Nat.floor_le (exp_pos (5000 : ℝ)).le
    linarith [base_gt_two]
  have hθA : Chebyshev.theta (exp 5000)/log (exp 5000) ≤ exp 5000 := by
    have hh := (theta_range (le_refl (exp 5000))).2
    rw [log_exp] at hh ⊢
    nlinarith [exp_pos (5000 : ℝ)]
  have hθA0 : 0 ≤ Chebyshev.theta (exp 5000)/log (exp 5000) := by
    rw [log_exp]
    positivity
  have hcountA0 : (0 : ℝ) ≤ Nat.primeCounting ⌊exp 5000⌋₊ := Nat.cast_nonneg _
  have hLA : lowerPrimitive (exp 5000) ≤ exp 5000 := by
    unfold lowerPrimitive
    rw [log_exp]
    nlinarith [exp_pos (5000 : ℝ)]
  have hUA : 0 ≤ upperPrimitive (exp 5000) := by
    unfold upperPrimitive
    rw [log_exp]
    positivity
  have hIu := integral_upper hx
  have hIl := integral_lower hx
  have he := primeCounting_anchored hx
  unfold lowerPrimitive at hIl
  unfold upperPrimitive at hIu
  unfold lowerPrimitive at hLA
  unfold upperPrimitive at hUA
  ring_nf at hcountA hcountA0 hθA hθA0 hθL hθU hLA hUA hIl hIu he ⊢
  constructor
  · linarith only [hcountA0, hθA, hLA, hθL, hIl, he]
  · linarith only [hcountA, hθA0, hUA, hθU, hIu, he]

/-- Both original strict Rosser prime-count bounds hold at every real point in
this explicit large range, without a prime-count or finite-table premise. -/
theorem bounds_above_exp_5100 {x : ℝ} (hx : exp 5100 ≤ x) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧
      (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x := by
  have hx0 := (exp_pos 5100).trans_le hx
  have hl : 5100 ≤ log x := (le_log_iff_exp_le hx0).mpr hx
  have hl0 : 0 < log x := by linarith
  have hδ : 0 < log x-1/2 := by linarith
  have hxA : exp 5000 ≤ x := (exp_le_exp.mpr (by norm_num : (5000 : ℝ) ≤ 5100)).trans hx
  have hr := primeCounting_bounds hxA
  have hb := early_cost hl
  rw [exp_log hx0] at hb
  have hsmall : (5/2)*x/log x^3 < (1/20)*x/log x^2 := by
    have hc : (5/2 : ℝ)/log x < 1/20 := (div_lt_iff₀ hl0).mpr (by linarith)
    have hh := mul_lt_mul_of_pos_right hc (div_pos hx0 (sq_pos_of_pos hl0))
    convert! hh using 1 <;> field_simp
  have hmid : x/log x+(55/100)*x/log x^2 < (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
    ring_nf at hr hb ⊢
    linarith only [hr.1, hb]
  have hup : (Nat.primeCounting ⌊x⌋₊ : ℝ) < x/log x+(3/2)*x/log x^2 := by
    ring_nf at hr hb hsmall ⊢
    linarith only [hr.2, hb, hsmall]
  have hcmp : lower x < x/log x+(55/100)*x/log x^2 := by
    unfold lower
    have he : x/log x+(55/100)*x/log x^2-x/(log x-1/2) =
        x*((1/20)*log x-11/40)/(log x^2*(log x-1/2)) := by
      ring_nf
      field_simp [show -1+log x*2 ≠ 0 by linarith]
      ring
    apply sub_pos.mp
    rw [he]
    exact div_pos (mul_pos hx0 (by linarith)) (mul_pos (sq_pos_of_pos hl0) hδ)
  refine ⟨hcmp.trans hmid, hup.trans_eq ?_⟩
  unfold upper
  field_simp

end
end RiemannGaussian.RosserSchoenfeldLargePrimeCounting

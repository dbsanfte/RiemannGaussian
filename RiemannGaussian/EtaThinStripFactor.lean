import RiemannGaussian.EtaZetaDyadicRectangle

/-!
# Dyadic factor control on variable-width strips

The actual eta factor is bounded below in proportion to the strip width
on both vertical edges. At positive real arguments the original eta mass
bound also gives a much smaller explicit constant at the zeta pole.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The dyadic factor stays a quarter strip-width away from zero on
both vertical edges, uniformly in the ordinate. -/
theorem quarter_width_le_norm_etaFactor_of_re_boundary {s : ℂ} {epsilon : ℝ}
    (he : 0 < epsilon) (hehi : epsilon ≤ 1 / 2)
    (hs : s.re = 1 - epsilon ∨ s.re = 1 + epsilon) :
    epsilon / 4 ≤ ‖1 - 2 * (2 : ℂ) ^ (-s)‖ := by
  have hp : 0 < (2 : ℝ) ^ epsilon := Real.rpow_pos_of_pos (by norm_num) _
  have hlo : 1 + epsilon / 2 ≤ (2 : ℝ) ^ epsilon := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    have h := Real.add_one_le_exp (Real.log 2 * epsilon)
    nlinarith [Real.log_two_gt_d9]
  have hhi : (2 : ℝ) ^ epsilon ≤ 2 :=
    (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (by linarith : epsilon ≤ 1)).trans_eq (Real.rpow_one 2)
  rcases hs with hs | hs
  · have h := norm_sub_norm_le (2 * (2 : ℂ) ^ (-s)) (1 : ℂ)
    rw [norm_two_mul_two_cpow_neg, hs, show 1 - (1 - epsilon) = epsilon by ring,
      norm_one, norm_sub_rev] at h
    linarith
  · have hi : ((2 : ℝ) ^ epsilon)⁻¹ ≤ 1 - epsilon / 4 := by
      rw [inv_eq_one_div, div_le_iff₀ hp]
      nlinarith [mul_le_mul_of_nonneg_left hhi he.le]
    have h := norm_sub_norm_le (1 : ℂ) (2 * (2 : ℂ) ^ (-s))
    rw [norm_one, norm_two_mul_two_cpow_neg, hs,
      show 1 - (1 + epsilon) = -epsilon by ring, Real.rpow_neg (by norm_num)] at h
    linarith

/-- Positive real eta mass bounds the original eta core by one. -/
theorem norm_pairedEtaCore_ofReal_le_one {x : ℝ} (hx : 0 < x) :
    ‖pairedEtaCore (x : ℂ)‖ ≤ 1 := by
  simpa [abs_of_pos hx, hx.ne'] using
    norm_pairedEtaCore_le_div_re (s := (x : ℂ)) hx

/-- The actual eta mass and dyadic factor give the explicit pole
bound `4/x`, without using a large complex-strip envelope at ordinate zero. -/
theorem norm_riemannZeta_one_add_le_four_div {x : ℝ} (hx : 0 < x) (hxhi : x ≤ 1 / 2) :
    ‖riemannZeta (1 + (x : ℂ))‖ ≤ 4 / x := by
  have hs : 0 < (1 + (x : ℂ)).re := by simp; linarith
  have hs1 : (1 + (x : ℂ)) ≠ 1 := by simp [hx.ne']
  have hfactor := quarter_width_le_norm_etaFactor_of_re_boundary hx hxhi
    (s := 1 + (x : ℂ)) (Or.inr (by simp))
  have he := congrArg norm (pairedEtaCore_eq_factor_riemannZeta_of_re_pos_of_ne_one hs hs1)
  rw [norm_mul] at he
  have heta : ‖pairedEtaCore (1 + (x : ℂ))‖ ≤ 1 := by
    simpa using norm_pairedEtaCore_ofReal_le_one (show 0 < 1 + x by linarith)
  have hm := mul_le_mul_of_nonneg_right hfactor (norm_nonneg (riemannZeta (1 + (x : ℂ))))
  rw [le_div_iff₀ hx]
  nlinarith

end

end RiemannGaussian

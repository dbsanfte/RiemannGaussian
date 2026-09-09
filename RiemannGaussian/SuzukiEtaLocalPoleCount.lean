/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiEtaLocalGrowth
import RiemannGaussian.SuzukiEtaClearedPoleOrder

/-!
# Logarithmic local count for the actual Suzuki denominator

Jensen's inequality is applied after removing the common Gamma scale
and clearing the elementary dyadic divisions. The resulting count
bounds the full denominator's zeros, with every multiplicity retained.
The exact divisor identity records the extra double dyadic zeros
separately. No simplicity, interior zero-free disk, or assumed residue
bound enters this local count.
-/

open Complex Filter MeromorphicOn Metric Set Topology
namespace RiemannGaussian
noncomputable section

/-- A fixed growth constant furnished by the actual eta and digamma
estimates, independent of the ordinate. -/
def suzukiEtaLocalClearedGrowthConstant : ℝ :=
  Classical.choose exists_norm_suzukiEtaLocalClearedDenominator_le_quadratic

/-- The chosen polynomial constant is at least one. -/
theorem one_le_suzukiEtaLocalClearedGrowthConstant :
    1 ≤ suzukiEtaLocalClearedGrowthConstant :=
  (Classical.choose_spec exists_norm_suzukiEtaLocalClearedDenominator_le_quadratic).1

/-- The fixed constant bounds the actual cleared denominator on every
outer disk, without deleting any zero. -/
theorem norm_suzukiEtaLocalClearedDenominator_le {T : ℝ} (hT : 2 ≤ T)
    {w : ℂ} (hw : w ∈ closedBall 0 (9 / 8)) :
    ‖suzukiEtaLocalClearedDenominator T w‖ ≤ suzukiEtaLocalClearedGrowthConstant * (T + 4) ^ 2 :=
  (Classical.choose_spec exists_norm_suzukiEtaLocalClearedDenominator_le_quadratic).2 T hT w hw

/-- The ratio of the fixed polynomial constant to the proved safe
center floor. This normalization removes the Gamma decay from Jensen. -/
def suzukiEtaLocalPoleJensenConstant : ℝ :=
  suzukiEtaLocalClearedGrowthConstant /
    (staticContourSafeEtaFactorFloor ^ 2 / staticContourSafeZetaDirichletMass)

/-- The Jensen constant is strictly positive. -/
theorem suzukiEtaLocalPoleJensenConstant_pos : 0 < suzukiEtaLocalPoleJensenConstant := by
  unfold suzukiEtaLocalPoleJensenConstant
  positivity [one_le_suzukiEtaLocalClearedGrowthConstant,
    staticContourSafeEtaFactorFloor_pos, one_le_staticContourSafeZetaDirichletMass]

/-- The multiplicity-weighted count of all cleared denominator zeros
in a fixed moving disk is logarithmic in the ordinate. -/
theorem sum_divisor_suzukiEtaLocalClearedDenominator_le_log {T : ℝ} (hT : 2 ≤ T) :
    (∑ᶠ w, divisor (suzukiEtaLocalClearedDenominator T) (closedBall 0 (17 / 16)) w : ℤ) ≤
      Real.log (suzukiEtaLocalPoleJensenConstant * (T + 4) ^ 2) / Real.log (18 / 17 : ℝ) := by
  let M := suzukiEtaLocalClearedGrowthConstant * (T + 4) ^ 2
  let b := staticContourSafeEtaFactorFloor ^ 2 / staticContourSafeZetaDirichletMass
  have hb : 0 < b := by
    dsimp [b]
    positivity [staticContourSafeEtaFactorFloor_pos, one_le_staticContourSafeZetaDirichletMass]
  have hcenter : b ≤ ‖suzukiEtaLocalClearedDenominator T 0‖ := by
    simpa only [suzukiEtaLocalClearedDenominator, add_zero] using
      safe_floor_le_norm_suzukiEtaClearedCarrierDenominator (by linarith : 0 < T)
  have hM : 1 ≤ M := by
    dsimp [M]
    nlinarith [one_le_suzukiEtaLocalClearedGrowthConstant,
      mul_le_mul_of_nonneg_left one_le_suzukiEtaLocalClearedGrowthConstant (sq_nonneg (T + 4))]
  have ha : AnalyticOnNhd ℂ (suzukiEtaLocalClearedDenominator T) (closedBall 0 |(9 / 8 : ℝ)|) := by
    norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 9 / 8)]
    exact analyticOnNhd_suzukiEtaLocalClearedDenominator hT
  have hj := ha.sum_divisor_le (r := 17 / 16) (R := 9 / 8) (M := M)
    (by norm_num) (by norm_num) hM (norm_pos_iff.mp (hb.trans_le hcenter)) (by
      intro w hw
      apply norm_suzukiEtaLocalClearedDenominator_le hT
      apply sphere_subset_closedBall
      simpa only [abs_of_pos (by norm_num : (0 : ℝ) < 9 / 8)] using hw)
  have hr : M / ‖suzukiEtaLocalClearedDenominator T 0‖ ≤
      suzukiEtaLocalPoleJensenConstant * (T + 4) ^ 2 := by
    calc
      _ ≤ M / b := div_le_div_of_nonneg_left (by linarith) hb hcenter
      _ = _ := by dsimp [M, b, suzukiEtaLocalPoleJensenConstant]; ring
  have hl := Real.log_le_log (div_pos (by linarith : 0 < M) (hb.trans_le hcenter)) hr
  have hj' :
      ((∑ᶠ w, divisor (suzukiEtaLocalClearedDenominator T) (closedBall 0 (17 / 16)) w : ℤ) : ℝ) ≤
        Real.log (M / ‖suzukiEtaLocalClearedDenominator T 0‖) / Real.log (18 / 17 : ℝ) := by
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 17 / 16)] at hj
    norm_num at hj
    exact hj
  exact hj'.trans (div_le_div_of_nonneg_right hl (Real.log_pos (by norm_num : (1 : ℝ) < 18 / 17)).le)

/-- The actual entire Suzuki denominator in the same translated disk.
This function has no artificial dyadic factor. -/
def suzukiXiLocalDenominator (T : ℝ) (w : ℂ) : ℂ :=
  suzukiXiEValue (I * (staticContourSafeEndpoint T + w - 1 / 2))

/-- The rotated local denominator is entire. -/
theorem analyticAt_suzukiXiLocalDenominator (T : ℝ) (w : ℂ) :
    AnalyticAt ℂ (suzukiXiLocalDenominator T) w :=
  (analyticAt_suzukiXiEValue _).comp (by fun_prop)

/-- The affine coordinate change preserves every actual denominator
order, including higher-order zeros. -/
theorem analyticOrderAt_suzukiXiLocalDenominator (T : ℝ) (w : ℂ) :
    analyticOrderAt (suzukiXiLocalDenominator T) w =
      analyticOrderAt suzukiXiEValue (I * (staticContourSafeEndpoint T + w - 1 / 2)) := by
  have hd : HasDerivAt (fun z : ℂ => I * (staticContourSafeEndpoint T + z - 1 / 2)) I w := by
    simpa only [id_eq, mul_one] using
      (((hasDerivAt_id w).const_add (staticContourSafeEndpoint T)).sub_const (1 / 2 : ℂ)).const_mul I
  exact analyticOrderAt_comp_of_deriv_ne_zero (by fun_prop) (by rw [hd.deriv]; exact I_ne_zero)

private lemma local_domain {T : ℝ} (hT : 2 ≤ T) {w : ℂ}
    (hw : w ∈ closedBall 0 (17 / 16)) :
    0 < (staticContourSafeEndpoint T + w).re ∧ staticContourSafeEndpoint T + w ≠ 1 := by
  have hn : ‖w‖ ≤ 17 / 16 := by simpa only [mem_closedBall, dist_zero_right] using hw
  have hr := (abs_le.mp (Complex.abs_re_le_norm w)).1
  have hi := (abs_le.mp (Complex.abs_im_le_norm w)).1
  constructor
  · simp only [staticContourSafeEndpoint, add_re, ofReal_re, mul_re, I_re, ofReal_im, I_im]
    linarith
  · intro he
    have he' := congrArg Complex.im he
    simp [staticContourSafeEndpoint] at he'
    linarith

private lemma local_cleared_order (T : ℝ) (w : ℂ) :
    analyticOrderAt (suzukiEtaLocalClearedDenominator T) w =
      analyticOrderAt suzukiEtaClearedCarrierDenominator (staticContourSafeEndpoint T + w) := by
  have hd : HasDerivAt (fun z : ℂ => staticContourSafeEndpoint T + z) 1 w := by
    simpa using (hasDerivAt_id w).const_add (staticContourSafeEndpoint T)
  exact analyticOrderAt_comp_of_deriv_ne_zero (by fun_prop) (by rw [hd.deriv]; exact one_ne_zero)

private lemma analytic_divisor_eq_natOrder {f : ℂ → ℂ} {U : Set ℂ} {w : ℂ}
    (ha : AnalyticOnNhd ℂ f U) (hw : w ∈ U) (hf : analyticOrderAt f w ≠ ⊤) :
    divisor f U w = (analyticOrderNatAt f w : ℤ) := by
  rw [ha.divisor_apply hw, ← Nat.cast_analyticOrderNatAt hf]
  simp

/-- Exact local divisor accounting: the cleared count equals the
genuine count plus two at each dyadic exception. -/
theorem divisor_suzukiEtaLocalClearedDenominator_eq {T : ℝ} (hT : 2 ≤ T) {w : ℂ}
    (hw : w ∈ closedBall 0 (17 / 16)) :
    divisor (suzukiEtaLocalClearedDenominator T) (closedBall 0 (17 / 16)) w =
      (if pairedEtaFactor (staticContourSafeEndpoint T + w) = 0 then 2 else 0) +
        divisor (suzukiXiLocalDenominator T) (closedBall 0 (17 / 16)) w := by
  obtain ⟨hs, h1⟩ := local_domain hT hw
  have hj : analyticOrderAt (suzukiEtaLocalClearedDenominator T) w ≠ ⊤ := by
    rw [local_cleared_order]
    exact analyticOrderAt_suzukiEtaClearedCarrierDenominator_ne_top hs h1
  have he : analyticOrderAt (suzukiXiLocalDenominator T) w ≠ ⊤ := by
    rw [analyticOrderAt_suzukiXiLocalDenominator]
    exact analyticOrderAt_suzukiXiEValue_ne_top _
  have haj : AnalyticOnNhd ℂ (suzukiEtaLocalClearedDenominator T) (closedBall 0 (17 / 16)) :=
    (analyticOnNhd_suzukiEtaLocalClearedDenominator hT).mono (closedBall_subset_closedBall (by norm_num))
  have hae : AnalyticOnNhd ℂ (suzukiXiLocalDenominator T) (closedBall 0 (17 / 16)) :=
    fun z _ => analyticAt_suzukiXiLocalDenominator T z
  rw [analytic_divisor_eq_natOrder haj hw hj, analytic_divisor_eq_natOrder hae hw he]
  have hnat : analyticOrderNatAt (suzukiEtaLocalClearedDenominator T) w =
      (if pairedEtaFactor (staticContourSafeEndpoint T + w) = 0 then 2 else 0) +
        analyticOrderNatAt (suzukiXiLocalDenominator T) w := by
    simpa only [analyticOrderNatAt, local_cleared_order, analyticOrderAt_suzukiXiLocalDenominator] using
      analyticOrderNatAt_suzukiEtaClearedCarrierDenominator hs h1
  rw [hnat, Nat.cast_add]
  split_ifs <;> norm_num

/-- The actual denominator's local multiplicity count has the same
logarithmic majorant. All dyadic extras are excluded from its left side. -/
theorem sum_divisor_suzukiXiLocalDenominator_le_log {T : ℝ} (hT : 2 ≤ T) :
    (∑ᶠ w, divisor (suzukiXiLocalDenominator T) (closedBall 0 (17 / 16)) w : ℤ) ≤
      Real.log (suzukiEtaLocalPoleJensenConstant * (T + 4) ^ 2) / Real.log (18 / 17 : ℝ) := by
  have hp (w : ℂ) : divisor (suzukiXiLocalDenominator T) (closedBall 0 (17 / 16)) w ≤
      divisor (suzukiEtaLocalClearedDenominator T) (closedBall 0 (17 / 16)) w := by
    by_cases hw : w ∈ closedBall (0 : ℂ) (17 / 16)
    · rw [divisor_suzukiEtaLocalClearedDenominator_eq hT hw]
      split_ifs <;> omega
    · simp [hw]
  have hf := finsum_le_finsum'
    ((divisor (suzukiXiLocalDenominator T) (closedBall 0 (17 / 16))).finiteSupport (isCompact_closedBall _ _))
    ((divisor (suzukiEtaLocalClearedDenominator T) (closedBall 0 (17 / 16))).finiteSupport
      (isCompact_closedBall _ _)) hp
  have hf' : ((∑ᶠ w, divisor (suzukiXiLocalDenominator T) (closedBall 0 (17 / 16)) w : ℤ) : ℝ) ≤
      ((∑ᶠ w, divisor (suzukiEtaLocalClearedDenominator T) (closedBall 0 (17 / 16)) w : ℤ) : ℝ) := by
    exact_mod_cast hf
  exact hf'.trans (sum_divisor_suzukiEtaLocalClearedDenominator_le_log hT)

end
end RiemannGaussian

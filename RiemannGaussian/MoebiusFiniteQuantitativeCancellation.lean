import RiemannGaussian.MoebiusExponentialContourBound

/-!
# Quantitative cancellation for the literal finite Möbius prefix

The shrinking-heat contour and the explicit square-root cutoff error
give exponential decay in the cubic logarithmic scale. The resulting
all-integer linear remainder has a specified dependence on that scale,
so it can be carried through growing finite divisor families.
-/

open Filter
open scoped Topology

namespace RiemannGaussian

noncomputable section

/-- A fixed constant covering cutoff displacement, rounding, negative centers, and every contour term. -/
def moebiusFiniteCancellationConstant : ℝ :=
  10 + moebiusDirichletMass 2 * Real.exp 4 / 2 + 2 * moebiusFiniteContourPrefactor

/-- The complete finite-cutoff cancellation constant is positive. -/
theorem moebiusFiniteCancellationConstant_pos : 0 < moebiusFiniteCancellationConstant := by
  have hD := one_le_moebiusDirichletMass (show (1 : ℝ) < 2 by norm_num)
  have hC := moebiusFiniteContourPrefactor_pos
  unfold moebiusFiniteCancellationConstant
  positivity

/-- The actual finite Möbius prefix has an exponential normalized gain whenever the explicit cubic-scale contour conditions hold. -/
theorem abs_moebiusLogPrefix_cubic_ratio_le {h : ℝ} (hh : 22 ≤ h)
    (hlarge : 1 / (500000 * zetaReciprocalLowHeightWidth) ≤ h)
    (htail : 4 * moebiusFiniteContourCenter h ≤ Real.exp h) :
    |moebiusLogPrefix (moebiusFiniteContourCenter h) / Real.exp (moebiusFiniteContourCenter h)| ≤
      moebiusFiniteCancellationConstant * Real.exp (-h / 2) := by
  let a := moebiusFiniteContourCenter h
  let D := moebiusDirichletMass 2 * Real.exp 4 / 2
  let C := moebiusFiniteContourPrefactor
  have hD : 0 ≤ D := by
    have hd := one_le_moebiusDirichletMass (show (1 : ℝ) < 2 by norm_num)
    dsimp [D]
    positivity
  have hC : 0 ≤ C := moebiusFiniteContourPrefactor_pos.le
  have ha : h ≤ a := by
    dsimp [a, moebiusFiniteContourCenter]
    nlinarith [mul_nonneg (sq_nonneg h) (show 0 ≤ h - 1 by linarith), sq_nonneg (h - 1)]
  have htau : 0 < Real.exp (-h) := Real.exp_pos _
  have htaule : Real.exp (-h) ≤ 1 / 4 := by
    have hd := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4)
      (show 4 ≤ Real.exp h by linarith [Real.add_one_le_exp h])
    simpa only [Real.exp_neg, one_div] using hd
  have hG := gaussianMoebiusContourMajorant_exponentialScale_le hh hlarge htail
  have hnum : moebiusDirichletMass 2 * Real.exp (4 * Real.exp (-h)) / 2 +
      2 * gaussianMoebiusContourMajorant a (Real.exp (-h)) (Real.exp h) ≤
        D + 2 * C * Real.exp (a - h) := by
    have hd := one_le_moebiusDirichletMass (show (1 : ℝ) < 2 by norm_num)
    have hb : moebiusDirichletMass 2 * Real.exp (4 * Real.exp (-h)) / 2 ≤ D := by
      dsimp [D]
      gcongr
      linarith
    nlinarith
  have hmass : Real.exp (-h / 2) ≤ moebiusCutoffGaussianMass (Real.exp (-h)) := by
    rw [moebiusCutoffGaussianMass_exp_neg]
    have hs : 1 ≤ Real.sqrt (4 * Real.pi) := by
      have hp : 1 ≤ 4 * Real.pi := by linarith [Real.pi_gt_three]
      simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hp
    nlinarith [Real.exp_pos (-h / 2)]
  have hden : Real.exp (a - h / 2) ≤ Real.exp a * moebiusCutoffGaussianMass (Real.exp (-h)) := by
    calc
      _ = Real.exp a * Real.exp (-h / 2) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hmass (Real.exp_pos a).le
  have hquot : (moebiusDirichletMass 2 * Real.exp (4 * Real.exp (-h)) / 2 +
      2 * gaussianMoebiusContourMajorant a (Real.exp (-h)) (Real.exp h)) /
        (Real.exp a * moebiusCutoffGaussianMass (Real.exp (-h))) ≤ (D + 2 * C) * Real.exp (-h / 2) := by
    apply (div_le_div_of_nonneg_right hnum (by positivity [moebiusCutoffGaussianMass_pos htau])).trans
    apply (div_le_div_of_nonneg_left (by positivity) (Real.exp_pos _) hden).trans
    rw [add_div]
    have hd : D / Real.exp (a - h / 2) ≤ D * Real.exp (-h / 2) := by
      rw [div_eq_mul_inv, ← Real.exp_neg]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hD
    have hc : (2 * C * Real.exp (a - h)) / Real.exp (a - h / 2) = 2 * C * Real.exp (-h / 2) := by
      rw [mul_div_assoc, ← Real.exp_sub]
      congr 2
      ring
    rw [hc]
    exact (add_le_add hd le_rfl).trans_eq (by ring)
  have hb := abs_moebiusLogPrefix_exp_ratio_le_contour (show 0 ≤ a by linarith)
    htau htaule (show 2 ≤ Real.exp h by linarith [Real.add_one_le_exp h])
  rw [sqrt_exp_neg_moebiusHeatTime] at hb
  have he : Real.exp (-a) ≤ Real.exp (-h / 2) := Real.exp_le_exp.mpr (by linarith)
  have hc : moebiusFiniteCancellationConstant = 10 + D + 2 * C := rfl
  rw [hc]
  linarith

/-- The complete unsmoothed finite sum has an eventual exponential gain on the cubic logarithmic scale. -/
theorem abs_moebiusLogPrefix_cubic_le_eventually :
    ∀ᶠ h : ℝ in atTop, |moebiusLogPrefix (moebiusFiniteContourCenter h)| ≤
      moebiusFiniteCancellationConstant * Real.exp (moebiusFiniteContourCenter h - h / 2) := by
  filter_upwards [eventually_moebiusExponentialContour_conditions] with h hh
  have hb := abs_moebiusLogPrefix_cubic_ratio_le hh.1 hh.2.1 hh.2.2
  rw [abs_div, abs_of_pos (Real.exp_pos _), div_le_iff₀ (Real.exp_pos _)] at hb
  apply hb.trans_eq
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- One threshold gives an explicit scale-dependent linear remainder for every actual integer cutoff, with no unspecified epsilon remainder. -/
theorem exists_moebiusFinitePrefix_exponential_remainder :
    ∃ H : ℝ, 22 ≤ H ∧ ∀ h : ℝ, H ≤ h → ∀ M : ℕ,
      |moebiusFinitePrefix M| ≤ moebiusFiniteCancellationConstant * Real.exp (-h / 2) * M +
        Real.exp (moebiusFiniteContourCenter h) := by
  obtain ⟨H, hH⟩ := eventually_atTop.mp abs_moebiusLogPrefix_cubic_le_eventually
  refine ⟨max H 22, le_max_right _ _, fun h hh M ↦ ?_⟩
  have hhh : 22 ≤ h := (le_max_right _ _).trans hh
  have hC := moebiusFiniteCancellationConstant_pos
  have ha : 0 ≤ moebiusFiniteContourCenter h := by unfold moebiusFiniteContourCenter; positivity
  by_cases hM : Real.exp (moebiusFiniteContourCenter h) ≤ (M : ℝ)
  · have hMp : (0 : ℝ) < M := (Real.exp_pos _).trans_le hM
    have hlog : moebiusFiniteContourCenter h ≤ Real.log (M : ℝ) :=
      (Real.le_log_iff_exp_le hMp).mpr hM
    let u := (Real.log (M : ℝ) / 1000000000000000) ^ ((3 : ℝ)⁻¹)
    have hu : 0 ≤ u := Real.rpow_nonneg (by positivity [ha.trans hlog]) _
    have hcub : u ^ 3 = Real.log (M : ℝ) / 1000000000000000 :=
      Real.rpow_inv_natCast_pow (by positivity [ha.trans hlog]) (by decide : (3 : ℕ) ≠ 0)
    have hcenter : moebiusFiniteContourCenter u = Real.log (M : ℝ) := by
      unfold moebiusFiniteContourCenter
      rw [hcub]
      ring
    have hhu : h ≤ u := (pow_le_pow_iff_left₀ (by linarith) hu (by decide : (3 : ℕ) ≠ 0)).mp (by
      rw [← hcenter] at hlog
      dsimp [moebiusFiniteContourCenter] at hlog
      nlinarith)
    have hb := hH u (((le_max_left _ _).trans hh).trans hhu)
    rw [hcenter, moebiusLogPrefix, Real.exp_log hMp, Nat.floor_natCast] at hb
    have hb' : |moebiusFinitePrefix M| ≤ moebiusFiniteCancellationConstant * Real.exp (-u / 2) * M := by
      apply hb.trans_eq
      rw [show Real.log (M : ℝ) - u / 2 = -u / 2 + Real.log (M : ℝ) by ring,
        Real.exp_add, Real.exp_log hMp]
      ring
    have hm := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith : -u / 2 ≤ -h / 2)) hC.le)
      hMp.le
    exact (hb'.trans hm).trans (le_add_of_nonneg_right (Real.exp_pos _).le)
  · have hb := abs_moebiusFinitePrefix_le M
    have hc : 0 ≤ moebiusFiniteCancellationConstant * Real.exp (-h / 2) * M := by positivity
    linarith

end

end RiemannGaussian

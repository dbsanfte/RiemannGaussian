/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovFordDefectRate

/-!
# Lower bounds for Ford's selected defect

The lower half of (3.17) follows directly from the actual rank interval.
It yields the multiplicative lower recurrence used in Ford's Lemma 3.6,
including after the selected iteration has stopped. All defects remain
strictly positive, as needed for the logarithmic potential.
-/

namespace RiemannGaussian.VinogradovFordLowerDefect
noncomputable section
open VinogradovFordScales VinogradovFordSchedule VinogradovFordRank
open VinogradovFordQuantitativeScale VinogradovFordSelectedIteration VinogradovFordDefectRate

/-- The lower half of Ford's (3.17) on the actual rounded-rank interval. -/
theorem ratio_lower {k d r : ℝ} (hk : 0 < k) (hd0 : 0 ≤ d) (hd : d ≤ 1)
    (hrlo : k * (1 - d) ≤ r) (hrhi : r ≤ k)
    (hden : 0 < 2 * r * k + 2 * d * k ^ 2 - (k - r) * (k - r + 1)) :
    (1 - d) / (2 * k) ≤ r / (2 * r * k + 2 * d * k ^ 2 - (k - r) * (k - r + 1)) := by
  apply (div_le_div_iff₀ (by positivity : 0 < 2 * k) hden).mpr
  have h₁ := mul_nonneg (show 0 ≤ 2 * d * k by positivity) (sub_nonneg.mpr hrlo)
  have h₂ := mul_nonneg (mul_nonneg (show 0 ≤ 1 - d by linarith)
    (sub_nonneg.mpr hrhi)) (show 0 ≤ k - r + 1 by linarith)
  nlinarith only [h₁, h₂]

/-- The exact stationary main term is a lower bound for the actual step. -/
theorem selectedStep_ge_stationary {k : ℕ} {delta : ℝ} (hk : 26 ≤ k)
    (hlower : (k : ℝ) ≤ delta) (hupper : delta ≤ (k : ℝ) * ((k : ℝ) - 1) / 2) :
    delta - 2 * k + 4 * (k : ℝ) ^ 2 * rank k delta /
      (2 * (rank k delta : ℝ) * k + depthReserve k (rank k delta) delta) ≤
        selectedStep k delta := by
  obtain ⟨hr4, _, _, _, hdepth, _⟩ := admissible hk hlower hupper
  have hy := (depth_nonneg (maximalDepth k (rank k delta) delta)).trans hdepth
  have hs := stationary_le_backwardScale (by omega : 0 < k)
    (by omega : 0 < rank k delta) hy hupper 0 (maximalDepth k (rank k delta) delta)
  change stationaryScale k (rank k delta) delta ≤
    schedule k (rank k delta) (maximalDepth k (rank k delta) delta) delta 0 at hs
  have ha := (scale_coefficient_bounds hk hlower hupper).1
  have hm := mul_nonneg (sub_nonneg.mpr hs) ha
  have hden := stationary_denominator_pos (by omega : 0 < k)
    (by omega : 0 < rank k delta) hy
  have he : selectedStep k delta = delta - 2 * k +
      4 * (k : ℝ) ^ 2 * rank k delta /
        (2 * (rank k delta : ℝ) * k + depthReserve k (rank k delta) delta) +
      (schedule k (rank k delta) (maximalDepth k (rank k delta) delta) delta 0 -
        stationaryScale k (rank k delta) delta) *
        (2 * (k : ℝ) * rank k delta - depthReserve k (rank k delta) delta) / 2 := by
    unfold selectedStep nextDefect stationaryScale
    have hd : (k : ℝ) * rank k delta * 2 + depthReserve k (rank k delta) delta ≠ 0 := by
      nlinarith
    field_simp [hd]
    unfold depthReserve
    ring
  linarith

/-- Ford's multiplicative lower defect bound for each active step. -/
theorem selectedStep_lower {k : ℕ} {delta : ℝ} (hk : 26 ≤ k)
    (hlower : (k : ℝ) ≤ delta) (hupper : delta ≤ (k : ℝ) * ((k : ℝ) - 1) / 2) :
    delta * (1 - 2 / (k : ℝ)) ≤ selectedStep k delta := by
  have hkR : (26 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  let d := delta / (k : ℝ) ^ 2
  have hd0 : 0 ≤ d := div_nonneg (by linarith) (sq_nonneg _)
  have hd : d ≤ 1 := (div_le_iff₀ (sq_pos_of_pos hkpos)).mpr (by nlinarith)
  have he : d * (k : ℝ) ^ 2 = delta := div_mul_cancel₀ _ (pow_ne_zero _ hkpos.ne')
  have hquot : delta / k = d * k := by dsimp [d]; field_simp
  obtain ⟨_, hrk, hrlo, _⟩ := rank_bounds hk hlower hupper
  have hden : 0 < 2 * (rank k delta : ℝ) * k + depthReserve k (rank k delta) delta :=
    lt_of_lt_of_le (by positivity) (stationary_denominator_ge hk hlower hupper)
  have hD : 2 * (rank k delta : ℝ) * k + 2 * d * (k : ℝ) ^ 2 -
      ((k : ℝ) - rank k delta) * ((k : ℝ) - rank k delta + 1) =
        2 * (rank k delta : ℝ) * k + depthReserve k (rank k delta) delta := by
    unfold depthReserve
    nlinarith only [he]
  have hr := ratio_lower hkpos hd0 hd
    (show (k : ℝ) * (1 - d) ≤ rank k delta by rw [hquot] at hrlo; nlinarith)
    (by exact_mod_cast hrk) (by rwa [hD])
  rw [hD] at hr
  have hs := selectedStep_ge_stationary hk hlower hupper
  have hm := mul_le_mul_of_nonneg_left hr (show (0 : ℝ) ≤ 4 * (k : ℝ) ^ 2 by positivity)
  have hsimple : delta - 2 * k + 4 * (k : ℝ) ^ 2 * ((1 - d) / (2 * k)) =
      delta * (1 - 2 / (k : ℝ)) := by dsimp [d]; field_simp; ring
  rw [← hsimple]
  simp only [div_eq_mul_inv] at hs hm ⊢
  nlinarith only [hs, hm]

/-- The same multiplicative lower recurrence holds through stopped steps. -/
theorem selectedDefect_succ_ge {k : ℕ} (hk : 26 ≤ k) (j : ℕ) :
    selectedDefect k j * (1 - 2 / (k : ℝ)) ≤ selectedDefect k (j + 1) := by
  rw [selectedDefect]
  split_ifs with hj
  · by_cases hd : (k : ℝ) ≤ selectedDefect k j
    · exact selectedStep_lower hk hd (selectedDefect_bounds hk j).2
    · exact selectedStep_boundary_lower hk hj.le (by linarith)
  · have hp := mul_nonneg (selectedDefect_bounds hk j).1 (show (0 : ℝ) ≤ 2 / k by positivity)
    nlinarith

/-- A nonzero initial defect can never collapse to zero in finitely many
selected steps. This provides the domain of the logarithmic potential. -/
theorem selectedDefect_pos {k : ℕ} (hk : 26 ≤ k) (j : ℕ) : 0 < selectedDefect k j := by
  have hkR : (26 : ℝ) ≤ k := by exact_mod_cast hk
  have hfactor : 0 < 1 - 2 / (k : ℝ) := by
    have hh : 2 / (k : ℝ) < 1 := (div_lt_one (by linarith : (0 : ℝ) < k)).mpr (by linarith)
    linarith
  induction j with
  | zero => exact div_pos (mul_pos (by linarith) (by linarith)) (by norm_num)
  | succ j ih => exact (mul_pos ih hfactor).trans_le (selectedDefect_succ_ge hk j)

/-- Iteration preserves the paper's lower geometric envelope. -/
theorem selectedDefect_geometric_lower {k : ℕ} (hk : 26 ≤ k) (j : ℕ) :
    (1 - 2 / (k : ℝ)) ^ j * ((k : ℝ) * ((k : ℝ) - 1) / 2) ≤ selectedDefect k j := by
  have hkR : (26 : ℝ) ≤ k := by exact_mod_cast hk
  have hfactor : 0 ≤ 1 - 2 / (k : ℝ) := by
    have hh : 2 / (k : ℝ) ≤ 1 := (div_le_one (by linarith : (0 : ℝ) < k)).mpr (by linarith)
    linarith
  induction j with
  | zero => simp only [pow_zero, one_mul, selectedDefect, le_refl]
  | succ j ih =>
    have hh := mul_le_mul_of_nonneg_right ih hfactor
    rw [pow_succ]
    nlinarith only [hh, selectedDefect_succ_ge hk j]

end
end RiemannGaussian.VinogradovFordLowerDefect

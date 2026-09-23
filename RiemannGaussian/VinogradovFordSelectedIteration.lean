/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovFordRank

/-!
# The published rank selection in the actual moment iteration

Ford's Lemma 3.6 applies its rounded rank and maximal depth while the defect
exceeds `k - 1`. This includes the last rank-k step from `(k-1,k]`;
freezing at `k` would not suffice at the top of the published order range.
Once the defect is at most `k-1`, the sequence keeps that defect and raises
the moment order by the trivial pointwise bound. The closed numerical defect and coefficient estimates are not
asserted here. Short-prime supply remains an explicit arithmetic premise.
-/

namespace RiemannGaussian.VinogradovFordSelectedIteration
noncomputable section
open VinogradovMeanValue VinogradovFordScales VinogradovFordSchedule
open VinogradovFordGlobalStep VinogradovFordRank VinogradovFordMomentSequence

/-- The exact original step with Ford's rounded rank and largest depth. -/
def selectedStep (k : ℕ) (delta : ℝ) : ℝ :=
  nextDefect k (rank k delta) delta
    (schedule k (rank k delta) (maximalDepth k (rank k delta) delta) delta 0)

/-- The published iteration, stopped after the final rank-k boundary step. -/
def selectedDefect (k : ℕ) : ℕ → ℝ
  | 0 => (k : ℝ) * ((k : ℝ) - 1) / 2
  | j + 1 => if (k : ℝ) - 1 < selectedDefect k j then selectedStep k (selectedDefect k j)
      else selectedDefect k j

/-- The exact maximum coefficient in every active step; a stopped step
needs no further coefficient loss. -/
def selectedCoefficient (k : ℕ) (omega : ℝ) : ℕ → ℝ
  | 0 => k.factorial
  | j + 1 => if (k : ℝ) - 1 < selectedDefect k j then
      selectedCoefficient k omega j *
        stepCoefficient k (order k j) omega (selectedDefect k j) (selectedDefect k (j + 1))
      else selectedCoefficient k omega j

/-- The last rank-k boundary step preserves the same lower envelope. -/
theorem selectedStep_boundary_lower {k : ℕ} {delta : ℝ} (hk : 26 ≤ k)
    (hlower : (k : ℝ) - 1 ≤ delta) (hsmall : delta ≤ k) :
    delta * (1 - 2 / (k : ℝ)) ≤ selectedStep k delta := by
  have hkR : (26 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  have hd0 : 0 < delta := by linarith
  have hupper : delta ≤ (k : ℝ) * ((k : ℝ) - 1) / 2 := by nlinarith
  obtain ⟨hr4, _, _, _, hdepth, hroot⟩ := admissible_to_boundary hk hlower hupper
  have hs := (schedule_bounds (by omega : 0 < k) (by omega : 0 < rank k delta)
    hupper hdepth hroot 0).2.1
  have hr := rank_eq_degree (by omega : 0 < k) hd0 hsmall
  rw [hr] at hs
  have hcost : 0 ≤ (k : ℝ) ^ 2 - delta := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hs hcost
  have he : selectedStep k delta = delta - k +
      schedule k k (maximalDepth k k delta) delta 0 * ((k : ℝ) ^ 2 - delta) := by
    unfold selectedStep
    rw [hr]
    unfold nextDefect
    ring
  have hb : delta * (1 - 2 / (k : ℝ)) ≤ delta - k + ((k : ℝ) ^ 2 - delta) / (k + 1) := by
    field_simp
    have hp := mul_nonneg (show 0 ≤ delta - ((k : ℝ) - 1) by linarith)
      (show 0 ≤ (k : ℝ) + 2 by positivity)
    nlinarith
  rw [he]
  simp only [div_eq_mul_inv] at hm hb ⊢
  nlinarith only [hm, hb]

/-- At or below `k`, the actual next step reaches at most `k-1`. -/
theorem selectedStep_boundary_upper {k : ℕ} {delta : ℝ} (hk : 26 ≤ k)
    (hlower : (k : ℝ) - 1 ≤ delta) (hsmall : delta ≤ k) :
    selectedStep k delta ≤ (k : ℝ) - 1 := by
  have hkR : (26 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  have hd0 : 0 < delta := by linarith
  have hupper : delta ≤ (k : ℝ) * ((k : ℝ) - 1) / 2 := by nlinarith
  obtain ⟨hr4, _, _, _, hdepth, hroot⟩ := admissible_to_boundary hk hlower hupper
  have hs := (schedule_bounds (by omega : 0 < k) (by omega : 0 < rank k delta)
    hupper hdepth hroot 0).2.2
  have hr := rank_eq_degree (by omega : 0 < k) hd0 hsmall
  rw [hr] at hs
  have hcost : 0 ≤ (k : ℝ) ^ 2 - delta := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hs hcost
  have he : selectedStep k delta = delta - k +
      schedule k k (maximalDepth k k delta) delta 0 * ((k : ℝ) ^ 2 - delta) := by
    unfold selectedStep
    rw [hr]
    unfold nextDefect
    ring
  have hb : delta - k + ((k : ℝ) ^ 2 - delta) / k ≤ (k : ℝ) - 1 := by
    have hp := mul_nonneg (show 0 ≤ (k : ℝ) - delta by linarith) (show 0 ≤ (k : ℝ) - 1 by linarith)
    have hh : ((k : ℝ) ^ 2 - delta) / k ≤ ((k : ℝ) - 1) - (delta - k) :=
      (div_le_iff₀ hkpos).mpr (by nlinarith)
    linarith
  rw [he]
  simp only [div_eq_mul_inv] at hm hb ⊢
  nlinarith only [hm, hb]

/-- The chosen active step preserves the full nonnegative defect range,
including the required last step below `k`. -/
theorem selectedStep_bounds {k : ℕ} {delta : ℝ} (hk : 26 ≤ k)
    (hlower : (k : ℝ) - 1 ≤ delta) (hupper : delta ≤ (k : ℝ) * ((k : ℝ) - 1) / 2) :
    0 ≤ selectedStep k delta ∧ selectedStep k delta ≤ delta := by
  obtain ⟨hr4, _, _, _, hdepth, hroot⟩ := admissible_to_boundary hk hlower hupper
  have hb := schedule_bounds (by omega : 0 < k) (by omega : 0 < rank k delta)
    hupper hdepth hroot 0
  constructor
  · by_cases hd : (k : ℝ) ≤ delta
    · have ha : 0 ≤ (k : ℝ) ^ 2 + k + (rank k delta : ℝ) ^ 2 - rank k delta - 2 * delta := by
        nlinarith [depth_nonneg (rank k delta), Nat.cast_nonneg (α := ℝ) k]
      have hp := mul_nonneg hb.1.le ha
      unfold selectedStep nextDefect
      nlinarith
    · have hkR : (26 : ℝ) ≤ k := by exact_mod_cast hk
      have hp : 0 ≤ 1 - 2 / (k : ℝ) := by
        have hh : 2 / (k : ℝ) ≤ 1 := (div_le_one (by linarith : (0 : ℝ) < k)).mpr (by linarith)
        linarith
      exact (mul_nonneg (by linarith : 0 ≤ delta) hp).trans
        (selectedStep_boundary_lower hk hlower (by linarith))
  · exact nextDefect_le (by omega) (by omega) hupper hdepth hroot

/-- All defects are nonnegative and at most the initial diagonal defect. -/
theorem selectedDefect_bounds {k : ℕ} (hk : 26 ≤ k) (j : ℕ) :
    0 ≤ selectedDefect k j ∧ selectedDefect k j ≤ (k : ℝ) * ((k : ℝ) - 1) / 2 := by
  induction j with
  | zero => exact ⟨div_nonneg (depth_nonneg k) (by norm_num), le_rfl⟩
  | succ j ih =>
    rw [selectedDefect]
    split_ifs with hj
    · have hh := selectedStep_bounds hk hj.le ih.2
      exact ⟨hh.1, hh.2.trans ih.2⟩
    · exact ih

/-- No step increases the chosen defect, including after stopping. -/
theorem selectedDefect_antitone {k : ℕ} (hk : 26 ≤ k) : Antitone (selectedDefect k) := by
  apply antitone_nat_of_succ_le
  intro j
  rw [selectedDefect]
  split_ifs with hj
  · exact (selectedStep_bounds hk hj.le (selectedDefect_bounds hk j).2).2
  · exact le_rfl

/-- The literal coefficient stays positive throughout the selected iteration. -/
theorem selectedCoefficient_pos {k : ℕ} (hk : 0 < k) {omega : ℝ}
    (homega : 0 < omega) (j : ℕ) : 0 < selectedCoefficient k omega j := by
  induction j with
  | zero =>
    change (0 : ℝ) < k.factorial
    exact_mod_cast Nat.factorial_pos k
  | succ j ih =>
    rw [selectedCoefficient]
    split_ifs
    · exact mul_pos ih (stepCoefficient_pos hk homega)
    · exact ih

/-- Raising the moment order trivially preserves an already achieved
defect and coefficient. This is the stopped branch of the paper's argument. -/
theorem raise_moment_bound {k s P : ℕ} {C delta : ℝ} (hP : 1 ≤ P)
    (hsource : meanValue s k P ≤ C * (P : ℝ) ^ sourceExponent k s delta) :
    meanValue (s + k) k P ≤ C * (P : ℝ) ^ sourceExponent k (s + k) delta := by
  have hp : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
  have hm : meanValue (s + k) k P ≤ (P : ℝ) ^ (2 * k) * meanValue s k P := by
    simpa only [meanValue, Nat.add_sub_cancel_left, Fintype.card_fin] using
      VinogradovPowerSumRigidity.moment_le_of_order_le (Nat.le_add_right s k)
        (fun n : Fin P => monomialFrequency k (n.val + 1))
  calc
    _ ≤ (P : ℝ) ^ (2 * k) * (C * (P : ℝ) ^ sourceExponent k s delta) :=
      hm.trans (mul_le_mul_of_nonneg_left hsource (by positivity))
    _ = _ := by
      rw [← Real.rpow_natCast, mul_left_comm, ← Real.rpow_add hp]
      congr 2
      unfold sourceExponent
      push_cast
      ring

/-- The actual all-endpoint moment estimate with the concrete published
rank and maximal depth. No scalar-admissible schedule is assumed. The
short-prime supply is the remaining arithmetic premise. -/
theorem selected_moment_bound {k J : ℕ} {omega : ℝ}
    (hk : 26 ≤ k) (horder : J + 1 ≤ k ^ 2)
    (homega : 0 < omega) (homegaHalf : omega ≤ 1 / 2)
    (hsupply : ShortPrimeSupply k omega) :
    ∀ P : ℕ, 1 ≤ P → meanValue (order k J) k P ≤
      selectedCoefficient k omega J * (P : ℝ) ^ sourceExponent k (order k J) (selectedDefect k J) := by
  induction J with
  | zero =>
    intro P _hP
    have he : sourceExponent k (order k 0) (selectedDefect k 0) = k := by
      simp only [sourceExponent, order, zero_add, one_mul, selectedDefect]
      ring
    rw [he, Real.rpow_natCast]
    simpa only [selectedCoefficient, order, zero_add, one_mul, mul_one, mul_comm] using
      (VinogradovPowerSumRigidity.meanValue_le (r := k) (k := k) (N := P) le_rfl)
  | succ J ih =>
    have hsource := ih (by omega)
    intro P hP
    by_cases hj : (k : ℝ) - 1 < selectedDefect k J
    · obtain ⟨hr4, hr, _, hcap, hdepth, hroot⟩ :=
        admissible_to_boundary hk hj.le (selectedDefect_bounds hk J).2
      have hs : k ≤ order k J := Nat.le_mul_of_pos_left _ (by omega)
      have hsMax : order k J ≤ k ^ 3 := by
        have hh := Nat.mul_le_mul_right k (show J + 1 ≤ k ^ 2 by omega)
        simpa only [order, pow_succ] using hh
      have hh := all_endpoint_bound k (rank k (selectedDefect k J))
        (maximalDepth k (rank k (selectedDefect k J)) (selectedDefect k J))
        (order k J) hk hs hsMax (by omega) hr hcap
        (selectedCoefficient_pos (by omega) homega J) homega homegaHalf
        (selectedDefect_bounds hk J).2 hdepth hroot hsupply hsource P hP
      simpa only [order_succ, selectedCoefficient, selectedDefect, if_pos hj, selectedStep] using hh
    · simpa only [order_succ, selectedCoefficient, selectedDefect, if_neg hj] using
        raise_moment_bound hP (hsource P hP)

end
end RiemannGaussian.VinogradovFordSelectedIteration

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovFordPotential

/-!
# Iterating Ford's logarithmic potential

All quantities below come from the actual selected moment recurrence.
The reciprocal-defect sum is paid before summing the potential errors;
the published uniform allowance is `1.34/k`.
-/

namespace RiemannGaussian.VinogradovFordPotentialIteration
noncomputable section
open VinogradovFordSelectedIteration VinogradovFordLowerDefect
open VinogradovFordDefectRate VinogradovFordPotential
open scoped BigOperators

/-- The normalized defect of the selected moment sequence. -/
def normalized (k j : ℕ) : ℝ := selectedDefect k j / (k : ℝ) ^ 2

/-- Ford's principal normalized rate. -/
def beta (k : ℕ) : ℝ := 2 / (k : ℝ) - 32 / (21 * (k : ℝ) ^ 2)

/-- Ford's third-order correction coefficient. -/
def correction (k : ℕ) : ℝ := 16 / (7 * (k : ℝ) ^ 3)

/-- The uniform contraction used to pay the reciprocal-defect sum. -/
def alpha (k : ℕ) : ℝ := (6 / 7) * (beta k - k * correction k)

/-- The uniform numerator in the one-step potential error. -/
def errorWeight (k : ℕ) : ℝ := correction k * (1 + 8 / (5 * (k : ℝ)))

/-- The principal rate and correction have the signs used in the iteration. -/
theorem parameter_bounds {k : ℕ} (hk : 1000 ≤ k) :
    0 < correction k ∧ 0 < beta k - k * correction k ∧ beta k ≤ 2 / (k : ℝ) ∧ beta k < 1 := by
  have hkR : (1000 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  have hc : 0 < correction k := by unfold correction; positivity
  have he : beta k - k * correction k = (42 * (k : ℝ) - 80) / (21 * (k : ℝ) ^ 2) := by
    unfold beta correction
    field_simp
    ring
  have hb : beta k ≤ 2 / (k : ℝ) := by unfold beta; exact sub_le_self _ (by positivity)
  have hh : 2 / (k : ℝ) < 1 := (div_lt_one hkpos).mpr (by linarith)
  exact ⟨hc, by rw [he]; exact div_pos (by linarith) (by positivity), hb, hb.trans_lt hh⟩

/-- The contraction is strictly between zero and one. -/
theorem alpha_bounds {k : ℕ} (hk : 1000 ≤ k) : 0 < alpha k ∧ alpha k < 1 := by
  obtain ⟨hc, hb, _, hb1⟩ := parameter_bounds hk
  have hkc : 0 ≤ (k : ℝ) * correction k := mul_nonneg (Nat.cast_nonneg _) hc.le
  unfold alpha
  constructor
  · positivity
  · linarith

/-- The second-order potential gain recovers the full `2/k` rate. -/
theorem beta_quadratic_ge {k : ℕ} (hk : 1000 ≤ k) :
    2 / (k : ℝ) ≤ beta k + (2 / 5) * beta k ^ 2 := by
  have hkR : (1000 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  unfold beta
  field_simp
  have hp := mul_nonneg (show 0 ≤ (k : ℝ) by positivity) (show 0 ≤ (k : ℝ) - 32 by linarith)
  nlinarith

/-- The complete reciprocal-error budget has the paper's `1.34/k` constant. -/
theorem error_budget {k : ℕ} (hk : 1000 ≤ k) :
    errorWeight k * k / alpha k ≤ 67 / (50 * (k : ℝ)) := by
  have hkR : (1000 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  have hden : 0 < 84 * (k : ℝ) - 160 := by linarith
  have he : errorWeight k * k / alpha k =
      112 * (5 * (k : ℝ) + 8) / (5 * k * (84 * (k : ℝ) - 160)) := by
    unfold errorWeight alpha beta correction
    field_simp
    ring_nf
    field_simp [show -560 + (k : ℝ) * 294 ≠ 0 by linarith,
      show -160 + (k : ℝ) * 84 ≠ 0 by linarith]
    ring
  rw [he]
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 5 * k * (84 * (k : ℝ) - 160)) (by positivity)).mpr
  have hp := mul_nonneg (show 0 ≤ (k : ℝ) by positivity) (show 0 ≤ 140 * (k : ℝ) - 98400 by linarith)
  nlinarith

/-- Every normalized defect belongs to the positive potential domain. -/
theorem normalized_bounds {k : ℕ} (hk : 26 ≤ k) (j : ℕ) :
    0 < normalized k j ∧ normalized k j ≤ 1 / 2 := by
  have hkR : (26 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  constructor
  · exact div_pos (selectedDefect_pos hk j) (sq_pos_of_pos hkpos)
  · apply (div_le_iff₀ (sq_pos_of_pos hkpos)).mpr
    have hh := (selectedDefect_bounds hk j).2
    nlinarith

/-- The final rank-k step, including the already stopped case. -/
theorem small_succ {k j : ℕ} (hk : 26 ≤ k) (hsmall : selectedDefect k j ≤ k) :
    selectedDefect k (j + 1) ≤ (k : ℝ) - 1 := by
  rw [selectedDefect]
  split_ifs with hj
  · exact selectedStep_boundary_upper hk hj.le hsmall
  · linarith

/-- An endpoint still above `k-1` certifies that all preceding steps were
in the active range of Ford's quantitative recurrence. -/
theorem active_prefix {k J : ℕ} (hk : 26 ≤ k) (hfinal : (k : ℝ) - 1 < selectedDefect k J) :
    ∀ i < J, (k : ℝ) < selectedDefect k i := by
  intro i hi
  by_contra hh
  have hs := small_succ hk (le_of_not_gt hh)
  have hm := selectedDefect_antitone hk (show i + 1 ≤ J by omega)
  linarith

/-- An active normalized defect is larger than `1/k`. -/
theorem active_normalized {k j : ℕ} (hk : 26 ≤ k) (hj : (k : ℝ) < selectedDefect k j) :
    1 / (k : ℝ) < normalized k j := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  unfold normalized
  apply (lt_div_iff₀ (sq_pos_of_pos hkpos)).mpr
  have he : 1 / (k : ℝ) * (k : ℝ) ^ 2 = k := by field_simp
  rwa [he]

/-- The effective rate lies between the fixed contraction rate and beta. -/
theorem effective_rate_bounds {k j : ℕ} (hk : 1000 ≤ k) (hj : (k : ℝ) < selectedDefect k j) :
    beta k - k * correction k ≤ beta k - correction k / normalized k j ∧
      0 < beta k - correction k / normalized k j ∧
        beta k - correction k / normalized k j < 1 := by
  obtain ⟨hc, hb, _, hb1⟩ := parameter_bounds hk
  have hd := (normalized_bounds (by omega : 26 ≤ k) j).1
  have hlo := active_normalized (by omega : 26 ≤ k) hj
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hkd : 1 ≤ (k : ℝ) * normalized k j := by
    have hh := (div_lt_iff₀ hkpos).mp hlo
    nlinarith
  have hcorr : correction k / normalized k j ≤ k * correction k := by
    apply (div_le_iff₀ hd).mpr
    have hh := mul_le_mul_of_nonneg_left hkd hc.le
    nlinarith
  have hnonneg := div_nonneg hc.le hd.le
  exact ⟨by linarith, by linarith, by linarith⟩

/-- The checked defect rate is the literal potential comparison step. -/
theorem normalized_step_le {k j : ℕ} (hk : 1000 ≤ k) (hj : (k : ℝ) < selectedDefect k j) :
    normalized k (j + 1) ≤ comparisonStep (normalized k j)
      (beta k - correction k / normalized k j) := by
  have hh := selectedDefect_rate hk hj
  change normalized k (j + 1) ≤ _ at hh
  have he : correction k / normalized k j = 16 / (7 * normalized k j * (k : ℝ) ^ 3) := by
    unfold correction
    rw [div_div]
    congr 1
    ring
  unfold comparisonStep rateRatio beta
  rw [he]
  exact hh

/-- The selected normalized defects contract by the paper's uniform alpha. -/
theorem normalized_contraction {k j : ℕ} (hk : 1000 ≤ k) (hj : (k : ℝ) < selectedDefect k j) :
    normalized k (j + 1) ≤ (1 - alpha k) * normalized k j := by
  have hd := normalized_bounds (by omega : 26 ≤ k) j
  have he := effective_rate_bounds hk hj
  have hr := rateRatio_bounds hd.1.le hd.2
  have hp := mul_le_mul hr.1 he.1 (parameter_bounds hk).2.1.le (by linarith)
  have hs := normalized_step_le hk hj
  unfold alpha comparisonStep at *
  nlinarith [mul_nonneg hd.1.le (sub_nonneg.mpr hp)]

/-- The actual one-step potential inequality, including its signed quadratic gain. -/
theorem potential_step {k j : ℕ} (hk : 1000 ≤ k) (hj : (k : ℝ) < selectedDefect k j) :
    potential (normalized k (j + 1)) ≤ potential (normalized k j) -
      (beta k + (2 / 5) * beta k ^ 2) + errorWeight k / normalized k j := by
  have hd := normalized_bounds (by omega : 26 ≤ k) j
  have he := effective_rate_bounds hk hj
  have hs := potential_step_le hd.1 hd.2 (normalized_bounds (by omega : 26 ≤ k) (j + 1)).1
    he.2.1.le he.2.2 (normalized_step_le hk hj)
  have hbeta := (parameter_bounds hk).2.2.1
  have hc := (parameter_bounds hk).1.le
  have herror : correction k * (1 + (4 / 5) * beta k) / normalized k j ≤
      errorWeight k / normalized k j := by
    unfold errorWeight
    have hp : (4 / 5 : ℝ) * beta k ≤ 8 / (5 * (k : ℝ)) := by
      calc
        _ ≤ (4 / 5 : ℝ) * (2 / (k : ℝ)) := mul_le_mul_of_nonneg_left hbeta (by norm_num)
        _ = _ := by ring
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (add_le_add le_rfl hp) hc) hd.1.le
  have halgebra : -(beta k - correction k / normalized k j) -
      (2 / 5) * (beta k - correction k / normalized k j) ^ 2 =
        -(beta k + (2 / 5) * beta k ^ 2) +
          correction k * (1 + (4 / 5) * beta k) / normalized k j -
          (2 / 5) * (correction k / normalized k j) ^ 2 := by ring
  have hsq := sq_nonneg (correction k / normalized k j)
  linarith

/-- A finite reciprocal sum is paid by its last term under the proved
uniform contraction. -/
theorem reciprocal_sum_le {d : ℕ → ℝ} {a : ℝ} (ha : a ≤ 1)
    (hd : ∀ i, 0 < d i) (J : ℕ)
    (hstep : ∀ i < J, d (i + 1) ≤ (1 - a) * d i) :
    a * ∑ i ∈ Finset.range (J + 1), 1 / d i ≤ 1 / d J := by
  induction J with
  | zero =>
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    have hh := mul_nonneg (show 0 ≤ 1 - a by linarith) (one_div_nonneg.mpr (hd 0).le)
    nlinarith
  | succ J ih =>
    have hp := ih (fun i hi => hstep i (by omega))
    have hnext : 1 / d J ≤ (1 - a) / d (J + 1) :=
      (div_le_div_iff₀ (hd J) (hd (J + 1))).mpr (by simpa using hstep J (by omega))
    rw [Finset.sum_range_succ]
    simp only [div_eq_mul_inv] at hp hnext ⊢
    nlinarith only [hp, hnext]

/-- The whole finite accumulated error is bounded by `1.34/k`, independently
of the number of active steps. -/
theorem accumulated_error_le {k J : ℕ} (hk : 1000 ≤ k)
    (hactive : ∀ i < J, (k : ℝ) < selectedDefect k i) :
    errorWeight k * ∑ i ∈ Finset.range J, 1 / normalized k i ≤ 67 / (50 * (k : ℝ)) := by
  have ha := alpha_bounds hk
  have hE : 0 ≤ errorWeight k := by
    unfold errorWeight
    exact mul_nonneg (parameter_bounds hk).1.le (by positivity)
  cases J with
  | zero => simp only [Finset.sum_range_zero, mul_zero]; positivity
  | succ J =>
    have hs := reciprocal_sum_le ha.2.le (fun i => (normalized_bounds (by omega : 26 ≤ k) i).1) J
      (fun i hi => normalized_contraction hk (hactive i (by omega)))
    have hd := (normalized_bounds (by omega : 26 ≤ k) J).1
    have hlo := active_normalized (by omega : 26 ≤ k) (hactive J (by omega))
    have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hlast : 1 / normalized k J ≤ k := by
      apply (div_le_iff₀ hd).mpr
      have hh := (div_lt_iff₀ hkpos).mp hlo
      nlinarith
    have hsum : (∑ i ∈ Finset.range (J + 1), 1 / normalized k i) ≤ (k : ℝ) / alpha k := by
      apply (le_div_iff₀ ha.1).mpr
      nlinarith only [hs, hlast]
    have hm := mul_le_mul_of_nonneg_left hsum hE
    have he : errorWeight k * ((k : ℝ) / alpha k) = errorWeight k * k / alpha k := by ring
    rw [he] at hm
    exact hm.trans (error_budget hk)

/-- Telescoping the actual potential retains every inverse-defect error. -/
theorem potential_sum {k J : ℕ} (hk : 1000 ≤ k)
    (hactive : ∀ i < J, (k : ℝ) < selectedDefect k i) :
    potential (normalized k J) ≤ potential (normalized k 0) -
      (J : ℝ) * (beta k + (2 / 5) * beta k ^ 2) +
        errorWeight k * ∑ i ∈ Finset.range J, 1 / normalized k i := by
  induction J with
  | zero => simp only [Nat.cast_zero, zero_mul, sub_zero, Finset.sum_range_zero, mul_zero, add_zero, le_refl]
  | succ J ih =>
    have hp := ih (fun i hi => hactive i (by omega))
    have hs := potential_step hk (hactive J (by omega))
    rw [Finset.sum_range_succ]
    push_cast
    simp only [div_eq_mul_inv, one_mul] at hp hs ⊢
    nlinarith only [hp, hs]

/-- Ford's complete potential estimate before evaluating its endpoints. -/
theorem potential_cumulative {k J : ℕ} (hk : 1000 ≤ k)
    (hactive : ∀ i < J, (k : ℝ) < selectedDefect k i) :
    potential (normalized k J) ≤ potential (normalized k 0) -
      2 * (J : ℝ) / k + 67 / (50 * (k : ℝ)) := by
  have hs := potential_sum hk hactive
  have he := accumulated_error_le hk hactive
  have hb := mul_le_mul_of_nonneg_left (beta_quadratic_ge hk) (Nat.cast_nonneg (α := ℝ) J)
  simp only [div_eq_mul_inv, one_mul] at hs he hb ⊢
  nlinarith only [hs, he, hb]

end
end RiemannGaussian.VinogradovFordPotentialIteration

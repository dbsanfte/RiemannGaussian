/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaClippedEulerMean
import RiemannGaussian.ZetaAngularPhaseAllowance

/-!
# Complete phase families for the sharp left Euler mean

The actual clipped left means and their sharp allowances are summable for
every nonnegative summable phase family with the existing logarithmic
frequency moment. The exact signed mean sum is retained before bounding
it. The common vertical shift cost decreases with increasing frequency.
-/

namespace RiemannGaussian.ZetaClippedEulerFamily
noncomputable section
open ZetaClippedEulerMean ZetaAngularPhaseAllowance
open ZetaNearOneBudgetLimit ZetaNearOneLogProfile ZetaLogarithmicShiftAllowance
open DerivativePowerExponents

/-- The direct Euler logarithmic profile keeps the same two-logarithm
frequency bound as the original profile, without the eta loss. -/
theorem profile_mul_le (k : ℕ) {t ω : ℝ} (ht : 1 ≤ scale t) (hω : 1 ≤ ω) :
    ZetaEulerLogProfile.profile k (ω * t) ≤ ZetaEulerLogProfile.profile k t + 2 * Real.log ω := by
  have h := (allowance_mul_bounds k 1 ht hω).2
  unfold ZetaNearOneJensen.allowance at h
  rw [← ZetaEulerLogProfile.profile_add_gain k t, ← ZetaEulerLogProfile.profile_add_gain k (ω * t)] at h
  linarith

/-- At a fixed vertical scale, the shift cost decreases as a phase frequency grows. -/
theorem shiftCost_mul_le (k : ℕ) (t b : ℝ) {ω : ℝ} (hω : 1 ≤ ω) :
    shiftCost k (ω * t) b ≤ shiftCost k t b := by
  have hωp : 0 < ω := zero_lt_one.trans_le hω
  have hh : height t ≤ height (ω * t) := by
    simp only [height, abs_mul, abs_of_pos hωp]
    nlinarith [abs_nonneg t]
  have ht : 0 < height t := by linarith [two_le_height t]
  have hw : 0 < height (ω * t) := ht.trans_le hh
  have hl : 0 < Real.log (height t) := Real.log_pos (by linarith [two_le_height t])
  have hα : 0 ≤ alpha k := (alpha_pos k).le
  have hi := one_div_le_one_div_of_le hl (Real.log_le_log ht hh)
  simp only [one_div] at hi
  have hn := mul_le_mul_of_nonneg_right (add_le_add (le_refl (alpha k)) hi) (abs_nonneg b)
  unfold shiftCost
  exact (div_le_div_of_nonneg_right hn hw.le).trans
    (div_le_div_of_nonneg_left (by positivity) ht hh)

/-- The full sharp allowance costs at most twice the logarithmic frequency. -/
theorem allowance_mul_le (k : ℕ) (b : ℝ) {t ω : ℝ} (ht : 1 ≤ scale t) (hω : 1 ≤ ω) :
    ZetaClippedEulerMean.allowance k (ω * t) b ≤
      ZetaClippedEulerMean.allowance k t b + 2 * Real.log ω := by
  have hp := profile_mul_le k ht hω
  have hs := mul_le_mul_of_nonneg_left (shiftCost_mul_le k t b hω)
    (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
  unfold ZetaClippedEulerMean.allowance
  linarith

/-- The exact full signed sum of nonconstant left means. -/
def totalMean (k : ℕ) (M t b : ℝ) (a ω : ℕ → ℝ) : ℝ :=
  ∑' n, tail a n * ZetaClippedEulerMean.mean k M (ω n * t) b

/-- The complete frequency-dependent sharp left allowance. -/
def totalAllowance (k : ℕ) (t b : ℝ) (a ω : ℕ → ℝ) : ℝ :=
  ∑' n, tail a n * ZetaClippedEulerMean.allowance k (ω n * t) b

/-- The full actual allowance is summable using only the existing logarithmic
frequency moment; no first-frequency moment or finite support is required. -/
theorem summable_allowance {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hω : ∀ n, n ≠ 0 → 1 ≤ ω n) (hlog : Summable (fun n => tail a n * Real.log (ω n)))
    (k : ℕ) (b : ℝ) {t : ℝ} (ht : 1 ≤ scale t) :
    Summable (fun n => tail a n * ZetaClippedEulerMean.allowance k (ω n * t) b) := by
  apply (((tail_summable ha hs).mul_right (ZetaClippedEulerMean.allowance k t b)).add
    (hlog.mul_left 2)).of_norm_bounded
  intro n
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (tail_nonneg ha n) (ZetaClippedEulerMean.allowance_nonneg k _ b))]
  by_cases hn : n = 0
  · simp [tail, hn]
  · have h := mul_le_mul_of_nonneg_left (allowance_mul_le k b ht (hω n hn)) (tail_nonneg ha n)
    nlinarith only [h]

/-- At every fixed retained negative depth, the complete original signed
left means are genuinely summable for the same general phase family. -/
theorem summable_means {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hω : ∀ n, n ≠ 0 → 1 ≤ ω n) (hlog : Summable (fun n => tail a n * Real.log (ω n)))
    (k : ℕ) (hk : 1 ≤ k) {M : ℝ} (hM : 0 ≤ M) (b : ℝ) {t : ℝ} (ht : 1 ≤ scale t) :
    Summable (fun n => tail a n * ZetaClippedEulerMean.mean k M (ω n * t) b) := by
  apply ((summable_allowance ha hs hω hlog k b ht).add ((tail_summable ha hs).mul_right M)).of_norm_bounded
  intro n
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (tail_nonneg ha n)]
  have h := mul_le_mul_of_nonneg_left (abs_mean_le k hk hM (ω n * t) b) (tail_nonneg ha n)
  nlinarith only [h]

/-- The full signed mean sum lies below the complete sharp allowance sum. -/
theorem totalMean_le {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hω : ∀ n, n ≠ 0 → 1 ≤ ω n) (hlog : Summable (fun n => tail a n * Real.log (ω n)))
    (k : ℕ) (hk : 1 ≤ k) {M : ℝ} (hM : 0 ≤ M) (b : ℝ) {t : ℝ} (ht : 1 ≤ scale t) :
    totalMean k M t b a ω ≤ totalAllowance k t b a ω :=
  (summable_means ha hs hω hlog k hk hM b ht).tsum_le_tsum
    (fun n => mul_le_mul_of_nonneg_left (mean_le k hk hM (ω n * t) b) (tail_nonneg ha n))
    (summable_allowance ha hs hω hlog k b ht)

/-- Only the nonconstant mass and logarithmic frequency moment remain in
the explicit sharp left bound; the exact signed mean stays upstream. -/
theorem totalAllowance_le {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hω : ∀ n, n ≠ 0 → 1 ≤ ω n) (hlog : Summable (fun n => tail a n * Real.log (ω n)))
    (k : ℕ) (b : ℝ) {t : ℝ} (ht : 1 ≤ scale t) :
    totalAllowance k t b a ω ≤ mass a * ZetaClippedEulerMean.allowance k t b + 2 * frequencyCost a ω := by
  have hbase := (tail_summable ha hs).mul_right (ZetaClippedEulerMean.allowance k t b)
  have hsum := summable_allowance ha hs hω hlog k b ht
  have h := hsum.tsum_le_tsum (fun n => show
      tail a n * ZetaClippedEulerMean.allowance k (ω n * t) b ≤
      tail a n * ZetaClippedEulerMean.allowance k t b + 2 * (tail a n * Real.log (ω n)) from by
    by_cases hn : n = 0
    · simp [tail, hn]
    · have hh := mul_le_mul_of_nonneg_left (allowance_mul_le k b ht (hω n hn)) (tail_nonneg ha n)
      nlinarith only [hh]) (hbase.add (hlog.mul_left 2))
  simpa only [totalAllowance, mass, frequencyCost, hbase.tsum_add (hlog.mul_left 2),
    tsum_mul_right, tsum_mul_left] using h

end
end RiemannGaussian.ZetaClippedEulerFamily

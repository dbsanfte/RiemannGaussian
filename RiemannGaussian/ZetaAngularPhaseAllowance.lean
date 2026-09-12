/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaLogLogBudget
import RiemannGaussian.ZetaPhaseArithmetic

/-!
# The complete angular allowance for general phase families

Every summable nonnegative family with a finite logarithmic frequency
moment has a genuinely summable actual boundary allowance. Its entire
frequency-dependent correction is bounded by twice that moment, uniformly
in the derivative order and Euler-side center. Infinite support is allowed.
-/

namespace RiemannGaussian.ZetaAngularPhaseAllowance
noncomputable section
open Filter ZetaNearOneBudgetLimit ZetaNearOneLogProfile ZetaNearOneJensen
open DerivativePowerExponents DerivativeOrderComparison
open scoped Topology

/-- The nonconstant coefficients, with the real-axis channel retained
separately at index zero. -/
def tail (a : ℕ → ℝ) (n : ℕ) : ℝ := if n = 0 then 0 else a n

/-- The total nonconstant mass, without restricting the support. -/
def mass (a : ℕ → ℝ) : ℝ := ∑' n, tail a n

/-- The full logarithmic frequency cost of the nonconstant channels. -/
def frequencyCost (a ω : ℕ → ℝ) : ℝ := ∑' n, tail a n * Real.log (ω n)

/-- The complete actual analytic allowance at every phase height. -/
def totalAllowance (k : ℕ) (x t : ℝ) (a ω : ℕ → ℝ) : ℝ :=
  ∑' n, tail a n * allowance k x (ω n * t)

/-- Removing the constant channel preserves nonnegativity. -/
theorem tail_nonneg {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (n : ℕ) : 0 ≤ tail a n := by
  unfold tail
  split_ifs
  · exact le_refl 0
  · exact ha n

/-- Removing one coefficient preserves summability for every
nonnegative family, including infinite support. -/
theorem tail_summable {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a) :
    Summable (tail a) := by
  apply hs.of_norm_bounded
  intro n
  rw [Real.norm_eq_abs, abs_of_nonneg (tail_nonneg ha n)]
  by_cases hn : n = 0 <;> simp [tail, hn, ha]

/-- Enlarging a frequency costs at most its logarithm at the first
logarithmic height, with the common height retained on both sides. -/
theorem scale_mul_bounds {ω : ℝ} (hω : 1 ≤ ω) (t : ℝ) :
    scale t ≤ scale (ω * t) ∧ scale (ω * t) ≤ scale t + Real.log ω := by
  have hp : 0 < ω := zero_lt_one.trans_le hω
  have hlo : height t ≤ height (ω * t) := by
    simp only [height, abs_mul, abs_of_pos hp]
    nlinarith [abs_nonneg t]
  have hhi : height (ω * t) ≤ ω * height t := by
    simp only [height, abs_mul, abs_of_pos hp]
    nlinarith
  refine ⟨Real.log_le_log (by linarith [two_le_height t]) hlo, ?_⟩
  have h := Real.log_le_log (by linarith [two_le_height (ω * t)]) hhi
  rw [Real.log_mul hp.ne' (by linarith [two_le_height t] : height t ≠ 0)] at h
  simpa only [scale, add_comm] using h

/-- The entire frequency cost is bounded independently of the order
and center: both logarithmic height terms are included. -/
theorem allowance_mul_bounds (k : ℕ) (x : ℝ) {t ω : ℝ}
    (ht : 1 ≤ scale t) (hω : 1 ≤ ω) :
    allowance k x t ≤ allowance k x (ω * t) ∧
      allowance k x (ω * t) ≤ allowance k x t + 2 * Real.log ω := by
  have hb := scale_mul_bounds hω t
  have hl := Real.log_nonneg hω
  have hloglo := Real.log_le_log (scale_pos t) hb.1
  have hd : scale (ω * t) / scale t - 1 ≤ Real.log ω := by
    apply sub_le_iff_le_add.mpr
    apply (div_le_iff₀ (scale_pos t)).mpr
    nlinarith
  have hloghi := Real.log_le_sub_one_of_pos (div_pos (scale_pos (ω * t)) (scale_pos t))
  rw [Real.log_div (scale_pos (ω * t)).ne' (scale_pos t).ne'] at hloghi
  have hαlo := mul_le_mul_of_nonneg_left hb.1 (alpha_pos k).le
  have hαhi := mul_le_mul_of_nonneg_left hb.2 (alpha_pos k).le
  have hα := alpha_le_half k
  dsimp only [scale] at hb hd hloglo hloghi hαlo hαhi ht
  constructor <;> dsimp only [allowance, profile] <;> nlinarith

/-- The full sum of actual allowances is summable under a finite
logarithmic frequency moment; no finite support is required. -/
theorem summable_allowance {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hω : ∀ n, n ≠ 0 → 1 ≤ ω n)
    (hlog : Summable (fun n ↦ tail a n * Real.log (ω n)))
    (k : ℕ) {x t : ℝ} (hx : 0 < x) (ht : 1 ≤ scale t) :
    Summable (fun n ↦ tail a n * allowance k x (ω n * t)) := by
  apply (((tail_summable ha hs).mul_right (allowance k x t)).add
    (hlog.mul_left 2)).of_norm_bounded
  intro n
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (tail_nonneg ha n) (allowance_nonneg k _ hx))]
  by_cases hn : n = 0
  · simp [tail, hn]
  · have hb := mul_le_mul_of_nonneg_left
      (allowance_mul_bounds k x ht (hω n hn)).2 (tail_nonneg ha n)
    nlinarith only [hb]

/-- All frequencies share the same leading allowance; the complete
remaining cost is at most twice the logarithmic frequency moment. -/
theorem totalAllowance_bounds {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hω : ∀ n, n ≠ 0 → 1 ≤ ω n)
    (hlog : Summable (fun n ↦ tail a n * Real.log (ω n)))
    (k : ℕ) {x t : ℝ} (hx : 0 < x) (ht : 1 ≤ scale t) :
    mass a * allowance k x t ≤ totalAllowance k x t a ω ∧
      totalAllowance k x t a ω ≤ mass a * allowance k x t + 2 * frequencyCost a ω := by
  have hbase := (tail_summable ha hs).mul_right (allowance k x t)
  have hsum := summable_allowance ha hs hω hlog k hx ht
  have hlo := hbase.tsum_le_tsum (fun n ↦ show
      tail a n * allowance k x t ≤ tail a n * allowance k x (ω n * t) from by
    by_cases hn : n = 0
    · simp [tail, hn]
    · exact mul_le_mul_of_nonneg_left
        (allowance_mul_bounds k x ht (hω n hn)).1 (tail_nonneg ha n)) hsum
  have hhi := hsum.tsum_le_tsum (fun n ↦ show
      tail a n * allowance k x (ω n * t) ≤
        tail a n * allowance k x t + 2 * (tail a n * Real.log (ω n)) from by
    by_cases hn : n = 0
    · simp [tail, hn]
    · have h := mul_le_mul_of_nonneg_left
        (allowance_mul_bounds k x ht (hω n hn)).2 (tail_nonneg ha n)
      nlinarith only [h]) (hbase.add (hlog.mul_left 2))
  simpa only [totalAllowance, mass, frequencyCost, hbase.tsum_add (hlog.mul_left 2),
    tsum_mul_right, tsum_mul_left] using And.intro hlo hhi

end
end RiemannGaussian.ZetaAngularPhaseAllowance

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovGaussianSpacing
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Summing the retained cubic decay over all dyadic scales

A cubic tail is bounded by an integrable Gaussian after rescaling by
log(t)^(2/3). The existing complete Gaussian sum pays every dyadic block
with a constant independent of the number of blocks or the strip index.
-/

namespace RiemannGaussian.VinogradovCubicSummation
noncomputable section

/-- Cubic decay is dominated by a Gaussian with one fixed exponential
factor, uniformly on the nonnegative half-line. -/
theorem cubic_ge_square_sub_one {x : ℝ} (hx : 0 ≤ x) : x ^ 2 - 1 ≤ x ^ 3 := by
  by_cases h : 1 ≤ x
  · nlinarith [mul_nonneg (sq_nonneg x) (show 0 ≤ x - 1 by linarith)]
  · have hx1 : x ≤ 1 := le_of_not_ge h
    nlinarith [pow_nonneg hx 3]

/-- Every finite dyadic cubic tail costs at most 1024 times the
two-thirds power of the height logarithm. -/
theorem sum_le {L : ℝ} (hL : 1 ≤ L) (J : ℕ) :
    (∑ j ∈ Finset.range J,
      Real.exp (-((j : ℝ) * Real.log 2) ^ 3 / (2097152 * L ^ 2))) ≤
        1024 * L ^ (2 / 3 : ℝ) := by
  have hLpos : 0 < L := by linarith
  let w := 256 * L ^ (2 / 3 : ℝ)
  have hw : 0 < w := by dsimp [w]; positivity
  have hLpow : (L ^ (2 / 3 : ℝ)) ^ (3 : ℕ) = L ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hLpos.le]
    norm_num
  have hw3 : w ^ 3 = 16777216 * L ^ 2 := by
    dsimp only [w]
    rw [mul_pow, hLpow]
    norm_num
  let c := 1 / w ^ 2
  have hc : 0 < c := by dsimp [c]; positivity
  have hterm (j : ℕ) :
      Real.exp (-((j : ℝ) * Real.log 2) ^ 3 / (2097152 * L ^ 2)) ≤
        Real.exp 1 * Real.exp (-c * (j : ℝ) ^ 2) := by
    have hj : (0 : ℝ) ≤ j := by positivity
    have hlog : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hp := pow_le_pow_left₀ (show 0 ≤ (j : ℝ) / 2 by positivity)
      (show (j : ℝ) / 2 ≤ j * Real.log 2 by nlinarith) 3
    have hx3 : ((j : ℝ) / w) ^ 3 ≤ ((j : ℝ) * Real.log 2) ^ 3 / (2097152 * L ^ 2) := by
      rw [div_pow, hw3]
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith [mul_nonneg (show 0 ≤ ((j : ℝ) * Real.log 2) ^ 3 - ((j : ℝ) / 2) ^ 3 by linarith)
        (sq_nonneg L)]
    have hsq := cubic_ge_square_sub_one (div_nonneg hj hw.le)
    have heq : ((j : ℝ) / w) ^ 2 = c * (j : ℝ) ^ 2 := by dsimp [c]; ring
    rw [heq] at hsq
    rw [← Real.exp_add]
    rw [neg_div]
    exact Real.exp_le_exp.mpr (by linarith)
  have hsum := (VinogradovGaussianSpacing.summable_gaussian_int hc)
  have hnat : Summable (fun j : ℕ => Real.exp (-c * (j : ℝ) ^ 2)) := by
    simpa only [Function.comp_def, Int.cast_natCast] using hsum.comp_injective
      (show Function.Injective (fun n : ℕ => (n : ℤ)) from fun _ _ h => by
        dsimp only at h
        exact_mod_cast h)
  have hs := hnat.sum_le_tsum (Finset.range J) (fun _ _ => (Real.exp_pos _).le)
  have hg := VinogradovGaussianSpacing.nat_gaussian_sum_le hc
  have hroot : Real.sqrt (Real.pi / c) ≤ 2 * w := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity, ?_⟩
    dsimp only [c]
    rw [div_div_eq_mul_div, div_one]
    nlinarith [mul_nonneg (show 0 ≤ 4 - Real.pi by linarith [Real.pi_lt_four]) (sq_nonneg w)]
  have hfinite : (∑ j ∈ Finset.range J, Real.exp (-c * (j : ℝ) ^ 2)) ≤ 1 + w := by
    linarith
  have hnonneg : 0 ≤ ∑ j ∈ Finset.range J, Real.exp (-c * (j : ℝ) ^ 2) :=
    Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le)
  have hwidth : 1 ≤ L ^ (2 / 3 : ℝ) := Real.one_le_rpow hL (by norm_num)
  calc
    _ ≤ ∑ j ∈ Finset.range J, Real.exp 1 * Real.exp (-c * (j : ℝ) ^ 2) :=
      Finset.sum_le_sum (fun j _ => hterm j)
    _ = Real.exp 1 * ∑ j ∈ Finset.range J, Real.exp (-c * (j : ℝ) ^ 2) := by
      rw [Finset.mul_sum]
    _ ≤ 3 * (1 + w) := mul_le_mul Real.exp_one_lt_three.le hfinite hnonneg (by norm_num)
    _ ≤ _ := by dsimp only [w]; linarith

end
end RiemannGaussian.VinogradovCubicSummation

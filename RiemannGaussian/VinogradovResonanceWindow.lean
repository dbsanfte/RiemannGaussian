/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovResonanceScaling

/-!
# The unwrapped degree window of the actual logarithmic phase

At t=M^(2k), z=M^4, every degree q>2k/3 stays within half a period once
M pays the tuple order. Its Gaussian coordinate costs M^(4q-2k), rather
than the full M^(2q), with explicit constants. Every other coordinate is
retained in the downstream full resonance product.
-/

namespace RiemannGaussian.VinogradovResonanceWindow
noncomputable section
open scoped BigOperators
open VinogradovGaussianBounds VinogradovGaussianKernel
open VinogradovExplicitKorobov VinogradovResonanceScaling

/-- The exact phase range of the actual monomial difference interval at power-related endpoints. -/
theorem power_phase_range_identity (k s : ℕ) {M : ℝ} (hM : 0 < M) (j : Fin k) :
    |VinogradovKorobovMoment.phaseCoefficients k (M ^ (2 * k)) (M ^ 4) j| *
      ((s : ℝ) * M ^ (j.val + 1)) =
      ((s : ℝ) / (2 * Real.pi * (j.val + 1))) *
        (M ^ (2 * k) / M ^ (3 * (j.val + 1))) := by
  rw [abs_phaseCoefficients k _ (by positivity), abs_of_pos (pow_pos hM _)]
  have he : (M ^ 4) ^ (j.val + 1) = M ^ (j.val + 1) * M ^ (3 * (j.val + 1)) := by
    rw [← pow_add, ← pow_mul]
    congr 1
    omega
  rw [he]
  field_simp

/-- Every degree above the exact two-thirds transition stays unwrapped once the endpoint pays the tuple order. -/
theorem power_phase_unwrapped (k s : ℕ) {M : ℝ} (hM : 1 ≤ M) (hsM : (s : ℝ) ≤ M)
    (j : Fin k) (hwindow : 2 * k < 3 * (j.val + 1)) :
    |VinogradovKorobovMoment.phaseCoefficients k (M ^ (2 * k)) (M ^ 4) j| *
      ((s : ℝ) * M ^ (j.val + 1)) ≤ 1 / 2 := by
  have hMpos : 0 < M := zero_lt_one.trans_le hM
  rw [power_phase_range_identity k s hMpos j]
  have hratio : M ^ (2 * k) / M ^ (3 * (j.val + 1)) ≤ 1 / M := by
    apply (div_le_div_iff₀ (pow_pos hMpos _) hMpos).mpr
    simpa only [one_mul, ← pow_succ] using
      pow_le_pow_right₀ hM (show 2 * k + 1 ≤ 3 * (j.val + 1) by omega)
  have hq : (1 : ℝ) ≤ (j.val : ℝ) + 1 := by linarith only [Nat.cast_nonneg (α := ℝ) j.val]
  have hpiq : 1 ≤ Real.pi * ((j.val : ℝ) + 1) :=
    one_le_mul_of_one_le_of_one_le (by linarith only [Real.pi_gt_three]) hq
  calc
    _ ≤ ((s : ℝ) / (2 * Real.pi * (j.val + 1))) * (1 / M) :=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = ((s : ℝ) / M) / (2 * Real.pi * (j.val + 1)) := by ring
    _ ≤ 1 / (2 * Real.pi * (j.val + 1)) :=
      div_le_div_of_nonneg_right ((div_le_one hMpos).mpr hsM) (by positivity)
    _ ≤ _ := one_div_le_one_div_of_le (by norm_num) (by nlinarith only [hpiq])

/-- The actual phase spacing is nonzero at every positive power-related endpoint. -/
theorem power_phase_nonzero (k : ℕ) {M : ℝ} (hM : 0 < M) (j : Fin k) :
    VinogradovKorobovMoment.phaseCoefficients k (M ^ (2 * k)) (M ^ 4) j ≠ 0 := by
  apply abs_pos.mp
  rw [abs_phaseCoefficients k _ (by positivity), abs_of_pos (pow_pos hM _)]
  positivity

/-- Each eligible high degree has an explicit power saving relative to its full two-family support cost. -/
theorem selected_coordinate_power_le (k r : ℕ) (hr : 0 < r) {M : ℝ} (hM : 1 ≤ M)
    (j : Fin k) (hwindow : 2 * k ≤ 3 * (j.val + 1)) :
    (2 / ((reciprocalScale r M (j.val + 1)) ^ (1 / 2 : ℝ) *
      (1 - Real.exp (-Real.pi / reciprocalScale r M (j.val + 1))))) *
      (1 + Real.sqrt (reciprocalScale r M (j.val + 1)) /
        |VinogradovKorobovMoment.phaseCoefficients k (M ^ (2 * k)) (M ^ 4) j|) ≤
    ((2 * (r : ℝ) / (1 - Real.exp (-Real.pi))) *
      (1 + 2 * Real.pi * (j.val + 1) / (r : ℝ))) * M ^ (4 * (j.val + 1) - 2 * k) := by
  have hMpos : 0 < M := zero_lt_one.trans_le hM
  have hpdiv : M ^ (3 * (j.val + 1)) / M ^ (2 * k) = M ^ (3 * (j.val + 1) - 2 * k) := by
    rw [div_eq_mul_inv, ← pow_sub₀ M hMpos.ne' hwindow]
  rw [power_phase_width_identity k r hr hMpos j, hpdiv]
  have hden : 0 < 1 - Real.exp (-Real.pi) := by
    simpa using tail_denominator_pos (a := 1) zero_lt_one
  have hwidth : 1 + (2 * Real.pi * (j.val + 1) / (r : ℝ)) * M ^ (3 * (j.val + 1) - 2 * k) ≤
      (1 + 2 * Real.pi * (j.val + 1) / (r : ℝ)) * M ^ (3 * (j.val + 1) - 2 * k) := by
    have hp := one_le_pow₀ (n := 3 * (j.val + 1) - 2 * k) hM
    nlinarith only [hp]
  calc
    _ ≤ ((2 * (r : ℝ) / (1 - Real.exp (-Real.pi))) * M ^ (j.val + 1)) *
        ((1 + 2 * Real.pi * (j.val + 1) / (r : ℝ)) * M ^ (3 * (j.val + 1) - 2 * k)) :=
      mul_le_mul (reciprocal_prefactor_le hr hM (j.val + 1)) hwidth
        (by positivity) (by positivity)
    _ = _ := by
      have he : j.val + 1 + (3 * (j.val + 1) - 2 * k) = 4 * (j.val + 1) - 2 * k := by omega
      calc
        _ = ((2 * (r : ℝ) / (1 - Real.exp (-Real.pi))) *
          (1 + 2 * Real.pi * (j.val + 1) / (r : ℝ))) *
          (M ^ (j.val + 1) * M ^ (3 * (j.val + 1) - 2 * k)) := by ring
        _ = _ := by rw [← pow_add, he]

end
end RiemannGaussian.VinogradovResonanceWindow

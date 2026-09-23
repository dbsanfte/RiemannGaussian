/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovNarrowGaussian

/-!
# The complete Gaussian cost at variable actual moment order

Every order between k and 8k^2 retains the same paid rectangular
resonance envelope. This permits the shorter proved moment iterations
to enter the original polynomial product without hiding a new constant.
-/

namespace RiemannGaussian.VinogradovVariableGaussian
noncomputable section
open VinogradovGaussianCost (scalar_prefactor_le half_le_tail_denominator)

/-- The coordinate cost is uniform over the whole quadratic range of
actual moment orders. -/
theorem coordinate_constant_le (k : ℕ) (hk : 12 ≤ k) (r : ℕ)
    (hkr : k ≤ r) (hrk : r ≤ 8 * k ^ 2) :
    (4 : ℝ) ^ k * ((2 * (r : ℝ) / (1 - Real.exp (-Real.pi))) *
      (2 * (r : ℝ) + 2 + 2 * Real.pi * (k : ℝ) / (r : ℝ))) ≤ (2 : ℝ) ^ (7 * k) := by
  have hr : 1 ≤ r := by omega
  have hb := scalar_prefactor_le hkr hr
  have hrk' : (r : ℝ) ≤ 8 * (k : ℝ) ^ 2 := by exact_mod_cast hrk
  have hs : (r : ℝ) ^ 2 ≤ 64 * (k : ℝ) ^ 4 := by
    have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ r) hrk' 2
    nlinarith only [h]
  have hkpow : (k : ℝ) ≤ (2 : ℝ) ^ k := by exact_mod_cast (show k < 2 ^ k from Nat.lt_two_pow_self).le
  have hsmall : (3072 : ℝ) ≤ (2 : ℝ) ^ k := by
    apply le_trans (show (3072 : ℝ) ≤ (2 : ℝ) ^ 12 by norm_num)
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hkp := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) k) hkpow 4
  calc
    _ ≤ (4 : ℝ) ^ k * (3072 * (k : ℝ) ^ 4) := by
      apply mul_le_mul_of_nonneg_left (hb.trans _) (by positivity)
      nlinarith only [hs]
    _ ≤ (4 : ℝ) ^ k * ((2 : ℝ) ^ k * ((2 : ℝ) ^ k) ^ 4) := by gcongr
    _ = _ := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
      congr 1
      omega

/-- The entire Gaussian cost includes the original quartered support
exponential and all translated tails. -/
theorem complete_gaussian_constant_le (k : ℕ) (hk : 12 ≤ k) (r : ℕ)
    (hkr : k ≤ r) (hrk : r ≤ 8 * k ^ 2) :
    Real.exp ((k : ℝ) * Real.pi / 4) *
      ((4 : ℝ) ^ k * ((2 * (r : ℝ) / (1 - Real.exp (-Real.pi))) *
        (2 * (r : ℝ) + 2 + 2 * Real.pi * (k : ℝ) / (r : ℝ)))) ^ k ≤
      (2 : ℝ) ^ (9 * k ^ 2) := by
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have he : Real.exp ((k : ℝ) * Real.pi / 4) ≤ (2 : ℝ) ^ (2 * k) := by
    calc
      _ ≤ Real.exp (k : ℝ) := Real.exp_le_exp.mpr (by
        have hp := mul_le_mul_of_nonneg_right Real.pi_lt_four.le hk0
        linarith only [hp])
      _ = Real.exp 1 ^ k := by simpa only [mul_one] using Real.exp_nat_mul 1 k
      _ ≤ (4 : ℝ) ^ k := pow_le_pow_left₀ (Real.exp_pos _).le
        (Real.exp_one_lt_three.le.trans (by norm_num)) _
      _ = _ := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
  have hc := coordinate_constant_le k hk r hkr hrk
  have hden : 0 < 1 - Real.exp (-Real.pi) := by
    have h := half_le_tail_denominator
    linarith only [h]
  calc
    _ ≤ (2 : ℝ) ^ (2 * k) * ((2 : ℝ) ^ (7 * k)) ^ k :=
      mul_le_mul he (pow_le_pow_left₀ (by positivity) hc k) (by positivity) (by positivity)
    _ = (2 : ℝ) ^ (2 * k + 7 * k * k) := by rw [← pow_mul, ← pow_add]
    _ ≤ _ := by
      apply pow_le_pow_right₀ (by norm_num)
      nlinarith only [hk]

open VinogradovGaussianBounds VinogradovGaussianKernel VinogradovIntervalResonance
open VinogradovResonanceScaling VinogradovResonanceWindow VinogradovResonancePower
open VinogradovRectangleResonance VinogradovPhaseRectangle

/-- The actual full rectangular resonance has its evaluated coefficient
at each admissible moment order, before taking the genuine moment root. -/
theorem actual_gaussian_resonance_le (k : ℕ) (hk : 12 ≤ k) (r : ℕ)
    (hkr : k ≤ r) (hrk : r ≤ 8 * k ^ 2)
    (M : ℕ) (hM : 1 ≤ M) (hrM : r ≤ M) (t z : ℝ)
    (htlo : (M : ℝ) ^ (2 * k - 2) ≤ t) (hthi : t ≤ (M : ℝ) ^ (2 * k))
    (hzlo : (M : ℝ) ^ 4 ≤ z) (hzhi : z ≤ 4 * (M : ℝ) ^ 4)
    (B : Finset ℕ) (hB : ∀ b ∈ B, b ≤ M) :
    Real.exp ((k : ℝ) * Real.pi / 4) *
      resonanceEnvelope r (fun j => reciprocalScale r M (j.val + 1))
        (VinogradovKorobovMoment.phaseCoefficients k t z)
        (fun b : B => VinogradovMeanValue.monomialFrequency k b.val) ≤
      (2 : ℝ) ^ (9 * k ^ 2) * (M : ℝ) ^ (k * (k + 1) - rectangleSaving k) := by
  have hr : 0 < r := by omega
  have h := actual_resonance_le_explicit k r r hr M hM hrM t z htlo hthi hzlo hzhi B hB
  have hscaled := mul_le_mul_of_nonneg_left h (Real.exp_pos ((k : ℝ) * Real.pi / 4)).le
  apply hscaled.trans
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (complete_gaussian_constant_le k hk r hkr hrk) (by positivity)

end
end RiemannGaussian.VinogradovVariableGaussian

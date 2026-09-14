/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovRemainderScaling

/-!
# Exact normalization of the congruencing scales

Retain the full source normalization at an arbitrary real moment exponent.
Its exact logarithmic identity makes the congruence powers and two higher
factors cancel to the exponent defect times the difference of scales.
Every intermediate level has its own exact additional fine-residue factor.
These positive real identities are independent of a moment estimate; their
application to actual signed moments is in `VinogradovNormalizedIteration`.
-/

namespace RiemannGaussian.VinogradovCongruencingScaling
noncomputable section

/-- The full positive source normalization at an explicit real moment exponent. -/
def momentScale (x P k u a b lam : ℝ) : ℝ :=
  (x / P ^ a) ^ (lam - 2 * k * u) * (x / P ^ b) ^ (2 * k * u)

/-- All source-scale factors and congruence powers cancel exactly to the moment-exponent defect. -/
theorem congruencing_scale_identity {x P k u a b lam : ℝ}
    (hx : 0 < x) (hP : 0 < P) (hu : u ≠ 0) :
    P ^ ((a + b) * (k * (k - 1) / 2) + k * (k * b - a)) *
      (x / P ^ b) ^ (lam * (1 - 1 / u)) *
      momentScale x P k u b (k * b) lam ^ (1 / u) =
    momentScale x P k u a b lam *
      P ^ (-(lam - 2 * k * (u + 1) + k * (k + 1) / 2) * (b - a)) := by
  unfold momentScale
  rw [Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_mul (by positivity), ← Real.rpow_mul (by positivity)]
  simp_rw [VinogradovRemainderScaling.quotient_power_exp hx hP]
  simp only [Real.rpow_def_of_pos hP, ← Real.exp_add]
  congr 1
  field_simp
  ring

/-- Every intermediate conditioned scale retains its exact additional fine-residue saving. -/
theorem intermediate_scale_identity {x P : ℝ} (hx : 0 < x) (hP : 0 < P)
    (k u b c h lam : ℝ) :
    momentScale x P k u b (c + h) lam =
      momentScale x P k u b c lam * P ^ (-2 * k * u * h) := by
  unfold momentScale
  simp_rw [VinogradovRemainderScaling.quotient_power_exp hx hP]
  simp only [Real.rpow_def_of_pos hP, ← Real.exp_add]
  congr 1
  ring

/-- The source normalization is strictly positive on the original positive scale domain. -/
theorem momentScale_pos {x P : ℝ} (hx : 0 < x) (hP : 0 < P) (k u a b lam : ℝ) :
    0 < momentScale x P k u a b lam := by
  unfold momentScale
  positivity

/-- The elementary exponent has exactly the previously proved source normalization. -/
theorem elementary_scale (p k a b X u : ℕ) :
    momentScale X p k u a b (((k * (2 * u + 1) : ℕ) : ℝ)) =
      ((X : ℝ) / (p : ℝ) ^ a) ^ k * ((X : ℝ) / (p : ℝ) ^ b) ^ (2 * (k * u)) := by
  unfold momentScale
  have he : ((k * (2 * u + 1) : ℕ) : ℝ) - 2 * (k : ℝ) * u = k := by push_cast; ring
  rw [he]
  simp only [← Real.rpow_natCast, Nat.cast_mul, Nat.cast_ofNat, mul_assoc]

/-- For the actual iteration range, the geometric exponent remains at least seven quarters of the tail order. -/
theorem intermediate_exponent_le {k u : ℝ} (hk : 2 ≤ k) (hu : k ≤ u) :
    (7 / 4 : ℝ) * k * u ≤ 2 * k * u - k + 1 := by
  have he := mul_nonneg (show 0 ≤ k by linarith) (show 0 ≤ u - k by linarith)
  nlinarith [sq_nonneg (k - 2)]

end
end RiemannGaussian.VinogradovCongruencingScaling

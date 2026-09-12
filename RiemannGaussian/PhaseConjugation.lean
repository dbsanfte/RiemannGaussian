/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.PhaseIncrementInverse

/-!
# Exact conjugation of finite phase sums

Reversing a real phase conjugates its rotation. Arbitrary complex
amplitudes must be conjugated as well; the full identity precedes its
norm consequence. In particular, either alternating derivative orientation
of a logarithmic phase has exactly the original finite-sum norm.
-/

namespace RiemannGaussian.PhaseConjugation
noncomputable section
open PhaseIncrementInverse
open scoped Classical

/-- Phase reversal is exact complex conjugation, preserving both
components rather than merely the norm. -/
theorem rotation_neg (x : ℝ) :
    rotation (-x) = starRingEnd ℂ (rotation x) := by
  simp only [PhaseIncrementInverse.rotation, ← Complex.exp_conj,
    map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg]
  congr 1
  ring

/-- The complete weighted sum conjugates exactly when both its complex
amplitudes and its real phases are transformed. -/
theorem weighted_sum_conj {ι : Type*} (S : Finset ι) (w : ι → ℂ) (φ : ι → ℝ) :
    (∑ n ∈ S, starRingEnd ℂ (w n) * rotation (-φ n)) =
      starRingEnd ℂ (∑ n ∈ S, w n * rotation (φ n)) := by
  simp only [rotation_neg, map_sum, map_mul]

/-- Reversing all phases preserves the norm of the original unweighted
finite sum, with no alteration to its index set. -/
theorem norm_sum_neg {ι : Type*} (S : Finset ι) (φ : ι → ℝ) :
    ‖∑ n ∈ S, rotation (-φ n)‖ = ‖∑ n ∈ S, rotation (φ n)‖ := by
  simp only [rotation_neg, ← map_sum, Complex.norm_conj]

/-- Every alternating derivative orientation preserves the norm of
the original finite sum. -/
theorem norm_sum_neg_one_pow {ι : Type*} (S : Finset ι) (φ : ι → ℝ) (k : ℕ) :
    ‖∑ n ∈ S, rotation ((-1 : ℝ) ^ k * φ n)‖ = ‖∑ n ∈ S, rotation (φ n)‖ := by
  induction k with
  | zero => simp only [pow_zero, one_mul]
  | succ k ih =>
    simp only [pow_succ, mul_neg_one, neg_mul]
    rw [norm_sum_neg]
    exact ih

/-- The square of each alternating orientation is exactly one. -/
theorem neg_one_pow_mul_self (k : ℕ) :
    (-1 : ℝ) ^ k * (-1 : ℝ) ^ k = 1 := by
  simpa only [mul_pow, one_pow] using
    congrArg (fun x : ℝ ↦ x ^ k) (show (-1 : ℝ) * -1 = 1 by norm_num)

end
end RiemannGaussian.PhaseConjugation

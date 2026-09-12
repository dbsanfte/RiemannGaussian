/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.AnalyticDerivativeCutoff

/-!
# The two terms in the uniform derivative power bound

The leading and complementary powers have exact squared identities under
differencing. Both the large-scale and long-shift cases are paid for by
the trivial length bound. A single coarse coefficient thirty-two controls
the second-derivative base at every positive scale.
-/

namespace RiemannGaussian.DerivativePowerEnvelope
noncomputable section
open DerivativePowerExponents AnalyticDerivativeCutoff DerivativeRecursionBudget

/-- The leading scale power with the full derivative-ratio factor. -/
def mainTerm (k : ℕ) (L ℓ A : ℝ) : ℝ := A ^ amp k * L * ℓ ^ alpha k

/-- The complementary length and inverse-scale power. -/
def errorTerm (k : ℕ) (L ℓ : ℝ) : ℝ := L ^ beta k * ℓ ^ (-alpha k)

/-- One coarse coefficient for both terms at every derivative order. -/
def envelope (k : ℕ) (L ℓ A : ℝ) : ℝ := 32 * (mainTerm k L ℓ A + errorTerm k L ℓ)

/-- The leading term is nonnegative on the actual parameter domain. -/
theorem main_nonneg (k : ℕ) {L ℓ A : ℝ} (hL : 0 ≤ L) (hℓ : 0 ≤ ℓ) (hA : 0 ≤ A) :
    0 ≤ mainTerm k L ℓ A := by unfold mainTerm; positivity

/-- The complementary term is nonnegative on the actual parameter domain. -/
theorem error_nonneg (k : ℕ) {L ℓ : ℝ} (hL : 0 ≤ L) (hℓ : 0 ≤ ℓ) :
    0 ≤ errorTerm k L ℓ := by unfold errorTerm; positivity

/-- The successor leading square is exactly the scaled leading term
arising from the full lag sum. -/
theorem main_square (k : ℕ) (L : ℝ) {ℓ A : ℝ} (hℓ : 0 ≤ ℓ) (hA : 0 ≤ A) :
    mainTerm (k + 1) L ℓ A ^ 2 = A ^ amp k * L ^ 2 * ℓ ^ (2 * alpha (k + 1)) := by
  unfold mainTerm
  rw [mul_pow, mul_pow, ← Real.rpow_mul_natCast hA, ← Real.rpow_mul_natCast hℓ, amp_succ]
  have hp : amp k / 2 * (2 : ℝ) = amp k := by ring
  norm_num only [Nat.cast_ofNat]
  rw [hp, mul_comm (alpha (k + 1)) 2]

/-- The successor complementary square retains the exact ideal shift
scale and the full preceding length power. -/
theorem error_square (k : ℕ) {L ℓ : ℝ} (hL : 0 ≤ L) (hℓ : 0 ≤ ℓ) :
    errorTerm (k + 1) L ℓ ^ 2 = L ^ (beta k + 1) * ideal k ℓ := by
  unfold errorTerm ideal
  rw [mul_pow, ← Real.rpow_mul_natCast hL, ← Real.rpow_mul_natCast hℓ, beta_succ]
  congr 1 <;> congr 1 <;> ring

/-- A scale at least one is already paid for by the leading term. -/
theorem main_ge_length (k : ℕ) {L ℓ A : ℝ} (hL : 0 ≤ L) (hℓ : 1 ≤ ℓ) (hA : 1 ≤ A) :
    L ≤ mainTerm k L ℓ A := by
  have ha := Real.one_le_rpow hA (amp_pos k).le
  have hl := Real.one_le_rpow hℓ (alpha_pos k).le
  have hp := mul_le_mul ha hl (by norm_num : (0 : ℝ) ≤ 1)
    (Real.rpow_nonneg (by linarith : 0 ≤ A) (amp k))
  have h := mul_le_mul_of_nonneg_left hp hL
  unfold mainTerm
  nlinarith

/-- An ideal shift longer than the cap is paid for by the complementary
term, so the induction needs no estimate outside its length regime. -/
theorem error_ge_length (k : ℕ) {L ℓ : ℝ} (hL : 1 ≤ L) (hℓ : 0 < ℓ)
    (hLu : L ≤ ideal k ℓ) : L ≤ errorTerm (k + 1) L ℓ := by
  have hL0 : 0 ≤ L := by linarith
  have hLp : 0 < L := by linarith
  apply (sq_le_sq₀ hL0 (error_nonneg _ hL0 hℓ.le)).mp
  rw [error_square k hL0 hℓ.le, Real.rpow_add hLp, Real.rpow_one]
  have hp := Real.one_le_rpow hL (beta_nonneg k)
  calc
    L ^ 2 = (1 * L) * L := by ring
    _ ≤ (L ^ beta k * L) * ideal k ℓ :=
      mul_le_mul (mul_le_mul_of_nonneg_right hp hL0) hLu hL0 (by positivity)

/-- The full envelope is nonnegative on the actual parameter domain. -/
theorem nonneg (k : ℕ) {L ℓ A : ℝ} (hL : 0 ≤ L) (hℓ : 0 ≤ ℓ) (hA : 0 ≤ A) :
    0 ≤ envelope k L ℓ A := by
  unfold envelope
  exact mul_nonneg (by norm_num) (add_nonneg (main_nonneg k hL hℓ hA) (error_nonneg k hL hℓ))

/-- The square-root base has the asserted universal coefficient, even
when the base recurrence uses its large-curvature trivial fallback. -/
theorem base_bound (κ : Cutoffs) (L : ℕ) {ℓ A : ℝ} (hℓ : 0 < ℓ) (hA : 1 ≤ A) :
    budget κ 0 L ℓ A ≤ envelope 0 L ℓ A := by
  apply (DerivativeRecursionBudget.base_le κ L hℓ hA).trans
  have hA0 : 0 ≤ A := by linarith
  have hc : (3 + 2 * Real.pi) / (2 * Real.pi) ≤ 32 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * Real.pi)).mpr
    linarith [Real.two_le_pi]
  have hc' : 2 * (3 + 2 * Real.pi) ≤ (32 : ℝ) := by linarith [Real.pi_le_four]
  have hs : 0 ≤ A * (L : ℝ) * Real.sqrt ℓ := by positivity
  have hi : 0 ≤ (Real.sqrt ℓ)⁻¹ := by positivity
  have hb := add_le_add (mul_le_mul_of_nonneg_right hc hs) (mul_le_mul_of_nonneg_right hc' hi)
  unfold envelope mainTerm errorTerm
  rw [amp_zero, beta_zero, alpha_zero, Real.rpow_one, Real.rpow_zero, one_mul,
    Real.rpow_neg hℓ.le, ← Real.sqrt_eq_rpow]
  convert! hb using 1 <;> ring

end
end RiemannGaussian.DerivativePowerEnvelope

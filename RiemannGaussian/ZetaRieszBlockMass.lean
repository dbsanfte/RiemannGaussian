/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovBlockMass
import RiemannGaussian.ZetaRieszConditionedEnergy

/-!
# An explicit block normalization for the original Riesz carrier

The literal Riesz carrier already receives the signed conditioned-energy
bound with its actual block count. A constructive falling-factorial and
floor estimate now gives an explicit denominator. Its positivity is paid
at the original band endpoint; every weighted mixed moment and sampling
cost remains unchanged. No saving in those moments is claimed here.
-/

namespace RiemannGaussian.ZetaRieszBlockMass
noncomputable section
open scoped Classical
open VinogradovBlockMass ZetaRieszConditionedEnergy

/-- The explicit number of nonsingular blocks supplied by complete next-digit windows at the original endpoint. -/
def lowerBlockMass (p k a N : ℕ) : ℕ :=
  p.descFactorial k * (2 ^ (32 * N) / p ^ (a + 1)) ^ k

/-- The explicit block mass is positive whenever a full next-digit window fits. -/
theorem lowerBlockMass_pos {p k a N : ℕ} [NeZero p]
    (hkp : k < p) (hX : p ^ (a + 1) ≤ 2 ^ (32 * N)) :
    0 < lowerBlockMass p k a N := by
  apply Nat.mul_pos (Nat.descFactorial_pos.mpr hkp.le)
  exact pow_pos (Nat.div_pos hX (pow_pos (Nat.pos_of_ne_zero (NeZero.ne p)) _)) _

/-- The explicit floor mass counts actual members of the original conditioned family. -/
theorem lowerBlockMass_le_blockCount {p k a N : ℕ} [NeZero p] :
    lowerBlockMass p k a N ≤ blockCount p k a 0 N :=
  conditionedWindow_floor_card_ge

/-- The actual Riesz carrier receives a proved explicit normalization, retaining the complete weighted mixed-moment numerator. -/
theorem actual_band_le_explicit_block_mass {p k a b r : ℕ} [Fact p.Prime]
    (hkp : k < p) (hk : 0 < k) (hab : a < b) (hr : 0 < r)
    (colour : Fin k → Bool) (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (y : ℝ)
    (hX : p ^ (a + 1) ≤ 2 ^ (32 * N)) :
    ‖zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient L) P N y‖ ^ (2 * r) ≤
      ((p ^ b : ℝ) ^ (2 * r - 1) * ∑ eta : Fin (p ^ b),
        (frequencyCost (p := p) (a := a) (b := b) (r := r) (xi := 0)
          (eta.val : ℤ) colour L P N y : ℝ) * congruenceCost p k a b colour *
          rieszMomentMaximum p b k r (eta.val : ℤ) L P N y) /
        (lowerBlockMass p k a N : ℝ) ^ 2 := by
  have hC : 0 < (lowerBlockMass p k a N : ℝ) := by
    exact_mod_cast lowerBlockMass_pos hkp hX
  have hc : (lowerBlockMass p k a N : ℝ) ≤ (blockCount p k a 0 N : ℝ) := by
    exact_mod_cast (lowerBlockMass_le_blockCount (p := p) (k := k) (a := a) (N := N))
  rw [le_div_iff₀ (sq_pos_of_pos hC), mul_comm]
  calc
    _ ≤ (blockCount p k a 0 N : ℝ) ^ 2 *
        ‖zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient L) P N y‖ ^ (2 * r) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hC.le hc 2) (by positivity)
    _ ≤ _ := actual_band_conditioned_bound (xi := 0) hkp hk hab hr colour L P N y

end
end RiemannGaussian.ZetaRieszBlockMass

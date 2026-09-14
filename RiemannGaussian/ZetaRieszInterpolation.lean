/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovInterpolation
import RiemannGaussian.ZetaRieszBlockMass
/-!
# Interpolation of the original Riesz carrier's mixed moments

The literal finer mixed-moment maximum is bounded by an actual higher
Riesz moment and the actual reverse mixed-moment maximum. This is the
continuous Holder interpolation applied to the original signed, complex
weights, with all continuity and torus integration conditions discharged.
The whole original carrier receives the result with its explicit constructive
block mass, attained-frequency cost and signed congruence cost.

No moment-budget hypothesis is introduced. Quantitative savings for these
remaining actual weighted moments, and the global zero-free goal, stay open.
-/

namespace RiemannGaussian.ZetaRieszInterpolation
noncomputable section
open scoped Classical BigOperators
open MeasureTheory UnitAddTorus
open VinogradovPartitionEnergy VinogradovProductEnergy VinogradovShiftedMoment
open VinogradovInterpolation ZetaRieszConditionedEnergy ZetaRieszBlockMass

/-- Use the original normalized Haar measure on the circle. -/
local instance unitCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
/-- The original circle measure has total mass one. -/
local instance unitCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- All actual finer-residue polynomials at the unchanged original band endpoint. -/
def fineFamily (p b k N : ℕ) (c : Fin (p ^ (k * b))) : UnitAddTorus (Fin k) → ℂ :=
  VinogradovCongruenceEnergy.residuePolynomial (p ^ (k * b)) c.val (2 ^ (32 * N)) k 1

/-- The actual higher torus moment of the original residue Riesz lift. -/
def higherRieszMoment (p b k r : ℕ) (eta : ℤ) (L : ℝ)
    (P : Polynomial ℂ) (N : ℕ) (y : ℝ) : ℝ :=
  ∫ theta : UnitAddTorus (Fin k), ‖residueLift p b k eta L P N y theta‖ ^ (2 * r + 2)

/-- The actual reverse mixed-moment maximum, with only a squared original Riesz factor. -/
def reverseRieszMaximum (p b k r : ℕ) [NeZero p] (eta : ℤ) (L : ℝ)
    (P : Polynomial ℂ) (N : ℕ) (y : ℝ) : ℝ :=
  reverseMaximum (fineFamily p b k N) (residueLift p b k eta L P N y) k r

/-- Apply the full interpolation theorem to the literal Riesz-weighted mixed maximum, with no assumed moment estimate. -/
theorem rieszMomentMaximum_le_interpolated {p b k r : ℕ} [NeZero p]
    (hr : 0 < r) (eta : ℤ) (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (y : ℝ) :
    rieszMomentMaximum p b k r eta L P N y ≤
      higherRieszMoment p b k r eta L P N y ^ (1 - 1 / (r : ℝ)) *
        reverseRieszMaximum p b k r eta L P N y ^ (1 / (r : ℝ)) := by
  unfold rieszMomentMaximum fineMomentMaximum
  apply Finset.sup'_le
  intro c hc
  have hn (theta : UnitAddTorus (Fin k)) :
      ‖polynomial (tailFrequency (k := k) (fun _ : Fin r => 1))
        (tupleWeight r (residueWeight p b eta L P N y)) theta‖ ^ 2 =
        ‖residueLift p b k eta L P N y theta‖ ^ (2 * r) := by
    rw [← residueLift_power_eq, norm_pow, ← pow_mul, Nat.mul_comm r 2]
  simp_rw [hn]
  apply mixed_le_higher_reverse_max hr (fineFamily p b k N) (residueLift p b k eta L P N y)
  · intro c
    unfold fineFamily VinogradovCongruenceEnergy.residuePolynomial
    fun_prop
  · unfold residueLift
    exact continuous_polynomial _ _

/-- The whole original Riesz carrier receives the interpolated actual moments with its proved explicit block denominator and all sampling and congruence costs. -/
theorem actual_band_le_interpolated_moments {p k a b r : ℕ} [Fact p.Prime]
    (hkp : k < p) (hk : 0 < k) (hab : a < b) (hr : 0 < r)
    (colour : Fin k → Bool) (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (y : ℝ)
    (hX : p ^ (a + 1) ≤ 2 ^ (32 * N)) :
    ‖zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient L) P N y‖ ^ (2 * r) ≤
      ((p ^ b : ℝ) ^ (2 * r - 1) * ∑ eta : Fin (p ^ b),
        (frequencyCost (p := p) (a := a) (b := b) (r := r) (xi := 0)
          (eta.val : ℤ) colour L P N y : ℝ) * congruenceCost p k a b colour *
          (higherRieszMoment p b k r (eta.val : ℤ) L P N y ^ (1 - 1 / (r : ℝ)) *
            reverseRieszMaximum p b k r (eta.val : ℤ) L P N y ^ (1 / (r : ℝ)))) /
        (lowerBlockMass p k a N : ℝ) ^ 2 := by
  apply (actual_band_le_explicit_block_mass hkp hk hab hr colour L P N y hX).trans
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro eta heta
  exact mul_le_mul_of_nonneg_left (rieszMomentMaximum_le_interpolated hr (eta.val : ℤ) L P N y)
    (by positivity)

end
end RiemannGaussian.ZetaRieszInterpolation

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovFibreCorrelation
import RiemannGaussian.VinogradovNormalizedIteration
import RiemannGaussian.ZetaRieszBlockMass

/-!
# The original Riesz carrier and the finite conditioned-energy recurrence

The exact complex weights on each original block-and-tail frequency fibre
are averaged before taking norms. Their actual finite maximum transfers
the Riesz-weighted energy to the unweighted mixed moment on the identical
configuration family. The proved finite conditioning recurrence then gives
the original arithmetic band an explicit deep remainder and the full sum
of actual normalized conditioned energies.

The endpoint pays the attained-frequency sampling cost, residue summation,
and the proved positive block denominator. All original Riesz coefficients,
logarithmic phases, damping, filters and cutoffs survive in the complex
fibre averages. No weighted-moment budget is assumed or identified with an
unweighted moment. A quantitative saving for the retained correlations and
conditioned levels, hence any wider zero-free region, remains open.
-/

namespace RiemannGaussian.ZetaRieszConditioningTransfer
noncomputable section
open scoped Classical BigOperators
open MeasureTheory UnitAddTorus VinogradovPartitionEnergy VinogradovProductEnergy
open VinogradovMomentPartition VinogradovFourierEvaluation VinogradovFibreCorrelation
open VinogradovResidueEnergy
open VinogradovSingularConditioning VinogradovConditioningRemainder
open VinogradovConditioningPowerSaving VinogradovCongruencingScaling VinogradovNormalizedIteration
open ZetaRieszConditionedEnergy ZetaRieszBlockMass

/-- The original normalized Haar measure on the circle. -/
local instance unitCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
/-- The original circle measure has total mass one. -/
local instance unitCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The actual maximum norm of the original Riesz configuration weights averaged on complete signed frequency fibres. -/
def rieszCorrelation {p k a b r xi : ℕ} (eta : ℤ) (colour : Fin k → Bool)
    (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (y : ℝ) : ℝ :=
  correlationMaximum
    (windowFrequency (p := p) (a := a) (b := b) (xi := xi)
      (X := 2 ^ (32 * N)) (eta := eta) colour (fun _ : Fin r => 1))
    (configurationWeight eta L P N y)

/-- The original amplified Riesz energy is exactly its multiplicity-weighted complex fibre-average energy. -/
theorem amplified_energy_eq_fibre_averages {p k a b r xi : ℕ} (eta : ℤ)
    (colour : Fin k → Bool) (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (y : ℝ) :
    (∫ theta : UnitAddTorus (Fin k),
      ‖polynomial (blockFrequency (p := p) (a := a) (xi := xi)
        (X := 2 ^ (32 * N)) colour) (fun _ => 1) theta‖ ^ 2 *
      ‖residueLift p b k eta L P N y theta‖ ^ (2 * r)) =
      ∑ c ∈ Finset.univ.image (windowFrequency (p := p) (a := a) (b := b) (xi := xi)
        (X := 2 ^ (32 * N)) (eta := eta) colour (fun _ : Fin r => 1)),
        (fibreMultiplicity (windowFrequency (p := p) (a := a) (b := b) (xi := xi)
          (X := 2 ^ (32 * N)) (eta := eta) colour (fun _ : Fin r => 1)) c : ℝ) ^ 2 *
        ‖fibreAverage (windowFrequency (p := p) (a := a) (b := b) (xi := xi)
          (X := 2 ^ (32 * N)) (eta := eta) colour (fun _ : Fin r => 1))
          (configurationWeight eta L P N y) c‖ ^ 2 := by
  have he := energy_eq_fibre_averages
    (windowFrequency (p := p) (a := a) (b := b) (xi := xi)
      (X := 2 ^ (32 * N)) (eta := eta) colour (fun _ : Fin r => 1))
    (configurationWeight eta L P N y)
  simpa only [amplified_lift_eq, norm_mul, mul_pow, norm_pow, ← pow_mul, Nat.mul_comm r 2] using he

/-- Unit weights on the very same original configuration family give its literal unweighted mixed moment. -/
theorem window_energy_one_eq_mixed {p k a b r xi eta X : ℕ}
    (heta : eta < p ^ b) (colour : Fin k → Bool) :
    (∫ theta : UnitAddTorus (Fin k),
      ‖polynomial (windowFrequency (p := p) (a := a) (b := b) (xi := xi)
        (X := X) (eta := (eta : ℤ)) colour (fun _ : Fin r => 1)) (fun _ => 1) theta‖ ^ 2) =
      mixedMoment p k a b xi eta X r colour := by
  have he : ((eta : ℤ) : ZMod (p ^ b)).val = eta := by
    rw [Int.cast_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt heta]
  unfold mixedMoment
  apply integral_congr_ae
  filter_upwards [] with theta
  have ht := tail_polynomial_eq_product (p := p) (k := k) (b := b) (X := X)
    (eta : ℤ) (fun _ : Fin r => 1) theta
  change polynomial (tailFrequency (p := p) (k := k) (b := b) (X := X)
    (eta := (eta : ℤ)) (fun _ : Fin r => 1)) (fun _ => 1) theta = _ at ht
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, he] at ht
  rw [window_polynomial_eq_product (eta : ℤ) colour (fun _ : Fin r => 1) (fun _ => 1), ht,
    norm_mul, mul_pow, norm_pow, ← pow_mul, Nat.mul_comm r 2]

/-- The original weighted energy transfers to its literal unweighted mixed moment with the actual complex fibre-correlation cost. -/
theorem amplified_energy_le_correlated_mixed {p k a b r xi eta : ℕ}
    (heta : eta < p ^ b) (colour : Fin k → Bool) (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (y : ℝ) :
    (∫ theta : UnitAddTorus (Fin k),
      ‖polynomial (blockFrequency (p := p) (a := a) (xi := xi)
        (X := 2 ^ (32 * N)) colour) (fun _ => 1) theta‖ ^ 2 *
      ‖residueLift p b k (eta : ℤ) L P N y theta‖ ^ (2 * r)) ≤
      rieszCorrelation (p := p) (a := a) (b := b) (r := r) (xi := xi)
        (eta : ℤ) colour L P N y ^ 2 * mixedMoment p k a b xi eta (2 ^ (32 * N)) r colour := by
  have he := energy_le_correlation_maximum
    (windowFrequency (p := p) (a := a) (b := b) (xi := xi)
      (X := 2 ^ (32 * N)) (eta := (eta : ℤ)) colour (fun _ : Fin r => 1))
    (configurationWeight (eta : ℤ) L P N y)
  rw [window_energy_one_eq_mixed heta colour] at he
  simpa only [amplified_lift_eq, norm_mul, mul_pow, norm_pow, ← pow_mul, Nat.mul_comm r 2,
    rieszCorrelation] using he

/-- Point evaluation of the original residue carrier pays the attained-frequency cost before the unweighted conditioning transfer. -/
theorem residue_sample_le_correlated_mixed {p k a b r xi eta : ℕ}
    (heta : eta < p ^ b) (colour : Fin k → Bool) (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (y : ℝ) :
    (blockCount p k a xi N : ℝ) ^ 2 * ‖residueLift p b k (eta : ℤ) L P N y 0‖ ^ (2 * r) ≤
      (frequencyCost (p := p) (a := a) (b := b) (r := r) (xi := xi)
        (eta : ℤ) colour L P N y : ℝ) *
      (rieszCorrelation (p := p) (a := a) (b := b) (r := r) (xi := xi)
        (eta : ℤ) colour L P N y ^ 2 * mixedMoment p k a b xi eta (2 ^ (32 * N)) r colour) := by
  have hs := active_sample_energy_le
    (windowFrequency (p := p) (a := a) (b := b) (xi := xi)
      (X := 2 ^ (32 * N)) (eta := (eta : ℤ)) colour (fun _ : Fin r => 1))
    (configurationWeight (eta : ℤ) L P N y) 0
  change _ ≤ (frequencyCost (p := p) (a := a) (b := b) (r := r) (xi := xi)
    (eta : ℤ) colour L P N y : ℝ) * _ at hs
  simp only [amplified_lift_eq, norm_mul, mul_pow, norm_pow, ← pow_mul,
    Nat.mul_comm r 2, block_polynomial_zero, Complex.norm_natCast] at hs
  exact hs.trans (mul_le_mul_of_nonneg_left (amplified_energy_le_correlated_mixed heta colour L P N y)
    (Nat.cast_nonneg _))

/-- The actual combined residue-summation, attained-frequency and complex-correlation cost for the original band. -/
def correlatedSamplingCost (p k a b r xi : ℕ) (colour : Fin k → Bool)
    (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (y : ℝ) : ℝ :=
  (p ^ b : ℝ) ^ (2 * r - 1) * ∑ eta : Fin (p ^ b),
    (frequencyCost (p := p) (a := a) (b := b) (r := r) (xi := xi)
      (eta.val : ℤ) colour L P N y : ℝ) *
    rieszCorrelation (p := p) (a := a) (b := b) (r := r) (xi := xi)
      (eta.val : ℤ) colour L P N y ^ 2

/-- The original correlated sampling cost is nonnegative, including empty residue configurations. -/
theorem correlatedSamplingCost_nonneg (p k a b r xi : ℕ) (colour : Fin k → Bool)
    (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (y : ℝ) :
    0 ≤ correlatedSamplingCost p k a b r xi colour L P N y := by
  unfold correlatedSamplingCost
  positivity

/-- The entire original band transfers to the actual original mixed level with its proved sampling and complex-correlation cost. -/
theorem actual_band_le_correlated_level {p k a b xi u : ℕ} [NeZero p]
    (hr : 0 < k * u) (colour : Fin k → Bool) (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (y : ℝ) :
    (blockCount p k a xi N : ℝ) ^ 2 *
      ‖zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient L) P N y‖ ^ (2 * (k * u)) ≤
      correlatedSamplingCost p k a b (k * u) xi colour L P N y *
        levelMixedMaximum p k a b xi (2 ^ (32 * N)) u colour := by
  have hh := VinogradovMomentReduction.norm_weighted_power_bound Finset.univ
    (fun _ : Fin (p ^ b) => 1)
    (fun eta => residueLift p b k (eta.val : ℤ) L P N y 0) (by simp)
    (p := 2 * (k * u)) (by omega)
  simp only [Complex.ofReal_one, one_mul, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one, Nat.cast_pow] at hh
  rw [actual_band_eq_residue_lifts (p := p) b k]
  calc
    _ ≤ (blockCount p k a xi N : ℝ) ^ 2 *
        ((p ^ b : ℝ) ^ (2 * (k * u) - 1) * ∑ eta : Fin (p ^ b),
          ‖residueLift p b k (eta.val : ℤ) L P N y 0‖ ^ (2 * (k * u))) :=
      mul_le_mul_of_nonneg_left hh (sq_nonneg _)
    _ = (p ^ b : ℝ) ^ (2 * (k * u) - 1) * ∑ eta : Fin (p ^ b),
        (blockCount p k a xi N : ℝ) ^ 2 *
          ‖residueLift p b k (eta.val : ℤ) L P N y 0‖ ^ (2 * (k * u)) := by
      rw [← Finset.mul_sum]
      ring
    _ ≤ (p ^ b : ℝ) ^ (2 * (k * u) - 1) * ∑ eta : Fin (p ^ b),
        (frequencyCost (p := p) (a := a) (b := b) (r := k * u) (xi := xi)
          (eta.val : ℤ) colour L P N y : ℝ) *
        (rieszCorrelation (p := p) (a := a) (b := b) (r := k * u) (xi := xi)
          (eta.val : ℤ) colour L P N y ^ 2 *
          levelMixedMaximum p k a b xi (2 ^ (32 * N)) u colour) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro eta heta
      apply (residue_sample_le_correlated_mixed (xi := xi) (r := k * u) eta.isLt colour L P N y).trans
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      exact Finset.le_sup' (fun c : Fin (p ^ b) =>
        mixedMoment p k a b xi c.val (2 ^ (32 * N)) (k * u) colour) (Finset.mem_univ eta)
    _ = _ := by
      unfold correlatedSamplingCost
      simp_rw [← mul_assoc]
      rw [← Finset.sum_mul]
      ring

/-- The literal Riesz carrier receives the proved finite normalized conditioning recurrence, with its actual fibre correlations and positive block mass. -/
theorem actual_band_le_conditioned_iteration {p k a b u H : ℕ} [NeZero p]
    (hk : 2 ≤ k) (hu : k ≤ u) (hab : a ≤ b) (hH : 1 ≤ H) (hgap : b - a ≤ 2 * H)
    (colour : Fin k → Bool) (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (y : ℝ)
    (hX : p ^ (b + H) ≤ 2 ^ (32 * N))
    (hp : (elementaryConstant k u * iterationConstant k u) ^ 2 ≤ (p : ℝ)) :
    ‖zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient L) P N y‖ ^ (2 * (k * u)) ≤
      (correlatedSamplingCost p k a b (k * u) 0 colour L P N y *
        (momentScale ((2 ^ (32 * N) : ℕ) : ℝ) p k u a b (((k * (2 * u + 1) : ℕ) : ℝ)) *
          conditioningAllowance p k a b 0 (2 ^ (32 * N)) u H colour
            (((k * (2 * u + 1) : ℕ) : ℝ)))) / (lowerBlockMass p k a N : ℝ) ^ 2 := by
  have hkp := degree_lt_of_budget hk hu (elementaryConstant_one_le k u) hp
  have hXa : p ^ (a + 1) ≤ 2 ^ (32 * N) :=
    (Nat.pow_le_pow_right (Nat.one_le_iff_ne_zero.mpr (NeZero.ne p)) (by omega : a + 1 ≤ b + H)).trans hX
  have hC : 0 < (lowerBlockMass p k a N : ℝ) := by exact_mod_cast lowerBlockMass_pos hkp hXa
  have hc : (lowerBlockMass p k a N : ℝ) ≤ (blockCount p k a 0 N : ℝ) := by
    exact_mod_cast (lowerBlockMass_le_blockCount (p := p) (k := k) (a := a) (N := N))
  rw [le_div_iff₀ (sq_pos_of_pos hC), mul_comm]
  calc
    _ ≤ (blockCount p k a 0 N : ℝ) ^ 2 *
        ‖zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient L) P N y‖ ^ (2 * (k * u)) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hC.le hc 2) (by positivity)
    _ ≤ correlatedSamplingCost p k a b (k * u) 0 colour L P N y *
        levelMixedMaximum p k a b 0 (2 ^ (32 * N)) u colour :=
      actual_band_le_correlated_level (Nat.mul_pos (by omega) (by omega)) colour L P N y
    _ ≤ _ := mul_le_mul_of_nonneg_left (mixed_le_scale_allowance hk hu hab hH hgap hX hp colour)
      (correlatedSamplingCost_nonneg p k a b (k * u) 0 colour L P N y)

/-- The original Riesz bound also receives the explicit geometric weights, retaining the full sum of actual normalized conditioned levels. -/
theorem actual_band_le_geometric_conditioned_iteration {p k a b u H : ℕ} [NeZero p]
    (hk : 2 ≤ k) (hu : k ≤ u) (hab : a ≤ b) (hH : 1 ≤ H) (hgap : b - a ≤ 2 * H)
    (colour : Fin k → Bool) (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (y : ℝ)
    (hX : p ^ (b + H) ≤ 2 ^ (32 * N))
    (hp : (elementaryConstant k u * iterationConstant k u) ^ 2 ≤ (p : ℝ)) :
    ‖zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient L) P N y‖ ^ (2 * (k * u)) ≤
      (correlatedSamplingCost p k a b (k * u) 0 colour L P N y *
        (momentScale ((2 ^ (32 * N) : ℕ) : ℝ) p k u a b (((k * (2 * u + 1) : ℕ) : ℝ)) *
          geometricAllowance p k a b 0 (2 ^ (32 * N)) u H colour
            (((k * (2 * u + 1) : ℕ) : ℝ)))) / (lowerBlockMass p k a N : ℝ) ^ 2 := by
  apply (actual_band_le_conditioned_iteration hk hu hab hH hgap colour L P N y hX hp).trans
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  apply mul_le_mul_of_nonneg_left _ (correlatedSamplingCost_nonneg p k a b (k * u) 0 colour L P N y)
  apply mul_le_mul_of_nonneg_left _ (by unfold momentScale; positivity)
  exact allowance_le_geometric (by omega) (by positivity) colour _

end
end RiemannGaussian.ZetaRieszConditioningTransfer

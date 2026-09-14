/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovNonsingularSelection
import RiemannGaussian.VinogradovConditioningHolder

/-!
# Explicit nonsingular bound and the actual finite conditioning step

The original nonsingular collision count is bounded by actual mixed moments
of the selected signed blocks. Its sum over position embeddings remains
available before passing to a maximum over colours. The complete selection
cost is (2s).descFactorial(k), with s=k*u, and all Holder and integral
conditions are proved.

Combining this bound with the actual singular contribution and weighted
AM-GM proves the one-step conditioning recurrence underlying Wooley (2012),
Lemma 5.1, with explicit (not optimized) constants:
https://annals.math.princeton.edu/wp-content/uploads/annals-v175-n3-p12-p.pdf
The explicit remainder saving at the elementary exponent is proved in
`VinogradovConditioningPowerSaving`. Improving the high-moment exponent,
the original weighted Riesz saving and the VK zero-free region remain open.
-/

namespace RiemannGaussian.VinogradovNonsingularConditioning
noncomputable section
open scoped Classical BigOperators ComplexConjugate
open UnitAddTorus MeasureTheory
open VinogradovMeanValue VinogradovPartitionEnergy
open VinogradovSingularConditioning VinogradovConditioningSupport VinogradovResidueDigits
open VinogradovResidueEnergy VinogradovResidueMoment VinogradovProductEnergy
/-- Use the original normalized circle Haar measure. -/
local instance unitCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
/-- The original circle Haar measure has mass one. -/
local instance unitCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
open VinogradovSignedComplement VinogradovNonsingularSelection VinogradovConditioningHolder

/-- The actual mixed moment of the original block and a signed conditioned block at the tail scale. -/
def conditionedMoment (p k a b xi eta X u : ℕ) (colourA colourB : Fin k → Bool) : ℝ :=
  ∫ theta : UnitAddTorus (Fin k),
    ‖polynomial (blockFrequency (p := p) (a := a) (xi := xi) (X := X) colourA) (fun _ => 1) theta‖ ^ 2 *
      ‖polynomial (blockFrequency (p := p) (a := b) (xi := eta) (X := X) colourB) (fun _ => 1) theta‖ ^ (2 * u)

/-- The complete target count receives the actual mixed norm integral after exact complex factorization. -/
theorem target_count_le_integral {p k a b xi eta X s : ℕ} (colour : Fin k → Bool)
    (e : Fin k ↪ (Fin s ⊕ Fin s)) :
    (targetCount (p := p) (a := a) (b := b) (xi := xi) (eta := eta) (X := X) colour e : ℝ) ≤
      ∫ theta : UnitAddTorus (Fin k),
        ‖polynomial (blockFrequency (p := p) (a := a) (xi := xi) (X := X) colour) (fun _ => 1) theta‖ ^ 2 *
        ‖polynomial (blockFrequency (p := p) (a := b) (xi := eta) (X := X)
          (fun j => pairedColour s (e j))) (fun _ => 1) theta‖ *
        ‖VinogradovCongruenceEnergy.residuePolynomial (p ^ b) eta X k 1 theta‖ ^ (2 * s - k) := by
  have he := norm_integral_le_integral_norm (μ := volume)
    (polynomial (targetFrequency (p := p) (a := a) (b := b) (xi := xi) (eta := eta) (X := X) colour e) (fun _ => 1))
  rw [polynomial_integral_zero_count] at he
  simp only [Complex.norm_natCast] at he
  apply he.trans_eq
  apply integral_congr_ae
  filter_upwards [] with theta
  rw [target_polynomial_eq_product]
  simp only [norm_mul, Complex.norm_conj]
  have hc : ‖polynomial (complementFrequency (p := p) (b := b) (eta := eta) (X := X) e (pairedColour s))
      (fun _ => 1) theta‖ =
      ‖VinogradovCongruenceEnergy.residuePolynomial (p ^ b) eta X k 1 theta‖ ^
        (Fintype.card (Fin s ⊕ Fin s) - k) := by
    convert norm_complement_polynomial (p := p) (b := b) (eta := eta) (X := X) e (pairedColour s) theta using 1
    congr!
  rw [hc]
  simp only [Fintype.card_sum, Fintype.card_fin, ← two_mul]
  ring

/-- The original target count receives the actual Holder factors for its induced sign pattern. -/
theorem target_count_le_moments {p k a b xi eta X u : ℕ} (hu : 0 < u) (colour : Fin k → Bool)
    (e : Fin k ↪ (Fin (k * u) ⊕ Fin (k * u))) :
    (targetCount (p := p) (a := a) (b := b) (xi := xi) (eta := eta) (X := X) colour e : ℝ) ≤
      conditionedMoment p k a b xi eta X u colour (fun j => pairedColour (k * u) (e j)) ^
        (1 / (2 * u : ℝ)) * mixedMoment p k a b xi eta X (k * u) colour ^ (1 - 1 / (2 * u : ℝ)) := by
  have hq : 1 < 2 * u := by omega
  have he := conditioning_holder (k := k) hq
    (polynomial (blockFrequency (p := p) (a := a) (xi := xi) (X := X) colour) (fun _ => 1))
    (polynomial (blockFrequency (p := p) (a := b) (xi := eta) (X := X)
      (fun j => pairedColour (k * u) (e j))) (fun _ => 1))
    (VinogradovCongruenceEnergy.residuePolynomial (p ^ b) eta X k 1)
    (continuous_polynomial _ _) (continuous_polynomial _ _) (by unfold VinogradovCongruenceEnergy.residuePolynomial; fun_prop)
  have hexp : k * (2 * u) = 2 * (k * u) := by ring
  have hexp' : k * (2 * u - 1) = 2 * (k * u) - k := by
    rw [Nat.mul_sub_left_distrib, mul_one, hexp]
  simp only [hexp, hexp', Nat.cast_mul, Nat.cast_ofNat] at he
  exact (target_count_le_integral colour e).trans he

/-- Retain the sum of actual induced-sign moments over all selected embeddings. -/
theorem nonsingular_count_le_signed_moments {p k a b xi eta X u : ℕ}
    (hu : 0 < u) (colour : Fin k → Bool) :
    (nonsingularCount (p := p) (a := a) (b := b) (xi := xi) (eta := eta) (X := X) (s := k * u) colour : ℝ) ≤
      ∑ e : Fin k ↪ (Fin (k * u) ⊕ Fin (k * u)),
        conditionedMoment p k a b xi eta X u colour (fun j => pairedColour (k * u) (e j)) ^
          (1 / (2 * u : ℝ)) * mixedMoment p k a b xi eta X (k * u) colour ^ (1 - 1 / (2 * u : ℝ)) := by
  have hN := nonsingular_count_le_selected_sum (p := p) (a := a) (b := b) (xi := xi) (eta := eta)
    (X := X) (s := k * u) colour
  have hR := (Nat.cast_le (α := ℝ)).mpr hN
  simp only [Nat.cast_sum] at hR
  apply hR.trans
  apply Finset.sum_le_sum
  intro e he
  exact ((Nat.cast_le (α := ℝ)).mpr (selected_count_le_target colour e)).trans
    (target_count_le_moments hu colour e)

/-- The finite maximum of actual conditioned moments over all block colours. -/
def conditionedMaximum (p k a b xi eta X u : ℕ) (colour : Fin k → Bool) : ℝ :=
  (Finset.univ : Finset (Fin k → Bool)).sup' Finset.univ_nonempty
    (conditionedMoment p k a b xi eta X u colour)

/-- Every actual conditioned mixed moment is nonnegative. -/
theorem conditionedMoment_nonneg (p k a b xi eta X u : ℕ) (colourA colourB : Fin k → Bool) :
    0 ≤ conditionedMoment p k a b xi eta X u colourA colourB :=
  integral_nonneg (fun _ => by positivity)

/-- Each original signed mixed moment lies below its actual finite colour maximum. -/
theorem conditionedMoment_le_maximum (p k a b xi eta X u : ℕ) (colourA colourB : Fin k → Bool) :
    conditionedMoment p k a b xi eta X u colourA colourB ≤ conditionedMaximum p k a b xi eta X u colourA :=
  Finset.le_sup' _ (Finset.mem_univ colourB)

/-- Bound the original nonsingular contribution by actual moments with the explicit falling-factorial selection cost. -/
theorem nonsingular_count_le_conditioned_max {p k a b xi eta X u : ℕ}
    (hu : 0 < u) (colour : Fin k → Bool) :
    (nonsingularCount (p := p) (a := a) (b := b) (xi := xi) (eta := eta) (X := X) (s := k * u) colour : ℝ) ≤
      ((2 * (k * u)).descFactorial k : ℝ) *
        conditionedMaximum p k a b xi eta X u colour ^ (1 / (2 * u : ℝ)) *
        mixedMoment p k a b xi eta X (k * u) colour ^ (1 - 1 / (2 * u : ℝ)) := by
  apply (nonsingular_count_le_signed_moments hu colour).trans
  calc
    _ ≤ ∑ _e : Fin k ↪ (Fin (k * u) ⊕ Fin (k * u)),
        conditionedMaximum p k a b xi eta X u colour ^ (1 / (2 * u : ℝ)) *
          mixedMoment p k a b xi eta X (k * u) colour ^ (1 - 1 / (2 * u : ℝ)) := by
      apply Finset.sum_le_sum
      intro e he
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (integral_nonneg (fun _ => by positivity)) _)
      apply Real.rpow_le_rpow (conditionedMoment_nonneg _ _ _ _ _ _ _ _ _ _)
        (conditionedMoment_le_maximum _ _ _ _ _ _ _ _ _ _)
      positivity
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_embedding_eq,
        Fintype.card_sum, Fintype.card_fin, ← two_mul]
      ring


/-- Combine both actual collision contributions and absorb the original moment to prove the explicit finite conditioning recurrence. -/
theorem conditioning_step {p k a b xi eta X u : ℕ} [NeZero p]
    (hkp : k ≤ p) (hk : 0 < k) (heta : eta < p ^ b) (hu : 0 < u)
    (colour : Fin k → Bool) :
    mixedMoment p k a b xi eta X (k * u) colour ≤
      (2 * u : ℝ) * ((p.choose (k - 1) : ℝ) * ((k - 1 : ℕ) : ℝ) ^ (2 * (k * u)) *
        nextMixedMaximum p k a b xi X (k * u) colour) +
      ((2 * (k * u)).descFactorial k : ℝ) ^ (2 * u) *
        conditionedMaximum p k a b xi eta X u colour := by
  have hsplit := mixedMoment_eq_singular_add_nonsingular (p := p) (a := a) (b := b)
    (xi := xi) (eta := eta) (X := X) (s := k * u) colour
  have h1 := singular_count_le_next_mixed_max (a := a) (xi := xi) (X := X)
    hkp heta (Nat.mul_pos hk hu) colour
  have h2 := nonsingular_count_le_conditioned_max (p := p) (a := a) (b := b)
    (xi := xi) (eta := eta) (X := X) hu colour
  have hI : 0 ≤ mixedMoment p k a b xi eta X (k * u) colour :=
    integral_nonneg (fun _ => by positivity)
  have hK : 0 ≤ conditionedMaximum p k a b xi eta X u colour :=
    (conditionedMoment_nonneg _ _ _ _ _ _ _ _ colour colour).trans
      (conditionedMoment_le_maximum _ _ _ _ _ _ _ _ colour colour)
  have hsum := add_le_add h1 h2
  rw [← hsplit] at hsum
  have he := holder_absorption (q := 2 * u)
    (S := (p.choose (k - 1) : ℝ) * ((k - 1 : ℕ) : ℝ) ^ (2 * (k * u)) *
      nextMixedMaximum p k a b xi X (k * u) colour)
    (by omega) hI hK (Nat.cast_nonneg ((2 * (k * u)).descFactorial k))
    (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hsum)
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using he

end
end RiemannGaussian.VinogradovNonsingularConditioning

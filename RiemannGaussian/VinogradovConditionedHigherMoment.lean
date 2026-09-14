/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovInterpolation
import RiemannGaussian.VinogradovSignedTailMoment

/-!
# Higher conditioned moments at the actual quotient length

An injective flattening keeps every signed power coordinate of the original
conditioned blocks. Their collision count is first bounded by the count of
full signed residue tuples; only then does sign crossing and affine transport
reach the literal homogeneous mean value. Nonsingularity is not assumed to
survive that crossing. Arbitrary bounded complex tuple weights receive the
same majorant after the exact frequency identity.

The actual higher conditioned moment and continuous Holder interpolation
supply the homogeneous comparison following Wooley (2012), equation (6.8).
Singular conditioning, the complete high-moment iteration and the required
Vinogradov--Korobov analytic saving are separate remaining obligations.
-/

namespace RiemannGaussian.VinogradovConditionedHigherMoment
noncomputable section
open scoped BigOperators Classical
open UnitAddTorus MeasureTheory
open VinogradovResidueEnergy VinogradovResidueMoment VinogradovProductEnergy
open VinogradovMeanValue VinogradovShiftedMoment VinogradovSignedTailMoment

/-- Use the original normalized circle Haar measure. -/
local instance unitCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
/-- The original circle Haar measure has mass one. -/
local instance unitCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Flatten the original conditioned blocks into full residue tuples, retaining every entry. -/
def flatten {p k b xi X u : ℕ} (xs : Fin u → ConditionedWindow p k b xi X) :
    Fin (u * k) → ResidueWindow (p ^ b) xi X := fun z =>
  ⟨(xs (finProdFinEquiv.symm z).1).val (finProdFinEquiv.symm z).2,
    (xs (finProdFinEquiv.symm z).1).property.1 (finProdFinEquiv.symm z).2⟩

/-- The full flattened tuple reconstructs every original conditioned block. -/
theorem flatten_injective {p k b xi X u : ℕ} :
    Function.Injective (flatten (p := p) (k := k) (b := b) (xi := xi) (X := X) (u := u)) := by
  intro xs ys he
  funext i
  apply Subtype.ext
  funext j
  have hj := congrArg (fun f => (f (finProdFinEquiv (i, j))).val) he
  simpa only [flatten, Equiv.symm_apply_apply] using hj

/-- Repeat the original sign pattern on every block without changing coordinate order. -/
def repeatColour {k : ℕ} (u : ℕ) (colour : Fin k → Bool) : Fin (u * k) → Bool :=
  fun j => colour (finProdFinEquiv.symm j).2

/-- Flattening preserves every signed power-sum coordinate exactly. -/
theorem flatten_frequency {p k b xi X u : ℕ} (colour : Fin k → Bool)
    (xs : Fin u → ConditionedWindow p k b xi X) :
    signedTupleFrequency (repeatColour u colour)
      (fun n : ResidueWindow (p ^ b) xi X => monomialFrequency k (n.val.val + 1))
      (flatten xs) = tupleFrequency u (blockFrequency colour) xs := by
  funext a
  simp only [signedTupleFrequency, tupleFrequency, blockFrequency, Finset.sum_apply]
  rw [← Fintype.sum_prod_type (fun ij : Fin u × Fin k =>
    VinogradovSignedCongruence.sign (colour ij.2) *
      (((xs ij.1).val ij.2).val + 1 : ℤ) ^ (a.val + 1))]
  apply Fintype.sum_equiv finProdFinEquiv.symm
  intro j
  simp only [repeatColour, flatten, monomialFrequency, Nat.cast_add, Nat.cast_one]

/-- Every shifted conditioned collision count is bounded by the literal homogeneous mean value at the quotient length. Inject before crossing signs, so no stability of block nonsingularity is assumed. -/
theorem conditioned_shift_count_le {p k b xi X u : ℕ} [NeZero p]
    (colour : Fin k → Bool) (h : Fin k → ℤ) :
    (differenceCount (tupleFrequency u
      (blockFrequency (p := p) (a := b) (xi := xi) (X := X) colour)) h : ℝ) ≤
      meanValue (u * k) k (X / p ^ b + 1) := by
  have hf := differenceCount_map_le
    (flatten (p := p) (k := k) (b := b) (xi := xi) (X := X) (u := u))
    flatten_injective
    (signedTupleFrequency (repeatColour u colour)
      (fun n : ResidueWindow (p ^ b) xi X => monomialFrequency k (n.val.val + 1))) h
  simp only [flatten_frequency] at hf
  have hfR : (differenceCount (tupleFrequency u
      (blockFrequency (p := p) (a := b) (xi := xi) (X := X) colour)) h : ℝ) ≤
      (differenceCount (signedTupleFrequency (repeatColour u colour)
        (fun n : ResidueWindow (p ^ b) xi X => monomialFrequency k (n.val.val + 1))) h : ℝ) := by
    exact_mod_cast hf
  exact hfR.trans
    (signed_residue_shift_le_meanValue (NeZero.ne (p ^ b)) (repeatColour u colour) k h)

/-- Arbitrary jointly weighted conditioned tuples receive the same shifted-count majorant when each full complex weight has norm at most one. -/
theorem conditioned_weighted_shift_le {p k b xi X u : ℕ} [NeZero p]
    (colour : Fin k → Bool) (w : (Fin u → ConditionedWindow p k b xi X) → ℂ)
    (hw : ∀ x, ‖w x‖ ≤ 1) (h : Fin k → ℤ) :
    ‖weightedShift (tupleFrequency u (blockFrequency colour)) w h‖ ≤
      meanValue (u * k) k (X / p ^ b + 1) :=
  (weightedShift_norm_le_count _ w hw h).trans (conditioned_shift_count_le colour h)

/-- Bound the actual higher conditioned torus moment by the homogeneous mean value, with its original cutoff and all quotient rounding paid. -/
theorem conditioned_moment_le {p k b xi X u : ℕ} [NeZero p]
    (colour : Fin k → Bool) :
    (∫ theta : UnitAddTorus (Fin k),
      ‖VinogradovPartitionEnergy.polynomial
        (blockFrequency (p := p) (a := b) (xi := xi) (X := X) colour)
        (fun _ => 1) theta‖ ^ (2 * u)) ≤
      meanValue (u * k) k (X / p ^ b + 1) := by
  simp only [VinogradovPartitionEnergy.polynomial, one_mul]
  change moment u (blockFrequency colour) ≤ _
  rw [moment_eq_collisionCount]
  have he := conditioned_shift_count_le (p := p) (b := b) (xi := xi) (X := X) (u := u) colour 0
  simpa only [tupleFrequency_count_zero] using he

/-- The actual mixed moment receives Holder interpolation and the proved higher homogeneous comparison, leaving its literal reverse mixed moment. -/
theorem conditioned_mixed_interpolation_le {p k a b xi X u : ℕ} [NeZero p]
    (hu : 0 < u) (colour : Fin k → Bool) (zeta : ℕ) :
    (∫ theta : UnitAddTorus (Fin k),
      ‖VinogradovCongruenceEnergy.residuePolynomial (p ^ b) zeta X k 1 theta‖ ^ (2 * k) *
        ‖VinogradovPartitionEnergy.polynomial
          (blockFrequency (p := p) (a := a) (xi := xi) (X := X) colour)
          (fun _ => 1) theta‖ ^ (2 * u)) ≤
      meanValue ((u + 1) * k) k (X / p ^ a + 1) ^ (1 - 1 / (u : ℝ)) *
        (∫ theta : UnitAddTorus (Fin k),
          ‖VinogradovPartitionEnergy.polynomial
            (blockFrequency (p := p) (a := a) (xi := xi) (X := X) colour)
            (fun _ => 1) theta‖ ^ 2 *
          ‖VinogradovCongruenceEnergy.residuePolynomial (p ^ b) zeta X k 1 theta‖ ^ (2 * k * u)) ^
            (1 / (u : ℝ)) := by
  have he := VinogradovInterpolation.mixed_interpolation (k := k) hu
    (VinogradovCongruenceEnergy.residuePolynomial (p ^ b) zeta X k 1)
    (VinogradovPartitionEnergy.polynomial
      (blockFrequency (p := p) (a := a) (xi := xi) (X := X) colour) (fun _ => 1))
    (by unfold VinogradovCongruenceEnergy.residuePolynomial; fun_prop)
    (VinogradovPartitionEnergy.continuous_polynomial _ _)
  have hm := conditioned_moment_le (p := p) (b := a) (xi := xi) (X := X) (u := u + 1) colour
  have hx : 2 * (u + 1) = 2 * u + 2 := by omega
  rw [hx] at hm
  have huR : (1 : ℝ) ≤ u := by exact_mod_cast hu
  have huR0 : (0 : ℝ) < u := by linarith
  have ht : 0 ≤ 1 - 1 / (u : ℝ) := by
    have := (div_le_one huR0).mpr huR
    linarith
  exact he.trans (mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow (integral_nonneg (fun _ => by positivity)) hm ht)
    (Real.rpow_nonneg (integral_nonneg (fun _ => by positivity)) _))

end
end RiemannGaussian.VinogradovConditionedHigherMoment

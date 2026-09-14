/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovConditionedHigherMoment

/-!
# A finite signed efficient-congruencing step

An exact finite image weight represents the power of the original conditioned
block polynomial inside the full tail interface. It retains all within-block
nonsingularity conditions and signs. The original product-energy theorem,
continuous Holder interpolation and the proved higher homogeneous comparison
then give the finite transfer from scales a,b to b,kb.

This supplies the finite inequality underlying Wooley (2012), Lemma 6.1,
with the actual positive window, explicit quotient rounding, canonical
finer-residue maximum and smaller two-colour factorial retained:
https://annals.math.princeton.edu/wp-content/uploads/annals-v175-n3-p12-p.pdf
It does not yet condition arbitrary singular tuples or complete the
high-moment iteration and Vinogradov--Korobov zero-free proof.
-/

namespace RiemannGaussian.VinogradovCongruencingStep
noncomputable section
open scoped BigOperators Classical
open UnitAddTorus MeasureTheory
open VinogradovResidueEnergy VinogradovResidueMoment VinogradovProductEnergy
open VinogradovMeanValue VinogradovShiftedMoment VinogradovConditionedHigherMoment

/-- Use the original normalized circle Haar measure. -/
local instance unitCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
/-- The original circle Haar measure has mass one. -/
local instance unitCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The exact image weight of the original block family, retaining every within-block residue and nonsingularity restriction jointly. -/
def conditionedTailWeight {p k b X u : ℕ} (eta : ℤ)
    (z : Fin (u * k) → VinogradovConditionedCompletion.PrimeTailWindow p b eta X) : ℂ :=
  if ∃ xs : Fin u → ConditionedWindow p k b (eta : ZMod (p ^ b)).val X,
      flatten xs = z then 1 else 0

/-- The exact block-image indicator has norm at most one at every full tail tuple. -/
theorem conditionedTailWeight_norm_le_one {p k b X u : ℕ} (eta : ℤ)
    (z : Fin (u * k) → VinogradovConditionedCompletion.PrimeTailWindow p b eta X) :
    ‖conditionedTailWeight eta z‖ ≤ 1 := by
  unfold conditionedTailWeight
  split_ifs <;> simp

/-- The complete weighted tail polynomial is exactly the powered original conditioned polynomial, with every sign and block restriction retained. -/
theorem conditioned_power_tail_eq {p k b X u : ℕ} (eta : ℤ) (colour : Fin k → Bool)
    (theta : UnitAddTorus (Fin k)) :
    VinogradovPartitionEnergy.polynomial
      (tailFrequency (p := p) (b := b) (X := X) (eta := eta)
        (fun j : Fin (u * k) => VinogradovSignedCongruence.sign (repeatColour u colour j)))
      (conditionedTailWeight eta) theta =
        VinogradovPartitionEnergy.polynomial
          (blockFrequency (p := p) (a := b) (xi := (eta : ZMod (p ^ b)).val) (X := X) colour)
          (fun _ => 1) theta ^ u := by
  trans VinogradovPartitionEnergy.polynomial
    (tupleFrequency u (blockFrequency (p := p) (a := b)
      (xi := (eta : ZMod (p ^ b)).val) (X := X) colour)) (fun _ => 1) theta
  · unfold VinogradovPartitionEnergy.polynomial conditionedTailWeight
    simp only [ite_mul, one_mul, zero_mul]
    rw [← Finset.sum_filter]
    have hs : (Finset.univ.filter (fun z =>
        ∃ xs : Fin u → ConditionedWindow p k b (eta : ZMod (p ^ b)).val X,
          flatten xs = z)) = Finset.univ.image
        (flatten (p := p) (k := k) (b := b) (xi := (eta : ZMod (p ^ b)).val) (X := X) (u := u)) := by
      ext z
      simp
    rw [hs, Finset.sum_image (fun x _ y _ hxy => flatten_injective hxy)]
    apply Finset.sum_congr rfl
    intro xs hxs
    apply congrArg (fun v => mFourier v theta)
    exact flatten_frequency colour xs
  · have hw : (fun _ : Fin u → ConditionedWindow p k b (eta : ZMod (p ^ b)).val X => (1 : ℂ)) =
        tupleWeight u (fun _ => (1 : ℂ)) := by funext xs; simp [tupleWeight]
    rw [hw]
    symm
    exact weighted_power_expansion u (blockFrequency colour) (fun _ => 1) theta

/-- The actual maximum of reverse mixed torus moments at the finer scale, keeping the original conditioned block and every canonical finer residue. -/
def reverseConditionedMaximum (p k b u X : ℕ) [NeZero p] (eta : ℤ)
    (colour : Fin k → Bool) : ℝ :=
  VinogradovInterpolation.reverseMaximum
    (fun c : Fin (p ^ (k * b)) =>
      VinogradovCongruenceEnergy.residuePolynomial (p ^ (k * b)) c.val X k 1)
    (VinogradovPartitionEnergy.polynomial
      (blockFrequency (p := p) (a := b) (xi := (eta : ZMod (p ^ b)).val) (X := X) colour)
      (fun _ => 1)) k u

/-- The exact block-power tail receives Holder interpolation and the proved homogeneous comparison, with its actual reverse mixed maximum. -/
theorem fine_conditioned_max_le {p k b X u : ℕ} [NeZero p]
    (hu : 0 < u) (eta : ℤ) (colour : Fin k → Bool) :
    fineMomentMaximum (k := k)
      (fun j : Fin (u * k) => VinogradovSignedCongruence.sign (repeatColour u colour j))
      (conditionedTailWeight (p := p) (b := b) (X := X) eta) ≤
      meanValue ((u + 1) * k) k (X / p ^ b + 1) ^ (1 - 1 / (u : ℝ)) *
        reverseConditionedMaximum p k b u X eta colour ^ (1 / (u : ℝ)) := by
  unfold fineMomentMaximum
  apply Finset.sup'_le
  intro c hc
  simp_rw [conditioned_power_tail_eq, norm_pow, ← pow_mul, Nat.mul_comm u 2]
  apply (conditioned_mixed_interpolation_le (a := b) (b := k * b) hu colour c.val).trans
  apply mul_le_mul_of_nonneg_left
  · apply Real.rpow_le_rpow (integral_nonneg (fun _ => by positivity)) _ (by positivity)
    exact Finset.le_sup' (fun c : Fin (p ^ (k * b)) =>
      ∫ theta : UnitAddTorus (Fin k),
        ‖VinogradovPartitionEnergy.polynomial
          (blockFrequency (p := p) (a := b) (xi := (eta : ZMod (p ^ b)).val) (X := X) colour)
          (fun _ => 1) theta‖ ^ 2 *
        ‖VinogradovCongruenceEnergy.residuePolynomial (p ^ (k * b)) c.val X k 1 theta‖ ^ (2 * k * u))
      (Finset.mem_univ c)
  · apply Real.rpow_nonneg
    rw [meanValue_eq_count]
    positivity

/-- Transfer the actual conditioned energy from scales a,b to the homogeneous quotient moment and actual reverse mixed maximum at b,kb. Every prime-power, sign-factorial and rounding cost is explicit; no moment budget is assumed. -/
theorem conditioned_congruencing_step {p k a b xi X u : ℕ} [Fact p.Prime]
    (hkp : k < p) (hk : 0 < k) (hab : a < b) (hu : 0 < u) (eta : ℤ)
    (colourA colourB : Fin k → Bool) :
    (∫ theta : UnitAddTorus (Fin k),
      ‖VinogradovPartitionEnergy.polynomial
        (blockFrequency (p := p) (a := a) (xi := xi) (X := X) colourA)
        (fun _ => 1) theta‖ ^ 2 *
      ‖VinogradovPartitionEnergy.polynomial
        (blockFrequency (p := p) (a := b) (xi := (eta : ZMod (p ^ b)).val) (X := X) colourB)
        (fun _ => 1) theta‖ ^ (2 * u)) ≤
      ((p ^ ((a + b) * (k * (k - 1) / 2)) *
        VinogradovSignedCongruence.colourFactorial colourA : ℕ) : ℝ) *
        ((p ^ (k * b - a)) ^ k : ℕ) *
        (meanValue ((u + 1) * k) k (X / p ^ b + 1) ^ (1 - 1 / (u : ℝ)) *
          reverseConditionedMaximum p k b u X eta colourB ^ (1 / (u : ℝ))) := by
  have he := conditioned_product_max_le (xi := xi) hkp hk hab eta colourA
    (fun j : Fin (u * k) => VinogradovSignedCongruence.sign (repeatColour u colourB j))
    (conditionedTailWeight (p := p) (b := b) (X := X) eta)
  have hn (theta : UnitAddTorus (Fin k)) :
      ‖VinogradovPartitionEnergy.polynomial
        (tailFrequency (p := p) (b := b) (X := X) (eta := eta)
          (fun j : Fin (u * k) => VinogradovSignedCongruence.sign (repeatColour u colourB j)))
        (conditionedTailWeight eta) theta‖ ^ 2 =
      ‖VinogradovPartitionEnergy.polynomial
        (blockFrequency (p := p) (a := b) (xi := (eta : ZMod (p ^ b)).val) (X := X) colourB)
        (fun _ => 1) theta‖ ^ (2 * u) := by
    rw [conditioned_power_tail_eq, norm_pow, ← pow_mul, Nat.mul_comm u 2]
  simp_rw [hn] at he
  exact he.trans (mul_le_mul_of_nonneg_left (fine_conditioned_max_le hu eta colourB) (by positivity))


end
end RiemannGaussian.VinogradovCongruencingStep

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovResidueMoment

/-!
# Exact signed tail transport and residue-window completion bounds

Crossing the two variables at negative positions is a bijection of complete
ordered tuple pairs. It preserves the full frequency difference, and an
explicit conjugation of the original weights preserves every complex pair
coefficient. Every fixed sign pattern therefore receives the literal
normalized residue-window mean value, including actual tail completions of
fixed integer-weighted moment blocks.

The crossing acts on the complete tuple product. Additional constraints
coupling entries within an individual tuple need separate transport proofs;
in particular, nonsingularity conditions are not silently carried through it.
-/

namespace RiemannGaussian.VinogradovSignedTailMoment
noncomputable section
open scoped BigOperators ComplexConjugate

/-- Swap the two entries at exactly the negative-colour positions.
Each original variable and its position are retained by this involution. -/
def crossedPair {ι : Type*} {r : ℕ} (colour : Fin r → Bool)
    (p : (Fin r → ι) × (Fin r → ι)) : (Fin r → ι) × (Fin r → ι) :=
  (fun j => if colour j then p.1 j else p.2 j,
   fun j => if colour j then p.2 j else p.1 j)

/-- Crossing negative positions twice restores the entire original pair. -/
theorem crossedPair_involutive {ι : Type*} {r : ℕ} (colour : Fin r → Bool) :
    Function.Involutive (crossedPair (ι := ι) colour) := by
  intro p
  apply Prod.ext
  · funext j
    cases hj : colour j <;> simp [crossedPair, hj]
  · funext j
    cases hj : colour j <;> simp [crossedPair, hj]

/-- The crossing map is an exact bijection of ordered tuple pairs. -/
def crossedEquiv {ι : Type*} {r : ℕ} (colour : Fin r → Bool) :
    ((Fin r → ι) × (Fin r → ι)) ≃ ((Fin r → ι) × (Fin r → ι)) :=
  Function.Involutive.toPerm (crossedPair colour) (crossedPair_involutive colour)

/-- The full signed tuple frequency keeps the original colour of each
coordinate, at every retained frequency component. -/
def signedTupleFrequency {ι d : Type*} {r : ℕ} (colour : Fin r → Bool)
    (v : ι → d → ℤ) (x : Fin r → ι) : d → ℤ := fun a =>
  ∑ j, VinogradovSignedCongruence.sign (colour j) * v (x j) a

/-- Crossing the two entries at negative positions preserves the complete
frequency difference exactly, before testing any particular target. -/
theorem signed_difference_eq_crossed {ι d : Type*} {r : ℕ}
    (colour : Fin r → Bool) (v : ι → d → ℤ) (p : (Fin r → ι) × (Fin r → ι)) :
    signedTupleFrequency colour v p.1 - signedTupleFrequency colour v p.2 =
      VinogradovShiftedMoment.tupleFrequency r v (crossedPair colour p).1 -
        VinogradovShiftedMoment.tupleFrequency r v (crossedPair colour p).2 := by
  funext a
  simp only [signedTupleFrequency, VinogradovShiftedMoment.tupleFrequency,
    Pi.sub_apply, Finset.sum_apply, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  cases hc : colour j <;> simp [crossedPair, VinogradovSignedCongruence.sign, hc]
  ring

/-- On the complete tuple product, every fixed signed target has exactly
as many realizations as the ordinary target. The bijection keeps the target
and swaps variables instead of forgetting their signs. -/
theorem signed_differenceCount_eq {ι d : Type*} [Fintype ι] [Fintype d] {r : ℕ}
    (colour : Fin r → Bool) (v : ι → d → ℤ) (h : d → ℤ) :
    VinogradovShiftedMoment.differenceCount (signedTupleFrequency colour v) h =
      VinogradovShiftedMoment.differenceCount (VinogradovShiftedMoment.tupleFrequency r v) h := by
  classical
  have he (p : (Fin r → ι) × (Fin r → ι)) :
      signedTupleFrequency colour v p.1 = signedTupleFrequency colour v p.2 + h ↔
      VinogradovShiftedMoment.tupleFrequency r v (crossedPair colour p).1 =
        VinogradovShiftedMoment.tupleFrequency r v (crossedPair colour p).2 + h := by
    rw [← sub_eq_iff_eq_add', ← sub_eq_iff_eq_add', signed_difference_eq_crossed]
  unfold VinogradovShiftedMoment.differenceCount
  apply Finset.card_bij (fun p _ => crossedPair colour p)
  · intro p hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (he p).mp (Finset.mem_filter.mp hp).2⟩
  · intro p hp q hq hpq
    exact (crossedEquiv colour).injective hpq
  · intro p hp
    refine ⟨crossedPair colour p, ?_, crossedPair_involutive colour p⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, (he (crossedPair colour p)).mpr ?_⟩
    simpa only [crossedPair_involutive colour p] using (Finset.mem_filter.mp hp).2

/-- All fixed tail sign patterns receive the same actual residue-window
mean-value bound, with no condition on which signs occur. -/
theorem signed_residue_shift_le_meanValue {q xi X : ℕ} (hq : q ≠ 0) {r : ℕ}
    (colour : Fin r → Bool) (k : ℕ) (h : Fin k → ℤ) :
    (VinogradovShiftedMoment.differenceCount
      (signedTupleFrequency colour
        (fun n : VinogradovResidueMoment.ResidueWindow q xi X =>
          VinogradovMeanValue.monomialFrequency k (n.val.val + 1))) h : ℝ) ≤
      VinogradovMeanValue.meanValue r k (X / q + 1) := by
  rw [signed_differenceCount_eq]
  exact VinogradovResidueMoment.residue_window_shift_le_meanValue hq r k h

/-- Conjugate the original weight at every negative position. This retains
its full complex value, rather than replacing it by its modulus. -/
def colouredTupleWeight {ι : Type*} {r : ℕ} (colour : Fin r → Bool)
    (w : ι → ℂ) (x : Fin r → ι) : ℂ :=
  ∏ j, if colour j then w (x j) else conj (w (x j))

/-- Crossing negative positions exactly transports each original complex
pair weight into the corresponding colour-conjugated pair weight. -/
theorem pair_weight_eq_crossed {ι : Type*} {r : ℕ} (colour : Fin r → Bool)
    (w : ι → ℂ) (p : (Fin r → ι) × (Fin r → ι)) :
    VinogradovShiftedMoment.tupleWeight r w p.1 *
        conj (VinogradovShiftedMoment.tupleWeight r w p.2) =
      colouredTupleWeight colour w (crossedPair colour p).1 *
        conj (colouredTupleWeight colour w (crossedPair colour p).2) := by
  simp only [VinogradovShiftedMoment.tupleWeight, colouredTupleWeight,
    map_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j hj
  cases hc : colour j <;> simp [crossedPair, hc, mul_comm]

/-- The entire complex Gram coefficient at every frequency target is
unchanged by crossing the signed coordinates and conjugating their weights.
This identity precedes every count, absolute value, or mean-value bound. -/
theorem signed_weightedShift_eq_crossed {ι d : Type*} [Fintype ι] [Fintype d] {r : ℕ}
    (colour : Fin r → Bool) (v : ι → d → ℤ) (w : ι → ℂ) (h : d → ℤ) :
    VinogradovShiftedMoment.weightedShift (signedTupleFrequency colour v)
      (VinogradovShiftedMoment.tupleWeight r w) h =
    VinogradovShiftedMoment.weightedShift (VinogradovShiftedMoment.tupleFrequency r v)
      (colouredTupleWeight colour w) h := by
  classical
  have he (p : (Fin r → ι) × (Fin r → ι)) :
      signedTupleFrequency colour v p.1 = signedTupleFrequency colour v p.2 + h ↔
      VinogradovShiftedMoment.tupleFrequency r v (crossedPair colour p).1 =
        VinogradovShiftedMoment.tupleFrequency r v (crossedPair colour p).2 + h := by
    rw [← sub_eq_iff_eq_add', ← sub_eq_iff_eq_add', signed_difference_eq_crossed]
  let f (p : (Fin r → ι) × (Fin r → ι)) : ℂ :=
    if signedTupleFrequency colour v p.1 = signedTupleFrequency colour v p.2 + h then
      VinogradovShiftedMoment.tupleWeight r w p.1 *
        conj (VinogradovShiftedMoment.tupleWeight r w p.2) else 0
  let g (p : (Fin r → ι) × (Fin r → ι)) : ℂ :=
    if VinogradovShiftedMoment.tupleFrequency r v p.1 =
        VinogradovShiftedMoment.tupleFrequency r v p.2 + h then
      colouredTupleWeight colour w p.1 * conj (colouredTupleWeight colour w p.2) else 0
  change (∑ i, ∑ j, f (i, j)) = ∑ i, ∑ j, g (i, j)
  rw [← Fintype.sum_prod_type f, ← Fintype.sum_prod_type g]
  apply Fintype.sum_equiv (crossedEquiv colour)
  intro p
  change (if signedTupleFrequency colour v p.1 = signedTupleFrequency colour v p.2 + h then
      VinogradovShiftedMoment.tupleWeight r w p.1 *
        conj (VinogradovShiftedMoment.tupleWeight r w p.2) else 0) =
    (if VinogradovShiftedMoment.tupleFrequency r v (crossedPair colour p).1 =
        VinogradovShiftedMoment.tupleFrequency r v (crossedPair colour p).2 + h then
      colouredTupleWeight colour w (crossedPair colour p).1 *
        conj (colouredTupleWeight colour w (crossedPair colour p).2) else 0)
  simp only [he p]
  split_ifs
  · exact pair_weight_eq_crossed colour w p
  · rfl

/-- Every fixed tail sign pattern and every bounded original complex
weight family has the normalized residue-window mean-value budget. -/
theorem signed_residue_weighted_shift_le_meanValue {q xi X : ℕ} (hq : q ≠ 0) {r : ℕ}
    (colour : Fin r → Bool) (k : ℕ) (w : VinogradovResidueMoment.ResidueWindow q xi X → ℂ)
    (hw : ∀ i, ‖w i‖ ≤ 1) (h : Fin k → ℤ) :
    ‖VinogradovShiftedMoment.weightedShift
      (signedTupleFrequency colour
        (fun n : VinogradovResidueMoment.ResidueWindow q xi X =>
          VinogradovMeanValue.monomialFrequency k (n.val.val + 1)))
      (VinogradovShiftedMoment.tupleWeight r w) h‖ ≤
      VinogradovMeanValue.meanValue r k (X / q + 1) :=
  (VinogradovShiftedMoment.weightedShift_norm_le_count _ _
    (VinogradovShiftedMoment.tupleWeight_norm_le_one r w hw) h).trans
      (signed_residue_shift_le_meanValue hq colour k h)

/-- For each fixed pair of arbitrarily integer-weighted blocks, every
fixed pattern of tail signs receives the actual normalized mean-value
completion bound. No assumption on the distribution of signs is made. -/
theorem signed_tail_completions_le_meanValue {q xi X : ℕ} (hq : q ≠ 0) {r : ℕ}
    (colour : Fin r → Bool) (k : ℕ) (c x y : Fin k → ℤ) :
    ((Finset.univ.filter (fun vw :
        (Fin r → VinogradovResidueMoment.ResidueWindow q xi X) ×
          (Fin r → VinogradovResidueMoment.ResidueWindow q xi X) =>
      ∀ i : Fin k,
        (∑ j, c j * x j ^ (i.val + 1)) +
          (∑ j, VinogradovSignedCongruence.sign (colour j) *
            ((vw.1 j).val.val + 1 : ℤ) ^ (i.val + 1)) =
        (∑ j, c j * y j ^ (i.val + 1)) +
          ∑ j, VinogradovSignedCongruence.sign (colour j) *
            ((vw.2 j).val.val + 1 : ℤ) ^ (i.val + 1))).card : ℝ) ≤
      VinogradovMeanValue.meanValue r k (X / q + 1) := by
  classical
  let h (i : Fin k) := (∑ j, c j * y j ^ (i.val + 1)) - ∑ j, c j * x j ^ (i.val + 1)
  have he (vw : (Fin r → VinogradovResidueMoment.ResidueWindow q xi X) ×
      (Fin r → VinogradovResidueMoment.ResidueWindow q xi X)) :
      (∀ i : Fin k,
        (∑ j, c j * x j ^ (i.val + 1)) +
          (∑ j, VinogradovSignedCongruence.sign (colour j) *
            ((vw.1 j).val.val + 1 : ℤ) ^ (i.val + 1)) =
        (∑ j, c j * y j ^ (i.val + 1)) +
          ∑ j, VinogradovSignedCongruence.sign (colour j) *
            ((vw.2 j).val.val + 1 : ℤ) ^ (i.val + 1)) ↔
      signedTupleFrequency colour
        (fun n : VinogradovResidueMoment.ResidueWindow q xi X =>
          VinogradovMeanValue.monomialFrequency k (n.val.val + 1)) vw.1 =
      signedTupleFrequency colour
        (fun n : VinogradovResidueMoment.ResidueWindow q xi X =>
          VinogradovMeanValue.monomialFrequency k (n.val.val + 1)) vw.2 + h := by
    constructor
    · intro hvw
      funext i
      simp only [signedTupleFrequency, Pi.add_apply,
        VinogradovMeanValue.monomialFrequency, Nat.cast_add, Nat.cast_one, h]
      linarith [hvw i]
    · intro hvw i
      have hi := congrFun hvw i
      simp only [signedTupleFrequency, Pi.add_apply,
        VinogradovMeanValue.monomialFrequency, Nat.cast_add, Nat.cast_one, h] at hi
      linarith
  have hb := signed_residue_shift_le_meanValue (xi := xi) (X := X) hq colour k h
  simpa only [VinogradovShiftedMoment.differenceCount, ← he] using hb

end
end RiemannGaussian.VinogradovSignedTailMoment

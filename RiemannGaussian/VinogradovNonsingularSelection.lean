/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovSignedComplement
import Mathlib.Data.Fintype.CardEmbedding

/-!
# Original nonsingular collisions select signed blocks from both tails

Every original nonsingular pair supplies a block selected from both sides
of its equation. The induced signs and exact complement are retained.
For each selected position embedding, an injection reaches the full target
frequency equation; its complex polynomial factors exactly into the original
block Gram factor, the selected signed block and its signed complement.
The finite covering cost is retained before any integral norm bound.

These are counting and exact-identity ingredients for Wooley (2012),
Lemma 5.1. The actual upper bound is in `VinogradovNonsingularConditioning`.
-/

namespace RiemannGaussian.VinogradovNonsingularSelection
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
open VinogradovSignedComplement

/-- Keep the original left and right tails as one indexed family. -/
def pairedTail {p k a b xi eta X s : ℕ}
    (xy : Configuration p k a b xi eta X s × Configuration p k a b xi eta X s) :
    Fin s ⊕ Fin s → ResidueWindow (p ^ b) eta X := Sum.elim xy.1.2 xy.2.2

/-- Retain the positive left-tail and negative right-tail signs. -/
def pairedColour (s : ℕ) : Fin s ⊕ Fin s → Bool := Sum.elim (fun _ => true) (fun _ => false)

/-- The paired attained classes are exactly the union of both original tail supports. -/
theorem paired_class_support {p k a b xi eta X s : ℕ}
    (xy : Configuration p k a b xi eta X s × Configuration p k a b xi eta X s) :
    Finset.univ.image (fun i => nextDigit (pairedTail xy i)) = classSupport xy.1 ∪ classSupport xy.2 := by
  ext d
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_union, classSupport]
  constructor
  · rintro ⟨i, hi⟩
    cases i with
    | inl j => exact Or.inl ⟨j, hi⟩
    | inr j => exact Or.inr ⟨j, hi⟩
  · rintro (h | h)
    · obtain ⟨j, hj⟩ := h
      exact ⟨Sum.inl j, hj⟩
    · obtain ⟨j, hj⟩ := h
      exact ⟨Sum.inr j, hj⟩

/-- The complete signed paired frequency is exactly the original left-minus-right tail difference. -/
theorem paired_frequency {p k a b xi eta X s : ℕ}
    (xy : Configuration p k a b xi eta X s × Configuration p k a b xi eta X s) :
    (fun i : Fin k => ∑ j, VinogradovSignedCongruence.sign (pairedColour s j) *
      ((pairedTail xy j).val.val + 1 : ℤ) ^ (i.val + 1)) =
    (fun i => ∑ j, ((xy.1.2 j).val.val + 1 : ℤ) ^ (i.val + 1)) -
      (fun i => ∑ j, ((xy.2.2 j).val.val + 1 : ℤ) ^ (i.val + 1)) := by
  funext i
  simp only [Fintype.sum_sum_type, pairedColour, pairedTail, Sum.elim_inl, Sum.elim_inr,
    VinogradovSignedCongruence.sign, if_true, Bool.false_eq_true, if_false, one_mul, neg_mul,
    Finset.sum_neg_distrib, Pi.sub_apply, sub_eq_add_neg]

/-- Select an actual block from both tails while retaining induced signs and every complementary frequency. -/
theorem nonsingular_pair_has_signed_block {p k a b xi eta X s : ℕ}
    (xy : Configuration p k a b xi eta X s × Configuration p k a b xi eta X s)
    (hk : k ≤ (classSupport xy.1 ∪ classSupport xy.2).card) :
    ∃ e : Fin k ↪ (Fin s ⊕ Fin s), ∃ z : ConditionedWindow p k b eta X,
      (∀ j, z.val j = (pairedTail xy (e j)).val) ∧
      (fun i : Fin k => ∑ j, VinogradovSignedCongruence.sign (pairedColour s j) *
        ((pairedTail xy j).val.val + 1 : ℤ) ^ (i.val + 1)) =
      blockFrequency (fun j => pairedColour s (e j)) z +
        (fun i => ∑ j ∈ (Finset.univ.map e)ᶜ,
          VinogradovSignedCongruence.sign (pairedColour s j) *
            ((pairedTail xy j).val.val + 1 : ℤ) ^ (i.val + 1)) := by
  have hc : k ≤ (Finset.univ.image (fun j => nextDigit (pairedTail xy j))).card := by
    rw [paired_class_support]
    exact hk
  obtain ⟨e, z, hz⟩ := select_conditioned_block (pairedTail xy) hc
  refine ⟨e, z, hz, ?_⟩
  convert selected_frequency_eq_add_complement (pairedTail xy) (pairedColour s) e z hz using 1
  congr!

/-- Retain both original conditioned blocks and the complete signed paired tail equation. -/
theorem collision_signed_equation {p k a b xi eta X s : ℕ}
    (colour : Fin k → Bool)
    (xy : Configuration p k a b xi eta X s × Configuration p k a b xi eta X s)
    (he : frequency colour xy.1 = frequency colour xy.2) :
    blockFrequency colour xy.1.1 - blockFrequency colour xy.2.1 +
      (fun i : Fin k => ∑ j, VinogradovSignedCongruence.sign (pairedColour s j) *
        ((pairedTail xy j).val.val + 1 : ℤ) ^ (i.val + 1)) = 0 := by
  rw [paired_frequency]
  funext i
  have hi := congrFun he i
  simp only [frequency, blockFrequency, VinogradovShiftedMoment.tupleFrequency,
    VinogradovMeanValue.monomialFrequency, Pi.add_apply, Finset.sum_apply,
    Nat.cast_add, Nat.cast_one] at hi
  simp only [blockFrequency, Pi.add_apply, Pi.sub_apply, Pi.zero_apply]
  omega

/-- An original nonsingular collision yields the exact signed selected-block and complement equation. -/
theorem nonsingular_collision_selected_equation {p k a b xi eta X s : ℕ}
    (colour : Fin k → Bool)
    (xy : Configuration p k a b xi eta X s × Configuration p k a b xi eta X s)
    (he : frequency colour xy.1 = frequency colour xy.2)
    (hk : k ≤ (classSupport xy.1 ∪ classSupport xy.2).card) :
    ∃ e : Fin k ↪ (Fin s ⊕ Fin s), ∃ z : ConditionedWindow p k b eta X,
      (∀ j, z.val j = (pairedTail xy (e j)).val) ∧
      blockFrequency colour xy.1.1 - blockFrequency colour xy.2.1 +
        blockFrequency (fun j => pairedColour s (e j)) z +
        (fun i => ∑ j ∈ (Finset.univ.map e)ᶜ,
          VinogradovSignedCongruence.sign (pairedColour s j) *
            ((pairedTail xy j).val.val + 1 : ℤ) ^ (i.val + 1)) = 0 := by
  obtain ⟨e, z, hz, hf⟩ := nonsingular_pair_has_signed_block xy hk
  refine ⟨e, z, hz, ?_⟩
  have h := collision_signed_equation colour xy he
  rw [hf] at h
  simpa only [add_assoc] using h


/-- Original colliding pairs whose specified selected positions have distinct next digits. -/
abbrev Selected {p k a b xi eta X s : ℕ} (colour : Fin k → Bool)
    (e : Fin k ↪ (Fin s ⊕ Fin s)) :=
  {xy : Configuration p k a b xi eta X s × Configuration p k a b xi eta X s //
    frequency colour xy.1 = frequency colour xy.2 ∧
    Function.Injective (fun j => nextDigit (pairedTail xy (e j)))}

/-- Both original conditioned blocks, the actual selected block, and every original complement entry. -/
abbrev Target {p k a b xi eta X s : ℕ} (e : Fin k ↪ (Fin s ⊕ Fin s)) :=
  (ConditionedWindow p k a xi X × ConditionedWindow p k a xi X) ×
    (ConditionedWindow p k b eta X × (Complement e → ResidueWindow (p ^ b) eta X))

/-- Keep the entire original signed equation in the selected target variables. -/
def targetFrequency {p k a b xi eta X s : ℕ} (colour : Fin k → Bool)
    (e : Fin k ↪ (Fin s ⊕ Fin s)) (z : Target (p := p) (a := a) (b := b) (xi := xi) (eta := eta) (X := X) e) :
    Fin k → ℤ :=
  (blockFrequency colour z.1.1 - blockFrequency colour z.1.2) +
    (blockFrequency (fun j => pairedColour s (e j)) z.2.1 + complementFrequency e (pairedColour s) z.2.2)

/-- Inject each qualifying original collision into its full selected target equation. -/
def selectedToTarget {p k a b xi eta X s : ℕ} (colour : Fin k → Bool)
    (e : Fin k ↪ (Fin s ⊕ Fin s)) (z : Selected (p := p) (a := a) (b := b) (xi := xi) (eta := eta) (X := X) colour e) :
    {t : Target (p := p) (a := a) (b := b) (xi := xi) (eta := eta) (X := X) e // targetFrequency colour e t = 0} := by
  refine ⟨((z.val.1.1, z.val.2.1), (selectedBlock e (pairedTail z.val) z.property.2,
    fun j => pairedTail z.val j.val)), ?_⟩
  have h := collision_signed_equation colour z.val z.property.1
  rw [selected_full_frequency e (pairedColour s) (pairedTail z.val) z.property.2] at h
  exact h

/-- No original solution is lost or identified by retaining selected and complementary entries. -/
theorem selectedToTarget_injective {p k a b xi eta X s : ℕ} (colour : Fin k → Bool)
    (e : Fin k ↪ (Fin s ⊕ Fin s)) :
    Function.Injective (selectedToTarget (p := p) (a := a) (b := b) (xi := xi) (eta := eta) (X := X) colour e) := by
  intro z w h
  have hA1 : z.val.1.1 = w.val.1.1 := congrArg (fun t => t.val.1.1) h
  have hA2 : z.val.2.1 = w.val.2.1 := congrArg (fun t => t.val.1.2) h
  have hB := congrArg (fun t => t.val.2.1) h
  have hC := congrArg (fun t => t.val.2.2) h
  have htail : pairedTail z.val = pairedTail w.val := by
    apply function_eq_of_selected_complement e
    · intro j
      apply Subtype.ext
      exact congrArg (fun t : ConditionedWindow p k b eta X => t.val j) hB
    · intro j
      exact congrFun hC j
  apply Subtype.ext
  apply Prod.ext
  · apply Prod.ext hA1
    funext j
    exact congrFun htail (Sum.inl j)
  · apply Prod.ext hA2
    funext j
    exact congrFun htail (Sum.inr j)

/-- The literal count of original collisions qualifying for a given selected embedding. -/
def selectedCount {p k a b xi eta X s : ℕ} (colour : Fin k → Bool)
    (e : Fin k ↪ (Fin s ⊕ Fin s)) : ℕ :=
  Fintype.card (Selected (p := p) (a := a) (b := b) (xi := xi) (eta := eta) (X := X) colour e)

/-- The full zero-frequency count in the actual selected target variables. -/
def targetCount {p k a b xi eta X s : ℕ} (colour : Fin k → Bool)
    (e : Fin k ↪ (Fin s ⊕ Fin s)) : ℕ :=
  (Finset.univ.filter (fun t : Target (p := p) (a := a) (b := b) (xi := xi) (eta := eta) (X := X) e =>
    targetFrequency colour e t = 0)).card

/-- The proved original-solution injection bounds the selected count by the full target count. -/
theorem selected_count_le_target {p k a b xi eta X s : ℕ} (colour : Fin k → Bool)
    (e : Fin k ↪ (Fin s ⊕ Fin s)) :
    selectedCount (p := p) (a := a) (b := b) (xi := xi) (eta := eta) (X := X) colour e ≤
      targetCount (p := p) (a := a) (b := b) (xi := xi) (eta := eta) (X := X) colour e := by
  have h := Fintype.card_le_of_injective _ (selectedToTarget_injective (p := p) (a := a) (b := b)
    (xi := xi) (eta := eta) (X := X) colour e)
  simpa only [Fintype.card_subtype, selectedCount, targetCount] using h

/-- Cover the original nonsingular contribution by actual selected-position families. -/
theorem nonsingular_count_le_selected_sum {p k a b xi eta X s : ℕ} (colour : Fin k → Bool) :
    nonsingularCount (p := p) (a := a) (b := b) (xi := xi) (eta := eta) (X := X) (s := s) colour ≤
      ∑ e : Fin k ↪ (Fin s ⊕ Fin s),
        selectedCount (p := p) (a := a) (b := b) (xi := xi) (eta := eta) (X := X) colour e := by
  let U := Finset.univ.filter (fun xy : Configuration p k a b xi eta X s × Configuration p k a b xi eta X s =>
    frequency colour xy.1 = frequency colour xy.2 ∧ k ≤ (classSupport xy.1 ∪ classSupport xy.2).card)
  let V (e : Fin k ↪ (Fin s ⊕ Fin s)) := Finset.univ.filter
    (fun xy : Configuration p k a b xi eta X s × Configuration p k a b xi eta X s =>
      frequency colour xy.1 = frequency colour xy.2 ∧
      Function.Injective (fun j => nextDigit (pairedTail xy (e j))))
  have hsub : U ⊆ Finset.univ.biUnion V := by
    intro xy hxy
    obtain ⟨hf, hk⟩ := (Finset.mem_filter.mp hxy).2
    have hc : k ≤ (Finset.univ.image (fun j => nextDigit (pairedTail xy j))).card := by
      rw [paired_class_support]
      exact hk
    obtain ⟨e, he⟩ := select_distinct_classes _ hc
    exact Finset.mem_biUnion.mpr ⟨e, Finset.mem_univ e,
      Finset.mem_filter.mpr ⟨Finset.mem_univ xy, hf, he⟩⟩
  have hb := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  change U.card ≤ _
  apply hb.trans_eq
  apply Finset.sum_congr rfl
  intro e he
  simp only [selectedCount, Fintype.card_subtype]
  rfl

/-- Reversing every original Fourier frequency is exactly complex conjugation. -/
theorem polynomial_one_neg {ι d : Type*} [Fintype ι] [Fintype d]
    (v : ι → d → ℤ) (theta : UnitAddTorus d) :
    polynomial (fun i => -v i) (fun _ => 1) theta = conj (polynomial v (fun _ => 1) theta) := by
  simp only [polynomial, one_mul, mFourier_neg, map_sum]

/-- The full target polynomial retains the original block Gram, selected block signs and exact complement product. -/
theorem target_polynomial_eq_product {p k a b xi eta X s : ℕ} (colour : Fin k → Bool)
    (e : Fin k ↪ (Fin s ⊕ Fin s)) (theta : UnitAddTorus (Fin k)) :
    polynomial (targetFrequency (p := p) (a := a) (b := b) (xi := xi) (eta := eta) (X := X) colour e)
      (fun _ => 1) theta =
      (polynomial (blockFrequency (p := p) (a := a) (xi := xi) (X := X) colour) (fun _ => 1) theta *
        conj (polynomial (blockFrequency (p := p) (a := a) (xi := xi) (X := X) colour) (fun _ => 1) theta)) *
      (polynomial (blockFrequency (p := p) (a := b) (xi := eta) (X := X)
        (fun j => pairedColour s (e j))) (fun _ => 1) theta *
        polynomial (complementFrequency (p := p) (b := b) (eta := eta) (X := X) e (pairedColour s))
          (fun _ => 1) theta) := by
  have hprod {α β : Type} [Fintype α] [Fintype β]
      (v : α → Fin k → ℤ) (w : β → Fin k → ℤ) :
      polynomial (fun t : α × β => v t.1 + w t.2) (fun _ => 1) theta =
        polynomial v (fun _ => 1) theta * polynomial w (fun _ => 1) theta := by
    simpa only [mul_one] using polynomial_prod v w (fun _ => 1) (fun _ => 1) theta
  unfold targetFrequency
  rw [hprod (fun z : ConditionedWindow p k a xi X × ConditionedWindow p k a xi X =>
    blockFrequency colour z.1 - blockFrequency colour z.2)
    (fun z : ConditionedWindow p k b eta X × (Complement e → ResidueWindow (p ^ b) eta X) =>
      blockFrequency (fun j => pairedColour s (e j)) z.1 + complementFrequency e (pairedColour s) z.2)]
  rw [hprod (blockFrequency (p := p) (a := b) (xi := eta) (X := X) (fun j => pairedColour s (e j)))
    (complementFrequency (p := p) (b := b) (eta := eta) (X := X) e (pairedColour s))]
  have hpair := hprod (blockFrequency (p := p) (a := a) (xi := xi) (X := X) colour)
    (fun z => -blockFrequency (p := p) (a := a) (xi := xi) (X := X) colour z)
  simp only [← sub_eq_add_neg, polynomial_one_neg] at hpair
  rw [hpair]

end
end RiemannGaussian.VinogradovNonsingularSelection

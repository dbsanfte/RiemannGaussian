/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovSingularConditioning

/-!
# Exact selected blocks and their full signed complements

A finite embedding partitions every original position into the selected
block and its literal complement. The signed complete frequency and complex
complement polynomial remain exact; only the downstream norm theorem
forgets complement signs. Fourier orthogonality identifies full zero-frequency
counts before the nonsingular conditioning estimate uses them.
-/

namespace RiemannGaussian.VinogradovSignedComplement
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

/-- All original positions outside the selected embedding, with their identities retained. -/
abbrev Complement {ι : Type*} {k : ℕ} (e : Fin k ↪ ι) := {i : ι // i ∉ Set.range e}

/-- The selected positions and their literal complement partition the entire original index type. -/
def splitIndex {ι : Type*} {k : ℕ} (e : Fin k ↪ ι) : Fin k ⊕ Complement e ≃ ι :=
  Equiv.ofBijective (Sum.elim e Subtype.val) (by
    constructor
    · intro i j hij
      cases i with
      | inl i =>
        cases j with
        | inl j => exact congrArg Sum.inl (e.injective hij)
        | inr j => exact False.elim (j.property ⟨i, hij⟩)
      | inr i =>
        cases j with
        | inl j => exact False.elim (i.property ⟨j, hij.symm⟩)
        | inr j => exact congrArg Sum.inr (Subtype.ext hij)
    · intro i
      by_cases hi : i ∈ Set.range e
      · obtain ⟨j, rfl⟩ := hi
        exact ⟨Sum.inl j, rfl⟩
      · exact ⟨Sum.inr ⟨i, hi⟩, rfl⟩)

/-- The selected part of the exact index partition is the original embedding. -/
theorem splitIndex_inl {ι : Type*} {k : ℕ} (e : Fin k ↪ ι) (j : Fin k) :
    splitIndex e (Sum.inl j) = e j := rfl

/-- The complementary part is the original position itself. -/
theorem splitIndex_inr {ι : Type*} {k : ℕ} (e : Fin k ↪ ι) (j : Complement e) :
    splitIndex e (Sum.inr j) = j.val := rfl

/-- Partition a full finite sum without deleting or estimating either part. -/
theorem sum_selected_add_complement {ι M : Type*} [Fintype ι] [AddCommMonoid M]
    {k : ℕ} (e : Fin k ↪ ι) (f : ι → M) :
    ∑ i, f i = (∑ j, f (e j)) + ∑ j : Complement e, f j.val := by
  rw [← Equiv.sum_comp (splitIndex e)]
  simp only [Fintype.sum_sum_type, splitIndex_inl, splitIndex_inr]

/-- Pay exactly the number of positions remaining after selection. -/
theorem complement_card {ι : Type*} [Fintype ι] {k : ℕ} (e : Fin k ↪ ι) :
    Fintype.card (Complement e) = Fintype.card ι - k := by
  have h := Fintype.card_congr (splitIndex e)
  simp only [Fintype.card_sum, Fintype.card_fin] at h
  omega

/-- The selected entries together with every complementary entry determine the original family. -/
theorem function_eq_of_selected_complement {ι α : Type*} {k : ℕ}
    (e : Fin k ↪ ι) {f g : ι → α}
    (he : ∀ j, f (e j) = g (e j)) (hc : ∀ j : Complement e, f j.val = g j.val) : f = g := by
  funext i
  obtain ⟨j, rfl⟩ := (splitIndex e).surjective i
  cases j with
  | inl j => exact he j
  | inr j => exact hc j

/-- Distinct next digits construct an actual conditioned block from the original residue entries. -/
def selectedBlock {ι : Type*} {p k b eta X : ℕ}
    (e : Fin k ↪ ι) (z : ι → ResidueWindow (p ^ b) eta X)
    (h : Function.Injective (fun j => nextDigit (z (e j)))) : ConditionedWindow p k b eta X :=
  ⟨fun j => (z (e j)).val, (fun j => (z (e j)).property), h⟩

/-- Keep every power coordinate and induced sign on the full original complement. -/
def complementFrequency {ι : Type*} [Fintype ι] {p k b eta X : ℕ}
    (e : Fin k ↪ ι) (colour : ι → Bool)
    (z : Complement e → ResidueWindow (p ^ b) eta X) : Fin k → ℤ :=
  fun i => ∑ j, VinogradovSignedCongruence.sign (colour j.val) *
    ((z j).val.val + 1 : ℤ) ^ (i.val + 1)

/-- The complete original signed frequency is exactly selected block plus signed complement. -/
theorem selected_full_frequency {ι : Type*} [Fintype ι] {p k b eta X : ℕ}
    (e : Fin k ↪ ι) (colour : ι → Bool) (z : ι → ResidueWindow (p ^ b) eta X)
    (h : Function.Injective (fun j => nextDigit (z (e j)))) :
    (fun i : Fin k => ∑ j, VinogradovSignedCongruence.sign (colour j) *
      ((z j).val.val + 1 : ℤ) ^ (i.val + 1)) =
      blockFrequency (fun j => colour (e j)) (selectedBlock e z h) +
        complementFrequency e colour (fun j => z j.val) := by
  funext i
  exact sum_selected_add_complement e _

/-- The full complex complement polynomial factors into original signed residue polynomials. -/
theorem complement_polynomial_eq_product {ι : Type*} [Fintype ι] {p k b eta X : ℕ}
    (e : Fin k ↪ ι) (colour : ι → Bool) (theta : UnitAddTorus (Fin k)) :
    polynomial (complementFrequency (p := p) (b := b) (eta := eta) (X := X) e colour)
      (fun _ => 1) theta =
      ∏ j : Complement e, VinogradovCongruenceEnergy.residuePolynomial
        (p ^ b) eta X k (VinogradovSignedCongruence.sign (colour j.val)) theta := by
  unfold polynomial VinogradovCongruenceEnergy.residuePolynomial complementFrequency
  rw [Fintype.prod_sum]
  simp only [one_mul]
  apply Finset.sum_congr rfl
  intro z hz
  rw [product_mFourier]
  apply congrArg (fun v : Fin k → ℤ => mFourier v theta)
  funext i
  simp only [Finset.sum_apply, monomialFrequency, Nat.cast_add, Nat.cast_one]

/-- Only after the exact factorization, take the norm and pay the actual complement cardinality. -/
theorem norm_complement_polynomial {ι : Type*} [Fintype ι] {p k b eta X : ℕ}
    (e : Fin k ↪ ι) (colour : ι → Bool) (theta : UnitAddTorus (Fin k)) :
    ‖polynomial (complementFrequency (p := p) (b := b) (eta := eta) (X := X) e colour)
      (fun _ => 1) theta‖ =
      ‖VinogradovCongruenceEnergy.residuePolynomial (p ^ b) eta X k 1 theta‖ ^
        (Fintype.card ι - k) := by
  rw [complement_polynomial_eq_product, norm_prod]
  simp only [VinogradovCongruenceEnergy.norm_residuePolynomial_sign,
    Finset.prod_const, Finset.card_univ, complement_card]

/-- Fourier orthogonality identifies the literal full zero-frequency count. -/
theorem polynomial_integral_zero_count {ι d : Type*} [Fintype ι] [Fintype d]
    (v : ι → d → ℤ) :
    (∫ theta : UnitAddTorus d, polynomial v (fun _ => 1) theta) =
      ((Finset.univ.filter (fun x => v x = 0)).card : ℂ) := by
  have hi (x : ι) : Integrable (fun theta : UnitAddTorus d => mFourier (v x) theta) :=
    (mFourier (v x)).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have he (x : ι) : (∫ theta : UnitAddTorus d, mFourier (v x) theta) =
      if v x = 0 then (1 : ℂ) else 0 := by
    simpa only [mFourier_zero, ContinuousMap.one_apply, map_one, mul_one] using integral_pair (v x) 0
  simp only [polynomial, one_mul]
  rw [integral_finsetSum _ (fun x _ => hi x)]
  simp only [he, Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro x hx
  split_ifs <;> norm_num

end
end RiemannGaussian.VinogradovSignedComplement

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovCongruencingStep

/-!
# Complete support and signed block selection for conditioning

Finite selection keeps every original signed frequency and its exact
complement. The class support may include variables from both sides of a
moment equation. Small supports are covered by literal sets of k-1 residue
classes, whose total number is the exact binomial coefficient. The original
singular collision count is bounded by a sum of actual restricted torus
energies, with all complete frequencies retained within each restriction.

These are the finite support ingredients for the conditioning process in
Wooley (2012), Section 5. Their actual mixed-moment application and explicit
singular bound are in `VinogradovSingularConditioning`.
-/

namespace RiemannGaussian.VinogradovConditioningSupport
noncomputable section
open scoped Classical BigOperators
open VinogradovResidueEnergy VinogradovResidueMoment
open UnitAddTorus MeasureTheory VinogradovPartitionEnergy VinogradovShiftedMoment
open scoped ComplexConjugate
/-- Use the original normalized circle Haar measure. -/
local instance unitCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
/-- The original circle Haar measure has mass one. -/
local instance unitCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Select positions with distinct classes whenever the full attained class support is large enough. -/
theorem select_distinct_classes {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    {k : ℕ} (c : ι → κ) (hk : k ≤ (Finset.univ.image c).card) :
    ∃ e : Fin k ↪ ι, Function.Injective (c ∘ e) := by
  obtain ⟨f, hf⟩ := Function.Embedding.exists_of_card_le_finset
    (α := Fin k) (by simpa only [Fintype.card_fin] using hk)
  have hex (j : Fin k) : ∃ i, c i = f j := by
    have hj := hf (Set.mem_range_self j)
    simpa only [Finset.mem_coe, Finset.mem_image, Finset.mem_univ, true_and] using hj
  choose g hg using hex
  have hgI : Function.Injective g := by
    intro i j hij
    apply f.injective
    rw [← hg i, ← hg j, hij]
  refine ⟨⟨g, hgI⟩, ?_⟩
  intro i j hij
  apply f.injective
  simpa only [Function.comp_apply, Function.Embedding.coeFn_mk, hg] using hij

/-- Extract an actual conditioned block from any original residue family with enough distinct quotient digits. -/
theorem select_conditioned_block {ι : Type*} [Fintype ι] {p k b eta X : ℕ}
    (z : ι → ResidueWindow (p ^ b) eta X)
    (hk : k ≤ (Finset.univ.image (fun i =>
      ((((z i).val.val + 1) / p ^ b : ℕ) : ZMod p))).card) :
    ∃ e : Fin k ↪ ι, ∃ x : ConditionedWindow p k b eta X,
      ∀ j, x.val j = (z (e j)).val := by
  obtain ⟨e, he⟩ := select_distinct_classes _ hk
  refine ⟨e, ⟨fun j => (z (e j)).val, fun j => (z (e j)).property, he⟩, ?_⟩
  intro j
  rfl

/-- Retain the exact full signed frequency as the selected block plus its original signed complement. -/
theorem selected_frequency_eq_add_complement {ι : Type*} [Fintype ι] {p k b eta X : ℕ}
    (z : ι → ResidueWindow (p ^ b) eta X) (colour : ι → Bool)
    (e : Fin k ↪ ι) (x : ConditionedWindow p k b eta X)
    (hx : ∀ j, x.val j = (z (e j)).val) :
    (fun a : Fin k => ∑ i, VinogradovSignedCongruence.sign (colour i) *
      ((z i).val.val + 1 : ℤ) ^ (a.val + 1)) =
    VinogradovProductEnergy.blockFrequency (fun j => colour (e j)) x +
      (fun a => ∑ i ∈ (Finset.univ.map e)ᶜ,
        VinogradovSignedCongruence.sign (colour i) *
          ((z i).val.val + 1 : ℤ) ^ (a.val + 1)) := by
  funext a
  simp only [Pi.add_apply, VinogradovProductEnergy.blockFrequency, hx]
  have he := Finset.sum_add_sum_compl (Finset.univ.map e)
    (fun i => VinogradovSignedCongruence.sign (colour i) *
      ((z i).val.val + 1 : ℤ) ^ (a.val + 1))
  simpa only [Finset.sum_map, Function.Embedding.coeFn_mk] using he.symm

/-- All literal sets of k-1 quotient-digit classes for the nonzero base. -/
def smallPalettes (p k : ℕ) [NeZero p] : Finset (Finset (ZMod p)) :=
  (Finset.univ : Finset (ZMod p)).powersetCard (k - 1)

/-- The complete class-set family has exactly the binomial cardinality. -/
theorem smallPalettes_card (p k : ℕ) [NeZero p] :
    (smallPalettes p k).card = p.choose (k - 1) := by
  simp [smallPalettes]

/-- Either the original family supplies a conditioned block or all its digits lie in one retained small class set. -/
theorem extract_or_small_palette {ι : Type*} [Fintype ι] {p k b eta X : ℕ} [NeZero p]
    (hkp : k ≤ p) (z : ι → ResidueWindow (p ^ b) eta X) :
    (∃ e : Fin k ↪ ι, ∃ x : ConditionedWindow p k b eta X,
      ∀ j, x.val j = (z (e j)).val) ∨
    ∃ S ∈ smallPalettes p k, ∀ i,
      ((((z i).val.val + 1) / p ^ b : ℕ) : ZMod p) ∈ S := by
  let c : ι → ZMod p := fun i => (((z i).val.val + 1) / p ^ b : ℕ)
  by_cases hk : k ≤ (Finset.univ.image c).card
  · exact Or.inl (select_conditioned_block z hk)
  · right
    have hc : (Finset.univ.image c).card ≤ k - 1 := by omega
    have hp : k - 1 ≤ (Finset.univ : Finset (ZMod p)).card := by
      simpa only [Finset.card_univ, ZMod.card] using (Nat.sub_le k 1).trans hkp
    obtain ⟨S, hsub, _, hcard⟩ := Finset.exists_subsuperset_card_eq
      (Finset.subset_univ (Finset.univ.image c)) hc hp
    refine ⟨S, ?_, fun i => hsub (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)⟩
    simp only [smallPalettes, Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ S, hcard⟩

/-- Cover original solutions with small complete class support by their actual class-set restrictions. -/
theorem small_support_count_le_palette_sum {ι : Type*} [Fintype ι]
    {p k : ℕ} [NeZero p] (hkp : k ≤ p)
    (R : ι → Prop) (support : ι → Finset (ZMod p)) :
    (Finset.univ.filter (fun x => R x ∧ (support x).card < k)).card ≤
      ∑ S ∈ smallPalettes p k,
        (Finset.univ.filter (fun x => R x ∧ support x ⊆ S)).card := by
  have hsub : (Finset.univ.filter (fun x => R x ∧ (support x).card < k)) ⊆
      (smallPalettes p k).biUnion (fun S => Finset.univ.filter (fun x => R x ∧ support x ⊆ S)) := by
    intro x hx
    obtain ⟨hR, hc⟩ := (Finset.mem_filter.mp hx).2
    have hp : k - 1 ≤ (Finset.univ : Finset (ZMod p)).card := by
      simpa only [Finset.card_univ, ZMod.card] using (Nat.sub_le k 1).trans hkp
    obtain ⟨S, hS, _, hcard⟩ := Finset.exists_subsuperset_card_eq
      (Finset.subset_univ (support x)) (by omega : (support x).card ≤ k - 1) hp
    apply Finset.mem_biUnion.mpr
    refine ⟨S, ?_, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hR, hS⟩⟩
    simp only [smallPalettes, Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ S, hcard⟩
  exact (Finset.card_le_card hsub).trans Finset.card_biUnion_le

/-- The actual restricted Fourier energy equals its full collision count, including both restricted variables. -/
theorem restricted_energy_eq_count {ι d : Type*} [Fintype ι] [Fintype d]
    (v : ι → d → ℤ) (P : ι → Prop) :
    (∫ theta : UnitAddTorus d, ‖polynomial v (fun x => if P x then 1 else 0) theta‖ ^ 2) =
      ((Finset.univ.filter (fun xy : ι × ι => v xy.1 = v xy.2 ∧ P xy.1 ∧ P xy.2)).card : ℝ) := by
  apply Complex.ofReal_injective
  simp only [polynomial]
  rw [← weightedShift_zero, weightedShift, Finset.card_filter]
  push_cast
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  by_cases he : v x = v y <;> by_cases hx : P x <;> by_cases hy : P y <;>
    simp [he, hx, hy]

/-- The small union of supports on both sides of each original collision is controlled by actual restricted torus energies. -/
theorem singular_count_le_palette_energy {ι d : Type*} [Fintype ι] [Fintype d]
    {p k : ℕ} [NeZero p] (hkp : k ≤ p)
    (v : ι → d → ℤ) (support : ι → Finset (ZMod p)) :
    ((Finset.univ.filter (fun xy : ι × ι => v xy.1 = v xy.2 ∧
      (support xy.1 ∪ support xy.2).card < k)).card : ℝ) ≤
      ∑ S ∈ smallPalettes p k,
        ∫ theta : UnitAddTorus d,
          ‖polynomial v (fun x => if support x ⊆ S then 1 else 0) theta‖ ^ 2 := by
  have he := small_support_count_le_palette_sum hkp
    (fun xy : ι × ι => v xy.1 = v xy.2)
    (fun xy => support xy.1 ∪ support xy.2)
  have heR : ((Finset.univ.filter (fun xy : ι × ι => v xy.1 = v xy.2 ∧
      (support xy.1 ∪ support xy.2).card < k)).card : ℝ) ≤
      ∑ S ∈ smallPalettes p k,
        ((Finset.univ.filter (fun xy : ι × ι =>
          v xy.1 = v xy.2 ∧ support xy.1 ∪ support xy.2 ⊆ S)).card : ℝ) := by
    have hr := (Nat.cast_le (α := ℝ)).mpr he
    simp only [Nat.cast_sum] at hr
    convert hr using 1 <;> congr!
  simp_rw [Finset.union_subset_iff] at heR
  apply heR.trans_eq
  apply Finset.sum_congr rfl
  intro S hS
  convert (restricted_energy_eq_count v (fun x => support x ⊆ S)).symm using 1 <;> congr!

end
end RiemannGaussian.VinogradovConditioningSupport

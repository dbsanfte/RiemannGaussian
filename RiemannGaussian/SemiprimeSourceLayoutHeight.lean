/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceLayout
import Mathlib

/-!
# Literal coefficient height of the constructed source layout

The bound follows the actual cleared-defect constraints through injective
universal-head maps, complete-block embeddings, singleton leftovers, and the
owner-fibre pullback. No constructed-row height is assumed in the final theorem.
-/
set_option autoImplicit false
noncomputable section
namespace RiemannGaussian.SemiprimeSourceLayoutHeight
open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open MulticolorTypes
open LayoutPullback LayoutExactBuckets
open RiemannGaussian.SemiprimeSourceLayout
attribute [local instance] Classical.propDecidable

/-- An injective embedding copies one coefficient or inserts zero. -/
theorem row_abs_le_of_injective {I V : Type*} [Fintype I] [DecidableEq V]
    (owner : I → V) (hinj : Function.Injective owner) (a : I → ℤ) (W : ℕ)
    (ha : ∀ i, |a i| ≤ (W : ℤ)) (v : V) : |row owner a v| ≤ (W : ℤ) := by
  classical
  by_cases hv : v ∈ Set.range owner
  · obtain ⟨i, rfl⟩ := hv
    rw [row_apply_injective owner hinj a i]
    exact ha i
  · rw [row_eq_zero owner a v hv]
    simp

/-- Literal owner-fibre sums multiply the entry bound by at most the fibre
cardinality, with no rational basis change or denominator growth. -/
theorem row_abs_le_fibre {I V : Type*} [Fintype I] [DecidableEq V]
    (owner : I → V) (a : I → ℤ) (B W : ℕ)
    (howner : ∀ v, (Finset.univ.filter (fun i => owner i = v)).card ≤ B)
    (ha : ∀ i, |a i| ≤ (W : ℤ)) (v : V) :
    |row owner a v| ≤ ((B * W : ℕ) : ℤ) := by
  classical
  rw [row, ← Finset.sum_filter]
  calc
    |∑ i ∈ Finset.univ.filter (fun i => owner i = v), a i| ≤
        ∑ i ∈ Finset.univ.filter (fun i => owner i = v), |a i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.univ.filter (fun i => owner i = v), (W : ℤ) :=
      Finset.sum_le_sum (fun i _ => ha i)
    _ = ((Finset.univ.filter (fun i => owner i = v)).card : ℤ) * W := by simp
    _ ≤ ((B * W : ℕ) : ℤ) := by
      exact_mod_cast Nat.mul_le_mul_right W (howner v)

/-- The universal joint-to-head map is injective on literal coordinates. -/
theorem jointOwner_injective {r Q : ℕ} (t : Fin Q) (g : Fin r) :
    Function.Injective (LayoutUniversal.jointOwner t g) := by
  intro x y h
  apply Subtype.ext
  exact congrArg (fun z : LayoutUniversal.Head t g => z.val) h

/-- Actual universal constraints inherit the cleared integer defect bound. -/
theorem universal_constraints_abs_le {r Q : ℕ} (A R : ℕ)
    (hAQ : A ≤ Q) (hQ : 1 ≤ Q) (t : Fin Q) (g : Fin r)
    (j : Joint t g (0 : Fin 1)) (v : LayoutUniversal.Head t g) :
    |LayoutUniversal.constraints A R t g j v| ≤ ((2 * (8 * Q) ^ (2 * R) : ℕ) : ℤ) := by
  apply row_abs_le_of_injective (LayoutUniversal.jointOwner t g) (jointOwner_injective t g)
  intro i
  have h := LayoutNumerator.clearedDefect_natAbs_le (0 : Fin 1) t g A R hAQ hQ j i
  rw [← Int.natCast_natAbs]
  exact_mod_cast h

/-- Finite row reindexing in the actual universal layout changes no values. -/
theorem universalLayout_constraints_abs_le {r Q : ℕ} (R : ℕ)
    (hAQ : Subexp.TailInterval.intervalStart r Q R ≤ Q) (hQ : 1 ≤ Q)
    (t : Fin Q) (g : Fin r)
    (j : Fin ((universalLayout r Q R).rowCount t g))
    (v : {u : UniversalType r Q 1 // (universalLayout r Q R).head t u = g}) :
    |(universalLayout r Q R).constraints t g j v| ≤ ((2 * (8 * Q) ^ (2 * R) : ℕ) : ℤ) := by
  change |LayoutUniversal.constraints (Subexp.TailInterval.intervalStart r Q R) R t g
    ((Fintype.equivFin (Joint t g (0 : Fin 1))).symm j) v| ≤ _
  exact universal_constraints_abs_le _ _ hAQ hQ t g _ v

/-- A complete block's head embedding is still injective. -/
theorem embedHead_injective {U I G : Type*} [Fintype U] [DecidableEq U]
    [DecidableEq G] {Q R b : ℕ} {label : I → U}
    (C : Layout.Data (O := ℚ) (G := G) (id : U → U) (id : U → U) Q R)
    (P : BlockPacking.CompleteBlocks label b) (t : Fin Q) (g : G) (j : Fin b) :
    Function.Injective (LayoutBlocks.embedHead C P t g j) := by
  intro x y h
  apply Subtype.ext
  have hp := P.embed.injective (congrArg Subtype.val h)
  exact congrArg Prod.snd hp

/-- Each raw block constraint copies a single universal row, or is a literal
singleton leftover. Rows from different blocks are not added together. -/
theorem block_constraints_abs_le {U I G : Type*} [Fintype U] [DecidableEq U]
    [DecidableEq I] [DecidableEq G] {Q R b : ℕ} {label : I → U}
    (C : Layout.Data (O := ℚ) (G := G) (id : U → U) (id : U → U) Q R)
    (P : BlockPacking.CompleteBlocks label b) (W : ℕ) (hW : 1 ≤ W)
    (hC : ∀ t g j v, |C.constraints t g j v| ≤ (W : ℤ))
    (t : Fin Q) (g : G) (j : LayoutBlocks.RowIndex C P t g)
    (v : {i : I // LayoutBlocks.copyHead C label t i = g}) :
    |LayoutBlocks.constraints C P t g j v| ≤ (W : ℤ) := by
  cases j with
  | inl jk =>
    change |row (LayoutBlocks.embedHead C P t g jk.1) (C.constraints t g jk.2) v| ≤ _
    exact row_abs_le_of_injective _ (embedHead_injective C P t g jk.1) _ W (hC t g jk.2) v
  | inr w =>
    change |(Pi.single w.val (1 : ℤ) : {i : I // LayoutBlocks.copyHead C label t i = g} → ℤ) v| ≤ _
    by_cases hv : v = w.val
    · simp only [Pi.single_apply, hv, ↓reduceIte, abs_one]
      exact_mod_cast hW
    · simp [hv]

/-- The indexed layout's row enumeration preserves every concrete bound. -/
theorem blocks_data_constraints_abs_le {U I E G : Type*} [Fintype U] [DecidableEq U]
    [Fintype I] [DecidableEq I] [DecidableEq G] {Q R b : ℕ} {label : I → U}
    (C : Layout.Data (O := ℚ) (G := G) (id : U → U) (id : U → U) Q R)
    (P : BlockPacking.CompleteBlocks label b) (factor : I → E) (color : E → Fin Q → G)
    (hcolor : ∀ i t, C.color (label i) t = color (factor i) t)
    (W : ℕ) (hW : 1 ≤ W) (hC : ∀ t g j v, |C.constraints t g j v| ≤ (W : ℤ))
    (t : Fin Q) (g : G) (j : Fin ((LayoutBlocks.data C P factor color hcolor).rowCount t g))
    (v : {i : I // (LayoutBlocks.data C P factor color hcolor).head t i = g}) :
    |(LayoutBlocks.data C P factor color hcolor).constraints t g j v| ≤ (W : ℤ) := by
  change |LayoutBlocks.constraints C P t g
    ((Fintype.equivFin (LayoutBlocks.RowIndex C P t g)).symm j) v| ≤ _
  exact block_constraints_abs_le C P W hW hC t g _ v

/-- Restricting owner fibres to a head cannot increase their cardinalities. -/
theorem headOwner_fibre_card_le {I V G : Type*} [Fintype I]
    [DecidableEq V] [DecidableEq G]
    (owner : I → V) (copyHead : I → G) (head : V → G)
    (hhead : ∀ i, copyHead i = head (owner i)) (B : ℕ)
    (howner : ∀ v, (Finset.univ.filter (fun i => owner i = v)).card ≤ B)
    (g : G) (v : {v : V // head v = g}) :
    (Finset.univ.filter (fun i : {i : I // copyHead i = g} =>
      LayoutHeadPullback.headOwner owner copyHead head hhead g i = v)).card ≤ B := by
  let f : {i : {i : I // copyHead i = g} //
      LayoutHeadPullback.headOwner owner copyHead head hhead g i = v} →
      {i : I // owner i = v.val} := fun i => ⟨i.val.val, congrArg Subtype.val i.property⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : {i : I // owner i = v.val} => z.val) h
  have hc := Fintype.card_le_of_injective f hf
  have hb : Fintype.card {i : I // owner i = v.val} ≤ B := by
    simpa only [Fintype.card_subtype] using howner v.val
  simpa only [Fintype.card_subtype] using hc.trans hb

/-- Actual original-variable constraints are sums over only the bounded
owner head fibre, not arbitrary sums over all copies or all rows. -/
theorem pullback_constraints_abs_le {I V E G : Type*} [Fintype I] [DecidableEq I]
    [Fintype V] [DecidableEq V] [DecidableEq G] {Q R : ℕ}
    (owner : I → V) (factor : I → E) (head : Fin Q → V → G)
    (C : Layout.Data (O := ℚ) (G := G) (id : I → I) factor Q R)
    (hhead : ∀ t i, C.head t i = head t (owner i)) (B W : ℕ)
    (howner : ∀ v, (Finset.univ.filter (fun i => owner i = v)).card ≤ B)
    (hC : ∀ t g j v, |C.constraints t g j v| ≤ (W : ℤ))
    (t : Fin Q) (g : G)
    (j : Fin ((LayoutHeadPullback.pullback owner factor head C hhead).rowCount t g))
    (v : {v : V // (LayoutHeadPullback.pullback owner factor head C hhead).head t v = g}) :
    |(LayoutHeadPullback.pullback owner factor head C hhead).constraints t g j v| ≤
      ((B * W : ℕ) : ℤ) := by
  change |row (LayoutHeadPullback.headOwner owner (C.head t) (head t) (hhead t) g)
    (C.constraints t g j) v| ≤ _
  exact row_abs_le_fibre _ _ B W
    (headOwner_fibre_card_le owner (C.head t) (head t) (hhead t) B howner g)
    (hC t g j) v

/-- Literal coefficient height of the ACTUALLY BUILT layout. Only public
owner-fibre, node-count and source-interval bounds are inputs; no constructed
row-height hypothesis appears here. -/
theorem builtLayout_constraints_abs_le {I V E : Type} [Fintype I] [DecidableEq I]
    [Fintype V] [DecidableEq V] [DecidableEq E]
    {r Q : ℕ} (owner : I → V) (factor : I → E)
    (en : Enumerations I V E r Q) (ε : ℚ) (R B : ℕ)
    (howner : ∀ v, (Finset.univ.filter (fun i => owner i = v)).card ≤ B)
    (hQ : 1 ≤ Q) (hAQ : Subexp.TailInterval.intervalStart r Q R ≤ Q)
    (t : Fin Q) (g : Fin r)
    (j : Fin ((builtLayout owner factor en ε R).rowCount t g))
    (v : {v : V // (builtLayout owner factor en ε R).head t v = g}) :
    |(builtLayout owner factor en ε R).constraints t g j v| ≤
      ((B * 2 * (8 * Q) ^ (2 * R) : ℕ) : ℤ) := by
  let pack := searchedPacking owner factor en ε
  let words := searchedWords owner factor en ε
  let C := universalLayout r Q R
  let D := LayoutBlocks.data C pack.completeBlocks factor (fun e => words (.inr e)) (by intro i t; rfl)
  have hW : 1 ≤ 2 * (8 * Q) ^ (2 * R) := by
    have hp : 1 ≤ (8 * Q) ^ (2 * R) := Nat.one_le_pow _ _ (by omega)
    omega
  have hC : ∀ t g j v, |C.constraints t g j v| ≤ ((2 * (8 * Q) ^ (2 * R) : ℕ) : ℤ) :=
    universalLayout_constraints_abs_le R hAQ hQ
  have hD : ∀ t g j v, |D.constraints t g j v| ≤ ((2 * (8 * Q) ^ (2 * R) : ℕ) : ℤ) :=
    blocks_data_constraints_abs_le C pack.completeBlocks factor (fun e => words (.inr e))
      (by intro i t; rfl) _ hW hC
  have h := pullback_constraints_abs_le owner factor (fun t v => words (.inl v) t) D
    (by intro t i; rfl) B _ howner hD t g j v
  simpa [builtLayout, D, C, pack, words, Nat.mul_assoc] using h

/-- Usual source spectral ranges discharge the interval condition too. -/
theorem builtLayout_constraints_abs_le_of_range {I V E : Type} [Fintype I] [DecidableEq I]
    [Fintype V] [DecidableEq V] [DecidableEq E]
    {r Q : ℕ} (owner : I → V) (factor : I → E)
    (en : Enumerations I V E r Q) (ε : ℚ) (R B : ℕ)
    (howner : ∀ v, (Finset.univ.filter (fun i => owner i = v)).card ≤ B)
    (hr : 2 ≤ r) (hR : 4 ≤ R) (hsize : 4 * R ≤ Q)
    (t : Fin Q) (g : Fin r)
    (j : Fin ((builtLayout owner factor en ε R).rowCount t g))
    (v : {v : V // (builtLayout owner factor en ε R).head t v = g}) :
    |(builtLayout owner factor en ε R).constraints t g j v| ≤
      ((B * 2 * (8 * Q) ^ (2 * R) : ℕ) : ℤ) := by
  have hAQ := Subexp.TailInterval.intervalStart_end_le hr hR hsize
  exact builtLayout_constraints_abs_le owner factor en ε R B howner (by omega) (by omega) t g j v

/-- Constructor-facing height API, in public-parameter/owner-bound order. -/
theorem builtLayout_height {I V E : Type} [Fintype I] [DecidableEq I]
    [Fintype V] [DecidableEq V] [DecidableEq E]
    {r Q : ℕ} (owner : I → V) (factor : I → E)
    (en : Enumerations I V E r Q) (ε : ℚ) (R B : ℕ)
    (hQ : 1 ≤ Q) (hA : Subexp.TailInterval.intervalStart r Q R ≤ Q)
    (hB : ∀ v, (Finset.univ.filter (fun i => owner i = v)).card ≤ B)
    (t : Fin Q) (g : Fin r)
    (j : Fin ((builtLayout owner factor en ε R).rowCount t g))
    (v : {v : V // (builtLayout owner factor en ε R).head t v = g}) :
    |(builtLayout owner factor en ε R).constraints t g j v| ≤
      ((B * 2 * (8 * Q) ^ (2 * R) : ℕ) : ℤ) :=
  builtLayout_constraints_abs_le owner factor en ε R B hB hQ hA t g j v

end RiemannGaussian.SemiprimeSourceLayoutHeight

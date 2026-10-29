/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimePaidConstraintCache
import RiemannGaussian.SemiprimeMaterializedSourcePullback

/-! # Integer constraint rows from acquired packing addresses
The runtime uses cached universal numerators and literal block addresses. It
does not invoke the old inverse-packing or uninstrumented numerator functions.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimePaidConstraintRows
open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT
open MulticolorTypes Subexp.ConstructivePacking SqrtLog
open SemiprimeMaterializedSourceUniversal
open SemiprimeMaterializedSourcePullback (Addresses address packingAddresses address_packing address_work)
variable {I : Type} [DecidableEq I] {r Q : ℕ}

/-- Original padded row addresses, using literal natural block IDs. -/
abbrev Index (I : Type) (r Q : ℕ) := (ℕ × UniversalType r Q 1) ⊕ I

/-- One actual copy-space constraint from the immutable packing and universal caches. -/
def copy (addresses : Addresses I r Q) (producer : I → Run (UniversalType r Q 1))
    (cache : SemiprimePaidConstraintCache.Cache (r:=r) (Q:=Q)) (t : Fin Q) (g : Fin r)
    (j : Index I r Q) (i : I) : Run ℤ :=
  match j with
  | .inl (b,u) =>
      let addr :=  address i addresses
      match addr.value with
      | none => ⟨0,addr.work+2⟩
      | some (c,y) =>
          if c=b then
            let out := SemiprimePaidConstraintCache.read cache t g u y
            ⟨out.value,addr.work+out.work+3⟩
          else ⟨0,addr.work+3⟩
  | .inr a =>
      let addr :=  address a addresses
      let label := producer a
      ⟨if addr.value=none ∧ label.value.head t=g ∧ i=a then 1 else 0,addr.work+label.work+8⟩

/-- A real block column has a unique universal type in that block. -/
theorem vertexAt_injective (P : PackingData I (UniversalType r Q 1))
    (b : Fin P.blockCount) : Function.Injective (P.vertexAt b) := by
  intro u y h
  have he : P.completeBlocks.embed (b,u)=P.completeBlocks.embed (b,y) := h
  exact congrArg Prod.snd (P.completeBlocks.embed.injective he)

/-- An uncovered incidence contributes no complete-block row entry. -/
theorem old_copy_none (P : PackingData I (UniversalType r Q 1))
    (head : UniversalType r Q 1 → Fin r) (g : Fin r)
    (C : UniversalType r Q 1 → UniversalType r Q 1 → ℤ)
    (b : Fin P.blockCount) (u : UniversalType r Q 1) (i : I) (hi : P.lookup i=none) :
    SemiprimePaddedBlockExecution.copyRow P head g C (.inl (b,u)) i=0 := by
  rw [SemiprimePaddedBlockExecution.copyRow,SemiprimePaddedBlockExecution.integerPullback_eq]
  apply LayoutPullback.row_eq_zero
  rintro ⟨y,hy⟩
  have hh := P.lookup_at b y
  rw [hy,hi] at hh
  cases hh

/-- Block-address equality is exactly the original embedded universal-row pullback. -/
theorem old_copy_at (P : PackingData I (UniversalType r Q 1))
    (head : UniversalType r Q 1 → Fin r) (g : Fin r)
    (C : UniversalType r Q 1 → UniversalType r Q 1 → ℤ)
    (b c : Fin P.blockCount) (u y : UniversalType r Q 1) :
    SemiprimePaddedBlockExecution.copyRow P head g C (.inl (b,u)) (P.vertexAt c y)=
      if c=b then C u y else 0 := by
  rw [SemiprimePaddedBlockExecution.copyRow,SemiprimePaddedBlockExecution.integerPullback_eq]
  by_cases h : c=b
  · subst c
    rw [ite_eq_left rfl]
    exact LayoutPullback.row_apply_injective _ (vertexAt_injective P b) _ y
  · rw [ite_eq_right h]
    apply LayoutPullback.row_eq_zero
    rintro ⟨z,hz⟩
    have he := congrArg P.lookup hz
    rw [P.lookup_at,P.lookup_at] at he
    exact h (congrArg Prod.fst (Option.some.inj he)).symm

/-- Literal Nat block IDs encode the original dependent padded row index. -/
def encode (P : PackingData I (UniversalType r Q 1)) :
    ((Fin P.blockCount × UniversalType r Q 1) ⊕ I) → Index I r Q
  | .inl (b,u) => .inl (b.val,u)
  | .inr i => .inr i

/-- The new cached copy program computes the SAME original padded integer row. -/
theorem copy_value (P : PackingData I (UniversalType r Q 1)) (A R : ℕ)
    (producer : I → Run (UniversalType r Q 1)) (hp : ∀ i, (producer i).value=P.label i)
    (t : Fin Q) (g : Fin r) (j : (Fin P.blockCount × UniversalType r Q 1) ⊕ I) (i : I) :
    (copy (packingAddresses P) producer (SemiprimePaidConstraintCache.acquire A R P.types.values).value
      t g (encode P j) i).value=
      SemiprimePaddedBlockExecution.copyRow P (fun u => u.head t) g
        (SemiprimeUniversalSourceExecution.constraint A R t g) j i := by
  cases j with
  | inl z =>
      rcases z with ⟨b,u⟩
      simp only [encode,copy,address_packing]
      cases hi : P.lookup i with
      | none =>
          simp only [Option.map_none]
          exact (old_copy_none P (fun u => u.head t) g _ b u i hi).symm
      | some z =>
          rcases z with ⟨c,y⟩
          simp only [Option.map_some]
          have he := P.lookup_sound i (c,y) hi
          rw [← he,old_copy_at]
          have hc : c.val=b.val ↔ c=b := Fin.val_inj
          simp only [hc]
          split_ifs
          · exact SemiprimePaidConstraintCache.read_acquire A R P.types.values P.types.complete t g u y
          · rfl
  | inr a =>
      simp only [encode,copy,address_packing,hp,SemiprimePaddedBlockExecution.copyRow,
        Option.map_eq_none_iff]

/-- Every block/leftover entry retains its address, label and universal-read work. -/
theorem copy_work (A R : ℕ) (keys : List (UniversalType r Q 1))
    (addresses : Addresses I r Q) (producer : I → Run (UniversalType r Q 1))
    (B : ℕ) (hp : ∀ i, (producer i).work≤B) (t : Fin Q) (g : Fin r)
    (j : Index I r Q) (i : I) :
    (copy addresses producer (SemiprimePaidConstraintCache.acquire A R keys).value t g j i).work≤
      3*addresses.length+B+9*Q+2*(keys.length*(7*Q+4)+1)+25 := by
  cases j with
  | inl z =>
      rcases z with ⟨b,u⟩
      have ha := address_work i addresses
      unfold copy
      dsimp only
      cases hi : (address i addresses).value with
      | none => dsimp only; omega
      | some z =>
          rcases z with ⟨c,y⟩
          dsimp only
          split_ifs <;> dsimp only
          · have hc := SemiprimePaidConstraintCache.read_acquire_work A R keys t g u y
            omega
          · omega
  | inr a =>
      have ha := address_work a addresses
      have hl := hp a
      simp only [copy]
      omega

/-- The actual original-variable owner pullback, retaining all incidence tests. -/
def source {V : Type} [DecidableEq V] (is : List I) (owner : I → V)
    (addresses : Addresses I r Q) (producer : I → Run (UniversalType r Q 1))
    (cache : SemiprimePaidConstraintCache.Cache (r:=r) (Q:=Q)) (t : Fin Q) (g : Fin r)
    (j : Index I r Q) (v : V) : Run ℤ :=
  sumRuns (fun i =>
    if owner i=v then let out := copy addresses producer cache t g j i; ⟨out.value,out.work+2⟩
    else ⟨0,2⟩) is

/-- Exact owner-fibre agreement with the original complete-block/leftover source matrix. -/
theorem source_value [Fintype I] {V : Type} [DecidableEq V]
    (P : PackingData I (UniversalType r Q 1)) (A R : ℕ) (owner : I → V)
    (producer : I → Run (UniversalType r Q 1)) (hp : ∀ i, (producer i).value=P.label i)
    (t : Fin Q) (g : Fin r) (j : (Fin P.blockCount × UniversalType r Q 1) ⊕ I) (v : V) :
    (source P.vertices.values owner (packingAddresses P) producer
      (SemiprimePaidConstraintCache.acquire A R P.types.values).value t g (encode P j) v).value=
      SemiprimePaddedBlockExecution.sourceRow P owner (fun u => u.head t) g
        (SemiprimeUniversalSourceExecution.constraint A R t g) j v := by
  unfold source
  rw [sumRuns_value,← List.sum_toFinset _ P.vertices.nodup]
  have hu : P.vertices.values.toFinset=Finset.univ := by
    ext i
    simp only [List.mem_toFinset,Finset.mem_univ,iff_true]
    exact P.vertices.complete i
  rw [hu,SemiprimePaddedBlockExecution.sourceRow,SemiprimePaddedBlockExecution.integerPullback_eq]
  unfold LayoutPullback.row
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : owner i=v
  · simp only [ite_eq_left h]
    exact copy_value P A R producer hp t g j i
  · simp only [ite_eq_right h]

theorem source_work {V : Type} [DecidableEq V] (A R : ℕ) (keys : List (UniversalType r Q 1))
    (is : List I) (owner : I → V) (addresses : Addresses I r Q)
    (producer : I → Run (UniversalType r Q 1)) (B : ℕ) (hp : ∀ i, (producer i).work≤B)
    (t : Fin Q) (g : Fin r) (j : Index I r Q) (v : V) :
    (source is owner addresses producer (SemiprimePaidConstraintCache.acquire A R keys).value t g j v).work≤
      is.length*(3*addresses.length+B+9*Q+2*(keys.length*(7*Q+4)+1)+29)+1 := by
  apply sumRuns_work
  intro i _
  have h := copy_work A R keys addresses producer B hp t g j i
  split_ifs <;> dsimp only <;> omega

end RiemannGaussian.SemiprimePaidConstraintRows

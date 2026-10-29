/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimePaidOriginalConstraints
import RiemannGaussian.SemiprimeAcquiredSourceCounter

/-! # Cached original integer family to the actual masked raw design
The runtime reads retained integer entries and head labels. The old searched
matrix appears only in the exact semantic equality theorem.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeCachedRawConstraints
open OAI.Algorithms.SubexponentialSAT
open MulticolorTypes Subexp.ConstructivePacking
open SemiprimeMaterializedSourceUniversal SemiprimeRuntimeDesignAcquisition
variable {n F r Q : ℕ}

/-- Raw designs with one shared original padded row count. -/
def make (head : Fin n → Fin r) (assigned : Fin F → Fin r) (p : ℕ)
    (rows : Fin r → Fin p → Fin n → ℤ) (W : ℕ) : RawDesign n F :=
  ⟨r,head,assigned,fun _ => p,rows,fun _ => W⟩

/-- Exact dependent-record equality from the literal row-index transport. -/
theorem make_congr (h₁ h₂ : Fin n → Fin r) (a₁ a₂ : Fin F → Fin r)
    (p₁ p₂ : ℕ) (C₁ : Fin r → Fin p₁ → Fin n → ℤ) (C₂ : Fin r → Fin p₂ → Fin n → ℤ)
    (W : ℕ) (hh : h₁=h₂) (ha : a₁=a₂) (hp : p₁=p₂)
    (hc : ∀ g j v, C₁ g j v=C₂ g (j.cast hp) v) :
    make h₁ a₁ p₁ C₁ W=make h₂ a₂ p₂ C₂ W := by
  subst p₂
  subst h₂
  subst a₂
  have he : C₁=C₂ := by funext g j v; exact hc g j v
  rw [he]

/-- Head masking is executed before each retained integer-family read. -/
def read {I : Type} (head : Fin n → Fin r)
    (family : SemiprimePaidConstraintAcquisition.Family I r Q)
    (t : Fin Q) (g : Fin r) (j : ℕ) (v : Fin n) : Run ℤ :=
  if head v=g then
    let out := SemiprimePaidOriginalConstraints.read family t.val g.val j v.val
    ⟨out.value,out.work+6⟩
  else ⟨0,6⟩

/-- Pure cached runtime fields; every row uses the explicit head mask. -/
def data {I : Type} (head : Fin n → Fin r) (assigned : Fin F → Fin r)
    (family : SemiprimePaidConstraintAcquisition.Family I r Q) (W : ℕ) (t : Fin Q) :
    RawDesign n F :=
  make head assigned family.indices.length (fun g j v => (read head family t g j.val v).value) W

/-- The actually acquired padded family has exactly the original row names. -/
theorem acquired_indices (arity : Fin F → ℕ)
    (coordinate : (e : Fin F) → Fin (arity e) → Fin n)
    (en : SemiprimeSourceLayout.Enumerations ((e : Fin F) × Fin (arity e)) (Fin n) (Fin F) r Q)
    (eps : ℚ) (R : ℕ) :
    (SemiprimePaidOriginalConstraints.acquire
      (fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2) Sigma.fst en eps R).value.indices=
      (SemiprimeSourceConstraintAcquisition.rowIndices
        (fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2) Sigma.fst en eps).values.map
        (SemiprimePaidConstraintRows.encode (SemiprimeSourceConstraintAcquisition.packing
          (fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2) Sigma.fst en eps)) := by
  let owner := fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2
  let P := SemiprimeFiniteEnumerations.searchPacking owner Sigma.fst en eps
  let producer := SemiprimeMaterializedSourceWords.producer owner Sigma.fst en.wordFirst en.wordTail
    en.terms.values en.indices.values
    (eps*(en.incidences.values.length : ℚ)/(en.types.values.length : ℚ)) ((n : ℚ)/(2*(r : ℚ)))
  have hp := SemiprimeMaterializedOriginalSource.label_value owner Sigma.fst en eps
  change (SemiprimePaidConstraintAcquisition.names en.types.values
    (SemiprimePaidPackingSnapshot.acquire en.incidences.values en.types.values producer.value).value.blocks
      en.incidences.values).value=_
  change (SemiprimePaidConstraintAcquisition.names P.types.values
    (SemiprimePaidPackingSnapshot.acquire P.vertices.values P.types.values producer.value).value.blocks
      P.vertices.values).value=_
  rw [SemiprimePaidPackingSnapshot.acquire_blocks P producer.value hp]
  exact SemiprimePaidConstraintAcquisition.names_packing P

theorem acquired_count (arity : Fin F → ℕ)
    (coordinate : (e : Fin F) → Fin (arity e) → Fin n)
    (en : SemiprimeSourceLayout.Enumerations ((e : Fin F) × Fin (arity e)) (Fin n) (Fin F) r Q)
    (eps : ℚ) (R : ℕ) :
    (SemiprimePaidOriginalConstraints.acquire
      (fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2) Sigma.fst en eps R).value.indices.length=
      (SemiprimeSourceConstraintAcquisition.rowIndices
        (fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2) Sigma.fst en eps).values.length := by
  rw [acquired_indices,List.length_map]

/-- Masked cached entries agree with the old raw matrix on EVERY original column. -/
theorem read_acquire (arity : Fin F → ℕ)
    (coordinate : (e : Fin F) → Fin (arity e) → Fin n)
    (en : SemiprimeSourceLayout.Enumerations ((e : Fin F) × Fin (arity e)) (Fin n) (Fin F) r Q)
    (eps : ℚ) (R : ℕ) (head : Fin n → Fin r) (t : Fin Q)
    (hh : ∀ v, head v=SemiprimeSourceConstraintAcquisition.head
      (fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2) Sigma.fst en eps t v)
    (g : Fin r)
    (j : Fin (SemiprimeSourceConstraintAcquisition.rowIndices
      (fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2) Sigma.fst en eps).values.length)
    (v : Fin n) :
    (read head (SemiprimePaidOriginalConstraints.acquire
      (fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2) Sigma.fst en eps R).value t g j.val v).value=
      SemiprimeSourceConstraintAcquisition.matrix
        (fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2) Sigma.fst en eps R t g j v := by
  unfold read
  rw [hh v]
  split_ifs with hv
  · exact SemiprimePaidOriginalConstraints.read_acquire _ _ en eps R t g j v hv
  · exact (SemiprimeSourceConstraintAcquisition.matrix_not_head _ _ en eps R t g j v hv).symm

variable [NeZero r]

/-- The cached, masked raw design is exactly the former searched raw design. -/
theorem data_eq (arity : Fin F → ℕ)
    (coordinate : (e : Fin F) → Fin (arity e) → Fin n) (eps : ℚ) (R B : ℕ) (t : Fin Q)
    (head : Fin n → Fin r) (assigned : Fin F → Fin r)
    (hh : ∀ v, head v=SemiprimeSourceConstraintAcquisition.head
      (fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2) Sigma.fst
      (SemiprimeFiniteEnumerations.indexed n F r Q arity) eps t v)
    (ha : ∀ e, assigned e=SemiprimeFiniteEnumerations.searchWords
      (fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2) Sigma.fst
      (SemiprimeFiniteEnumerations.indexed n F r Q arity) eps (.inr e) t) :
    data head assigned (SemiprimePaidOriginalConstraints.acquire
      (fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2) Sigma.fst
      (SemiprimeFiniteEnumerations.indexed n F r Q arity) eps R).value
      (SemiprimeAcquiredSourceCounter.measurementBound B Q R) t=
      SemiprimeAcquiredSourceCounter.raw (r:=r) arity coordinate eps R B t := by
  let en := SemiprimeFiniteEnumerations.indexed n F r Q arity
  let owner := fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2
  let family := (SemiprimePaidOriginalConstraints.acquire owner Sigma.fst en eps R).value
  have hp := acquired_count arity coordinate en eps R
  change make head assigned family.indices.length
    (fun g j v => (read head family t g j.val v).value) _ =
    make (SemiprimeSourceConstraintAcquisition.head owner Sigma.fst en eps t)
      (fun e => SemiprimeFiniteEnumerations.searchWords owner Sigma.fst en eps (.inr e) t)
      (SemiprimeSourceConstraintAcquisition.rowIndices owner Sigma.fst en eps).values.length
      (SemiprimeSourceConstraintAcquisition.matrix owner Sigma.fst en eps R t) _
  apply make_congr _ _ _ _ _ _ _ _ _ (funext hh) (funext ha) hp
  intro g j v
  exact read_acquire arity coordinate en eps R head t hh g (j.cast hp) v

omit [NeZero r] in
/-- Each masked access retains its four list scans and its head read/test. -/
theorem read_acquire_work (arity : Fin F → ℕ)
    (coordinate : (e : Fin F) → Fin (arity e) → Fin n)
    (en : SemiprimeSourceLayout.Enumerations ((e : Fin F) × Fin (arity e)) (Fin n) (Fin F) r Q)
    (eps : ℚ) (R : ℕ) (head : Fin n → Fin r) (t : Fin Q) (g : Fin r)
    (j : Fin (SemiprimeSourceConstraintAcquisition.rowIndices
      (fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2) Sigma.fst en eps).values.length)
    (v : Fin n) :
    (read head (SemiprimePaidOriginalConstraints.acquire
      (fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2) Sigma.fst en eps R).value t g j.val v).work≤
      2*(Q+r+(SemiprimeSourceConstraintAcquisition.rowIndices
        (fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2) Sigma.fst en eps).values.length+n)+14 := by
  have h := SemiprimePaidOriginalConstraints.read_acquire_work
    (fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2) Sigma.fst en eps R t g j v
  unfold read
  split_ifs <;> dsimp only <;> omega

omit [NeZero r] in
/-- The actual cached padded row count has a conservative original-input polynomial bound. -/
theorem acquired_count_le (arity : Fin F → ℕ)
    (coordinate : (e : Fin F) → Fin (arity e) → Fin n)
    (en : SemiprimeSourceLayout.Enumerations ((e : Fin F) × Fin (arity e)) (Fin n) (Fin F) r Q)
    (eps : ℚ) (R : ℕ) :
    (SemiprimePaidOriginalConstraints.acquire
      (fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2) Sigma.fst en eps R).value.indices.length≤
      en.incidences.values.length*en.types.values.length+en.incidences.values.length := by
  let P := SemiprimeSourceConstraintAcquisition.packing
    (fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2) Sigma.fst en eps
  rw [acquired_count]
  change (SemiprimePaddedBlockExecution.indices P).values.length≤_
  rw [SemiprimePaddedBlockExecution.indices_length]
  have hb := SemiprimePaidConstraintAcquisition.blocks_le P
  change P.blockCount*P.types.values.length+P.vertices.values.length≤
    P.vertices.values.length*P.types.values.length+P.vertices.values.length
  exact Nat.add_le_add_right (Nat.mul_le_mul_right _ hb) _

end RiemannGaussian.SemiprimeCachedRawConstraints

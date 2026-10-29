/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimePaidConstraintAcquisition
import RiemannGaussian.SemiprimeMaterializedOriginalSource

/-! # Original searched network to stored integer constraints
The actual searched labels, packing and universal numerators are constructed
internally. There is no label, row, or row-acquisition budget oracle.
Finite-enumeration generation and primitive bit refinements remain separate.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimePaidOriginalConstraints
open OAI.Algorithms.SubexponentialSAT
open MulticolorTypes Subexp.ConstructivePacking
open SemiprimeMaterializedSourceUniversal
variable {I E : Type} [Fintype I] [DecidableEq I] [DecidableEq E] {n r Q : ℕ}

/-- Acquire the original computed label search, then all original integer rows. -/
def acquire (owner : I → Fin n) (factor : I → E)
    (en : SemiprimeSourceLayout.Enumerations I (Fin n) E r Q) (eps : ℚ) (R : ℕ) :
    Run (SemiprimePaidConstraintAcquisition.Family I r Q) :=
  let x := eps*(en.incidences.values.length : ℚ)/(en.types.values.length : ℚ)
  let y := (n : ℚ)/(2*(r : ℚ))
  let producer := SemiprimeMaterializedSourceWords.producer owner factor en.wordFirst en.wordTail
    en.terms.values en.indices.values x y
  let out := SemiprimePaidConstraintAcquisition.acquire (Subexp.TailInterval.intervalStart r Q R) R
    en.incidences.values owner en.types.values producer.value
  ⟨out.value,producer.work+out.work+en.incidences.values.length+en.types.values.length+25⟩

/-- Exact original padded row order after the actual deterministic source search. -/
theorem acquire_entries (owner : I → Fin n) (factor : I → E)
    (en : SemiprimeSourceLayout.Enumerations I (Fin n) E r Q) (eps : ℚ) (R : ℕ) :
    (acquire owner factor en eps R).value.entries=
      (List.finRange Q).map (fun t => (List.finRange r).map (fun g =>
        (SemiprimeSourceConstraintAcquisition.rowIndices owner factor en eps).values.map
          (fun j => (List.finRange n).map (SemiprimePaddedBlockExecution.sourceRow
            (SemiprimeSourceConstraintAcquisition.packing owner factor en eps) owner
            (fun u => u.head t) g
            (SemiprimeUniversalSourceExecution.constraint (Subexp.TailInterval.intervalStart r Q R) R t g) j)))) :=
  SemiprimePaidConstraintAcquisition.acquire_entries
    (SemiprimeFiniteEnumerations.searchPacking owner factor en eps)
    (Subexp.TailInterval.intervalStart r Q R) R owner _
    (SemiprimeMaterializedOriginalSource.label_value owner factor en eps)

/-- Every scalar/list work term depends only on the original network dimensions. -/
def budget (M n A D T N Q R start r blocks : ℕ) : ℕ :=
  SemiprimeMaterializedSourceWords.producerBudget A T N Q+
  SemiprimePaidConstraintAcquisition.budget start R M n D (4*N+6*(N+1)^2+7) Q r blocks+M+D+25

/-- Closed label-search and complete integer-row acquisition ledger. -/
theorem acquire_work (owner : I → Fin n) (factor : I → E)
    (en : SemiprimeSourceLayout.Enumerations I (Fin n) E r Q) (eps : ℚ) (R : ℕ) :
    (acquire owner factor en eps R).work≤
      budget en.incidences.values.length n en.wordTail.length en.types.values.length
        en.terms.values.length en.indices.values.length Q R
        (Subexp.TailInterval.intervalStart r Q R) r
        (SemiprimeFiniteEnumerations.searchPacking owner factor en eps).blockCount := by
  let x := eps*(en.incidences.values.length : ℚ)/(en.types.values.length : ℚ)
  let y := (n : ℚ)/(2*(r : ℚ))
  let producer := SemiprimeMaterializedSourceWords.producer owner factor en.wordFirst en.wordTail
    en.terms.values en.indices.values x y
  have hp := SemiprimeMaterializedSourceWords.producer_work owner factor en.wordFirst en.wordTail
    en.terms.values en.indices.values x y
  have ho := SemiprimePaidConstraintAcquisition.acquire_work
    (SemiprimeFiniteEnumerations.searchPacking owner factor en eps)
    (Subexp.TailInterval.intervalStart r Q R) R owner producer.value
    (SemiprimeMaterializedOriginalSource.label_value owner factor en eps)
    (4*en.indices.values.length+6*(en.indices.values.length+1)^2+7)
    (SemiprimeMaterializedSourceWords.producer_label_work owner factor en.wordFirst en.wordTail
      en.terms.values en.indices.values x y)
  unfold acquire budget
  dsimp only
  exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add hp ho) _) _) 25

/-- Four real finite-list scans read one stored original-coordinate entry. -/
def read (family : SemiprimePaidConstraintAcquisition.Family I r Q)
    (t g j v : ℕ) : Run ℤ :=
  let node := SemiprimePaidConstraintCache.getRun family.entries t
  let head := SemiprimePaidConstraintCache.getRun (node.value.getD []) g
  let row := SemiprimePaidConstraintCache.getRun (head.value.getD []) j
  let entry := SemiprimePaidConstraintCache.getRun (row.value.getD []) v
  ⟨entry.value.getD 0,node.work+head.work+row.work+entry.work+4⟩

omit [Fintype I] [DecidableEq I] [DecidableEq E] in
/-- Reading a well-indexed stored map uses the intended original index. -/
theorem getRun_map {α β : Type*} (xs : List α) (f : α → β) (j : Fin xs.length) :
    (SemiprimePaidConstraintCache.getRun (xs.map f) j.val).value=some (f (xs.get j)) := by
  rw [SemiprimePaidConstraintCache.getRun_value,List.getElem?_map,
    List.getElem?_eq_getElem j.isLt]
  rfl

omit [Fintype I] [DecidableEq I] [DecidableEq E] in
/-- A stored finite-coordinate map is read by its literal coordinate. -/
theorem getRun_fin {α : Type*} {k : ℕ} (f : Fin k → α) (j : Fin k) :
    (SemiprimePaidConstraintCache.getRun ((List.finRange k).map f) j.val).value=some (f j) := by
  rw [SemiprimePaidConstraintCache.getRun_value,List.getElem?_map,
    List.getElem?_eq_getElem (by simp),List.getElem_finRange]
  rfl

/-- On every original head column the stored entry is exactly the old integer matrix. -/
theorem read_acquire (owner : I → Fin n) (factor : I → E)
    (en : SemiprimeSourceLayout.Enumerations I (Fin n) E r Q) (eps : ℚ) (R : ℕ)
    (t : Fin Q) (g : Fin r)
    (j : Fin (SemiprimeSourceConstraintAcquisition.rowIndices owner factor en eps).values.length)
    (v : Fin n) (hv : SemiprimeSourceConstraintAcquisition.head owner factor en eps t v=g) :
    (read (acquire owner factor en eps R).value t.val g.val j.val v.val).value=
      SemiprimeSourceConstraintAcquisition.matrix owner factor en eps R t g j v := by
  unfold read
  dsimp only
  rw [acquire_entries,getRun_fin,Option.getD_some,getRun_fin,Option.getD_some,
    getRun_map,Option.getD_some,getRun_fin,Option.getD_some]
  unfold SemiprimeSourceConstraintAcquisition.matrix
  rw [ite_eq_left hv]
  rfl

/-- The actual four scans have a linear cell-visit bound in the stored dimensions. -/
theorem read_acquire_work (owner : I → Fin n) (factor : I → E)
    (en : SemiprimeSourceLayout.Enumerations I (Fin n) E r Q) (eps : ℚ) (R : ℕ)
    (t : Fin Q) (g : Fin r)
    (j : Fin (SemiprimeSourceConstraintAcquisition.rowIndices owner factor en eps).values.length)
    (v : Fin n) :
    (read (acquire owner factor en eps R).value t.val g.val j.val v.val).work≤
      2*(Q+r+(SemiprimeSourceConstraintAcquisition.rowIndices owner factor en eps).values.length+n)+8 := by
  let family := (acquire owner factor en eps R).value
  let node := SemiprimePaidConstraintCache.getRun family.entries t.val
  let head := SemiprimePaidConstraintCache.getRun (node.value.getD []) g.val
  let row := SemiprimePaidConstraintCache.getRun (head.value.getD []) j.val
  have ht := SemiprimePaidConstraintCache.getRun_work family.entries t.val
  have hg := SemiprimePaidConstraintCache.getRun_work (node.value.getD []) g.val
  have hj := SemiprimePaidConstraintCache.getRun_work (head.value.getD []) j.val
  have hv := SemiprimePaidConstraintCache.getRun_work (row.value.getD []) v.val
  have hn : family.entries.length=Q := by
    rw [acquire_entries,List.length_map,List.length_finRange]
  have hgl : (node.value.getD []).length=r := by
    dsimp only [node,family]
    rw [acquire_entries,getRun_fin,Option.getD_some,List.length_map,List.length_finRange]
  have hjl : (head.value.getD []).length=
      (SemiprimeSourceConstraintAcquisition.rowIndices owner factor en eps).values.length := by
    dsimp only [head,node,family]
    rw [acquire_entries,getRun_fin,Option.getD_some,getRun_fin,Option.getD_some,List.length_map]
  have hvl : (row.value.getD []).length=n := by
    dsimp only [row,head,node,family]
    rw [acquire_entries,getRun_fin,Option.getD_some,getRun_fin,Option.getD_some,
      getRun_map,Option.getD_some,List.length_map,List.length_finRange]
  rw [hn] at ht
  rw [hgl] at hg
  rw [hjl] at hj
  rw [hvl] at hv
  change node.work≤2*Q+1 at ht
  change head.work≤2*r+1 at hg
  change row.work≤2*(SemiprimeSourceConstraintAcquisition.rowIndices owner factor en eps).values.length+1 at hj
  change node.work+head.work+row.work+
    (SemiprimePaidConstraintCache.getRun (row.value.getD []) v.val).work+4≤_
  omega

/-- Closed fixed-polynomial scalar/list envelope for the original searched family. -/
def polynomial (M n A D T N Q R start r : ℕ) : ℕ :=
  SemiprimeMaterializedSourceWords.producerBudget A T N Q+
  SemiprimePaidConstraintAcquisition.polynomial start R M n D (4*N+6*(N+1)^2+7) Q r+M+D+25

/-- No packing-size or label-work advice remains in the native acquisition envelope. -/
theorem acquire_work_native (owner : I → Fin n) (factor : I → E)
    (en : SemiprimeSourceLayout.Enumerations I (Fin n) E r Q) (hr : 2≤r) (eps : ℚ) (R : ℕ) :
    (acquire owner factor en eps R).work≤
      polynomial en.incidences.values.length n en.wordTail.length en.types.values.length
        en.terms.values.length en.indices.values.length Q R
        (Subexp.TailInterval.intervalStart r Q R) r := by
  apply (acquire_work owner factor en eps R).trans
  have hD : 2^(2*Q)≤en.types.values.length := by
    rw [en.types.length_eq_card,card_universalType]
    simpa only [show Q*(1+1)=2*Q by omega] using Nat.pow_le_pow_left hr (2*Q)
  have hb := SemiprimePaidConstraintAcquisition.blocks_le
    (SemiprimeFiniteEnumerations.searchPacking owner factor en eps)
  have hc := SemiprimePaidConstraintAcquisition.budget_polynomial
    (Subexp.TailInterval.intervalStart r Q R) R en.incidences.values.length n en.types.values.length
    (4*en.indices.values.length+6*(en.indices.values.length+1)^2+7) Q r
    (SemiprimeFiniteEnumerations.searchPacking owner factor en eps).blockCount hD hb
  unfold budget polynomial
  omega

end RiemannGaussian.SemiprimePaidOriginalConstraints

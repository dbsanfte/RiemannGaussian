/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootPhaseFreshRecordsCleanup
import RiemannGaussian.SemiprimeD1StackRootPhaseFreshRecordsView
/-! # Exact cleanup return retains immutable input heap/counter and literal root header -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootPhaseFreshRecordsCleanView
open SemiprimeD1StackRootPhaseFreshRecords SemiprimeD1StackRootPhaseFreshRecordsEncoding
open SemiprimeD1StackRootPhaseFreshRecordsCleanup SemiprimeD1StackRootPhaseFreshRecordsView
/-- Full physical cleanup predicate after all145 literal drain sites. -/
theorem cleared_full (bank:Stack→List Bool) (k:Stack) :
    cleared bank 145 k=(@ite (List Bool) (k∈roles) (Classical.propDecidable _) [] (bank k)) :=by
  classical
  change (if k∈roles.take 145 then [] else bank k)=_
  rw [List.take_of_length_le (show roles.length ≤ 145 by rw [roles_length])]
/-- Actual complete cleanup retains sourceheap/counter/header and every caller
word except pointer/currentrecord/newref. All private roles and shadows are EMPTY. -/
theorem cleared_view (root:R.Stack→List Bool) (q:Q.Stack→List Bool)
    (reader currentRecord hp cn ref hist out:List Bool) :
    cleared (view root q (work reader currentRecord hp cn ref hist out)) 145=
      view root (SemiprimeD1StackPhaseCacheFresh.input (q I.sourceHeap) (q I.sourceCounter) [] (q I.oldHeader))
        (work reader [] hp cn [] hist out) :=by
  classical
  funext k
  rw [cleared_full]
  rcases k with k|k
  · change (if rootStack k∈roles then [] else view root q (work reader currentRecord hp cn ref hist out) (rootStack k))=_
    rw [ite_eq_right (root_not_mem k)]
    rcases k with k|k
    · rfl
    · rcases k with k|k
      · rfl
      · cases k <;> rfl
  · rcases k with k|k
    · by_cases hk:k=I.oldHeader
      · subst k
        rw [ite_eq_right (by intro h;exact ((private_mem _).mp h) rfl)]
        rfl
      · change (if cachePrivate k∈roles then [] else view root q (work reader currentRecord hp cn ref hist out) (cachePrivate k))=_
        rw [ite_eq_left ((private_mem k).mpr hk)]
        change []=privateCache (SemiprimeD1StackPhaseCacheFresh.input (q I.sourceHeap) (q I.sourceCounter) [] (q I.oldHeader)) k
        rw [private_input]
        simp only [hk,ite_false]
    · change (if aux k∈roles then [] else auxView q (work reader currentRecord hp cn ref hist out) k)=_
      simp only [aux_mem]
      cases k <;> simp [view,data,auxView,work,SemiprimeD1StackPhaseCacheFresh.input,
        SemiprimeD1StackPhaseCacheFresh.data,SemiprimeD1StackHeapRead.input,
        SemiprimeD1StackRootPhaseFreshRecordsInventory.sourceReference,
        SemiprimeD1StackPhaseCacheFresh.restoreStack,SemiprimeD1StackPhaseBankRestore.heapStack]
end RiemannGaussian.SemiprimeD1StackRootPhaseFreshRecordsCleanView

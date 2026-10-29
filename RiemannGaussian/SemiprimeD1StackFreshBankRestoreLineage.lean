/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackHeapReadBounds
/-! # Actual allocator histories and issued chronological references
These proof-side histories contain genuine executions of the literal allocator.
They do not execute phase arithmetic or reconstruct any stored coefficient word.
-/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackFreshBankRestoreLineage
namespace H
export SemiprimeD1StackHeapReadBounds (History Issued)
end H
namespace A
export SemiprimeD1StackHeapAllocate (heapBytes heapBytes_append allocate_run done)
end A
/-- Every chronological byte history is built by the real append-only allocator. -/
theorem history (rows:List (List Bool)) :H.History rows (A.heapBytes rows) (List.replicate rows.length true):=by
  induction rows using List.reverseRecOn with
  | nil=>exact SemiprimeD1StackHeapReadBounds.History.empty
  | append_singleton rows word ih=>
    have h:=SemiprimeD1StackHeapReadBounds.History.allocate ih word
    rw [A.heapBytes_append]
    simpa only [List.length_append,List.length_cons,List.length_nil,List.replicate_succ] using h
/-- The newest reference is read from the actual allocator result's pointer role. -/
theorem issued_last (rows:List (List Bool)) (word:List Bool):
    H.Issued (rows++[word]) (List.replicate rows.length true):=by
  have h:=SemiprimeD1StackHeapReadBounds.Issued.fresh (history rows) word _
    (A.allocate_run word (A.heapBytes rows) (List.replicate rows.length true) none)
  exact h
/-- Every issued ordinal remains valid after all subsequent physical allocations. -/
theorem issued (rows:List (List Bool)) :∀i:Fin rows.length,H.Issued rows (List.replicate i.val true):=by
  induction rows using List.reverseRecOn with
  | nil=>intro i;exact Fin.elim0 i
  | append_singleton rows word ih=>
    intro i
    by_cases hi:i.val<rows.length
    · exact SemiprimeD1StackHeapReadBounds.Issued.keep (ih ⟨i.val,hi⟩) word
    · have hx:=i.isLt
      simp only [List.length_append,List.length_cons,List.length_nil] at hx
      have he:i.val=rows.length:=by omega
      rw [he]
      exact issued_last rows word
end RiemannGaussian.SemiprimeD1StackFreshBankRestoreLineage

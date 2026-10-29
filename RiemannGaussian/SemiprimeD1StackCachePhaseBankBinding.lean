/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackCachePhaseBankReady
import RiemannGaussian.SemiprimeD1StackCachePhaseBankStopped
import RiemannGaussian.SemiprimeD1StackCachePhaseBankClearEncoding
/-! # Exact shared heap/counter retention and cleared next-phase input
Generic full-bank bridges precede any original-N instantiation, preventing
native graph/context normalization from entering the actual source handoff.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackCachePhaseBankBinding
open SemiprimeD1StackCachePhaseBank SemiprimeD1StackCachePhaseBankClearEncoding
open SemiprimeD1StackCachePhaseBankStopped
/-- Fixed actual heap role in the complete238-role bank. -/
def heapRole:P.Stack:=P.restoreStack (SemiprimeD1StackCachePhase.Restore.heapStack .heap)
/-- Fixed actual counter role in the complete238-role bank. -/
def counterRole:P.Stack:=P.restoreStack (SemiprimeD1StackCachePhase.Restore.heapStack .counter)
/-- Every actually initialized fold word is empty before children/context are acquired. -/
theorem fold_empty (k:SemiprimeD1StackCachePhase.Fold.Stack):
    ((SemiprimeD1StackCachePhase.Fold.initial [] [] []).data k)=[]:=by
  have h:=SemiprimeD1StackCachePhaseStorage.fold_initial_length [] k
  exact List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero h)
/-- Exactly heap/counter are present in the genuinely clean next-phase callee input. -/
theorem input_base (hp cn:List Bool):P.input hp cn [] []=
    (fun k=>if k=heapRole then hp else if k=counterRole then cn else []):=by
  funext k
  rcases k with r|tail
  · rcases r with fresh|h
    · rfl
    · cases h <;> rfl
  · rcases tail with fold|tail
    · exact fold_empty fold
    · rcases tail with blocks|u <;> rfl
/-- Actual physical cleanup yields EXACT the next callee input, without resetting any word by advice. -/
theorem cleared_input (bank:P.Stack→List Bool) (hp cn:List Bool)
    (hh:bank heapRole=hp) (hc:bank counterRole=cn):cleared bank=P.input hp cn [] []:=by
  rw [input_base]
  funext k
  by_cases hk:k=heapRole
  · subst k
    rw [cleared_retained bank heapRole (by decide),ite_eq_left rfl]
    exact hh
  · by_cases hcn:k=counterRole
    · subst k
      rw [cleared_retained bank counterRole (by decide),ite_eq_right hk,ite_eq_left rfl]
      exact hc
    · have hper:persistent k=false:=by
        apply Bool.eq_false_of_not_eq_true
        intro htrue
        rcases (SemiprimeD1StackCachePhaseBankState.persistent_heap k).mp htrue with he|he
        · exact hk (cached_injective he)
        · exact hcn (cached_injective he)
      simp only [cleared,hper,Bool.false_eq_true,ite_false,ite_eq_right hk,ite_eq_right hcn]
namespace O
export SemiprimeD1StackCachePhaseRootOriginal (rootDone)
end O
namespace A
export SemiprimeD1StackFreshBankRestoreOriginal (banks root_heap root_counter)
end A
namespace R
export SemiprimeD1StackRootPhaseFreshRecords (heap aux)
export SemiprimeD1StackRootPhaseFreshRecordsEncoding (result)
end R
open SemiprimeD1StackJetFoldWords (Modes)
attribute [local irreducible] SemiprimeD1StackRootPhaseFreshRecordsEncoding.result
  SemiprimeD1StackFreshBankRestoreOriginal.banks
  SemiprimeD1StackRootPhaseFreshRecordsEncoding.freshResult
  SemiprimeD1StackRootPhaseParametersEncoding.phases
  SemiprimeD1StackRootPhaseParametersEncoding.exponentValue
  SemiprimeD1StackRootPhaseParametersEncoding.levelsValue
  SemiprimeD1StackRootPhaseParametersEncoding.edgeValue
  SemiprimeD1StackCachePhaseRootOriginal.good
  SemiprimeD1StackCachePhaseRootOriginal.dimension
  SemiprimeD1StackCachePhaseRootOriginal.newPrecision
  SemiprimeD1StackCachePhaseExecution.done
  SemiprimeD1StackCachePhaseRejected.done
/-- The actual original source's accepted/rejected guard NEVER changes the retained physical heap. -/
theorem original_heap (bits:List Bool) (i:Fin (SemiprimeD1StackRootPhaseParametersEncoding.phases bits).length)
    (modes:Modes):(O.rootDone bits i modes).data heapRole=R.result bits R.heap:=by
  unfold O.rootDone
  split_ifs
  · rw [heapRole,accepted_heap]
    exact (A.root_heap bits).symm
  · rw [heapRole,rejected_heap]
    exact (A.root_heap bits).symm
/-- The actual original source's accepted/rejected guard NEVER changes the retained allocation counter. -/
theorem original_counter (bits:List Bool) (i:Fin (SemiprimeD1StackRootPhaseParametersEncoding.phases bits).length)
    (modes:Modes):(O.rootDone bits i modes).data counterRole=R.result bits (R.aux .counter):=by
  unfold O.rootDone
  split_ifs
  · rw [counterRole,accepted_counter]
    exact (A.root_counter bits).symm
  · rw [counterRole,rejected_counter]
    exact (A.root_counter bits).symm
/-- The entire real238-role sweep closes EXACT the next original callee's clean physical input. -/
theorem original_cleared (bits:List Bool) (i:Fin (SemiprimeD1StackRootPhaseParametersEncoding.phases bits).length)
    (modes:Modes):cleared (O.rootDone bits i modes).data=
      P.input (R.result bits R.heap) (R.result bits (R.aux .counter)) [] []:=
  cleared_input _ _ _ (original_heap bits i modes) (original_counter bits i modes)
end RiemannGaussian.SemiprimeD1StackCachePhaseBankBinding

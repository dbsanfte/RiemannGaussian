/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackCachePhaseBankState
/-! # Actual stopped-callee scratch emptiness and immutable heap/counter
These properties follow from the real stopped accepted/rejected source banks,
not an assumed cleared scratch. Final outer status is written only afterward.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackCachePhaseBankStopped
open SemiprimeD1StackCachePhaseBank
namespace X
export SemiprimeD1StackCachePhaseExecution (done heap counter)
end X
namespace R
export SemiprimeD1StackCachePhaseRejected (done)
end R
namespace O
export SemiprimeD1StackCachePhaseRootOriginal (rootDone good)
end O
open SemiprimeD1StackJetFoldWords (Modes)
/-- The actual four-input callee starts with its real shared copy scratch empty. -/
theorem initial_scratch (hp cn ref children:List Bool):P.input hp cn ref children P.copyScratch=[]:=rfl
/-- The actual accepted238-role halt has empty real copy scratch. -/
theorem accepted_scratch (banks:List (SemiprimeD1StackCachePhase.Fresh.Stack→List Bool)) (i:Fin banks.length)
    (axes:List Nat) (p:List Bool) (q:Nat) (newP:List Bool) (modes:Modes):
    (X.done banks i axes p q newP modes).data P.copyScratch=[]:=rfl
/-- The actual rejected238-role halt also has empty real copy scratch. -/
theorem rejected_scratch (banks:List (SemiprimeD1StackCachePhase.Fresh.Stack→List Bool)) (i:Fin banks.length)
    (children:List Bool):(R.done banks i children).data P.copyScratch=[]:=rfl
/-- The original family derives scratch emptiness from the actual restored guard, without a supplied branch flag. -/
theorem original_scratch (bits:List Bool)
    (i:Fin (SemiprimeD1StackRootPhaseParametersEncoding.phases bits).length) (modes:Modes):
    (O.rootDone bits i modes).data P.copyScratch=[]:=by
  unfold O.rootDone
  split_ifs <;> rfl
/-- Actual accepted source retains the physical heap, with every other cache field still accounted for. -/
theorem accepted_heap (banks:List (SemiprimeD1StackCachePhase.Fresh.Stack→List Bool)) (i:Fin banks.length)
    (axes:List Nat) (p:List Bool) (q:Nat) (newP:List Bool) (modes:Modes):
    (X.done banks i axes p q newP modes).data
      (P.restoreStack (SemiprimeD1StackCachePhase.Restore.heapStack .heap))=X.heap banks:=rfl
/-- Actual rejected source retains the same physical heap. -/
theorem rejected_heap (banks:List (SemiprimeD1StackCachePhase.Fresh.Stack→List Bool)) (i:Fin banks.length)
    (children:List Bool):(R.done banks i children).data
      (P.restoreStack (SemiprimeD1StackCachePhase.Restore.heapStack .heap))=X.heap banks:=rfl
/-- Actual accepted source retains the physical allocation counter. -/
theorem accepted_counter (banks:List (SemiprimeD1StackCachePhase.Fresh.Stack→List Bool)) (i:Fin banks.length)
    (axes:List Nat) (p:List Bool) (q:Nat) (newP:List Bool) (modes:Modes):
    (X.done banks i axes p q newP modes).data
      (P.restoreStack (SemiprimeD1StackCachePhase.Restore.heapStack .counter))=X.counter banks:=rfl
/-- Actual rejected source retains the same physical allocation counter. -/
theorem rejected_counter (banks:List (SemiprimeD1StackCachePhase.Fresh.Stack→List Bool)) (i:Fin banks.length)
    (children:List Bool):(R.done banks i children).data
      (P.restoreStack (SemiprimeD1StackCachePhase.Restore.heapStack .counter))=X.counter banks:=rfl
end RiemannGaussian.SemiprimeD1StackCachePhaseBankStopped

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPhaseCacheFresh
/-! # Actual alias-preserving heap restore and P48-cache fresh calls -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPhaseCacheFreshComponents
open SemiprimeD1StackPhaseCacheFresh SemiprimeD1StackProcedureTrace
local notation "ctl" => (Sum.inl : Control→Label)
/-- Exact actual phase cache previously acquired and serialized by the producer. -/
def phase (a u edges:Nat) (t p:List Bool) :P.Stack→List Bool :=
  SemiprimeD1StackPhaseWorkingPrecisionComponents.result a u edges t p
/-- Real heap/48field result installs the selected literal bank through the shared48alias. -/
def after (bank:P.Stack→List Bool) (heap counter reference axes:List Bool) :Stack→List Bool :=
  data (Heap.input heap counter reference) (freshReadyBank bank axes)
/-- Exact fresh whole cache/output, original heap/counter/reference retained and all48shadowsEMPTY. -/
def completed (a u edges:Nat) (t p:List Bool) (axes:List Nat) (heap counter reference:List Bool) :Stack→List Bool :=
  data (Heap.input heap counter reference) (SemiprimeD1StackPhaseChildContextFreshComponents.result a u edges t p axes)
/-- Every actual included Fresh role directly views the corresponding real shared/private word. -/
theorem fresh_data (heap:Heap.Stack→List Bool) (fresh:F.Stack→List Bool) (k:F.Stack) :
    data heap fresh (freshStack k)=fresh k :=by
  rcases k with k|k
  · rcases k with k|k <;> rfl
  · rfl
/-- Empty physical P48 shadow slots do not depend on the restored cache's mathematical interpretation. -/
theorem private_ready (bank:P.Stack→List Bool) (axes:List Bool) :
    privateView (freshReadyBank bank axes)=privateView (freshReadyBank (fun _=>[]) axes) :=by
  funext k
  rcases k with k|k
  · rcases k with k|k <;> rfl
  · rfl
/-- Actual P48cache ready source is exactly the restored-bank plus actual old-header projection. -/
theorem fresh_ready_eq (a u edges:Nat) (t p axes:List Bool) :
    freshReadyBank (phase a u edges t p) axes=(SemiprimeD1StackPhaseChildContextFresh.phaseReady a u edges t p axes).data :=rfl
/-- Actual chronological real-call composition retains arbitrary real caller frames. -/
theorem join {m n:Nat} {pc mid finish:Label} {before between after:Stack→List Bool}
    (h:Runs program m pc before mid between) (g:Runs program n mid between finish after) :
    Runs program (m+n) pc before finish after :=runs_trans program m n pc mid finish before between after h g
/-- The entire REAL58-role dereference/restore source executes, preserving the old-header/private bank. -/
theorem restore_call (banks:List (P.Stack→List Bool)) (i:Fin banks.length) (axes:List Bool) :
    ∃q≤ SemiprimeD1StackPhaseBankRestoreExecution.runBound banks i+1,
      Runs program q (ctl .start)
        (input (SemiprimeD1StackHeapAllocate.heapBytes (SemiprimeD1StackPhaseBankRestoreExecution.records banks))
          (List.replicate banks.length true) (List.replicate i.val true) axes)
        (ctl .fresh)
        (after banks[i.val] (SemiprimeD1StackHeapAllocate.heapBytes (SemiprimeD1StackPhaseBankRestoreExecution.records banks))
          (List.replicate banks.length true) (List.replicate i.val true) axes) :=by
  obtain ⟨q,hq,hr⟩:=SemiprimeD1StackPhaseBankRestoreExecution.source_run banks i
  refine ⟨q+1,by omega,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program restoreStack restoreLabel restore_injective
    R.program (.inl .start) (fun _=>rfl) (ctl .start) (ctl .fresh) rfl q
    (SemiprimeD1StackPhaseBankRestoreExecution.source banks i) (SemiprimeD1StackPhaseBankRestoreExecution.target banks i)
    _ _ rfl rfl rfl rfl hr
  · constructor
    · intro k;rcases k with k|k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k;rcases k with k|k <;> rfl
    · intro k hk
      rcases k with k|k
      · exact (hk k rfl).elim
      · exact congrFun (private_ready banks[i.val] axes) k
/-- REAL Fresh.phaseReady consumes the directly aliased restored48cache; no geometry/P source reruns. -/
theorem fresh_call (a u edges:Nat) (t p:List Bool) (axes:List Nat) (hp:∀x∈axes,0<x) (heap counter reference:List Bool) :
    ∃q≤ SemiprimeD1StackPhaseChildContextFreshExecution.phaseReadyBound a u edges t p axes+1,
      Runs program q (ctl .fresh)
        (after (phase a u edges t p) heap counter reference (SemiprimeD1StackPhaseChildContextPrimitives.header axes))
        (ctl .done) (completed a u edges t p axes heap counter reference) :=by
  obtain ⟨q,hq,hr⟩:=SemiprimeD1StackPhaseChildContextFreshExecution.phase_ready_run a u edges t p axes hp
  refine ⟨q+1,by omega,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program freshStack freshLabel fresh_injective
    F.program .phaseReady (fun _=>rfl) (ctl .fresh) (ctl .done) rfl q
    (SemiprimeD1StackPhaseChildContextFresh.phaseReady a u edges t p (SemiprimeD1StackPhaseChildContextPrimitives.header axes))
    (SemiprimeD1StackPhaseChildContextFreshExecution.done a u edges t p axes) _ _ rfl rfl rfl rfl hr
  · constructor
    · intro k
      exact fresh_data _ _ k
    · intro k _;rfl
  · constructor
    · intro k
      exact fresh_data _ _ k
    · intro k hk
      rcases k with k|k
      · rcases k with k|k
        · exact (hk (F.contextStack (H.phaseStack k)) rfl).elim
        · rfl
      · rcases k with k|k
        · rcases k with k|k
          · rfl
          · exact (hk (.inl (.inr k)) rfl).elim
        · exact (hk (.inr k) rfl).elim
end RiemannGaussian.SemiprimeD1StackPhaseCacheFreshComponents

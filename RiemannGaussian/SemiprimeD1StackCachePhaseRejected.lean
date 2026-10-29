/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackCachePhaseExecution
/-! # Rejected phases restore their real record and emit an empty block vector
No prepared child field or context is consumed by the rejected branch. The
complete restored record and original child tape remain physically retained.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackCachePhaseRejected
open SemiprimeD1StackCachePhase SemiprimeD1StackCachePhaseView SemiprimeD1StackCachePhaseExecution
open SemiprimeD1StackCachePhasePrimitives SemiprimeD1StackCachePhaseCalls SemiprimeD1StackCachePhaseGuard
open SemiprimeD1StackProcedureTrace
local notation "ctl" => Label.local
/-- The same actual four-word input; children may be any literal tape on rejection. -/
def source (banks:List (Fresh.Stack→List Bool)) (i:Fin banks.length) (children:List Bool) :C.State Stack Label :=
  initial (heap banks) (counter banks) (reference banks i) children
/-- All238 words after actual rejection: full restored bank, original children and empty output vector. -/
def result (banks:List (Fresh.Stack→List Bool)) (i:Fin banks.length) (children:List Bool) :Stack→List Bool :=
  data (restored banks i) (Fold.initial [] [] children).data
    (Function.update (fun _=>[]) (Blocks.aux .output) [false]) []
/-- Genuine rejected halt with all source/work/return flags clear. -/
def done (banks:List (Fresh.Stack→List Bool)) (i:Fin banks.length) (children:List Bool) :C.State Stack Label :=
  ⟨none,none,none,result banks i children,[]⟩
/-- Full rejected source really performs restore, guard peek, terminal push and halt. -/
theorem source_run (banks:List (Fresh.Stack→List Bool)) (i:Fin banks.length) (children:List Bool)
    (hg:banks[i.val] (Fresh.contextStack (Header.aux .valid))=[false]) :
    ∃t≤SemiprimeD1StackFreshBankRestoreExecution.runBound banks i+4,
      SemiprimeD1StackCalls.run program t (source banks i children)=some (done banks i children) :=by
  obtain ⟨a,ha,h0⟩:=restore_call banks i (Fold.initial [] [] children).data (fun _=>[]) []
  have h1:=guard_run (data (restored banks i) (Fold.initial [] [] children).data (fun _=>[]) []) false hg
  change Runs program 1 (ctl .check) _ (ctl .reject) _ at h1
  have h2:=reject_run (data (restored banks i) (Fold.initial [] [] children).data (fun _=>[]) [])
  change Runs program 1 _ _ _ (Function.update
    (data (restored banks i) (Fold.initial [] [] children).data (fun _=>[]) [])
    (blockStack (Blocks.aux .output)) [false]) at h2
  rw [data_blocks] at h2
  have h:=join (join h0 h1) h2
  obtain ⟨out,ho,hAt⟩:=h [] (source banks i children) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program (ctl .done) rfl (result banks i children) [] out hAt
  exact ⟨(a+1+1)+1,by omega,by rw [SemiprimeD1StackReturnLink.run_add,ho,Option.bind_some];exact hh⟩
end RiemannGaussian.SemiprimeD1StackCachePhaseRejected

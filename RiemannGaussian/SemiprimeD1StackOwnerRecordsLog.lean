/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOwnerRecordsEmit
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackOwnerRecordsLog
open SemiprimeD1StackOwnerRecords SemiprimeD1StackOwnerRecordsView
open SemiprimeD1StackProcedureTrace (Runs)
/-- Real logger operand alias map is injective, including the34-role wrapper. -/
theorem log_injective : Function.Injective logStack :=
  record_injective.comp SemiprimeD1StackOwnerRecord.recordStack_injective
/-- Actual logger bytecode call on the complete physical source store. -/
theorem log_call (s:S.Stack→List Bool) (a:Aux→List Bool) (entry:L.Label) (pc next:Label)
    (hc:program pc=.call (.log entry) next) (time:Nat) (hist out hist' out':List Bool)
    (hr:SemiprimeD1StackBytecode.run L.code time ⟨some entry,none,L.data [] [] hist out⟩=
      some ⟨none,none,L.data [] [] hist' out'⟩) :
    Runs program (time+1) pc (data s (payload [] [] [] hist out) a)
      next (data s (payload [] [] [] hist' out') a):=by
  apply SemiprimeD1StackVertexRecordStreamExecution.call program logStack Label.log log_injective
    entry (fun _=>rfl) pc next hc time (L.data [] [] hist out) (L.data [] [] hist' out')
  · exact hr
  · constructor
    · intro k;cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k;cases k <;> rfl
    · intro k hk
      rcases k with k|k
      · rfl
      · rcases k with k|k
        · fin_cases k <;> first | rfl | (exfalso;revert hk;decide)
        · rfl
/-- The ONE final list sentinel is physically pushed onto OUTPUT, never history. -/
theorem initialize_call (s:S.Stack→List Bool) (a:Aux→List Bool) :
    Runs program 3 (.local .initialize) (data s (payload [] [] [] [] []) a)
      (.local .loop) (data s (payload [] [] [] [] [false]) a):=by
  exact log_call s a .initialize (.local .initialize) (.local .loop) rfl 2 [] [] [] [false]
    (SemiprimeD1StackVertexRecordStream.initialize_run [] [] [] [] none)
/-- A real single final reversal emits the catalogue's original forward row order. -/
theorem reverse_call (s:S.Stack→List Bool) (a:Aux→List Bool) (hist out:List Bool) :
    Runs program (2*hist.length+3) (.local .reverse) (data s (payload [] [] [] hist out) a)
      (.local .halt) (data s (payload [] [] [] [] (hist.reverse++out)) a):=by
  exact log_call s a .reverse (.local .reverse) (.local .halt) rfl (2*hist.length+2)
    hist out [] (hist.reverse++out) (SemiprimeD1StackVertexRecordStream.reverse_run hist [] [] out none)
end RiemannGaussian.SemiprimeD1StackOwnerRecordsLog

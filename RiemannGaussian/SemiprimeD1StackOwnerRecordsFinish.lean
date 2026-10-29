/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOwnerRecordsLoop
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackOwnerRecordsFinish
open SemiprimeD1StackOwnerRecords SemiprimeD1StackOwnerRecordsView
open SemiprimeD1StackOwnerRecordsLog SemiprimeD1StackOwnerRecordsLoop
open SemiprimeD1StackProcedureTrace (Runs runs_trans one_base)
/-- Actual list EOF is consumed after ALL original owners, independently of M. -/
theorem eof_run (s:S.Stack→List Bool) (hist out pre:List Bool) :
    Runs program 1 (.local .loop) (data s (payload [] [] [] hist out) (rowAux [false] pre))
      (.local .reverse) (data s (payload [] [] [] hist out) (rowAux [] pre)):=by
  apply one_base program _ _ (.pop (aux .reader) (.local .reverse) (.local .reverse) (.local (.field false))) _ _ rfl rfl
  simp only [SemiprimeD1StackBytecode.execute,data_aux,update_aux]
  congr 1;funext k;cases k <;> rfl
/-- Actual final EOF and single physical reversal return the original forward rows. -/
theorem finish_run (s:S.Stack→List Bool) (raw pre:List Bool) :
    Runs program (2*raw.length+4) (.local .loop)
      (data s (payload [] [] [] raw.reverse [false]) (rowAux [false] pre)) (.local .halt)
      (data s (payload [] [] [] [] (raw++[false])) (rowAux [] pre)):=by
  have h0:=eof_run s raw.reverse [false] pre
  have h1:=reverse_call s (rowAux [] pre) raw.reverse [false]
  have h:=runs_trans program _ _ _ _ _ _ _ _ h0 h1
  simpa only [List.length_reverse,List.reverse_reverse,show 1+(2*raw.length+3)=2*raw.length+4 by omega] using h
/-- All34 work roles and actual outer parser/copy words finish empty, with prefix/source retained. -/
def result (s:S.Stack→List Bool) (raw pre:List Bool) :C.State Stack Label:=
  ⟨none,none,none,data s (payload [] [] [] [] (raw++[false])) (rowAux [] pre),[]⟩
end RiemannGaussian.SemiprimeD1StackOwnerRecordsFinish

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryPrimitives
/-! # Complete paid reuse boundary after every observed packet bucket
All three packet-local words and ALL twelve ordinal-converter tapes are
physically drained, including its retained binary bank and unary result.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketReuse
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryWiring
open SemiprimeD1StackChildGroupFactory SemiprimeD1StackChildGroupFactoryPrimitives
open SemiprimeD1StackProcedureTrace
/-- Exact fifteen actual reusable role labels, fixed before every input. -/
def role:Fin 15→Stack
  | 0=>aux .packetKey
  | 1=>aux .jointKey
  | 2=>aux .portBank
  | 3=>ordinal .bank
  | 4=>ordinal .reader
  | 5=>ordinal .word
  | 6=>ordinal .fieldScratch
  | 7=>ordinal .valid
  | 8=>ordinal .copyScratch
  | 9=>ordinal .digits
  | 10=>ordinal .unaryScratch
  | 11=>ordinal .unary
  | 12=>ordinal .logScratch
  | 13=>ordinal .history
  | 14=>ordinal .output
/-- Every field and callee word is physically cleared. -/
def result (before:Stack→List Bool):Stack→List Bool:=
  Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (before) (aux .packetKey) []) (aux .jointKey) []) (aux .portBank) []) (ordinal .bank) []) (ordinal .reader) []) (ordinal .word) []) (ordinal .fieldScratch) []) (ordinal .valid) []) (ordinal .copyScratch) []) (ordinal .digits) []) (ordinal .unaryScratch) []) (ordinal .unary) []) (ordinal .logScratch) []) (ordinal .history) []) (ordinal .output) []
/-- Actual bytes erased and all fifteen actual EOF pops. -/
def timeBound (before:Stack→List Bool):Nat:=
  (before (aux .packetKey)).length+(before (aux .jointKey)).length+(before (aux .portBank)).length+(before (ordinal .bank)).length+(before (ordinal .reader)).length+(before (ordinal .word)).length+(before (ordinal .fieldScratch)).length+(before (ordinal .valid)).length+(before (ordinal .copyScratch)).length+(before (ordinal .digits)).length+(before (ordinal .unaryScratch)).length+(before (ordinal .unary)).length+(before (ordinal .logScratch)).length+(before (ordinal .history)).length+(before (ordinal .output)).length+15
/-- Complete real cleanup before the next actual observed packet is read. -/
theorem source_trace (before:Stack→List Bool):
    Runs program (timeBound before) (.local 8 17) before (.local 6 18) (result before):=by
  let b0:=before
  let b1:Stack→List Bool:=Function.update b0 (aux .packetKey) []
  have h0:Runs program ((before (aux .packetKey)).length+1) (.local 8 17) b0 (.local 8 18) b1:=
    drain_loop (.local 8 17) (.local 8 18) (aux .packetKey) rfl b0 (before (aux .packetKey)) (by simp [b0,aux])
  let b2:Stack→List Bool:=Function.update b1 (aux .jointKey) []
  have h1:Runs program ((before (aux .jointKey)).length+1) (.local 8 18) b1 (.local 8 19) b2:=
    drain_loop (.local 8 18) (.local 8 19) (aux .jointKey) rfl b1 (before (aux .jointKey)) (by simp [b0,b1,aux])
  let b3:Stack→List Bool:=Function.update b2 (aux .portBank) []
  have h2:Runs program ((before (aux .portBank)).length+1) (.local 8 19) b2 (.local 8 20) b3:=
    drain_loop (.local 8 19) (.local 8 20) (aux .portBank) rfl b2 (before (aux .portBank)) (by simp [b0,b1,b2,aux])
  let b4:Stack→List Bool:=Function.update b3 (ordinal .bank) []
  have h3:Runs program ((before (ordinal .bank)).length+1) (.local 8 20) b3 (.local 8 21) b4:=
    drain_loop (.local 8 20) (.local 8 21) (ordinal .bank) rfl b3 (before (ordinal .bank)) (by simp [b0,b1,b2,b3,aux,ordinal])
  let b5:Stack→List Bool:=Function.update b4 (ordinal .reader) []
  have h4:Runs program ((before (ordinal .reader)).length+1) (.local 8 21) b4 (.local 8 22) b5:=
    drain_loop (.local 8 21) (.local 8 22) (ordinal .reader) rfl b4 (before (ordinal .reader)) (by simp [b0,b1,b2,b3,b4,aux,ordinal])
  let b6:Stack→List Bool:=Function.update b5 (ordinal .word) []
  have h5:Runs program ((before (ordinal .word)).length+1) (.local 8 22) b5 (.local 8 23) b6:=
    drain_loop (.local 8 22) (.local 8 23) (ordinal .word) rfl b5 (before (ordinal .word)) (by simp [b0,b1,b2,b3,b4,b5,aux,ordinal])
  let b7:Stack→List Bool:=Function.update b6 (ordinal .fieldScratch) []
  have h6:Runs program ((before (ordinal .fieldScratch)).length+1) (.local 8 23) b6 (.local 8 24) b7:=
    drain_loop (.local 8 23) (.local 8 24) (ordinal .fieldScratch) rfl b6 (before (ordinal .fieldScratch)) (by simp [b0,b1,b2,b3,b4,b5,b6,aux,ordinal])
  let b8:Stack→List Bool:=Function.update b7 (ordinal .valid) []
  have h7:Runs program ((before (ordinal .valid)).length+1) (.local 8 24) b7 (.local 8 25) b8:=
    drain_loop (.local 8 24) (.local 8 25) (ordinal .valid) rfl b7 (before (ordinal .valid)) (by simp [b0,b1,b2,b3,b4,b5,b6,b7,aux,ordinal])
  let b9:Stack→List Bool:=Function.update b8 (ordinal .copyScratch) []
  have h8:Runs program ((before (ordinal .copyScratch)).length+1) (.local 8 25) b8 (.local 8 26) b9:=
    drain_loop (.local 8 25) (.local 8 26) (ordinal .copyScratch) rfl b8 (before (ordinal .copyScratch)) (by simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,aux,ordinal])
  let b10:Stack→List Bool:=Function.update b9 (ordinal .digits) []
  have h9:Runs program ((before (ordinal .digits)).length+1) (.local 8 26) b9 (.local 8 27) b10:=
    drain_loop (.local 8 26) (.local 8 27) (ordinal .digits) rfl b9 (before (ordinal .digits)) (by simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,aux,ordinal])
  let b11:Stack→List Bool:=Function.update b10 (ordinal .unaryScratch) []
  have h10:Runs program ((before (ordinal .unaryScratch)).length+1) (.local 8 27) b10 (.local 8 28) b11:=
    drain_loop (.local 8 27) (.local 8 28) (ordinal .unaryScratch) rfl b10 (before (ordinal .unaryScratch)) (by simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,aux,ordinal])
  let b12:Stack→List Bool:=Function.update b11 (ordinal .unary) []
  have h11:Runs program ((before (ordinal .unary)).length+1) (.local 8 28) b11 (.local 8 29) b12:=
    drain_loop (.local 8 28) (.local 8 29) (ordinal .unary) rfl b11 (before (ordinal .unary)) (by simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,aux,ordinal])
  let b13:Stack→List Bool:=Function.update b12 (ordinal .logScratch) []
  have h12:Runs program ((before (ordinal .logScratch)).length+1) (.local 8 29) b12 (.local 8 30) b13:=
    drain_loop (.local 8 29) (.local 8 30) (ordinal .logScratch) rfl b12 (before (ordinal .logScratch)) (by simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,aux,ordinal])
  let b14:Stack→List Bool:=Function.update b13 (ordinal .history) []
  have h13:Runs program ((before (ordinal .history)).length+1) (.local 8 30) b13 (.local 8 31) b14:=
    drain_loop (.local 8 30) (.local 8 31) (ordinal .history) rfl b13 (before (ordinal .history)) (by simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,aux,ordinal])
  let b15:Stack→List Bool:=Function.update b14 (ordinal .output) []
  have h14:Runs program ((before (ordinal .output)).length+1) (.local 8 31) b14 (.local 6 18) b15:=
    drain_loop (.local 8 31) (.local 6 18) (ordinal .output) rfl b14 (before (ordinal .output)) (by simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,aux,ordinal])
  have hwhole:=join h0 (join h1 (join h2 (join h3 (join h4 (join h5 (join h6 (join h7 (join h8 (join h9 (join h10 (join h11 (join h12 (join h13 (h14))))))))))))))
  have ht:((before (aux .packetKey)).length+1)+((before (aux .jointKey)).length+1)+((before (aux .portBank)).length+1)+((before (ordinal .bank)).length+1)+((before (ordinal .reader)).length+1)+((before (ordinal .word)).length+1)+((before (ordinal .fieldScratch)).length+1)+((before (ordinal .valid)).length+1)+((before (ordinal .copyScratch)).length+1)+((before (ordinal .digits)).length+1)+((before (ordinal .unaryScratch)).length+1)+((before (ordinal .unary)).length+1)+((before (ordinal .logScratch)).length+1)+((before (ordinal .history)).length+1)+((before (ordinal .output)).length+1)=timeBound before:=by dsimp only [timeBound];omega
  simpa only [←ht,Nat.add_assoc,result,b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15] using hwhole
/-- Every reusable word is now really empty. -/
theorem result_role (before:Stack→List Bool) (i:Fin 15):result before (role i)=[]:=by fin_cases i <;> rfl
/-- All caller words outside the fifteen actual drained tapes are retained. -/
theorem result_other (before:Stack→List Bool) (k:Stack) (h:∀i,role i≠k):result before k=before k:=by
  have h0:=Ne.symm (h 0)
  have h1:=Ne.symm (h 1)
  have h2:=Ne.symm (h 2)
  have h3:=Ne.symm (h 3)
  have h4:=Ne.symm (h 4)
  have h5:=Ne.symm (h 5)
  have h6:=Ne.symm (h 6)
  have h7:=Ne.symm (h 7)
  have h8:=Ne.symm (h 8)
  have h9:=Ne.symm (h 9)
  have h10:=Ne.symm (h 10)
  have h11:=Ne.symm (h 11)
  have h12:=Ne.symm (h 12)
  have h13:=Ne.symm (h 13)
  have h14:=Ne.symm (h 14)
  simp only [role] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  simp only [result,Function.update_of_ne h14,Function.update_of_ne h13,Function.update_of_ne h12,Function.update_of_ne h11,Function.update_of_ne h10,Function.update_of_ne h9,Function.update_of_ne h8,Function.update_of_ne h7,Function.update_of_ne h6,Function.update_of_ne h5,Function.update_of_ne h4,Function.update_of_ne h3,Function.update_of_ne h2,Function.update_of_ne h1,Function.update_of_ne h0]
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketReuse

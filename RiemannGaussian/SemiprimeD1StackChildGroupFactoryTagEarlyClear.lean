/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryPrimitives
/-! # Complete actual early-stop disposal after the first raw-tag hit
All unread nested-source suffixes and all current raw child fields are really
drained. The actual old-port reader, tag, local counter and answer are retained.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryTagEarlyClear
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryWiring
open SemiprimeD1StackChildGroupFactory SemiprimeD1StackChildGroupFactoryPrimitives
open SemiprimeD1StackProcedureTrace
/-- The eleven actual early-stop work tapes, fixed before all inputs. -/
def role:Fin 11→Stack
  | 0=>aux .outerReader
  | 1=>aux .childReader
  | 2=>aux .endpointReader
  | 3=>aux .rowBuffer
  | 4=>aux .ownerKey
  | 5=>aux .sourceKey
  | 6=>aux .slotWord
  | 7=>aux .edgeWord
  | 8=>aux .sideWord
  | 9=>aux .globalPosition
  | 10=>aux .candidateTag
/-- Complete actual early-stop cleanup, preserving every other physical word. -/
def result (before:Stack→List Bool):Stack→List Bool:=
  Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (before) (aux .outerReader) []) (aux .childReader) []) (aux .endpointReader) []) (aux .rowBuffer) []) (aux .ownerKey) []) (aux .sourceKey) []) (aux .slotWord) []) (aux .edgeWord) []) (aux .sideWord) []) (aux .globalPosition) []) (aux .candidateTag) []
/-- Actual remaining-source/field bytes and every actual EOF pop are paid. -/
def timeBound (before:Stack→List Bool):Nat:=
  (before (aux .outerReader)).length+(before (aux .childReader)).length+(before (aux .endpointReader)).length+(before (aux .rowBuffer)).length+(before (aux .ownerKey)).length+(before (aux .sourceKey)).length+(before (aux .slotWord)).length+(before (aux .edgeWord)).length+(before (aux .sideWord)).length+(before (aux .globalPosition)).length+(before (aux .candidateTag)).length+11
/-- Exact actual early-stop cleanup before logging the computed answer. -/
theorem source_trace (before:Stack→List Bool):
    Runs program (timeBound before) (.local 13 20) before (.local 14 0) (result before):=by
  let b0:=before
  let b1:Stack→List Bool:=Function.update b0 (aux .outerReader) []
  have h0:Runs program ((before (aux .outerReader)).length+1) (.local 13 20) b0 (.local 13 21) b1:=
    drain_loop (.local 13 20) (.local 13 21) (aux .outerReader) rfl b0 (before (aux .outerReader)) (by simp [b0,aux])
  let b2:Stack→List Bool:=Function.update b1 (aux .childReader) []
  have h1:Runs program ((before (aux .childReader)).length+1) (.local 13 21) b1 (.local 13 22) b2:=
    drain_loop (.local 13 21) (.local 13 22) (aux .childReader) rfl b1 (before (aux .childReader)) (by simp [b0,b1,aux])
  let b3:Stack→List Bool:=Function.update b2 (aux .endpointReader) []
  have h2:Runs program ((before (aux .endpointReader)).length+1) (.local 13 22) b2 (.local 13 23) b3:=
    drain_loop (.local 13 22) (.local 13 23) (aux .endpointReader) rfl b2 (before (aux .endpointReader)) (by simp [b0,b1,b2,aux])
  let b4:Stack→List Bool:=Function.update b3 (aux .rowBuffer) []
  have h3:Runs program ((before (aux .rowBuffer)).length+1) (.local 13 23) b3 (.local 13 24) b4:=
    drain_loop (.local 13 23) (.local 13 24) (aux .rowBuffer) rfl b3 (before (aux .rowBuffer)) (by simp [b0,b1,b2,b3,aux])
  let b5:Stack→List Bool:=Function.update b4 (aux .ownerKey) []
  have h4:Runs program ((before (aux .ownerKey)).length+1) (.local 13 24) b4 (.local 13 25) b5:=
    drain_loop (.local 13 24) (.local 13 25) (aux .ownerKey) rfl b4 (before (aux .ownerKey)) (by simp [b0,b1,b2,b3,b4,aux])
  let b6:Stack→List Bool:=Function.update b5 (aux .sourceKey) []
  have h5:Runs program ((before (aux .sourceKey)).length+1) (.local 13 25) b5 (.local 13 26) b6:=
    drain_loop (.local 13 25) (.local 13 26) (aux .sourceKey) rfl b5 (before (aux .sourceKey)) (by simp [b0,b1,b2,b3,b4,b5,aux])
  let b7:Stack→List Bool:=Function.update b6 (aux .slotWord) []
  have h6:Runs program ((before (aux .slotWord)).length+1) (.local 13 26) b6 (.local 13 27) b7:=
    drain_loop (.local 13 26) (.local 13 27) (aux .slotWord) rfl b6 (before (aux .slotWord)) (by simp [b0,b1,b2,b3,b4,b5,b6,aux])
  let b8:Stack→List Bool:=Function.update b7 (aux .edgeWord) []
  have h7:Runs program ((before (aux .edgeWord)).length+1) (.local 13 27) b7 (.local 13 28) b8:=
    drain_loop (.local 13 27) (.local 13 28) (aux .edgeWord) rfl b7 (before (aux .edgeWord)) (by simp [b0,b1,b2,b3,b4,b5,b6,b7,aux])
  let b9:Stack→List Bool:=Function.update b8 (aux .sideWord) []
  have h8:Runs program ((before (aux .sideWord)).length+1) (.local 13 28) b8 (.local 13 29) b9:=
    drain_loop (.local 13 28) (.local 13 29) (aux .sideWord) rfl b8 (before (aux .sideWord)) (by simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,aux])
  let b10:Stack→List Bool:=Function.update b9 (aux .globalPosition) []
  have h9:Runs program ((before (aux .globalPosition)).length+1) (.local 13 29) b9 (.local 13 30) b10:=
    drain_loop (.local 13 29) (.local 13 30) (aux .globalPosition) rfl b9 (before (aux .globalPosition)) (by simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,aux])
  let b11:Stack→List Bool:=Function.update b10 (aux .candidateTag) []
  have h10:Runs program ((before (aux .candidateTag)).length+1) (.local 13 30) b10 (.local 14 0) b11:=
    drain_loop (.local 13 30) (.local 14 0) (aux .candidateTag) rfl b10 (before (aux .candidateTag)) (by simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,aux])
  have hwhole:=join h0 (join h1 (join h2 (join h3 (join h4 (join h5 (join h6 (join h7 (join h8 (join h9 (h10))))))))))
  have ht:((before (aux .outerReader)).length+1)+((before (aux .childReader)).length+1)+((before (aux .endpointReader)).length+1)+((before (aux .rowBuffer)).length+1)+((before (aux .ownerKey)).length+1)+((before (aux .sourceKey)).length+1)+((before (aux .slotWord)).length+1)+((before (aux .edgeWord)).length+1)+((before (aux .sideWord)).length+1)+((before (aux .globalPosition)).length+1)+((before (aux .candidateTag)).length+1)=timeBound before:=by dsimp only [timeBound];omega
  simpa only [←ht,Nat.add_assoc,result,b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11] using hwhole
/-- Every actual skipped-suffix/current-field word is physically empty. -/
theorem result_role (before:Stack→List Bool) (i:Fin 11):result before (role i)=[]:=by fin_cases i <;> rfl
/-- All old-port/counter/cache words outside the real disposal image are retained. -/
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
  simp only [role] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  simp only [result,Function.update_of_ne h10,Function.update_of_ne h9,Function.update_of_ne h8,Function.update_of_ne h7,Function.update_of_ne h6,Function.update_of_ne h5,Function.update_of_ne h4,Function.update_of_ne h3,Function.update_of_ne h2,Function.update_of_ne h1,Function.update_of_ne h0]
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryTagEarlyClear

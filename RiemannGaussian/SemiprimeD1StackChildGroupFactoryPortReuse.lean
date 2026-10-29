/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryPrimitives
/-! # Complete paid ordinal-bank reuse after left-port or original-order logging
These are the two actual fixed source families. Every allocated converter word,
including its retained binary bank and unary output, is physically drained.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryPortReuse
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryWiring
open SemiprimeD1StackChildGroupFactory SemiprimeD1StackChildGroupFactoryPrimitives
open SemiprimeD1StackProcedureTrace
/-- Actual two binary metadata-bank roles, never a runtime choice parameter. -/
def bankRole (ordering:Bool):Stack:=aux (if ordering then .orderBank else .portBank)
/-- Thirteen actually drained fixed physical roles. -/
def role (ordering:Bool):Fin 13→Stack
  | 0=>bankRole ordering
  | 1=>ordinal .bank
  | 2=>ordinal .reader
  | 3=>ordinal .word
  | 4=>ordinal .fieldScratch
  | 5=>ordinal .valid
  | 6=>ordinal .copyScratch
  | 7=>ordinal .digits
  | 8=>ordinal .unaryScratch
  | 9=>ordinal .unary
  | 10=>ordinal .logScratch
  | 11=>ordinal .history
  | 12=>ordinal .output
/-- Literal cleanup families and their genuine next continuations. -/
def pc (ordering:Bool) (slot:Fin 14):Label:=if ordering then match slot.val with
  | 0=>(.local 14 16)
  | 1=>(.local 14 17)
  | 2=>(.local 14 18)
  | 3=>(.local 14 19)
  | 4=>(.local 14 20)
  | 5=>(.local 14 21)
  | 6=>(.local 14 22)
  | 7=>(.local 14 23)
  | 8=>(.local 14 24)
  | 9=>(.local 14 25)
  | 10=>(.local 14 26)
  | 11=>(.local 14 27)
  | 12=>(.local 14 28)
  | _=>(.local 14 29)
else match slot.val with
  | 0=>(.local 10 25)
  | 1=>(.local 10 26)
  | 2=>(.local 10 27)
  | 3=>(.local 10 28)
  | 4=>(.local 10 29)
  | 5=>(.local 10 30)
  | 6=>(.local 10 31)
  | 7=>(.local 11 0)
  | 8=>(.local 11 1)
  | 9=>(.local 11 2)
  | 10=>(.local 11 3)
  | 11=>(.local 11 4)
  | 12=>(.local 11 5)
  | _=>(.local 11 6)
/-- Complete actual physical cleanup. -/
def result (ordering:Bool) (before:Stack→List Bool):Stack→List Bool:=
  Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (before) (role ordering 0) []) (role ordering 1) []) (role ordering 2) []) (role ordering 3) []) (role ordering 4) []) (role ordering 5) []) (role ordering 6) []) (role ordering 7) []) (role ordering 8) []) (role ordering 9) []) (role ordering 10) []) (role ordering 11) []) (role ordering 12) []
/-- Actual erased bytes and all thirteen actual EOF tests. -/
def timeBound (ordering:Bool) (before:Stack→List Bool):Nat:=
  (before (role ordering 0)).length+(before (role ordering 1)).length+(before (role ordering 2)).length+(before (role ordering 3)).length+(before (role ordering 4)).length+(before (role ordering 5)).length+(before (role ordering 6)).length+(before (role ordering 7)).length+(before (role ordering 8)).length+(before (role ordering 9)).length+(before (role ordering 10)).length+(before (role ordering 11)).length+(before (role ordering 12)).length+13
/-- Both actual cleanup families preserve every other full115-role word and real outer returns. -/
theorem source_trace (ordering:Bool) (before:Stack→List Bool):
    Runs program (timeBound ordering before) (pc ordering 0) before (pc ordering 13) (result ordering before):=by
  let b0:=before
  let b1:Stack→List Bool:=Function.update b0 (role ordering 0) []
  have h0:Runs program ((before (role ordering 0)).length+1) (pc ordering 0) b0 (pc ordering 1) b1:=
    drain_loop (pc ordering 0) (pc ordering 1) (role ordering 0) (by cases ordering <;> rfl) b0
      (before (role ordering 0)) (by cases ordering <;> simp [b0,role,bankRole,aux])
  let b2:Stack→List Bool:=Function.update b1 (role ordering 1) []
  have h1:Runs program ((before (role ordering 1)).length+1) (pc ordering 1) b1 (pc ordering 2) b2:=
    drain_loop (pc ordering 1) (pc ordering 2) (role ordering 1) (by cases ordering <;> rfl) b1
      (before (role ordering 1)) (by cases ordering <;> simp [b0,b1,role,bankRole,aux,ordinal])
  let b3:Stack→List Bool:=Function.update b2 (role ordering 2) []
  have h2:Runs program ((before (role ordering 2)).length+1) (pc ordering 2) b2 (pc ordering 3) b3:=
    drain_loop (pc ordering 2) (pc ordering 3) (role ordering 2) (by cases ordering <;> rfl) b2
      (before (role ordering 2)) (by cases ordering <;> simp [b0,b1,b2,role,bankRole,aux,ordinal])
  let b4:Stack→List Bool:=Function.update b3 (role ordering 3) []
  have h3:Runs program ((before (role ordering 3)).length+1) (pc ordering 3) b3 (pc ordering 4) b4:=
    drain_loop (pc ordering 3) (pc ordering 4) (role ordering 3) (by cases ordering <;> rfl) b3
      (before (role ordering 3)) (by cases ordering <;> simp [b0,b1,b2,b3,role,bankRole,aux,ordinal])
  let b5:Stack→List Bool:=Function.update b4 (role ordering 4) []
  have h4:Runs program ((before (role ordering 4)).length+1) (pc ordering 4) b4 (pc ordering 5) b5:=
    drain_loop (pc ordering 4) (pc ordering 5) (role ordering 4) (by cases ordering <;> rfl) b4
      (before (role ordering 4)) (by cases ordering <;> simp [b0,b1,b2,b3,b4,role,bankRole,aux,ordinal])
  let b6:Stack→List Bool:=Function.update b5 (role ordering 5) []
  have h5:Runs program ((before (role ordering 5)).length+1) (pc ordering 5) b5 (pc ordering 6) b6:=
    drain_loop (pc ordering 5) (pc ordering 6) (role ordering 5) (by cases ordering <;> rfl) b5
      (before (role ordering 5)) (by cases ordering <;> simp [b0,b1,b2,b3,b4,b5,role,bankRole,aux,ordinal])
  let b7:Stack→List Bool:=Function.update b6 (role ordering 6) []
  have h6:Runs program ((before (role ordering 6)).length+1) (pc ordering 6) b6 (pc ordering 7) b7:=
    drain_loop (pc ordering 6) (pc ordering 7) (role ordering 6) (by cases ordering <;> rfl) b6
      (before (role ordering 6)) (by cases ordering <;> simp [b0,b1,b2,b3,b4,b5,b6,role,bankRole,aux,ordinal])
  let b8:Stack→List Bool:=Function.update b7 (role ordering 7) []
  have h7:Runs program ((before (role ordering 7)).length+1) (pc ordering 7) b7 (pc ordering 8) b8:=
    drain_loop (pc ordering 7) (pc ordering 8) (role ordering 7) (by cases ordering <;> rfl) b7
      (before (role ordering 7)) (by cases ordering <;> simp [b0,b1,b2,b3,b4,b5,b6,b7,role,bankRole,aux,ordinal])
  let b9:Stack→List Bool:=Function.update b8 (role ordering 8) []
  have h8:Runs program ((before (role ordering 8)).length+1) (pc ordering 8) b8 (pc ordering 9) b9:=
    drain_loop (pc ordering 8) (pc ordering 9) (role ordering 8) (by cases ordering <;> rfl) b8
      (before (role ordering 8)) (by cases ordering <;> simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,role,bankRole,aux,ordinal])
  let b10:Stack→List Bool:=Function.update b9 (role ordering 9) []
  have h9:Runs program ((before (role ordering 9)).length+1) (pc ordering 9) b9 (pc ordering 10) b10:=
    drain_loop (pc ordering 9) (pc ordering 10) (role ordering 9) (by cases ordering <;> rfl) b9
      (before (role ordering 9)) (by cases ordering <;> simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,role,bankRole,aux,ordinal])
  let b11:Stack→List Bool:=Function.update b10 (role ordering 10) []
  have h10:Runs program ((before (role ordering 10)).length+1) (pc ordering 10) b10 (pc ordering 11) b11:=
    drain_loop (pc ordering 10) (pc ordering 11) (role ordering 10) (by cases ordering <;> rfl) b10
      (before (role ordering 10)) (by cases ordering <;> simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,role,bankRole,aux,ordinal])
  let b12:Stack→List Bool:=Function.update b11 (role ordering 11) []
  have h11:Runs program ((before (role ordering 11)).length+1) (pc ordering 11) b11 (pc ordering 12) b12:=
    drain_loop (pc ordering 11) (pc ordering 12) (role ordering 11) (by cases ordering <;> rfl) b11
      (before (role ordering 11)) (by cases ordering <;> simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,role,bankRole,aux,ordinal])
  let b13:Stack→List Bool:=Function.update b12 (role ordering 12) []
  have h12:Runs program ((before (role ordering 12)).length+1) (pc ordering 12) b12 (pc ordering 13) b13:=
    drain_loop (pc ordering 12) (pc ordering 13) (role ordering 12) (by cases ordering <;> rfl) b12
      (before (role ordering 12)) (by cases ordering <;> simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,role,bankRole,aux,ordinal])
  have hwhole:=join h0 (join h1 (join h2 (join h3 (join h4 (join h5 (join h6 (join h7 (join h8 (join h9 (join h10 (join h11 (h12))))))))))))
  have ht:((before (role ordering 0)).length+1)+((before (role ordering 1)).length+1)+((before (role ordering 2)).length+1)+((before (role ordering 3)).length+1)+((before (role ordering 4)).length+1)+((before (role ordering 5)).length+1)+((before (role ordering 6)).length+1)+((before (role ordering 7)).length+1)+((before (role ordering 8)).length+1)+((before (role ordering 9)).length+1)+((before (role ordering 10)).length+1)+((before (role ordering 11)).length+1)+((before (role ordering 12)).length+1)=timeBound ordering before:=by dsimp only [timeBound];omega
  simpa only [←ht,Nat.add_assoc,result,b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13] using hwhole
/-- Every physical conversion role is really empty. -/
theorem result_role (ordering:Bool) (before:Stack→List Bool) (i:Fin 13):result ordering before (role ordering i)=[]:=by
  fin_cases i <;> cases ordering <;> rfl
/-- Complete retention outside the actual drained word image. -/
theorem result_other (ordering:Bool) (before:Stack→List Bool) (k:Stack)
    (h:∀i,role ordering i≠k):result ordering before k=before k:=by
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
  simp only [result,Function.update_of_ne h12,Function.update_of_ne h11,Function.update_of_ne h10,Function.update_of_ne h9,Function.update_of_ne h8,Function.update_of_ne h7,Function.update_of_ne h6,Function.update_of_ne h5,Function.update_of_ne h4,Function.update_of_ne h3,Function.update_of_ne h2,Function.update_of_ne h1,Function.update_of_ne h0]
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryPortReuse

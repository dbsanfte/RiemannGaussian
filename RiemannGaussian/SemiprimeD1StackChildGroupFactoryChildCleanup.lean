/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryPrimitives
/-! # Complete paid six-field cleanup at both child scan sites
Every acquired raw child field and its actual global position are physically
drained before the next child endpoint is read.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryChildCleanup
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryWiring
open SemiprimeD1StackChildGroupFactory SemiprimeD1StackChildGroupFactoryPrimitives
open SemiprimeD1StackProcedureTrace
/-- The six actual parsed child roles, fixed before every input. -/
def role:Fin 6→Stack
  | 0=>aux .ownerKey
  | 1=>aux .sourceKey
  | 2=>aux .slotWord
  | 3=>aux .edgeWord
  | 4=>aux .sideWord
  | 5=>aux .globalPosition
/-- Both fixed cleanup families and their actual inner-loop continuation. -/
def pc (search:Bool) (slot:Fin 7):Label:=if search then match slot.val with
  | 0=>(.local 12 30)
  | 1=>(.local 12 31)
  | 2=>(.local 13 0)
  | 3=>(.local 13 1)
  | 4=>(.local 13 2)
  | 5=>(.local 13 3)
  | _=>(.local 12 9)
else match slot.val with
  | 0=>(.local 10 9)
  | 1=>(.local 10 10)
  | 2=>(.local 10 11)
  | 3=>(.local 10 12)
  | 4=>(.local 10 13)
  | 5=>(.local 10 14)
  | _=>(.local 9 20)
/-- Complete actual physical cleanup, retaining all unrelated words. -/
def result (before:Stack→List Bool):Stack→List Bool:=
  Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (before) (aux .ownerKey) []) (aux .sourceKey) []) (aux .slotWord) []) (aux .edgeWord) []) (aux .sideWord) []) (aux .globalPosition) []
/-- Own actual payload pops and every real EOF pop. -/
def timeBound (before:Stack→List Bool):Nat:=
  (before (aux .ownerKey)).length+(before (aux .sourceKey)).length+(before (aux .slotWord)).length+(before (aux .edgeWord)).length+(before (aux .sideWord)).length+(before (aux .globalPosition)).length+6
/-- Whole six-field erasure at either actual source location. -/
theorem source_trace (search:Bool) (before:Stack→List Bool):
    Runs program (timeBound before) (pc search 0) before (pc search 6) (result before):=by
  let b0:=before
  let b1:Stack→List Bool:=Function.update b0 (aux .ownerKey) []
  have h0:Runs program ((before (aux .ownerKey)).length+1) (pc search 0) b0 (pc search 1) b1:=
    drain_loop (pc search 0) (pc search 1) (aux .ownerKey) (by cases search <;> rfl) b0 (before (aux .ownerKey)) (by simp [b0,aux])
  let b2:Stack→List Bool:=Function.update b1 (aux .sourceKey) []
  have h1:Runs program ((before (aux .sourceKey)).length+1) (pc search 1) b1 (pc search 2) b2:=
    drain_loop (pc search 1) (pc search 2) (aux .sourceKey) (by cases search <;> rfl) b1 (before (aux .sourceKey)) (by simp [b0,b1,aux])
  let b3:Stack→List Bool:=Function.update b2 (aux .slotWord) []
  have h2:Runs program ((before (aux .slotWord)).length+1) (pc search 2) b2 (pc search 3) b3:=
    drain_loop (pc search 2) (pc search 3) (aux .slotWord) (by cases search <;> rfl) b2 (before (aux .slotWord)) (by simp [b0,b1,b2,aux])
  let b4:Stack→List Bool:=Function.update b3 (aux .edgeWord) []
  have h3:Runs program ((before (aux .edgeWord)).length+1) (pc search 3) b3 (pc search 4) b4:=
    drain_loop (pc search 3) (pc search 4) (aux .edgeWord) (by cases search <;> rfl) b3 (before (aux .edgeWord)) (by simp [b0,b1,b2,b3,aux])
  let b5:Stack→List Bool:=Function.update b4 (aux .sideWord) []
  have h4:Runs program ((before (aux .sideWord)).length+1) (pc search 4) b4 (pc search 5) b5:=
    drain_loop (pc search 4) (pc search 5) (aux .sideWord) (by cases search <;> rfl) b4 (before (aux .sideWord)) (by simp [b0,b1,b2,b3,b4,aux])
  let b6:Stack→List Bool:=Function.update b5 (aux .globalPosition) []
  have h5:Runs program ((before (aux .globalPosition)).length+1) (pc search 5) b5 (pc search 6) b6:=
    drain_loop (pc search 5) (pc search 6) (aux .globalPosition) (by cases search <;> rfl) b5 (before (aux .globalPosition)) (by simp [b0,b1,b2,b3,b4,b5,aux])
  have hwhole:=join h0 (join h1 (join h2 (join h3 (join h4 (h5)))))
  have ht:((before (aux .ownerKey)).length+1)+((before (aux .sourceKey)).length+1)+((before (aux .slotWord)).length+1)+((before (aux .edgeWord)).length+1)+((before (aux .sideWord)).length+1)+((before (aux .globalPosition)).length+1)=timeBound before:=by dsimp only [timeBound];omega
  simpa only [←ht,Nat.add_assoc,result,b0,b1,b2,b3,b4,b5,b6] using hwhole
/-- Every acquired raw child field has really been erased. -/
theorem result_role (before:Stack→List Bool) (i:Fin 6):result before (role i)=[]:=by fin_cases i <;> rfl
/-- Every other caller word is retained literally. -/
theorem result_other (before:Stack→List Bool) (k:Stack) (h:∀i,role i≠k):result before k=before k:=by
  have h0:=Ne.symm (h 0)
  have h1:=Ne.symm (h 1)
  have h2:=Ne.symm (h 2)
  have h3:=Ne.symm (h 3)
  have h4:=Ne.symm (h 4)
  have h5:=Ne.symm (h 5)
  simp only [role] at h0 h1 h2 h3 h4 h5
  simp only [result,Function.update_of_ne h5,Function.update_of_ne h4,Function.update_of_ne h3,Function.update_of_ne h2,Function.update_of_ne h1,Function.update_of_ne h0]
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryChildCleanup

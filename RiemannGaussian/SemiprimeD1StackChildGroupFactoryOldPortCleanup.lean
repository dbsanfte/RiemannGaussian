/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryPrimitives
/-! # Complete paid original-port cleanup at both actual source sites
Every acquired original vertex/edge/side word is physically erased either
before its real first-index search or before skipping to the next old port.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryOldPortCleanup
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryWiring
open SemiprimeD1StackChildGroupFactory SemiprimeD1StackChildGroupFactoryPrimitives
open SemiprimeD1StackProcedureTrace
/-- The three actual raw original-port fields. -/
def role:Fin 3→Stack
  | 0=>aux .ownerKey
  | 1=>aux .edgeWord
  | 2=>aux .sideWord
/-- Two fixed actual code families: start real search, or skip this other vertex. -/
def pc (search:Bool) (slot:Fin 4):Label:=if search then match slot.val with
  | 0=>(.local 11 24)
  | 1=>(.local 11 25)
  | 2=>(.local 11 26)
  | _=>(.local 11 27)
else match slot.val with
  | 0=>(.local 14 6)
  | 1=>(.local 14 7)
  | 2=>(.local 14 8)
  | _=>(.local 11 7)
/-- Exact actual full115-word erasure effect. -/
def result (before:Stack→List Bool):Stack→List Bool:=
  Function.update (Function.update (Function.update (before) (aux .ownerKey) []) (aux .edgeWord) []) (aux .sideWord) []
/-- All actual raw bytes and three real EOF pops. -/
def timeBound (before:Stack→List Bool):Nat:=
  (before (aux .ownerKey)).length+(before (aux .edgeWord)).length+(before (aux .sideWord)).length+3
/-- Literal actual three-field erasure at either real caller site. -/
theorem source_trace (search:Bool) (before:Stack→List Bool):
    Runs program (timeBound before) (pc search 0) before (pc search 3) (result before):=by
  let b0:=before
  let b1:Stack→List Bool:=Function.update b0 (aux .ownerKey) []
  have h0:Runs program ((before (aux .ownerKey)).length+1) (pc search 0) b0 (pc search 1) b1:=
    drain_loop (pc search 0) (pc search 1) (aux .ownerKey) (by cases search <;> rfl) b0 (before (aux .ownerKey)) (by simp [b0,aux])
  let b2:Stack→List Bool:=Function.update b1 (aux .edgeWord) []
  have h1:Runs program ((before (aux .edgeWord)).length+1) (pc search 1) b1 (pc search 2) b2:=
    drain_loop (pc search 1) (pc search 2) (aux .edgeWord) (by cases search <;> rfl) b1 (before (aux .edgeWord)) (by simp [b0,b1,aux])
  let b3:Stack→List Bool:=Function.update b2 (aux .sideWord) []
  have h2:Runs program ((before (aux .sideWord)).length+1) (pc search 2) b2 (pc search 3) b3:=
    drain_loop (pc search 2) (pc search 3) (aux .sideWord) (by cases search <;> rfl) b2 (before (aux .sideWord)) (by simp [b0,b1,b2,aux])
  have hwhole:=join h0 (join h1 h2)
  have ht:((before (aux .ownerKey)).length+1)+((before (aux .edgeWord)).length+1)+((before (aux .sideWord)).length+1)=timeBound before:=by dsimp only [timeBound];omega
  simpa only [←ht,Nat.add_assoc,result,b0,b1,b2,b3] using hwhole
/-- Every original-port field is physically empty. -/
theorem result_role (before:Stack→List Bool) (i:Fin 3):result before (role i)=[]:=by fin_cases i <;> rfl
/-- All actual caller/cache words outside those three fields are retained literally. -/
theorem result_other (before:Stack→List Bool) (k:Stack) (h:∀i,role i≠k):result before k=before k:=by
  have h0:=Ne.symm (h 0)
  have h1:=Ne.symm (h 1)
  have h2:=Ne.symm (h 2)
  simp only [role] at h0 h1 h2
  simp only [result,Function.update_of_ne h2,Function.update_of_ne h1,Function.update_of_ne h0]
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryOldPortCleanup

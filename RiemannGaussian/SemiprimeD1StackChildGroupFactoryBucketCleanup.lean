/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketParse
/-! # Complete paid per-incidence raw-field erasure
Every parsed field is physically drained through its actual EOF instruction.
The five finite positions are already literal source labels, not input counts.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketCleanup
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryWiring
open SemiprimeD1StackChildGroupFactory SemiprimeD1StackChildGroupFactoryPrimitives
open SemiprimeD1StackChildGroupFactoryBucketParse (Endpoint)
open SemiprimeD1StackProcedureTrace
/-- The exact five actual raw-field roles. -/
def role:Fin 5→Stack
  | 0=>aux .ownerKey
  | 1=>aux .sourceKey
  | 2=>aux .slotWord
  | 3=>aux .edgeWord
  | 4=>aux .sideWord
/-- Exact words acquired by the preceding actual parser. -/
def word (f:Endpoint):Fin 5→List Bool
  | 0=>f.vertex
  | 1=>f.packet
  | 2=>f.slot
  | 3=>f.edge
  | 4=>f.side
/-- Actual fixed cleanup sites, ending at the real endpoint-reader loop. -/
def pc:Fin 6→Label
  | 0=>(.local 7 31)
  | 1=>(.local 8 0)
  | 2=>(.local 8 1)
  | 3=>(.local 8 2)
  | 4=>(.local 8 3)
  | 5=>(.local 6 23)
/-- Complete physical effect; every other115-role word is retained. -/
def result (before:Stack→List Bool):Stack→List Bool:=
  Function.update (Function.update (Function.update (Function.update (Function.update before
    (aux .ownerKey) []) (aux .sourceKey) []) (aux .slotWord) []) (aux .edgeWord) []) (aux .sideWord) []
/-- Every actual field pop and every actual EOF pop is paid. -/
def timeBound (f:Endpoint):Nat:=f.vertex.length+f.packet.length+f.slot.length+f.edge.length+f.side.length+5
/-- Complete actual physical cleanup between two bucket endpoint visits. -/
theorem source_trace (before:Stack→List Bool) (f:Endpoint)
    (hread:∀i,before (role i)=word f i):
    Runs program (timeBound f) (pc 0) before (pc 5) (result before):=by
  have hx0:before (aux .ownerKey)=f.vertex:=hread 0
  have hx1:before (aux .sourceKey)=f.packet:=hread 1
  have hx2:before (aux .slotWord)=f.slot:=hread 2
  have hx3:before (aux .edgeWord)=f.edge:=hread 3
  have hx4:before (aux .sideWord)=f.side:=hread 4
  simp only [aux] at hx0 hx1 hx2 hx3 hx4
  let b0:=before
  let b1:Stack→List Bool:=Function.update b0 (aux .ownerKey) []
  have h0:Runs program (f.vertex.length+1) (pc 0) b0 (pc 1) b1:=
    drain_loop (pc 0) (pc 1) (aux .ownerKey) rfl b0 f.vertex (by simp [b0,aux,hx0])
  let b2:Stack→List Bool:=Function.update b1 (aux .sourceKey) []
  have h1:Runs program (f.packet.length+1) (pc 1) b1 (pc 2) b2:=
    drain_loop (pc 1) (pc 2) (aux .sourceKey) rfl b1 f.packet (by simp [b0,b1,aux,hx1])
  let b3:Stack→List Bool:=Function.update b2 (aux .slotWord) []
  have h2:Runs program (f.slot.length+1) (pc 2) b2 (pc 3) b3:=
    drain_loop (pc 2) (pc 3) (aux .slotWord) rfl b2 f.slot (by simp [b0,b1,b2,aux,hx2])
  let b4:Stack→List Bool:=Function.update b3 (aux .edgeWord) []
  have h3:Runs program (f.edge.length+1) (pc 3) b3 (pc 4) b4:=
    drain_loop (pc 3) (pc 4) (aux .edgeWord) rfl b3 f.edge (by simp [b0,b1,b2,b3,aux,hx3])
  let b5:Stack→List Bool:=Function.update b4 (aux .sideWord) []
  have h4:Runs program (f.side.length+1) (pc 4) b4 (pc 5) b5:=
    drain_loop (pc 4) (pc 5) (aux .sideWord) rfl b4 f.side (by simp [b0,b1,b2,b3,b4,aux,hx4])
  have hwhole:=join h0 (join h1 (join h2 (join h3 h4)))
  have ht:(f.vertex.length+1)+(f.packet.length+1)+(f.slot.length+1)+(f.edge.length+1)+(f.side.length+1)=timeBound f:=by dsimp only [timeBound];omega
  simpa only [←ht,Nat.add_assoc,result,b0,b1,b2,b3,b4,b5] using hwhole
/-- Every actual raw-field tape is empty at the next endpoint visit. -/
theorem result_role (before:Stack→List Bool) (i:Fin 5):result before (role i)=[]:=by fin_cases i <;> rfl
/-- All roles outside these five tapes retain their actual bytes. -/
theorem result_other (before:Stack→List Bool) (k:Stack) (h:∀i,role i≠k):result before k=before k:=by
  have h0:=Ne.symm (h 0)
  have h1:=Ne.symm (h 1)
  have h2:=Ne.symm (h 2)
  have h3:=Ne.symm (h 3)
  have h4:=Ne.symm (h 4)
  simp only [role] at h0 h1 h2 h3 h4
  simp only [result,Function.update_of_ne h4,Function.update_of_ne h3,
    Function.update_of_ne h2,Function.update_of_ne h1,Function.update_of_ne h0]
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketCleanup

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryEndpointParse
/-! # Complete paid per-incidence raw-field erasure
Every parsed field is physically drained through its actual EOF instruction.
The seven finite positions are already literal source labels, not input counts.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryEndpointCleanup
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryWiring
open SemiprimeD1StackChildGroupFactory SemiprimeD1StackChildGroupFactoryPrimitives
open SemiprimeD1StackChildGroupFactoryEndpointParse (Fields)
open SemiprimeD1StackProcedureTrace
/-- The exact seven actual raw-field roles. -/
def role:Fin 7→Stack
  | 0=>aux .ownerKey
  | 1=>aux .factorKey
  | 2=>aux .sourceKey
  | 3=>aux .paddingKey
  | 4=>aux .packetKey
  | 5=>aux .slotWord
  | 6=>aux .edgeWord
/-- Exact words acquired by the real preceding parser. -/
def word (f:Fields):Fin 7→List Bool
  | 0=>f.owner
  | 1=>f.factor
  | 2=>f.source
  | 3=>f.padding
  | 4=>f.packet
  | 5=>f.slot
  | 6=>f.edge
/-- The actual fixed cleanup positions and their loop continuation. -/
def pc:Fin 8→Label
  | 0=>(.local 6 6)
  | 1=>(.local 6 7)
  | 2=>(.local 6 8)
  | 3=>(.local 6 9)
  | 4=>(.local 6 10)
  | 5=>(.local 6 11)
  | 6=>(.local 6 12)
  | 7=>(.local 2 20)
/-- Complete physical effect; every other115-role word is retained. -/
def result (before:Stack→List Bool):Stack→List Bool:=
  Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (before) (aux .ownerKey) []) (aux .factorKey) []) (aux .sourceKey) []) (aux .paddingKey) []) (aux .packetKey) []) (aux .slotWord) []) (aux .edgeWord) []
/-- Own sum of all actual payload pops and all seven actual EOF pops. -/
def timeBound (f:Fields):Nat:=f.owner.length+f.factor.length+f.source.length+f.padding.length+
  f.packet.length+f.slot.length+f.edge.length+7
/-- Whole real per-incidence cleanup, with no implicit discarded raw fields. -/
theorem source_trace (before:Stack→List Bool) (f:Fields)
    (hread:∀i,before (role i)=word f i):
    Runs program (timeBound f) (pc 0) before (pc 7) (result before):=by
  have hx0:before (aux .ownerKey)=f.owner:=hread 0
  have hx1:before (aux .factorKey)=f.factor:=hread 1
  have hx2:before (aux .sourceKey)=f.source:=hread 2
  have hx3:before (aux .paddingKey)=f.padding:=hread 3
  have hx4:before (aux .packetKey)=f.packet:=hread 4
  have hx5:before (aux .slotWord)=f.slot:=hread 5
  have hx6:before (aux .edgeWord)=f.edge:=hread 6
  simp only [aux] at hx0 hx1 hx2 hx3 hx4 hx5 hx6
  let b0:=before
  let b1:Stack→List Bool:=Function.update b0 (aux .ownerKey) []
  have h0:Runs program (f.owner.length+1) (pc 0) b0 (pc 1) b1:=
    drain_loop (pc 0) (pc 1) (aux .ownerKey) rfl b0 f.owner (by simp [b0,aux,hx0])
  let b2:Stack→List Bool:=Function.update b1 (aux .factorKey) []
  have h1:Runs program (f.factor.length+1) (pc 1) b1 (pc 2) b2:=
    drain_loop (pc 1) (pc 2) (aux .factorKey) rfl b1 f.factor (by simp [b0,b1,aux,hx1])
  let b3:Stack→List Bool:=Function.update b2 (aux .sourceKey) []
  have h2:Runs program (f.source.length+1) (pc 2) b2 (pc 3) b3:=
    drain_loop (pc 2) (pc 3) (aux .sourceKey) rfl b2 f.source (by simp [b0,b1,b2,aux,hx2])
  let b4:Stack→List Bool:=Function.update b3 (aux .paddingKey) []
  have h3:Runs program (f.padding.length+1) (pc 3) b3 (pc 4) b4:=
    drain_loop (pc 3) (pc 4) (aux .paddingKey) rfl b3 f.padding (by simp [b0,b1,b2,b3,aux,hx3])
  let b5:Stack→List Bool:=Function.update b4 (aux .packetKey) []
  have h4:Runs program (f.packet.length+1) (pc 4) b4 (pc 5) b5:=
    drain_loop (pc 4) (pc 5) (aux .packetKey) rfl b4 f.packet (by simp [b0,b1,b2,b3,b4,aux,hx4])
  let b6:Stack→List Bool:=Function.update b5 (aux .slotWord) []
  have h5:Runs program (f.slot.length+1) (pc 5) b5 (pc 6) b6:=
    drain_loop (pc 5) (pc 6) (aux .slotWord) rfl b5 f.slot (by simp [b0,b1,b2,b3,b4,b5,aux,hx5])
  let b7:Stack→List Bool:=Function.update b6 (aux .edgeWord) []
  have h6:Runs program (f.edge.length+1) (pc 6) b6 (pc 7) b7:=
    drain_loop (pc 6) (pc 7) (aux .edgeWord) rfl b6 f.edge (by simp [b0,b1,b2,b3,b4,b5,b6,aux,hx6])
  have hwhole:=join h0 (join h1 (join h2 (join h3 (join h4 (join h5 (h6))))))
  have ht:((f.owner.length+1))+((f.factor.length+1))+((f.source.length+1))+((f.padding.length+1))+((f.packet.length+1))+((f.slot.length+1))+((f.edge.length+1))=timeBound f:=by dsimp only [timeBound];omega
  simpa only [←ht,Nat.add_assoc,result,b0,b1,b2,b3,b4,b5,b6,b7] using hwhole
/-- Every one of the seven actual fields is empty at the next real row boundary. -/
theorem result_role (before:Stack→List Bool) (i:Fin 7):result before (role i)=[]:=by
  fin_cases i <;> rfl
/-- The actual cleanup retains every physical role outside its fixed seven-word image. -/
theorem result_other (before:Stack→List Bool) (k:Stack) (h:∀i,role i≠k):result before k=before k:=by
  have h0:=Ne.symm (h 0)
  have h1:=Ne.symm (h 1)
  have h2:=Ne.symm (h 2)
  have h3:=Ne.symm (h 3)
  have h4:=Ne.symm (h 4)
  have h5:=Ne.symm (h 5)
  have h6:=Ne.symm (h 6)
  simp only [role] at h0 h1 h2 h3 h4 h5 h6
  simp only [result,Function.update_of_ne h6,Function.update_of_ne h5,
    Function.update_of_ne h4,Function.update_of_ne h3,Function.update_of_ne h2,
    Function.update_of_ne h1,Function.update_of_ne h0]
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryEndpointCleanup

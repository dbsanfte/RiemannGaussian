/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryFields
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketEmit
/-! # Actual six-field child-endpoint parser at both literal scan sites
The Boolean theorem index names two fixed source-code families only; no search
mode, child record or decoded address is an additional runtime operand.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryChildParse
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryWiring
open SemiprimeD1StackChildGroupFactory SemiprimeD1StackChildGroupFactoryPrimitives
open SemiprimeD1StackChildGroupFactoryFields SemiprimeD1StackProcedureTrace
open SemiprimeD1StackChildGroupFactoryBucketParse (Endpoint)
open SemiprimeD1StackChildGroupFactoryBucketEmit (payload)
open SemiprimeSourceHistogramKeyBits (frame)
/-- Two literal location families, fixed before all inputs. -/
def pc (search:Bool) (slot:Fin 18):Label:=if search then match slot.val with
  | 0=>(.local 12 9)
  | 1=>(.local 12 10)
  | 2=>(.local 12 11)
  | 3=>(.local 12 12)
  | 4=>(.local 12 13)
  | 5=>(.local 12 14)
  | 6=>(.local 12 15)
  | 7=>(.local 12 16)
  | 8=>(.local 12 17)
  | 9=>(.local 12 18)
  | 10=>(.local 12 19)
  | 11=>(.local 12 20)
  | 12=>(.local 12 21)
  | 13=>(.local 12 22)
  | 14=>(.local 12 23)
  | 15=>(.local 12 24)
  | 16=>(.local 12 25)
  | 17=>(.local 12 26)
  | _=>(.local 12 26)
else match slot.val with
  | 0=>(.local 9 20)
  | 1=>(.local 9 21)
  | 2=>(.local 9 22)
  | 3=>(.local 9 23)
  | 4=>(.local 9 24)
  | 5=>(.local 9 25)
  | 6=>(.local 9 26)
  | 7=>(.local 9 27)
  | 8=>(.local 9 28)
  | 9=>(.local 9 29)
  | 10=>(.local 9 30)
  | 11=>(.local 9 31)
  | 12=>(.local 10 0)
  | 13=>(.local 10 1)
  | 14=>(.local 10 2)
  | 15=>(.local 10 3)
  | 16=>(.local 10 4)
  | 17=>(.local 10 5)
  | _=>(.local 10 5)
/-- Every real destination and parser-private role is physically fresh. -/
def cleanRoles:List Stack:=[aux .ownerKey,aux .sourceKey,aux .slotWord,aux .edgeWord,aux .sideWord,
  aux .globalPosition,aux .rowBuffer,field (.inl .scratch),field (.inr ())]
/-- Full actual parsed child bank with literal original fields and actual fresh-global ID. -/
def result (before:Stack→List Bool) (e:Endpoint) (position tail:List Bool):Stack→List Bool:=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update before (aux .endpointReader) tail) (aux .ownerKey) e.vertex)
      (aux .sourceKey) e.packet) (aux .slotWord) e.slot) (aux .edgeWord) e.edge) (aux .sideWord) e.side)
      (aux .globalPosition) position
/-- Seven actual Field calls/validity pops, one vector-tag pop and one actual EOF test. -/
def timeBound (e:Endpoint) (position:List Bool):Nat:=
  8*((payload e position).length+e.vertex.length+e.packet.length+e.slot.length+e.edge.length+e.side.length+position.length)+58
/-- The literal six-field child source at either actually present program site. -/
theorem source_trace (search:Bool) (before:Stack→List Bool) (e:Endpoint) (position tail:List Bool)
    (hi:before (aux .endpointReader)=true::frame (payload e position) tail)
    (hz:∀k∈cleanRoles,before k=[]):
    Runs program (timeBound e position) (pc search 0) before (pc search 17) (result before e position tail):=by
  have hz0:before (aux .ownerKey)=[]:=hz _ (by simp [cleanRoles])
  have hz1:before (aux .sourceKey)=[]:=hz _ (by simp [cleanRoles])
  have hz2:before (aux .slotWord)=[]:=hz _ (by simp [cleanRoles])
  have hz3:before (aux .edgeWord)=[]:=hz _ (by simp [cleanRoles])
  have hz4:before (aux .sideWord)=[]:=hz _ (by simp [cleanRoles])
  have hz5:before (aux .globalPosition)=[]:=hz _ (by simp [cleanRoles])
  have hz6:before (aux .rowBuffer)=[]:=hz _ (by simp [cleanRoles])
  have hz7:before (field (.inl .scratch))=[]:=hz _ (by simp [cleanRoles])
  have hz8:before (field (.inr ()))=[]:=hz _ (by simp [cleanRoles])
  simp only [aux,field,payload] at hi hz0 hz1 hz2 hz3 hz4 hz5 hz6 hz7 hz8
  let b0:=before
  let b1:Stack→List Bool:=Function.update b0 (aux .endpointReader) (frame (payload e position) tail)
  have h0a:=pop_run (pc search 0) abort (pc search 1) (pc search 2) (aux .endpointReader) b0
      (true::frame (payload e position) tail) (by cases search <;> rfl) (by simp [b0,aux,payload,hi])
  have h0:Runs program 1 (pc search 0) b0 (pc search 2) b1:=by
    simpa only [List.head?_cons,List.tail_cons,SemiprimeD1StackBytecode.choose] using h0a
  let b2:Stack→List Bool:=Function.update (Function.update b1 (aux .endpointReader) tail) (aux .rowBuffer) (payload e position)
  have h1:Runs program (8*((payload e position)).length+8) (pc search 2) b1 (pc search 4) b2:=
    field_read 11 (pc search 2) (pc search 3) (pc search 4) abort abort
      (by cases search <;> rfl) (by cases search <;> rfl)
      b1 (payload e position) tail (by simp [b0,b1,aux,fieldStack,fieldPorts,payload]) (by simp [b0,b1,aux,fieldStack,fieldPorts,payload,hz6]) (by simp [b0,b1,aux,field,payload,hz7]) (by simp [b0,b1,aux,field,payload,hz8])
  let b3:Stack→List Bool:=Function.update (Function.update b2 (aux .rowBuffer) (frame e.packet (frame e.slot (frame e.edge (frame e.side (frame position [])))))) (aux .ownerKey) e.vertex
  have h2:Runs program (8*(e.vertex).length+8) (pc search 4) b2 (pc search 6) b3:=
    field_read 12 (pc search 4) (pc search 5) (pc search 6) abort abort
      (by cases search <;> rfl) (by cases search <;> rfl)
      b2 e.vertex (frame e.packet (frame e.slot (frame e.edge (frame e.side (frame position []))))) (by simp [b0,b1,b2,aux,fieldStack,fieldPorts,payload]) (by simp [b0,b1,b2,aux,fieldStack,fieldPorts,payload,hz0]) (by simp [b0,b1,b2,aux,field,payload,hz7]) (by simp [b0,b1,b2,aux,field,payload,hz8])
  let b4:Stack→List Bool:=Function.update (Function.update b3 (aux .rowBuffer) (frame e.slot (frame e.edge (frame e.side (frame position []))))) (aux .sourceKey) e.packet
  have h3:Runs program (8*(e.packet).length+8) (pc search 6) b3 (pc search 8) b4:=
    field_read 13 (pc search 6) (pc search 7) (pc search 8) abort abort
      (by cases search <;> rfl) (by cases search <;> rfl)
      b3 e.packet (frame e.slot (frame e.edge (frame e.side (frame position [])))) (by simp [b0,b1,b2,b3,aux,fieldStack,fieldPorts,payload]) (by simp [b0,b1,b2,b3,aux,fieldStack,fieldPorts,payload,hz1]) (by simp [b0,b1,b2,b3,aux,field,payload,hz7]) (by simp [b0,b1,b2,b3,aux,field,payload,hz8])
  let b5:Stack→List Bool:=Function.update (Function.update b4 (aux .rowBuffer) (frame e.edge (frame e.side (frame position [])))) (aux .slotWord) e.slot
  have h4:Runs program (8*(e.slot).length+8) (pc search 8) b4 (pc search 10) b5:=
    field_read 14 (pc search 8) (pc search 9) (pc search 10) abort abort
      (by cases search <;> rfl) (by cases search <;> rfl)
      b4 e.slot (frame e.edge (frame e.side (frame position []))) (by simp [b0,b1,b2,b3,b4,aux,fieldStack,fieldPorts,payload]) (by simp [b0,b1,b2,b3,b4,aux,fieldStack,fieldPorts,payload,hz2]) (by simp [b0,b1,b2,b3,b4,aux,field,payload,hz7]) (by simp [b0,b1,b2,b3,b4,aux,field,payload,hz8])
  let b6:Stack→List Bool:=Function.update (Function.update b5 (aux .rowBuffer) (frame e.side (frame position []))) (aux .edgeWord) e.edge
  have h5:Runs program (8*(e.edge).length+8) (pc search 10) b5 (pc search 12) b6:=
    field_read 15 (pc search 10) (pc search 11) (pc search 12) abort abort
      (by cases search <;> rfl) (by cases search <;> rfl)
      b5 e.edge (frame e.side (frame position [])) (by simp [b0,b1,b2,b3,b4,b5,aux,fieldStack,fieldPorts,payload]) (by simp [b0,b1,b2,b3,b4,b5,aux,fieldStack,fieldPorts,payload,hz3]) (by simp [b0,b1,b2,b3,b4,b5,aux,field,payload,hz7]) (by simp [b0,b1,b2,b3,b4,b5,aux,field,payload,hz8])
  let b7:Stack→List Bool:=Function.update (Function.update b6 (aux .rowBuffer) (frame position [])) (aux .sideWord) e.side
  have h6:Runs program (8*(e.side).length+8) (pc search 12) b6 (pc search 14) b7:=
    field_read 16 (pc search 12) (pc search 13) (pc search 14) abort abort
      (by cases search <;> rfl) (by cases search <;> rfl)
      b6 e.side (frame position []) (by simp [b0,b1,b2,b3,b4,b5,b6,aux,fieldStack,fieldPorts,payload]) (by simp [b0,b1,b2,b3,b4,b5,b6,aux,fieldStack,fieldPorts,payload,hz4]) (by simp [b0,b1,b2,b3,b4,b5,b6,aux,field,payload,hz7]) (by simp [b0,b1,b2,b3,b4,b5,b6,aux,field,payload,hz8])
  let b8:Stack→List Bool:=Function.update (Function.update b7 (aux .rowBuffer) []) (aux .globalPosition) position
  have h7:Runs program (8*(position).length+8) (pc search 14) b7 (pc search 16) b8:=
    field_read 19 (pc search 14) (pc search 15) (pc search 16) abort abort
      (by cases search <;> rfl) (by cases search <;> rfl)
      b7 position [] (by simp [b0,b1,b2,b3,b4,b5,b6,b7,aux,fieldStack,fieldPorts,payload]) (by simp [b0,b1,b2,b3,b4,b5,b6,b7,aux,fieldStack,fieldPorts,payload,hz5]) (by simp [b0,b1,b2,b3,b4,b5,b6,b7,aux,field,payload,hz7]) (by simp [b0,b1,b2,b3,b4,b5,b6,b7,aux,field,payload,hz8])
  have h8a:=peek_run (pc search 16) (pc search 17) abort abort (aux .rowBuffer) b8 []
      (by cases search <;> rfl) (by simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,aux,payload])
  have h8:Runs program 1 (pc search 16) b8 (pc search 17) b8:=by
    simpa only [List.head?_nil,SemiprimeD1StackBytecode.choose] using h8a
  have hout:b8=result before e position tail:=by
    funext k
    rcases k with k|k|k|k|k|k
    · simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,aux,payload,result]
    · simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,aux,payload,result]
    · simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,aux,payload,result]
    · simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,aux,payload,result]
    · simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,aux,payload,result]
    · cases k <;> simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,aux,payload,hz6,result]
  have hwhole:=join h0 (join h1 (join h2 (join h3 (join h4 (join h5 (join h6 (join h7 (h8))))))))
  rw [hout] at hwhole
  have ht:(1)+((8*((payload e position)).length+8))+((8*(e.vertex).length+8))+((8*(e.packet).length+8))+((8*(e.slot).length+8))+((8*(e.edge).length+8))+((8*(e.side).length+8))+((8*(position).length+8))+(1)=timeBound e position:=by dsimp only [timeBound];omega
  simpa only [←ht,Nat.add_assoc] using hwhole
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryChildParse

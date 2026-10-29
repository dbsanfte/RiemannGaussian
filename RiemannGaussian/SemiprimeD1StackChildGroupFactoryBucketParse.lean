/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryFields
/-! # Actual selected endpoint parsing inside every raw-packet scan
The record type describes already present bytes only. The fixed program
physically reads the vector tag and every framed field and tests actual EOF.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketParse
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryWiring
open SemiprimeD1StackChildGroupFactory SemiprimeD1StackChildGroupFactoryPrimitives
open SemiprimeD1StackChildGroupFactoryFields SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
/-- Raw acquired endpoint fields, never extra runtime operands. -/
structure Endpoint where
  /-- Actual original owner/factor vertex key. -/
  vertex:List Bool
  /-- Whole acquired raw packet word, retaining its padding. -/
  packet:List Bool
  /-- Actual original packet-slot field. -/
  slot:List Bool
  /-- Actual original occurrence edge-key field. -/
  edge:List Bool
  /-- Actual singleton endpoint-side field. -/
  side:List Bool
/-- Exact five-field raw endpoint payload. -/
def payload (e:Endpoint):List Bool:=frame e.vertex (frame e.packet (frame e.slot (frame e.edge (frame e.side []))))
/-- Exact raw endpoint vector. -/
def records:List Endpoint→List Bool
  | []=>[false]
  | e::es=>true::frame (payload e) (records es)
/-- All actual fresh destinations, including both real parser-private tapes. -/
def cleanRoles:List Stack:=[aux .ownerKey,aux .sourceKey,aux .slotWord,aux .edgeWord,aux .sideWord,
  aux .rowBuffer,field (.inl .scratch),field (.inr ())]
/-- Full115-word actual parse result. The whole raw packet is kept without normalization. -/
def result (before:Stack→List Bool) (e:Endpoint) (tail:List Bool):Stack→List Bool:=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update before (aux .endpointReader) tail) (aux .ownerKey) e.vertex)
      (aux .sourceKey) e.packet) (aux .slotWord) e.slot) (aux .edgeWord) e.edge) (aux .sideWord) e.side
/-- Six real Field calls with validity pops, one vector-tag pop and one actual EOF test. -/
def timeBound (e:Endpoint):Nat:=8*((payload e).length+e.vertex.length+e.packet.length+e.slot.length+e.edge.length+e.side.length)+50
/-- Actual bytecode path to the sentinel-protected whole-packet comparison. -/
theorem source_trace (before:Stack→List Bool) (e:Endpoint) (tail:List Bool)
    (hi:before (aux .endpointReader)=true::frame (payload e) tail)
    (hz:∀k∈cleanRoles,before k=[]):
    Runs program (timeBound e) (.local 6 23) before (.local 7 6) (result before e tail):=by
  have hz0:before (aux .ownerKey)=[]:=hz _ (by simp [cleanRoles])
  have hz1:before (aux .sourceKey)=[]:=hz _ (by simp [cleanRoles])
  have hz2:before (aux .slotWord)=[]:=hz _ (by simp [cleanRoles])
  have hz3:before (aux .edgeWord)=[]:=hz _ (by simp [cleanRoles])
  have hz4:before (aux .sideWord)=[]:=hz _ (by simp [cleanRoles])
  have hz5:before (aux .rowBuffer)=[]:=hz _ (by simp [cleanRoles])
  have hz6:before (field (.inl .scratch))=[]:=hz _ (by simp [cleanRoles])
  have hz7:before (field (.inr ()))=[]:=hz _ (by simp [cleanRoles])
  simp only [aux,field,payload] at hi hz0 hz1 hz2 hz3 hz4 hz5 hz6 hz7
  let b0:=before
  let b1:Stack→List Bool:=Function.update b0 (aux .endpointReader) (frame (payload e) tail)
  have h0a:=pop_run (.local 6 23) (.local 15 14) (.local 6 24) (.local 6 25) (aux .endpointReader) b0 (true::frame (payload e) tail) rfl (by simp [b0,aux,payload,hi])
  have h0:Runs program 1 (.local 6 23) b0 (.local 6 25) b1:=by
    simpa only [List.head?_cons,List.tail_cons,SemiprimeD1StackBytecode.choose] using h0a
  let b2:Stack→List Bool:=Function.update (Function.update b1 (aux .endpointReader) tail) (aux .rowBuffer) (payload e)
  have h1:Runs program (8*((payload e)).length+8) (.local 6 25) b1 (.local 6 27) b2:=
    field_read 11 (.local 6 25) (.local 6 26) (.local 6 27) abort abort rfl rfl
      b1 (payload e) tail (by simp [b0,b1,aux,fieldStack,fieldPorts,payload]) (by simp [b0,b1,aux,fieldStack,fieldPorts,payload,hz5]) (by simp [b0,b1,aux,field,payload,hz6]) (by simp [b0,b1,aux,field,payload,hz7])
  let b3:Stack→List Bool:=Function.update (Function.update b2 (aux .rowBuffer) (frame e.packet (frame e.slot (frame e.edge (frame e.side []))))) (aux .ownerKey) e.vertex
  have h2:Runs program (8*(e.vertex).length+8) (.local 6 27) b2 (.local 6 29) b3:=
    field_read 12 (.local 6 27) (.local 6 28) (.local 6 29) abort abort rfl rfl
      b2 e.vertex (frame e.packet (frame e.slot (frame e.edge (frame e.side [])))) (by simp [b0,b1,b2,aux,fieldStack,fieldPorts,payload]) (by simp [b0,b1,b2,aux,fieldStack,fieldPorts,payload,hz0]) (by simp [b0,b1,b2,aux,field,payload,hz6]) (by simp [b0,b1,b2,aux,field,payload,hz7])
  let b4:Stack→List Bool:=Function.update (Function.update b3 (aux .rowBuffer) (frame e.slot (frame e.edge (frame e.side [])))) (aux .sourceKey) e.packet
  have h3:Runs program (8*(e.packet).length+8) (.local 6 29) b3 (.local 6 31) b4:=
    field_read 13 (.local 6 29) (.local 6 30) (.local 6 31) abort abort rfl rfl
      b3 e.packet (frame e.slot (frame e.edge (frame e.side []))) (by simp [b0,b1,b2,b3,aux,fieldStack,fieldPorts,payload]) (by simp [b0,b1,b2,b3,aux,fieldStack,fieldPorts,payload,hz1]) (by simp [b0,b1,b2,b3,aux,field,payload,hz6]) (by simp [b0,b1,b2,b3,aux,field,payload,hz7])
  let b5:Stack→List Bool:=Function.update (Function.update b4 (aux .rowBuffer) (frame e.edge (frame e.side []))) (aux .slotWord) e.slot
  have h4:Runs program (8*(e.slot).length+8) (.local 6 31) b4 (.local 7 1) b5:=
    field_read 14 (.local 6 31) (.local 7 0) (.local 7 1) abort abort rfl rfl
      b4 e.slot (frame e.edge (frame e.side [])) (by simp [b0,b1,b2,b3,b4,aux,fieldStack,fieldPorts,payload]) (by simp [b0,b1,b2,b3,b4,aux,fieldStack,fieldPorts,payload,hz2]) (by simp [b0,b1,b2,b3,b4,aux,field,payload,hz6]) (by simp [b0,b1,b2,b3,b4,aux,field,payload,hz7])
  let b6:Stack→List Bool:=Function.update (Function.update b5 (aux .rowBuffer) (frame e.side [])) (aux .edgeWord) e.edge
  have h5:Runs program (8*(e.edge).length+8) (.local 7 1) b5 (.local 7 3) b6:=
    field_read 15 (.local 7 1) (.local 7 2) (.local 7 3) abort abort rfl rfl
      b5 e.edge (frame e.side []) (by simp [b0,b1,b2,b3,b4,b5,aux,fieldStack,fieldPorts,payload]) (by simp [b0,b1,b2,b3,b4,b5,aux,fieldStack,fieldPorts,payload,hz3]) (by simp [b0,b1,b2,b3,b4,b5,aux,field,payload,hz6]) (by simp [b0,b1,b2,b3,b4,b5,aux,field,payload,hz7])
  let b7:Stack→List Bool:=Function.update (Function.update b6 (aux .rowBuffer) []) (aux .sideWord) e.side
  have h6:Runs program (8*(e.side).length+8) (.local 7 3) b6 (.local 7 5) b7:=
    field_read 16 (.local 7 3) (.local 7 4) (.local 7 5) abort abort rfl rfl
      b6 e.side [] (by simp [b0,b1,b2,b3,b4,b5,b6,aux,fieldStack,fieldPorts,payload]) (by simp [b0,b1,b2,b3,b4,b5,b6,aux,fieldStack,fieldPorts,payload,hz4]) (by simp [b0,b1,b2,b3,b4,b5,b6,aux,field,payload,hz6]) (by simp [b0,b1,b2,b3,b4,b5,b6,aux,field,payload,hz7])
  have h7a:=peek_run (.local 7 5) (.local 7 6) (.local 15 14) (.local 15 14) (aux .rowBuffer) b7 [] rfl (by simp [b0,b1,b2,b3,b4,b5,b6,b7,aux,payload])
  have h7:Runs program 1 (.local 7 5) b7 (.local 7 6) b7:=by
    simpa only [List.head?_nil,SemiprimeD1StackBytecode.choose] using h7a
  have hout:b7=result before e tail:=by
    funext k
    rcases k with k|k|k|k|k|k
    · simp [b0,b1,b2,b3,b4,b5,b6,b7,aux,payload,result]
    · simp [b0,b1,b2,b3,b4,b5,b6,b7,aux,payload,result]
    · simp [b0,b1,b2,b3,b4,b5,b6,b7,aux,payload,result]
    · simp [b0,b1,b2,b3,b4,b5,b6,b7,aux,payload,result]
    · simp [b0,b1,b2,b3,b4,b5,b6,b7,aux,payload,result]
    · cases k <;> simp [b0,b1,b2,b3,b4,b5,b6,b7,aux,payload,hz5,result]
  have hwhole:=join h0 (join h1 (join h2 (join h3 (join h4 (join h5 (join h6 (h7)))))))
  rw [hout] at hwhole
  have ht:(1)+((8*((payload e)).length+8))+((8*(e.vertex).length+8))+((8*(e.packet).length+8))+((8*(e.slot).length+8))+((8*(e.edge).length+8))+((8*(e.side).length+8))+(1)=timeBound e:=by
    simp only [timeBound]
    omega
  simpa only [←ht,Nat.add_assoc] using hwhole
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketParse

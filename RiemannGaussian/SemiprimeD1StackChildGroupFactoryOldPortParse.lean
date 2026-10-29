/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryFields
/-! # Actual original-port record acquisition for first-index ordering
Every original endpoint record is retained in its original source order. Its
binary vertex/edge and literal side word are parsed from actual physical bytes.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryOldPortParse
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryWiring
open SemiprimeD1StackChildGroupFactory SemiprimeD1StackChildGroupFactoryPrimitives
open SemiprimeD1StackChildGroupFactoryFields SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
/-- Proof interpretation of three actual raw original-port fields, never a runtime object. -/
structure Point where
  /-- Actual original owner/factor vertex key. -/
  vertex:List Bool
  /-- Whole acquired original edge-key word. -/
  edge:List Bool
  /-- Actual singleton endpoint-side field. -/
  side:List Bool
/-- Exact original endpoint payload. -/
def payload (p:Point):List Bool:=frame p.vertex (frame p.edge (frame p.side []))
/-- Exact original endpoint vector grammar. -/
def records:List Point→List Bool
  | []=>[false]
  | p::ps=>true::frame (payload p) (records ps)
/-- Actual physically fresh destinations and real parser-private roles. -/
def cleanRoles:List Stack:=[aux .ownerKey,aux .edgeWord,aux .sideWord,aux .rowBuffer,
  field (.inl .scratch),field (.inr ())]
/-- Complete115-word actual read boundary. -/
def result (before:Stack→List Bool) (p:Point) (tail:List Bool):Stack→List Bool:=
  Function.update (Function.update (Function.update (Function.update before
    (aux .oldReader) tail) (aux .ownerKey) p.vertex) (aux .edgeWord) p.edge) (aux .sideWord) p.side
/-- Four actual Field calls with validity pops, actual tag pop and physical payload-EOF test. -/
def timeBound (p:Point):Nat:=8*((payload p).length+p.vertex.length+p.edge.length+p.side.length)+34
/-- Whole original-port record acquisition from real bytes, without a decoded original endpoint input. -/
theorem source_trace (before:Stack→List Bool) (p:Point) (tail:List Bool)
    (hi:before (aux .oldReader)=true::frame (payload p) tail)
    (hz:∀k∈cleanRoles,before k=[]):
    Runs program (timeBound p) (.local 11 7) before (.local 11 18) (result before p tail):=by
  have hz0:before (aux .ownerKey)=[]:=hz _ (by simp [cleanRoles])
  have hz1:before (aux .edgeWord)=[]:=hz _ (by simp [cleanRoles])
  have hz2:before (aux .sideWord)=[]:=hz _ (by simp [cleanRoles])
  have hz3:before (aux .rowBuffer)=[]:=hz _ (by simp [cleanRoles])
  have hz4:before (field (.inl .scratch))=[]:=hz _ (by simp [cleanRoles])
  have hz5:before (field (.inr ()))=[]:=hz _ (by simp [cleanRoles])
  simp only [aux,field,payload] at hi hz0 hz1 hz2 hz3 hz4 hz5
  let b0:=before
  let b1:Stack→List Bool:=Function.update b0 (aux .oldReader) (frame (payload p) tail)
  have h0a:=pop_run (.local 11 7) abort (.local 11 8) (.local 11 9) (aux .oldReader) b0 (true::frame (payload p) tail) rfl (by simp [b0,aux,payload,hi])
  have h0:Runs program 1 (.local 11 7) b0 (.local 11 9) b1:=by
    simpa only [List.head?_cons,List.tail_cons,SemiprimeD1StackBytecode.choose] using h0a
  let b2:Stack→List Bool:=Function.update (Function.update b1 (aux .oldReader) tail) (aux .rowBuffer) (payload p)
  have h1:Runs program (8*((payload p)).length+8) (.local 11 9) b1 (.local 11 11) b2:=
    field_read 20 (.local 11 9) (.local 11 10) (.local 11 11) abort abort rfl rfl
      b1 (payload p) tail (by simp [b0,b1,aux,fieldStack,fieldPorts,payload]) (by simp [b0,b1,aux,fieldStack,fieldPorts,payload,hz3]) (by simp [b0,b1,aux,field,payload,hz4]) (by simp [b0,b1,aux,field,payload,hz5])
  let b3:Stack→List Bool:=Function.update (Function.update b2 (aux .rowBuffer) (frame p.edge (frame p.side []))) (aux .ownerKey) p.vertex
  have h2:Runs program (8*(p.vertex).length+8) (.local 11 11) b2 (.local 11 13) b3:=
    field_read 12 (.local 11 11) (.local 11 12) (.local 11 13) abort abort rfl rfl
      b2 p.vertex (frame p.edge (frame p.side [])) (by simp [b0,b1,b2,aux,fieldStack,fieldPorts,payload]) (by simp [b0,b1,b2,aux,fieldStack,fieldPorts,payload,hz0]) (by simp [b0,b1,b2,aux,field,payload,hz4]) (by simp [b0,b1,b2,aux,field,payload,hz5])
  let b4:Stack→List Bool:=Function.update (Function.update b3 (aux .rowBuffer) (frame p.side [])) (aux .edgeWord) p.edge
  have h3:Runs program (8*(p.edge).length+8) (.local 11 13) b3 (.local 11 15) b4:=
    field_read 15 (.local 11 13) (.local 11 14) (.local 11 15) abort abort rfl rfl
      b3 p.edge (frame p.side []) (by simp [b0,b1,b2,b3,aux,fieldStack,fieldPorts,payload]) (by simp [b0,b1,b2,b3,aux,fieldStack,fieldPorts,payload,hz1]) (by simp [b0,b1,b2,b3,aux,field,payload,hz4]) (by simp [b0,b1,b2,b3,aux,field,payload,hz5])
  let b5:Stack→List Bool:=Function.update (Function.update b4 (aux .rowBuffer) []) (aux .sideWord) p.side
  have h4:Runs program (8*(p.side).length+8) (.local 11 15) b4 (.local 11 17) b5:=
    field_read 16 (.local 11 15) (.local 11 16) (.local 11 17) abort abort rfl rfl
      b4 p.side [] (by simp [b0,b1,b2,b3,b4,aux,fieldStack,fieldPorts,payload]) (by simp [b0,b1,b2,b3,b4,aux,fieldStack,fieldPorts,payload,hz2]) (by simp [b0,b1,b2,b3,b4,aux,field,payload,hz4]) (by simp [b0,b1,b2,b3,b4,aux,field,payload,hz5])
  have h5a:=peek_run (.local 11 17) (.local 11 18) abort abort (aux .rowBuffer) b5 [] rfl (by simp [b0,b1,b2,b3,b4,b5,aux,payload])
  have h5:Runs program 1 (.local 11 17) b5 (.local 11 18) b5:=by
    simpa only [List.head?_nil,SemiprimeD1StackBytecode.choose] using h5a
  have hout:b5=result before p tail:=by
    funext k
    rcases k with k|k|k|k|k|k
    · simp [b0,b1,b2,b3,b4,b5,aux,payload,result]
    · simp [b0,b1,b2,b3,b4,b5,aux,payload,result]
    · simp [b0,b1,b2,b3,b4,b5,aux,payload,result]
    · simp [b0,b1,b2,b3,b4,b5,aux,payload,result]
    · simp [b0,b1,b2,b3,b4,b5,aux,payload,result]
    · cases k <;> simp [b0,b1,b2,b3,b4,b5,aux,payload,hz3,result]
  have hwhole:=join h0 (join h1 (join h2 (join h3 (join h4 (h5)))))
  rw [hout] at hwhole
  have ht:(1)+((8*((payload p)).length+8))+((8*(p.vertex).length+8))+((8*(p.edge).length+8))+((8*(p.side).length+8))+(1)=timeBound p:=by dsimp only [timeBound];omega
  simpa only [←ht,Nat.add_assoc] using hwhole
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryOldPortParse

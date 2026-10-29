/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryFields
/-! # Literal paired occurrence/placement acquisition for one original incidence
Every field below is read from actual framed bytes, with real validity and
EOF tests. Fields is proof notation only, never a runtime input or evaluator.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryEndpointParse
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryWiring
open SemiprimeD1StackChildGroupFactory SemiprimeD1StackChildGroupFactoryPrimitives
open SemiprimeD1StackChildGroupFactoryFields SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
/-- Exact raw words physically parsed from the real pair and placement streams. -/
structure Fields where
  /-- Actual binary old-owner key, with any source padding retained. -/
  owner:List Bool
  /-- Actual binary old-factor key, with any source padding retained. -/
  factor:List Bool
  /-- Actual full selected-ID joint source key. -/
  source:List Bool
  /-- Actual original padding joint key. -/
  padding:List Bool
  /-- Whole raw packet bytes; literal identity will receive a physical sentinel. -/
  packet:List Bool
  /-- Actual packet-local slot word. -/
  slot:List Bool
  /-- Positive ORIGINAL occurrence ID, distinct from a new child-global ID. -/
  edge:List Bool
/-- Actual six-field placement payload, including the physically tested singleton TRUE. -/
def payload (f:Fields):List Bool:=frame f.source (frame f.padding
  (frame f.packet (frame f.slot (frame f.edge (frame [true] [])))))
/-- Every fresh output and real parser flag is physically empty before this read. -/
def cleanRoles:List Stack:=[aux .ownerKey,aux .factorKey,aux .sourceKey,aux .paddingKey,
  aux .packetKey,aux .slotWord,aux .edgeWord,aux .childReader,aux .validWord,
  field (.inl .scratch),field (.inr ())]
/-- Complete actual postbank: both source readers advance and all seven raw fields are retained. -/
def result (before:Stack→List Bool) (f:Fields) (pairTail placementTail:List Bool):Stack→List Bool:=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update before
      (aux .pairReader) pairTail) (aux .placementReader) placementTail)
      (aux .ownerKey) f.owner) (aux .factorKey) f.factor) (aux .sourceKey) f.source)
      (aux .paddingKey) f.padding) (aux .packetKey) f.packet) (aux .slotWord) f.slot) (aux .edgeWord) f.edge
/-- Sum of nine actual Field calls/valid-pops and five actual header/EOF instructions. -/
def timeBound (f:Fields):Nat:=8*(f.owner.length+f.factor.length+(payload f).length+
  f.source.length+f.padding.length+f.packet.length+f.slot.length+f.edge.length+1)+77
/-- Whole paired read comes from the actual source program, preserving every unrelated115-role word. -/
theorem source_trace (before:Stack→List Bool) (f:Fields) (pairTail placementTail:List Bool)
    (hpair:before (aux .pairReader)=true::frame f.owner (frame f.factor pairTail))
    (hplacement:before (aux .placementReader)=true::frame (payload f) placementTail)
    (hclean:∀k∈cleanRoles,before k=[]):
    Runs program (timeBound f) (.local 2 20) before (.local 3 14) (result before f pairTail placementTail):=by
  have hz0:before (aux .ownerKey)=[]:=hclean _ (by simp [cleanRoles])
  have hz1:before (aux .factorKey)=[]:=hclean _ (by simp [cleanRoles])
  have hz2:before (aux .sourceKey)=[]:=hclean _ (by simp [cleanRoles])
  have hz3:before (aux .paddingKey)=[]:=hclean _ (by simp [cleanRoles])
  have hz4:before (aux .packetKey)=[]:=hclean _ (by simp [cleanRoles])
  have hz5:before (aux .slotWord)=[]:=hclean _ (by simp [cleanRoles])
  have hz6:before (aux .edgeWord)=[]:=hclean _ (by simp [cleanRoles])
  have hz7:before (aux .childReader)=[]:=hclean _ (by simp [cleanRoles])
  have hz8:before (aux .validWord)=[]:=hclean _ (by simp [cleanRoles])
  have hz9:before (field (.inl .scratch))=[]:=hclean _ (by simp [cleanRoles])
  have hz10:before (field (.inr ()))=[]:=hclean _ (by simp [cleanRoles])
  simp only [aux,field,payload] at hpair hplacement hz0 hz1 hz2 hz3 hz4 hz5 hz6 hz7 hz8 hz9 hz10
  let b0:=before
  let b1:Stack→List Bool:=Function.update b0 (aux .pairReader) (frame f.owner (frame f.factor pairTail))
  have h0a:=pop_run (.local 2 20) (.local 15 14) (.local 2 21) (.local 2 24) (aux .pairReader) b0 (true::frame f.owner (frame f.factor pairTail)) rfl (by simp [b0,aux,hpair])
  have h0:Runs program 1 (.local 2 20) b0 (.local 2 24) b1:=by
    simpa only [List.head?_cons,List.tail_cons,SemiprimeD1StackBytecode.choose] using h0a
  let b2:Stack→List Bool:=Function.update (Function.update b1 (aux .pairReader) (frame f.factor pairTail)) (aux .ownerKey) f.owner
  have h1:Runs program (8*(f.owner).length+8) (.local 2 24) b1 (.local 2 26) b2:=
    field_read 1 (.local 2 24) (.local 2 25) (.local 2 26) abort abort rfl rfl
      b1 f.owner (frame f.factor pairTail) (by simp [b0,b1,aux,fieldStack,fieldPorts]) (by simp [b0,b1,aux,fieldStack,fieldPorts,hz0]) (by simp [b0,b1,aux,field,hz9]) (by simp [b0,b1,aux,field,hz10])
  let b3:Stack→List Bool:=Function.update (Function.update b2 (aux .pairReader) pairTail) (aux .factorKey) f.factor
  have h2:Runs program (8*(f.factor).length+8) (.local 2 26) b2 (.local 2 28) b3:=
    field_read 2 (.local 2 26) (.local 2 27) (.local 2 28) abort abort rfl rfl
      b2 f.factor pairTail (by simp [b0,b1,b2,aux,fieldStack,fieldPorts]) (by simp [b0,b1,b2,aux,fieldStack,fieldPorts,hz1]) (by simp [b0,b1,b2,aux,field,hz9]) (by simp [b0,b1,b2,aux,field,hz10])
  let b4:Stack→List Bool:=Function.update b3 (aux .placementReader) (frame (payload f) placementTail)
  have h3a:=pop_run (.local 2 28) (.local 15 14) (.local 15 14) (.local 2 29) (aux .placementReader) b3 (true::frame (payload f) placementTail) rfl (by simp [b0,b1,b2,b3,aux,payload,hplacement])
  have h3:Runs program 1 (.local 2 28) b3 (.local 2 29) b4:=by
    simpa only [List.head?_cons,List.tail_cons,SemiprimeD1StackBytecode.choose] using h3a
  let b5:Stack→List Bool:=Function.update (Function.update b4 (aux .placementReader) placementTail) (aux .childReader) (payload f)
  have h4:Runs program (8*((payload f)).length+8) (.local 2 29) b4 (.local 2 31) b5:=
    field_read 3 (.local 2 29) (.local 2 30) (.local 2 31) abort abort rfl rfl
      b4 (payload f) placementTail (by simp [b0,b1,b2,b3,b4,aux,fieldStack,fieldPorts,payload]) (by simp [b0,b1,b2,b3,b4,aux,fieldStack,fieldPorts,payload,hz7]) (by simp [b0,b1,b2,b3,b4,aux,field,payload,hz9]) (by simp [b0,b1,b2,b3,b4,aux,field,payload,hz10])
  let b6:Stack→List Bool:=Function.update (Function.update b5 (aux .childReader) (frame f.padding (frame f.packet (frame f.slot (frame f.edge (frame [true] [])))))) (aux .sourceKey) f.source
  have h5:Runs program (8*(f.source).length+8) (.local 2 31) b5 (.local 3 1) b6:=
    field_read 4 (.local 2 31) (.local 3 0) (.local 3 1) abort abort rfl rfl
      b5 f.source (frame f.padding (frame f.packet (frame f.slot (frame f.edge (frame [true] []))))) (by simp [b0,b1,b2,b3,b4,b5,aux,fieldStack,fieldPorts,payload]) (by simp [b0,b1,b2,b3,b4,b5,aux,fieldStack,fieldPorts,payload,hz2]) (by simp [b0,b1,b2,b3,b4,b5,aux,field,payload,hz9]) (by simp [b0,b1,b2,b3,b4,b5,aux,field,payload,hz10])
  let b7:Stack→List Bool:=Function.update (Function.update b6 (aux .childReader) (frame f.packet (frame f.slot (frame f.edge (frame [true] []))))) (aux .paddingKey) f.padding
  have h6:Runs program (8*(f.padding).length+8) (.local 3 1) b6 (.local 3 3) b7:=
    field_read 5 (.local 3 1) (.local 3 2) (.local 3 3) abort abort rfl rfl
      b6 f.padding (frame f.packet (frame f.slot (frame f.edge (frame [true] [])))) (by simp [b0,b1,b2,b3,b4,b5,b6,aux,fieldStack,fieldPorts,payload]) (by simp [b0,b1,b2,b3,b4,b5,b6,aux,fieldStack,fieldPorts,payload,hz3]) (by simp [b0,b1,b2,b3,b4,b5,b6,aux,field,payload,hz9]) (by simp [b0,b1,b2,b3,b4,b5,b6,aux,field,payload,hz10])
  let b8:Stack→List Bool:=Function.update (Function.update b7 (aux .childReader) (frame f.slot (frame f.edge (frame [true] [])))) (aux .packetKey) f.packet
  have h7:Runs program (8*(f.packet).length+8) (.local 3 3) b7 (.local 3 5) b8:=
    field_read 6 (.local 3 3) (.local 3 4) (.local 3 5) abort abort rfl rfl
      b7 f.packet (frame f.slot (frame f.edge (frame [true] []))) (by simp [b0,b1,b2,b3,b4,b5,b6,b7,aux,fieldStack,fieldPorts,payload]) (by simp [b0,b1,b2,b3,b4,b5,b6,b7,aux,fieldStack,fieldPorts,payload,hz4]) (by simp [b0,b1,b2,b3,b4,b5,b6,b7,aux,field,payload,hz9]) (by simp [b0,b1,b2,b3,b4,b5,b6,b7,aux,field,payload,hz10])
  let b9:Stack→List Bool:=Function.update (Function.update b8 (aux .childReader) (frame f.edge (frame [true] []))) (aux .slotWord) f.slot
  have h8:Runs program (8*(f.slot).length+8) (.local 3 5) b8 (.local 3 7) b9:=
    field_read 7 (.local 3 5) (.local 3 6) (.local 3 7) abort abort rfl rfl
      b8 f.slot (frame f.edge (frame [true] [])) (by simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,aux,fieldStack,fieldPorts,payload]) (by simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,aux,fieldStack,fieldPorts,payload,hz5]) (by simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,aux,field,payload,hz9]) (by simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,aux,field,payload,hz10])
  let b10:Stack→List Bool:=Function.update (Function.update b9 (aux .childReader) (frame [true] [])) (aux .edgeWord) f.edge
  have h9:Runs program (8*(f.edge).length+8) (.local 3 7) b9 (.local 3 9) b10:=
    field_read 8 (.local 3 7) (.local 3 8) (.local 3 9) abort abort rfl rfl
      b9 f.edge (frame [true] []) (by simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,aux,fieldStack,fieldPorts,payload]) (by simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,aux,fieldStack,fieldPorts,payload,hz6]) (by simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,aux,field,payload,hz9]) (by simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,aux,field,payload,hz10])
  let b11:Stack→List Bool:=Function.update (Function.update b10 (aux .childReader) []) (aux .validWord) [true]
  have h10:Runs program (8*([true]).length+8) (.local 3 9) b10 (.local 3 11) b11:=
    field_read 9 (.local 3 9) (.local 3 10) (.local 3 11) abort abort rfl rfl
      b10 [true] [] (by simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,aux,fieldStack,fieldPorts,payload]) (by simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,aux,fieldStack,fieldPorts,payload,hz8]) (by simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,aux,field,payload,hz9]) (by simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,aux,field,payload,hz10])
  have h11a:=peek_run (.local 3 11) (.local 3 12) (.local 15 14) (.local 15 14) (aux .childReader) b11 [] rfl (by simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,aux,payload])
  have h11:Runs program 1 (.local 3 11) b11 (.local 3 12) b11:=by
    simpa only [List.head?_nil,SemiprimeD1StackBytecode.choose] using h11a
  let b12:Stack→List Bool:=Function.update b11 (aux .validWord) []
  have h12a:=pop_run (.local 3 12) (.local 15 14) (.local 15 14) (.local 3 13) (aux .validWord) b11 [true] rfl (by simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,aux,payload])
  have h12:Runs program 1 (.local 3 12) b11 (.local 3 13) b12:=by
    simpa only [List.head?_cons,List.tail_cons,SemiprimeD1StackBytecode.choose] using h12a
  have h13a:=peek_run (.local 3 13) (.local 3 14) (.local 15 14) (.local 15 14) (aux .validWord) b12 [] rfl (by simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,aux,payload])
  have h13:Runs program 1 (.local 3 13) b12 (.local 3 14) b12:=by
    simpa only [List.head?_nil,SemiprimeD1StackBytecode.choose] using h13a
  have hout:b12=result before f pairTail placementTail:=by
    funext k
    rcases k with k|k|k|k|k|k
    · simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,aux,payload,result]
    · simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,aux,payload,result]
    · simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,aux,payload,result]
    · simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,aux,payload,result]
    · simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,aux,payload,result]
    · cases k <;> simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,aux,payload,hz7,hz8,result]
  have hwhole:=join h0 (join h1 (join h2 (join h3 (join h4 (join h5 (join h6 (join h7 (join h8 (join h9 (join h10 (join h11 (join h12 (h13)))))))))))))
  rw [hout] at hwhole
  have ht:(1)+((8*(f.owner).length+8))+((8*(f.factor).length+8))+(1)+((8*((payload f)).length+8))+((8*(f.source).length+8))+((8*(f.padding).length+8))+((8*(f.packet).length+8))+((8*(f.slot).length+8))+((8*(f.edge).length+8))+((8*([true]).length+8))+(1)+(1)+(1)=timeBound f:=by
    simp only [timeBound,List.length_cons,List.length_nil]
    omega
  simpa only [←ht,Nat.add_assoc] using hwhole
/-- The same complete parse clock is linear in actual paired source bytes, not in decoded addresses. -/
theorem timeBound_le (f:Fields) (pairTail placementTail:List Bool):
    timeBound f≤64*((true::frame f.owner (frame f.factor pairTail)).length+
      (true::frame (payload f) placementTail).length+1):=by
  simp only [timeBound,payload,List.length_cons,List.length_nil,
    SemiprimeSourceHistogramKeyBits.frame_length]
  omega
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryEndpointParse

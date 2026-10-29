/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketParse
/-! # Actual selected bucket record and fresh-global port emission
The six-field child record preserves all five original raw fields and appends
its actual current binary child-global position. Both histories are physical.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketEmit
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryWiring
open SemiprimeD1StackChildGroupFactory SemiprimeD1StackChildGroupFactoryPrimitives
open SemiprimeD1StackProcedureTrace
open SemiprimeD1StackChildGroupFactoryBucketParse (Endpoint)
open SemiprimeSourceHistogramKeyBits (frame)
/-- Actual child endpoint: original five raw fields plus fresh binary global ID. -/
def payload (e:Endpoint) (position:List Bool):List Bool:=
  frame e.vertex (frame e.packet (frame e.slot (frame e.edge (frame e.side (frame position [])))))
/-- Actual child endpoint vector record. -/
def row (e:Endpoint) (position:List Bool):List Bool:=true::frame (payload e position) []
/-- Actual binary port record, to be fed to the real ordinal converter later. -/
def portRow (position:List Bool):List Bool:=true::frame position []
/-- Complete actual postbank, preserving all raw source fields. -/
def result (before:Stack→List Bool) (e:Endpoint) (position:List Bool):Stack→List Bool:=
  Function.update (Function.update before (aux .bucketHistory) ((row e position).reverse++before (aux .bucketHistory)))
    (aux .portHistory) ((portRow position).reverse++before (aux .portHistory))
/-- Every preserving frame, real tag/reversal and actual temporary-payload drain. -/
def timeBound (e:Endpoint) (position:List Bool):Nat:=
  (6*position.length+5)+(6*e.side.length+5)+(6*e.edge.length+5)+(6*e.slot.length+5)+
  (6*e.packet.length+5)+(6*e.vertex.length+5)+(6*(payload e position).length+5)+1+
  (2*(row e position).length+3)+((payload e position).length+1)+
  (6*position.length+5)+1+(2*(portRow position).length+3)
/-- The actual matched branch emits bytes and a port; no row builder is a runtime operation. -/
theorem source_trace (before:Stack→List Bool) (e:Endpoint) (position:List Bool)
    (hv:before (aux .ownerKey)=e.vertex) (hp:before (aux .sourceKey)=e.packet)
    (hs:before (aux .slotWord)=e.slot) (he:before (aux .edgeWord)=e.edge)
    (hside:before (aux .sideWord)=e.side) (hpos:before (aux .globalPosition)=position)
    (hr:before (aux .rowBuffer)=[]) (hb:before (aux .frameBuffer)=[])
    (hc:before (aux .copyScratch)=[]):
    Runs program (timeBound e position) (.local 7 12) before (.local 7 25) (result before e position):=by
  simp only [aux] at hv hp hs he hside hpos hr hb hc
  let b0:=before
  let b1:Stack→List Bool:=Function.update b0 (aux .rowBuffer) (frame position [])
  have h0:Runs program (6*(position).length+5) (.local 7 12) b0 (.local 7 13) b1:=
    frame_call 10 (.local 7 12) (.local 7 13) rfl b0 position [] (by simp [b0,aux,frameStack,framePorts,hpos]) (by simp [b0,aux,frameStack,framePorts,hr]) (by simp [b0,aux,frameStack,hc])
  let b2:Stack→List Bool:=Function.update b1 (aux .rowBuffer) (frame e.side (frame position []))
  have h1:Runs program (6*(e.side).length+5) (.local 7 13) b1 (.local 7 14) b2:=
    frame_call 3 (.local 7 13) (.local 7 14) rfl b1 e.side (frame position []) (by simp [b0,b1,aux,frameStack,framePorts,hside]) (by simp [b0,b1,aux,frameStack,framePorts]) (by simp [b0,b1,aux,frameStack,hc])
  let b3:Stack→List Bool:=Function.update b2 (aux .rowBuffer) (frame e.edge (frame e.side (frame position [])))
  have h2:Runs program (6*(e.edge).length+5) (.local 7 14) b2 (.local 7 15) b3:=
    frame_call 4 (.local 7 14) (.local 7 15) rfl b2 e.edge (frame e.side (frame position [])) (by simp [b0,b1,b2,aux,frameStack,framePorts,he]) (by simp [b0,b1,b2,aux,frameStack,framePorts]) (by simp [b0,b1,b2,aux,frameStack,hc])
  let b4:Stack→List Bool:=Function.update b3 (aux .rowBuffer) (frame e.slot (frame e.edge (frame e.side (frame position []))))
  have h3:Runs program (6*(e.slot).length+5) (.local 7 15) b3 (.local 7 16) b4:=
    frame_call 7 (.local 7 15) (.local 7 16) rfl b3 e.slot (frame e.edge (frame e.side (frame position []))) (by simp [b0,b1,b2,b3,aux,frameStack,framePorts,hs]) (by simp [b0,b1,b2,b3,aux,frameStack,framePorts]) (by simp [b0,b1,b2,b3,aux,frameStack,hc])
  let b5:Stack→List Bool:=Function.update b4 (aux .rowBuffer) (frame e.packet (frame e.slot (frame e.edge (frame e.side (frame position [])))))
  have h4:Runs program (6*(e.packet).length+5) (.local 7 16) b4 (.local 7 17) b5:=
    frame_call 11 (.local 7 16) (.local 7 17) rfl b4 e.packet (frame e.slot (frame e.edge (frame e.side (frame position [])))) (by simp [b0,b1,b2,b3,b4,aux,frameStack,framePorts,hp]) (by simp [b0,b1,b2,b3,b4,aux,frameStack,framePorts]) (by simp [b0,b1,b2,b3,b4,aux,frameStack,hc])
  let b6:Stack→List Bool:=Function.update b5 (aux .rowBuffer) (frame e.vertex (frame e.packet (frame e.slot (frame e.edge (frame e.side (frame position []))))))
  have h5:Runs program (6*(e.vertex).length+5) (.local 7 17) b5 (.local 7 18) b6:=
    frame_call 5 (.local 7 17) (.local 7 18) rfl b5 e.vertex (frame e.packet (frame e.slot (frame e.edge (frame e.side (frame position []))))) (by simp [b0,b1,b2,b3,b4,b5,aux,frameStack,framePorts,hv]) (by simp [b0,b1,b2,b3,b4,b5,aux,frameStack,framePorts]) (by simp [b0,b1,b2,b3,b4,b5,aux,frameStack,hc])
  let b7:Stack→List Bool:=Function.update b6 (aux .frameBuffer) (frame (frame e.vertex (frame e.packet (frame e.slot (frame e.edge (frame e.side (frame position [])))))) [])
  have h6:Runs program (6*((frame e.vertex (frame e.packet (frame e.slot (frame e.edge (frame e.side (frame position []))))))).length+5) (.local 7 18) b6 (.local 7 19) b7:=
    frame_call 6 (.local 7 18) (.local 7 19) rfl b6 (frame e.vertex (frame e.packet (frame e.slot (frame e.edge (frame e.side (frame position [])))))) [] (by simp [b0,b1,b2,b3,b4,b5,b6,aux,frameStack,framePorts]) (by simp [b0,b1,b2,b3,b4,b5,b6,aux,frameStack,framePorts,hb]) (by simp [b0,b1,b2,b3,b4,b5,b6,aux,frameStack,hc])
  let b8:Stack→List Bool:=Function.update b7 (aux .frameBuffer) (true::(frame (frame e.vertex (frame e.packet (frame e.slot (frame e.edge (frame e.side (frame position [])))))) []))
  have h7p:b7 (aux .frameBuffer)=(frame (frame e.vertex (frame e.packet (frame e.slot (frame e.edge (frame e.side (frame position [])))))) []):=(by simp [b0,b1,b2,b3,b4,b5,b6,b7,aux])
  have h7a:=push_run (.local 7 19) (.local 7 20) (aux .frameBuffer) true b7 rfl
  have h7:Runs program 1 (.local 7 19) b7 (.local 7 20) b8:=by simpa only [h7p,b8] using h7a
  let b9:Stack→List Bool:=Function.update (Function.update b8 (aux .frameBuffer) []) (aux .bucketHistory) ((row e position).reverse++(before (aux .bucketHistory)))
  have h8:Runs program (2*(row e position).length+3) (.local 7 20) b8 (.local 7 21) b9:=
    reverse_call 5 (.local 7 20) (.local 7 21) rfl b8 (row e position) (before (aux .bucketHistory)) (by simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,payload,row,aux,reverseStack,reversePorts]) (by simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,aux,reverseStack,reversePorts])
  let b10:Stack→List Bool:=Function.update b9 (aux .rowBuffer) []
  have h9:Runs program ((payload e position).length+1) (.local 7 21) b9 (.local 7 22) b10:=
    drain_loop (.local 7 21) (.local 7 22) (aux .rowBuffer) rfl b9 (payload e position) (by simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,payload,row,aux])
  let b11:Stack→List Bool:=Function.update b10 (aux .frameBuffer) (frame position [])
  have h10:Runs program (6*(position).length+5) (.local 7 22) b10 (.local 7 23) b11:=
    frame_call 12 (.local 7 22) (.local 7 23) rfl b10 position [] (by simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,payload,row,aux,frameStack,framePorts,hpos]) (by simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,payload,row,aux,frameStack,framePorts]) (by simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,payload,row,aux,frameStack,hc])
  let b12:Stack→List Bool:=Function.update b11 (aux .frameBuffer) (true::(frame position []))
  have h11p:b11 (aux .frameBuffer)=(frame position []):=(by simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,payload,row,aux])
  have h11a:=push_run (.local 7 23) (.local 7 24) (aux .frameBuffer) true b11 rfl
  have h11:Runs program 1 (.local 7 23) b11 (.local 7 24) b12:=by simpa only [h11p,b12] using h11a
  let b13:Stack→List Bool:=Function.update (Function.update b12 (aux .frameBuffer) []) (aux .portHistory) ((portRow position).reverse++(before (aux .portHistory)))
  have h12:Runs program (2*(portRow position).length+3) (.local 7 24) b12 (.local 7 25) b13:=
    reverse_call 6 (.local 7 24) (.local 7 25) rfl b12 (portRow position) (before (aux .portHistory)) (by simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,payload,row,portRow,aux,reverseStack,reversePorts]) (by simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,payload,row,aux,reverseStack,reversePorts])
  have hout:b13=result before e position:=by
    funext k
    rcases k with k|k|k|k|k|k
    · simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,payload,row,portRow,aux,result]
    · simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,payload,row,portRow,aux,result]
    · simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,payload,row,portRow,aux,result]
    · simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,payload,row,portRow,aux,result]
    · simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,payload,row,portRow,aux,result]
    · cases k <;> simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,payload,row,portRow,aux,hv,hp,hs,he,hside,hpos,hr,hb,hc,result]
  have hwhole:=join h0 (join h1 (join h2 (join h3 (join h4 (join h5 (join h6 (join h7 (join h8 (join h9 (join h10 (join h11 (h12))))))))))))
  rw [hout] at hwhole
  simpa only [timeBound,payload,row,portRow,Nat.add_assoc] using hwhole
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketEmit

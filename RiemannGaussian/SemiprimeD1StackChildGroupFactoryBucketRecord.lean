/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryPrimitives
/-! # Actual whole raw-packet bucket logger, including empty observed buckets
The already physically converted unary right-port tape is framed with the
actual packet and its actual selected endpoint vector, preserving exact order.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketRecord
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryWiring
open SemiprimeD1StackChildGroupFactory SemiprimeD1StackChildGroupFactoryPrimitives
open SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
/-- Exact actual bucket payload, preserving the whole raw packet key and any empty endpoint vector. -/
def payload (packet children ports:List Bool):List Bool:=frame packet (frame children (frame ports []))
/-- Exact bucket vector row. -/
def row (packet children ports:List Bool):List Bool:=true::frame (payload packet children ports) []
/-- All physical frames, row tag, reversal and temporary payload drain. -/
def timeBound (packet children ports:List Bool):Nat:=
  (6*ports.length+5)+(6*children.length+5)+(6*packet.length+5)+
  (6*(payload packet children ports).length+5)+1+
  (2*(row packet children ports).length+3)+((payload packet children ports).length+1)
/-- The real whole-bucket logger, without any bucket or port answer supplier. -/
theorem source_trace (before:Stack→List Bool) (packet children ports:List Bool)
    (hp:before (aux .packetKey)=packet) (hj:before (aux .jointKey)=children)
    (hu:before (ordinal .output)=ports) (hr:before (aux .rowBuffer)=[])
    (hb:before (aux .frameBuffer)=[]) (hc:before (aux .copyScratch)=[]):
    Runs program (timeBound packet children ports) (.local 8 10) before (.local 8 17)
      (Function.update before (aux .factorHistory)
        ((row packet children ports).reverse++before (aux .factorHistory))):=by
  simp only [aux,ordinal] at hp hj hu hr hb hc
  let b0:=before
  let b1:Stack→List Bool:=Function.update b0 (aux .rowBuffer) (frame ports [])
  have h0:Runs program (6*(ports).length+5) (.local 8 10) b0 (.local 8 11) b1:=
    frame_call 13 (.local 8 10) (.local 8 11) rfl b0 ports [] (by simp [b0,aux,ordinal,frameStack,framePorts,hu]) (by simp [b0,aux,ordinal,frameStack,framePorts,hr]) (by simp [b0,aux,frameStack,hc])
  let b2:Stack→List Bool:=Function.update b1 (aux .rowBuffer) (frame children (frame ports []))
  have h1:Runs program (6*(children).length+5) (.local 8 11) b1 (.local 8 12) b2:=
    frame_call 14 (.local 8 11) (.local 8 12) rfl b1 children (frame ports []) (by simp [b0,b1,aux,frameStack,framePorts,hj]) (by simp [b0,b1,aux,frameStack,framePorts]) (by simp [b0,b1,aux,frameStack,hc])
  let b3:Stack→List Bool:=Function.update b2 (aux .rowBuffer) (frame packet (frame children (frame ports [])))
  have h2:Runs program (6*(packet).length+5) (.local 8 12) b2 (.local 8 13) b3:=
    frame_call 8 (.local 8 12) (.local 8 13) rfl b2 packet (frame children (frame ports [])) (by simp [b0,b1,b2,aux,frameStack,framePorts,hp]) (by simp [b0,b1,b2,aux,frameStack,framePorts]) (by simp [b0,b1,b2,aux,frameStack,hc])
  let b4:Stack→List Bool:=Function.update b3 (aux .frameBuffer) (frame (payload packet children ports) [])
  have h3:Runs program (6*((payload packet children ports)).length+5) (.local 8 13) b3 (.local 8 14) b4:=
    frame_call 6 (.local 8 13) (.local 8 14) rfl b3 (payload packet children ports) [] (by simp [b0,b1,b2,b3,payload,aux,frameStack,framePorts]) (by simp [b0,b1,b2,b3,aux,frameStack,framePorts,hb]) (by simp [b0,b1,b2,b3,aux,frameStack,hc])
  let b5:Stack→List Bool:=Function.update b4 (aux .frameBuffer) (row packet children ports)
  have h4p:b4 (aux .frameBuffer)=(frame (payload packet children ports) []):=(by simp [b0,b1,b2,b3,b4,payload,aux])
  have h4a:=push_run (.local 8 14) (.local 8 15) (aux .frameBuffer) true b4 rfl
  have h4:Runs program 1 (.local 8 14) b4 (.local 8 15) b5:=by simpa only [h4p,b5,row] using h4a
  let b6:Stack→List Bool:=Function.update (Function.update b5 (aux .frameBuffer) []) (aux .factorHistory) ((row packet children ports).reverse++(before (aux .factorHistory)))
  have h5:Runs program (2*(row packet children ports).length+3) (.local 8 15) b5 (.local 8 16) b6:=
    reverse_call 9 (.local 8 15) (.local 8 16) rfl b5 (row packet children ports) (before (aux .factorHistory)) (by simp [b0,b1,b2,b3,b4,b5,payload,row,aux,reverseStack,reversePorts]) (by simp [b0,b1,b2,b3,b4,b5,payload,row,aux,reverseStack,reversePorts])
  let b7:Stack→List Bool:=Function.update b6 (aux .rowBuffer) []
  have h6:Runs program ((payload packet children ports).length+1) (.local 8 16) b6 (.local 8 17) b7:=
    drain_loop (.local 8 16) (.local 8 17) (aux .rowBuffer) rfl b6 (payload packet children ports) (by simp [b0,b1,b2,b3,b4,b5,b6,payload,row,aux])
  have hout:b7=Function.update before (aux .factorHistory) ((row packet children ports).reverse++before (aux .factorHistory)):=by
    funext k
    rcases k with k|k|k|k|k|k
    · simp [b0,b1,b2,b3,b4,b5,b6,b7,payload,row,aux]
    · simp [b0,b1,b2,b3,b4,b5,b6,b7,payload,row,aux]
    · simp [b0,b1,b2,b3,b4,b5,b6,b7,payload,row,aux]
    · simp [b0,b1,b2,b3,b4,b5,b6,b7,payload,row,aux]
    · simp [b0,b1,b2,b3,b4,b5,b6,b7,payload,row,aux]
    · cases k <;> simp [b0,b1,b2,b3,b4,b5,b6,b7,payload,row,aux,hp,hj,hr,hb,hc]
  have hwhole:=join h0 (join h1 (join h2 (join h3 (join h4 (join h5 (h6))))))
  rw [hout] at hwhole
  simpa only [timeBound,Nat.add_assoc] using hwhole
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketRecord

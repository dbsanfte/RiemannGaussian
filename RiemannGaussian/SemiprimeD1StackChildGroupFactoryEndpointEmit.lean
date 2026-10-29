/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryEndpointOldLog
/-! # Actual selected endpoint row emission
The preceding actual lookup branches to these literal source sites. All five
fields are framed from retained parsed bytes, including WHOLE raw packet bytes.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryEndpointEmit
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryWiring
open SemiprimeD1StackChildGroupFactory SemiprimeD1StackChildGroupFactoryPrimitives
open SemiprimeD1StackProcedureTrace
open SemiprimeD1StackChildGroupFactoryEndpointOldLog (vertex)
open SemiprimeSourceHistogramKeyBits (frame)
/-- The two finite literal row-emission code families, never input modes. -/
def pc (owner:Bool) (slot:Fin 10):Label:=if owner then match slot.val with
  | 0=>(.local 4 16)
  | 1=>(.local 4 17)
  | 2=>(.local 4 18)
  | 3=>(.local 4 19)
  | 4=>(.local 4 20)
  | 5=>(.local 4 21)
  | 6=>(.local 4 22)
  | 7=>(.local 4 23)
  | 8=>(.local 4 24)
  | 9=>(.local 4 25)
  | _=>(.local 4 25)
else match slot.val with
  | 0=>(.local 5 28)
  | 1=>(.local 5 29)
  | 2=>(.local 5 30)
  | 3=>(.local 5 31)
  | 4=>(.local 6 0)
  | 5=>(.local 6 1)
  | 6=>(.local 6 2)
  | 7=>(.local 6 3)
  | 8=>(.local 6 4)
  | 9=>(.local 6 5)
  | _=>(.local 6 5)
/-- Exact five-field actual endpoint payload in original occurrence-major side order. -/
def endpoint (owner:Bool) (v packet slot edge:List Bool):List Bool:=
  frame v (frame packet (frame slot (frame edge (frame [owner] []))))
/-- Exact physical vector record put on the reversed actual endpoint log. -/
def row (owner:Bool) (v packet slot edge:List Bool):List Bool:=true::frame (endpoint owner v packet slot edge) []
/-- All six preserving frames, actual tag, consuming reversal and buffer erase. -/
def timeBound (owner:Bool) (v packet slot edge:List Bool):Nat:=
  (6*([owner]:List Bool).length+5)+(6*edge.length+5)+(6*slot.length+5)+(6*packet.length+5)+
  (6*v.length+5)+(6*(endpoint owner v packet slot edge).length+5)+1+
  (2*(row owner v packet slot edge).length+3)+((endpoint owner v packet slot edge).length+1)
/-- Actual endpoint logger preserves raw packet padding and every unrelated physical word. -/
theorem source_trace (owner:Bool) (before:Stack→List Bool) (v packet slot edge:List Bool)
    (hv:before (vertex owner)=v) (hp:before (aux .packetKey)=packet)
    (hs:before (aux .slotWord)=slot) (he:before (aux .edgeWord)=edge)
    (hside:before (aux .sideWord)=[owner]) (hr:before (aux .rowBuffer)=[])
    (hb:before (aux .frameBuffer)=[]) (hc:before (aux .copyScratch)=[]):
    Runs program (timeBound owner v packet slot edge) (pc owner 0) before (pc owner 9)
      (Function.update before (aux .endpointHistory)
        ((row owner v packet slot edge).reverse++before (aux .endpointHistory))):=by
  simp only [vertex,aux] at hv hp hs he hside hr hb hc
  let b0:=before
  let b1:Stack→List Bool:=Function.update b0 (aux .rowBuffer) (frame [owner] [])
  have h0:Runs program (6*([owner]).length+5) (pc owner 0) b0 (pc owner 1) b1:=
    frame_call 3 (pc owner 0) (pc owner 1) (by cases owner <;> rfl)
      b0 [owner] [] (by cases owner <;> simp at hv <;> simp [b0,aux,frameStack,framePorts,hside]) (by cases owner <;> simp at hv <;> simp [b0,aux,frameStack,framePorts,hr]) (by cases owner <;> simp at hv <;> simp [b0,aux,frameStack,hc])
  let b2:Stack→List Bool:=Function.update b1 (aux .rowBuffer) (frame edge (frame [owner] []))
  have h1:Runs program (6*(edge).length+5) (pc owner 1) b1 (pc owner 2) b2:=
    frame_call 4 (pc owner 1) (pc owner 2) (by cases owner <;> rfl)
      b1 edge (frame [owner] []) (by cases owner <;> simp at hv <;> simp [b0,b1,aux,frameStack,framePorts,he]) (by cases owner <;> simp at hv <;> simp [b0,b1,aux,frameStack,framePorts]) (by cases owner <;> simp at hv <;> simp [b0,b1,aux,frameStack,hc])
  let b3:Stack→List Bool:=Function.update b2 (aux .rowBuffer) (frame slot (frame edge (frame [owner] [])))
  have h2:Runs program (6*(slot).length+5) (pc owner 2) b2 (pc owner 3) b3:=
    frame_call 7 (pc owner 2) (pc owner 3) (by cases owner <;> rfl)
      b2 slot (frame edge (frame [owner] [])) (by cases owner <;> simp at hv <;> simp [b0,b1,b2,aux,frameStack,framePorts,hs]) (by cases owner <;> simp at hv <;> simp [b0,b1,b2,aux,frameStack,framePorts]) (by cases owner <;> simp at hv <;> simp [b0,b1,b2,aux,frameStack,hc])
  let b4:Stack→List Bool:=Function.update b3 (aux .rowBuffer) (frame packet (frame slot (frame edge (frame [owner] []))))
  have h3:Runs program (6*(packet).length+5) (pc owner 3) b3 (pc owner 4) b4:=
    frame_call 8 (pc owner 3) (pc owner 4) (by cases owner <;> rfl)
      b3 packet (frame slot (frame edge (frame [owner] []))) (by cases owner <;> simp at hv <;> simp [b0,b1,b2,b3,aux,frameStack,framePorts,hp]) (by cases owner <;> simp at hv <;> simp [b0,b1,b2,b3,aux,frameStack,framePorts]) (by cases owner <;> simp at hv <;> simp [b0,b1,b2,b3,aux,frameStack,hc])
  let b5:Stack→List Bool:=Function.update b4 (aux .rowBuffer) (frame v (frame packet (frame slot (frame edge (frame [owner] [])))))
  have h4a:=frame_call (if owner then 5 else 9) (pc owner 4) (pc owner 5) (by cases owner <;> rfl)
      b4 v (frame packet (frame slot (frame edge (frame [owner] [])))) (by cases owner <;> simp at hv <;> simp [b0,b1,b2,b3,b4,aux,frameStack,framePorts,hv]) (by cases owner <;> simp at hv <;> simp [b0,b1,b2,b3,b4,aux,frameStack,framePorts]) (by cases owner <;> simp at hv <;> simp [b0,b1,b2,b3,b4,aux,frameStack,hc])
  have h4:Runs program (6*(v).length+5) (pc owner 4) b4 (pc owner 5) b5:=by
    cases owner <;> simpa [b5,frameStack,framePorts] using h4a
  let b6:Stack→List Bool:=Function.update b5 (aux .frameBuffer) (frame (endpoint owner v packet slot edge) [])
  have h5:Runs program (6*((endpoint owner v packet slot edge)).length+5) (pc owner 5) b5 (pc owner 6) b6:=
    frame_call 6 (pc owner 5) (pc owner 6) (by cases owner <;> rfl)
      b5 (endpoint owner v packet slot edge) [] (by cases owner <;> simp at hv <;> simp [b0,b1,b2,b3,b4,b5,endpoint,aux,frameStack,framePorts]) (by cases owner <;> simp at hv <;> simp [b0,b1,b2,b3,b4,b5,aux,frameStack,framePorts,hb]) (by cases owner <;> simp at hv <;> simp [b0,b1,b2,b3,b4,b5,aux,frameStack,hc])
  let b7:Stack→List Bool:=Function.update b6 (aux .frameBuffer) (row owner v packet slot edge)
  have h6p:b6 (aux .frameBuffer)=frame (endpoint owner v packet slot edge) []:=(by cases owner <;> simp at hv <;> simp [b0,b1,b2,b3,b4,b5,b6,endpoint,aux])
  have h6a:=push_run (pc owner 6) (pc owner 7) (aux .frameBuffer) true b6 (by cases owner <;> rfl)
  have h6:Runs program 1 (pc owner 6) b6 (pc owner 7) b7:=by simpa only [h6p,b7,row] using h6a
  let b8:Stack→List Bool:=Function.update (Function.update b7 (aux .frameBuffer) []) (aux .endpointHistory) ((row owner v packet slot edge).reverse++before (aux .endpointHistory))
  have h7:Runs program (2*(row owner v packet slot edge).length+3) (pc owner 7) b7 (pc owner 8) b8:=
    reverse_call 2 (pc owner 7) (pc owner 8) (by cases owner <;> rfl) b7 (row owner v packet slot edge) (before (aux .endpointHistory)) (by cases owner <;> simp at hv <;> simp [b0,b1,b2,b3,b4,b5,b6,b7,endpoint,row,aux,reverseStack,reversePorts]) (by cases owner <;> simp at hv <;> simp [b0,b1,b2,b3,b4,b5,b6,b7,endpoint,row,aux,reverseStack,reversePorts])
  let b9:Stack→List Bool:=Function.update b8 (aux .rowBuffer) []
  have h8:Runs program ((endpoint owner v packet slot edge).length+1) (pc owner 8) b8 (pc owner 9) b9:=
    drain_loop (pc owner 8) (pc owner 9) (aux .rowBuffer) (by cases owner <;> rfl) b8 (endpoint owner v packet slot edge) (by cases owner <;> simp at hv <;> simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,endpoint,row,aux])
  have hout:b9=Function.update before (aux .endpointHistory) ((row owner v packet slot edge).reverse++before (aux .endpointHistory)):=by
    funext k
    rcases k with k|k|k|k|k|k
    · cases owner <;> simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,endpoint,row,aux]
    · cases owner <;> simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,endpoint,row,aux]
    · cases owner <;> simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,endpoint,row,aux]
    · cases owner <;> simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,endpoint,row,aux]
    · cases owner <;> simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,endpoint,row,aux]
    · cases k <;> cases owner <;> simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,endpoint,row,aux,hp,hs,he,hside,hr,hb,hc]
  have hwhole:=join h0 (join h1 (join h2 (join h3 (join h4 (join h5 (join h6 (join h7 (h8))))))))
  rw [hout] at hwhole
  simpa only [timeBound,Nat.add_assoc] using hwhole
/-- The real selected-endpoint logger is linear in its actual raw field bytes. -/
theorem timeBound_le (owner:Bool) (v packet slot edge:List Bool):
    timeBound owner v packet slot edge≤256*(v.length+packet.length+slot.length+edge.length+1):=by
  simp only [timeBound,row,endpoint,List.length_cons,List.length_nil,
    SemiprimeSourceHistogramKeyBits.frame_length]
  omega
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryEndpointEmit

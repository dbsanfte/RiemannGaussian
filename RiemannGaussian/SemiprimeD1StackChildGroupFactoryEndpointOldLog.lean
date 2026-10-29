/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryPrimitives
/-! # Real unconditional original owner/factor endpoint-tag logger
The Boolean here names the two literal call-site families in the proof; the
source itself pushes TRUE for owner then FALSE for factor, without input advice.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryEndpointOldLog
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryWiring
open SemiprimeD1StackChildGroupFactory SemiprimeD1StackChildGroupFactoryPrimitives
open SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
/-- The two fixed old-vertex fields actually parsed from the occurrence stream. -/
def vertex (owner:Bool):Stack:=aux (if owner then .ownerKey else .factorKey)
/-- Literal source positions, all fixed independently of every input word. -/
def pc (owner:Bool) (slot:Fin 9):Label:=if owner then match slot.val with
  | 0=>(.local 3 14)
  | 1=>(.local 3 15)
  | 2=>(.local 3 16)
  | 3=>(.local 3 17)
  | 4=>(.local 3 18)
  | 5=>(.local 3 19)
  | 6=>(.local 3 20)
  | 7=>(.local 3 21)
  | 8=>(.local 3 22)
  | _=>(.local 3 22)
else match slot.val with
  | 0=>(.local 4 26)
  | 1=>(.local 4 27)
  | 2=>(.local 4 28)
  | 3=>(.local 4 29)
  | 4=>(.local 4 30)
  | 5=>(.local 4 31)
  | 6=>(.local 5 0)
  | 7=>(.local 5 1)
  | 8=>(.local 5 2)
  | _=>(.local 5 2)
/-- Exact three-field old tag retained for original port order, independent of activation. -/
def oldPoint (owner:Bool) (v e:List Bool):List Bool:=frame v (frame e (frame [owner] []))
/-- Actual vector-row bytes put on the reversed physical log. -/
def row (owner:Bool) (v e:List Bool):List Bool:=true::frame (oldPoint owner v e) []
/-- Same-source literal push/frame/reverse/drain clock. -/
def timeBound (owner:Bool) (v e:List Bool):Nat:=1+(6*([owner]:List Bool).length+5)+
  (6*e.length+5)+(6*v.length+5)+(6*(oldPoint owner v e).length+5)+1+
  (2*(row owner v e).length+3)+((oldPoint owner v e).length+1)
/-- Every old endpoint is really logged, whether active, inactive, both, or neither. -/
theorem source_trace (owner:Bool) (before:Stack→List Bool) (v e:List Bool)
    (hv:before (vertex owner)=v) (he:before (aux .edgeWord)=e)
    (hs:before (aux .sideWord)=[]) (hr:before (aux .rowBuffer)=[])
    (hb:before (aux .frameBuffer)=[]) (hc:before (aux .copyScratch)=[]):
    Runs program (timeBound owner v e) (pc owner 0) before (pc owner 8)
      (Function.update (Function.update before (aux .sideWord) [owner]) (aux .oldHistory)
        ((row owner v e).reverse++before (aux .oldHistory))):=by
  simp only [vertex,aux] at hv he hs hr hb hc
  let b0:=before
  let b1:Stack→List Bool:=Function.update b0 (aux .sideWord) [owner]
  have h0p:b0 (aux .sideWord)=[]:=(by cases owner <;> simp at hv <;> simp [b0,aux,hs])
  have h0a:=push_run (pc owner 0) (pc owner 1) (aux .sideWord) owner b0 (by cases owner <;> rfl)
  have h0:Runs program 1 (pc owner 0) b0 (pc owner 1) b1:=by simpa only [h0p] using h0a
  let b2:Stack→List Bool:=Function.update b1 (aux .rowBuffer) (frame [owner] [])
  have h1:Runs program (6*([owner]).length+5) (pc owner 1) b1 (pc owner 2) b2:=
    frame_call 3 (pc owner 1) (pc owner 2) (by cases owner <;> rfl)
      b1 [owner] [] (by cases owner <;> simp at hv <;> simp [b0,b1,aux,frameStack,framePorts]) (by cases owner <;> simp at hv <;> simp [b0,b1,aux,frameStack,framePorts,hr]) (by cases owner <;> simp at hv <;> simp [b0,b1,aux,frameStack,hc])
  let b3:Stack→List Bool:=Function.update b2 (aux .rowBuffer) (frame e (frame [owner] []))
  have h2:Runs program (6*(e).length+5) (pc owner 2) b2 (pc owner 3) b3:=
    frame_call 4 (pc owner 2) (pc owner 3) (by cases owner <;> rfl)
      b2 e (frame [owner] []) (by cases owner <;> simp at hv <;> simp [b0,b1,b2,aux,frameStack,framePorts,he]) (by cases owner <;> simp at hv <;> simp [b0,b1,b2,aux,frameStack,framePorts]) (by cases owner <;> simp at hv <;> simp [b0,b1,b2,aux,frameStack,hc])
  let b4:Stack→List Bool:=Function.update b3 (aux .rowBuffer) (frame v (frame e (frame [owner] [])))
  have h3a:=
    frame_call (if owner then 5 else 9) (pc owner 3) (pc owner 4) (by cases owner <;> rfl)
      b3 v (frame e (frame [owner] [])) (by cases owner <;> simp at hv <;> simp [b0,b1,b2,b3,aux,frameStack,framePorts,hv]) (by cases owner <;> simp at hv <;> simp [b0,b1,b2,b3,aux,frameStack,framePorts]) (by cases owner <;> simp at hv <;> simp [b0,b1,b2,b3,aux,frameStack,hc])
  have h3:Runs program (6*(v).length+5) (pc owner 3) b3 (pc owner 4) b4:=by
    cases owner <;> simpa [b4,frameStack,framePorts] using h3a
  let b5:Stack→List Bool:=Function.update b4 (aux .frameBuffer) (frame (oldPoint owner v e) [])
  have h4:Runs program (6*((oldPoint owner v e)).length+5) (pc owner 4) b4 (pc owner 5) b5:=
    frame_call 6 (pc owner 4) (pc owner 5) (by cases owner <;> rfl)
      b4 (oldPoint owner v e) [] (by cases owner <;> simp at hv <;> simp [b0,b1,b2,b3,b4,oldPoint,aux,frameStack,framePorts]) (by cases owner <;> simp at hv <;> simp [b0,b1,b2,b3,b4,aux,frameStack,framePorts,hb]) (by cases owner <;> simp at hv <;> simp [b0,b1,b2,b3,b4,aux,frameStack,hc])
  let b6:Stack→List Bool:=Function.update b5 (aux .frameBuffer) (row owner v e)
  have h5p:b5 (aux .frameBuffer)=frame (oldPoint owner v e) []:=(by cases owner <;> simp at hv <;> simp [b0,b1,b2,b3,b4,b5,oldPoint,aux])
  have h5a:=push_run (pc owner 5) (pc owner 6) (aux .frameBuffer) true b5 (by cases owner <;> rfl)
  have h5:Runs program 1 (pc owner 5) b5 (pc owner 6) b6:=by simpa only [h5p,b6,row] using h5a
  let b7:Stack→List Bool:=Function.update (Function.update b6 (aux .frameBuffer) []) (aux .oldHistory) ((row owner v e).reverse++before (aux .oldHistory))
  have h6:Runs program (2*(row owner v e).length+3) (pc owner 6) b6 (pc owner 7) b7:=
    reverse_call 1 (pc owner 6) (pc owner 7) (by cases owner <;> rfl) b6 (row owner v e) (before (aux .oldHistory)) (by cases owner <;> simp at hv <;> simp [b0,b1,b2,b3,b4,b5,b6,oldPoint,row,aux,reverseStack,reversePorts]) (by cases owner <;> simp at hv <;> simp [b0,b1,b2,b3,b4,b5,b6,oldPoint,row,aux,reverseStack,reversePorts])
  let b8:Stack→List Bool:=Function.update b7 (aux .rowBuffer) []
  have h7:Runs program ((oldPoint owner v e).length+1) (pc owner 7) b7 (pc owner 8) b8:=
    drain_loop (pc owner 7) (pc owner 8) (aux .rowBuffer) (by cases owner <;> rfl) b7 (oldPoint owner v e) (by cases owner <;> simp at hv <;> simp [b0,b1,b2,b3,b4,b5,b6,b7,oldPoint,row,aux])
  have hout:b8=Function.update (Function.update before (aux .sideWord) [owner]) (aux .oldHistory) ((row owner v e).reverse++before (aux .oldHistory)):=by
    funext k
    rcases k with k|k|k|k|k|k
    · cases owner <;> simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,oldPoint,row,aux]
    · cases owner <;> simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,oldPoint,row,aux]
    · cases owner <;> simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,oldPoint,row,aux]
    · cases owner <;> simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,oldPoint,row,aux]
    · cases owner <;> simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,oldPoint,row,aux]
    · cases k <;> cases owner <;> simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,oldPoint,row,aux,he,hr,hb,hc]
  have hwhole:=join h0 (join h1 (join h2 (join h3 (join h4 (join h5 (join h6 (h7)))))))
  rw [hout] at hwhole
  simpa only [timeBound,Nat.add_assoc] using hwhole
/-- Whole original tag logging is linear in physically acquired vertex/edge bytes. -/
theorem timeBound_le (owner:Bool) (v e:List Bool):timeBound owner v e≤128*(v.length+e.length+1):=by
  simp only [timeBound,row,oldPoint,List.length_cons,List.length_nil,
    SemiprimeSourceHistogramKeyBits.frame_length]
  omega
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryEndpointOldLog

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryEndpointEmit
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryEndpointFlag
/-! # Whole actual owner-or-factor endpoint acquisition
Each original tag is always logged. A real lookup of the generated activation
map decides selected-row emission, then the literal side word is drained.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryEndpointSide
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryWiring
open SemiprimeD1StackChildGroupFactory SemiprimeD1StackChildGroupFactoryPrimitives
open SemiprimeD1StackProcedureTrace
namespace Old
export SemiprimeD1StackChildGroupFactoryEndpointOldLog (vertex pc row timeBound source_trace)
end Old
namespace Test
export SemiprimeD1StackChildGroupFactoryEndpointFlag (pc next timeBound source_trace)
end Test
namespace Emit
export SemiprimeD1StackChildGroupFactoryEndpointEmit (pc row timeBound source_trace)
end Emit
/-- Literal endpoint-side erasure, including its actual EOF pop. -/
def clearPC (owner:Bool):Label:=if owner then .local 4 25 else .local 6 5
/-- Original owner ALWAYS precedes factor; then the original field cleanup follows. -/
def next (owner:Bool):Label:=if owner then .local 4 26 else .local 6 6
/-- Actual old-tag history with its real side word still present. -/
def oldBank (owner:Bool) (before:Stack→List Bool) (v edge:List Bool):Stack→List Bool:=
  Function.update (Function.update before (aux .sideWord) [owner]) (aux .oldHistory)
    ((Old.row owner v edge).reverse++before (aux .oldHistory))
/-- Actual selected-row history after emission, before the side word is erased. -/
def emitted (owner:Bool) (before:Stack→List Bool) (v packet slot edge:List Bool):Stack→List Bool:=
  Function.update (oldBank owner before v edge) (aux .endpointHistory)
    ((Emit.row owner v packet slot edge).reverse++before (aux .endpointHistory))
/-- Full physical result; every unrelated word and all source inputs remain literal. -/
def result (owner flag:Bool) (before:Stack→List Bool) (v packet slot edge:List Bool):Stack→List Bool:=
  let old:=Function.update before (aux .oldHistory) ((Old.row owner v edge).reverse++before (aux .oldHistory))
  if flag then Function.update old (aux .endpointHistory)
    ((Emit.row owner v packet slot edge).reverse++before (aux .endpointHistory)) else old
/-- Own whole source cost includes both real calls and every helper/side cleanup. -/
def timeBound (owner flag:Bool) (v packet slot edge table unread:List Bool)
    (entries:List (List Bool×List Bool)):Nat:=
  Old.timeBound owner v edge+Test.timeBound v table entries unread+
    (if flag then Emit.timeBound owner v packet slot edge else 0)+2
/-- Physical side erasure restores exactly the original side allocation. -/
theorem clear_old (owner:Bool) (before:Stack→List Bool) (v packet slot edge:List Bool)
    (hs:before (aux .sideWord)=[]):
    Function.update (oldBank owner before v edge) (aux .sideWord) []=result owner false before v packet slot edge:=by
  dsimp only [oldBank,result]
  rw [Function.update_comm (by decide:aux .oldHistory≠aux .sideWord),Function.update_idem]
  have h:Function.update before (aux .sideWord) []=before:=by rw [←hs];exact Function.update_eq_self _ _
  rw [h]
  rfl
/-- The true branch also physically restores the side allocation, retaining both actual histories. -/
theorem clear_emitted (owner:Bool) (before:Stack→List Bool) (v packet slot edge:List Bool)
    (hs:before (aux .sideWord)=[]):
    Function.update (emitted owner before v packet slot edge) (aux .sideWord) []=
      result owner true before v packet slot edge:=by
  dsimp only [emitted,oldBank,result]
  rw [Function.update_comm (by decide:aux .endpointHistory≠aux .sideWord),
    Function.update_comm (by decide:aux .oldHistory≠aux .sideWord),Function.update_idem]
  have h:Function.update before (aux .sideWord) []=before:=by rw [←hs];exact Function.update_eq_self _ _
  rw [h]
  rfl
/-- Entire original endpoint side, with classification COMPUTED by its real numeric map source. -/
theorem source_trace (owner flag:Bool) (before:Stack→List Bool) (v packet slot edge unread:List Bool)
    (entries:List (List Bool×List Bool))
    (hv:before (Old.vertex owner)=v) (hp:before (aux .packetKey)=packet)
    (hs:before (aux .slotWord)=slot) (he:before (aux .edgeWord)=edge)
    (hside:before (aux .sideWord)=[]) (hr:before (aux .rowBuffer)=[])
    (hb:before (aux .frameBuffer)=[]) (hc:before (aux .copyScratch)=[])
    (hl:∀k,before (lookup k)=[])
    (hm:before (aux .activationMap)=SemiprimeD1StackOwnerLookup.records entries [])
    (hget:SemiprimeD1StackOwnerLookup.result v entries []=([flag],unread)):
    Runs program (timeBound owner flag v packet slot edge (SemiprimeD1StackOwnerLookup.records entries []) unread entries)
      (Old.pc owner 0) before (next owner) (result owner flag before v packet slot edge):=by
  have h0:=Old.source_trace owner before v edge hv he hside hr hb hc
  change Runs program _ _ _ _ (oldBank owner before v edge) at h0
  have hv':oldBank owner before v edge (SemiprimeD1StackChildGroupFactoryEndpointFlag.vertex owner)=v:=by
    cases owner <;> simp [Old.vertex,aux] at hv <;> simp [oldBank,SemiprimeD1StackChildGroupFactoryEndpointFlag.vertex,aux,hv]
  have hm':oldBank owner before v edge (aux .activationMap)=SemiprimeD1StackOwnerLookup.records entries []:=by
    simpa [oldBank,aux] using hm
  have hc':oldBank owner before v edge (aux .copyScratch)=[]:=by simpa [oldBank,aux] using hc
  have hl':∀k,oldBank owner before v edge (lookup k)=[]:=by intro k;simpa [oldBank,aux,lookup] using hl k
  have h1:=Test.source_trace owner flag (oldBank owner before v edge) v unread entries hv' hm' hc' hl' hget
  have hjoin:Old.pc owner 8=Test.pc owner 0:=by cases owner <;> rfl
  rw [hjoin] at h0
  cases flag with
  | false=>
    have hnext:Test.next owner false=clearPC owner:=by cases owner <;> rfl
    rw [hnext] at h1
    have hd:program (clearPC owner)=.base (.pop (aux .sideWord) (next owner) (clearPC owner) (clearPC owner)):=by
      cases owner <;> rfl
    have h2:=drain_loop (clearPC owner) (next owner) (aux .sideWord) hd
      (oldBank owner before v edge) [owner] (by simp [oldBank,aux])
    rw [clear_old owner before v packet slot edge hside] at h2
    have hwhole:=join h0 (join h1 h2)
    simpa [timeBound,Nat.add_assoc] using hwhole
  | true=>
    have hnext:Test.next owner true=Emit.pc owner 0:=by cases owner <;> rfl
    rw [hnext] at h1
    have hv'':oldBank owner before v edge (Old.vertex owner)=v:=hv'
    have hp':oldBank owner before v edge (aux .packetKey)=packet:=by simpa [oldBank,aux] using hp
    have hs':oldBank owner before v edge (aux .slotWord)=slot:=by simpa [oldBank,aux] using hs
    have he':oldBank owner before v edge (aux .edgeWord)=edge:=by simpa [oldBank,aux] using he
    have hside':oldBank owner before v edge (aux .sideWord)=[owner]:=by simp [oldBank,aux]
    have hr':oldBank owner before v edge (aux .rowBuffer)=[]:=by simpa [oldBank,aux] using hr
    have hb':oldBank owner before v edge (aux .frameBuffer)=[]:=by simpa [oldBank,aux] using hb
    have h2:=Emit.source_trace owner (oldBank owner before v edge) v packet slot edge hv'' hp' hs' he' hside' hr' hb' hc'
    have hhist:oldBank owner before v edge (aux .endpointHistory)=before (aux .endpointHistory):=by simp [oldBank,aux]
    rw [hhist] at h2
    change Runs program _ _ _ _ (emitted owner before v packet slot edge) at h2
    have hclear:Emit.pc owner 9=clearPC owner:=by cases owner <;> rfl
    rw [hclear] at h2
    have hd:program (clearPC owner)=.base (.pop (aux .sideWord) (next owner) (clearPC owner) (clearPC owner)):=by
      cases owner <;> rfl
    have h3:=drain_loop (clearPC owner) (next owner) (aux .sideWord) hd
      (emitted owner before v packet slot edge) [owner] (by simp [emitted,oldBank,aux])
    rw [clear_emitted owner before v packet slot edge hside] at h3
    have hwhole:=join h0 (join h1 (join h2 h3))
    simpa [timeBound,Nat.add_assoc] using hwhole
/-- Every actual source/parsed/private role outside the two log histories is retained at the stopped boundary. -/
theorem result_other (owner flag:Bool) (before:Stack→List Bool) (v packet slot edge:List Bool)
    (k:Stack) (ho:k≠aux .oldHistory) (he:k≠aux .endpointHistory):
    result owner flag before v packet slot edge k=before k:=by
  cases flag <;> simp [result,Function.update_of_ne ho,Function.update_of_ne he]
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryEndpointSide

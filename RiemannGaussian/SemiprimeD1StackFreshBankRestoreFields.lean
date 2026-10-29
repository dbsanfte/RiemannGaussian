/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackFreshBankRestorePrimitives
/-! # Eighty-five actual field parses into the literal stopped Fresh-bank roles
The partialBank bank, remaining frames and byte mass are proof invariants only. The
executed program has one fixed finite parser call site per literal physical role.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackFreshBankRestoreFields
open SemiprimeD1StackFreshBankRestore SemiprimeD1StackFreshBankRestorePrimitives
open SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
local notation "ctl" => (Sum.inl : Control→Label)
/-- Exactly the physically parsed prefix of the fixed complete role list is installed. -/
noncomputable def partialBank (bank:F.Stack→List Bool) (n:Nat) :F.Stack→List Bool :=by
  classical
  exact fun k=>if k∈I.roles.take n then bank k else []
/-- Unconsumed consecutive field frames; there are NO vector-constructor tags. -/
def remaining (bank:F.Stack→List Bool) (n:Nat) :List Bool :=
  (I.roles.drop n).foldr (fun k tail=>frame (bank k) tail) []
/-- Actual total word-byte mass remaining at a field boundary. -/
def mass (bank:F.Stack→List Bool) (n:Nat) :Nat :=
  ((I.roles.drop n).map (fun k=>(bank k).length)).sum
/-- The finite field control selected by a proof index, or the real EOF label at eighty-five. -/
def fieldAt (n:Nat) :Label :=if h:n<85 then ctl (.field ⟨n,h⟩) else ctl .eof
/-- Fixed next-control code matches the next literal parser position and final EOF branch. -/
theorem next_at (part:Fin 85) :next part=fieldAt (part.val+1) :=by
  by_cases h:part.val<84
  · have hs:part.val+1<85:=by omega
    simp [next,fieldAt,h,hs]
  · have hs:¬part.val+1<85:=by omega
    simp [next,fieldAt,h,hs]
/-- No literal destination has occurred in the already restored prefix. -/
theorem role_fresh (n:Nat) (hn:n<85) :I.role ⟨n,hn⟩∉I.roles.take n :=by
  have hd:List.Disjoint (I.roles.take n) (I.roles.drop n):=List.disjoint_of_nodup_append (by
    rw [List.take_append_drop]
    exact I.roles_nodup)
  have hl:n<I.roles.length:=by simpa only [I.roles_length] using hn
  have hr:I.role ⟨n,hn⟩=I.roles[n]:=rfl
  have hm:I.role ⟨n,hn⟩∈I.roles.drop n:=by
    rw [List.drop_eq_getElem_cons hl,hr]
    exact List.mem_cons_self
  exact fun h=>(List.disjoint_left.mp hd) h hm
/-- Each real field parser begins with its actual physical destination EMPTY. -/
theorem partial_empty (bank:F.Stack→List Bool) (n:Nat) (hn:n<85) :
    partialBank bank n (I.role ⟨n,hn⟩)=[] :=by
  simp only [partialBank,role_fresh n hn,ite_false]
/-- One physical role update is EXACTLY the next acquired prefix bank. -/
theorem partial_update (bank:F.Stack→List Bool) (n:Nat) (hn:n<85) :
    Function.update (partialBank bank n) (I.role ⟨n,hn⟩) (bank (I.role ⟨n,hn⟩))=partialBank bank (n+1) :=by
  classical
  have hl:n<I.roles.length:=by simpa only [I.roles_length] using hn
  have hr:I.role ⟨n,hn⟩=I.roles[n]:=rfl
  have ht:=List.take_succ_eq_append_getElem hl
  rw [←hr] at ht
  funext k
  by_cases hk:k=I.role ⟨n,hn⟩
  · subst k
    simp only [Function.update_same,partialBank,ht,List.mem_append,List.mem_singleton_self,or_true,ite_true]
  · rw [Function.update_noteq hk]
    change (if k∈I.roles.take n then bank k else [])=(if k∈I.roles.take (n+1) then bank k else [])
    rw [ht]
    simp only [List.mem_append,List.mem_singleton,hk,or_false]
/-- The next field parser consumes the exact next existing-ABI frame. -/
theorem remaining_cons (bank:F.Stack→List Bool) (n:Nat) (hn:n<85) :
    remaining bank n=frame (bank (I.role ⟨n,hn⟩)) (remaining bank (n+1)) :=by
  have hl:n<I.roles.length:=by simpa only [I.roles_length] using hn
  have hr:I.role ⟨n,hn⟩=I.roles[n]:=rfl
  unfold remaining
  rw [List.drop_eq_getElem_cons hl,←hr]
  rfl
/-- Exact physical word mass falls by the actual word just parsed. -/
theorem mass_step (bank:F.Stack→List Bool) (n:Nat) (hn:n<85) :
    mass bank n=(bank (I.role ⟨n,hn⟩)).length+mass bank (n+1) :=by
  have hl:n<I.roles.length:=by simpa only [I.roles_length] using hn
  have hr:I.role ⟨n,hn⟩=I.roles[n]:=rfl
  unfold mass
  rw [List.drop_eq_getElem_cons hl,←hr]
  rfl
/-- Initially no Fresh-cache word is supplied. -/
theorem partial_zero (bank:F.Stack→List Bool) :partialBank bank 0=fun _=>[] :=by
  funext k
  simp only [partialBank,List.take_zero,List.not_mem_nil,ite_false]
/-- Completeness restores EVERY actual phase role, including original/rejected/work fields. -/
theorem partial_full (bank:F.Stack→List Bool) :partialBank bank 85=bank :=by
  funext k
  have ht:I.roles.take 85=I.roles:=by rw [←I.roles_length,List.take_length]
  simp only [partialBank,ht,I.roles_complete,ite_true]
/-- All eighty-five consecutive frames have been physically consumed at EOF. -/
theorem remaining_full (bank:F.Stack→List Bool) :remaining bank 85=[] :=by
  unfold remaining
  rw [←I.roles_length,List.drop_length]
  rfl
/-- No physical coefficient-parameter word remains after the final field. -/
theorem mass_full (bank:F.Stack→List Bool) :mass bank 85=0 :=by
  unfold mass
  rw [←I.roles_length,List.drop_length]
  rfl
/-- The whole fixed field loop pays every parser/call/validation pop and the actual EOF test. -/
theorem loop (bank:F.Stack→List Bool) (heap counter reference:List Bool) (n r:Nat) (hnr:n+r=85) :
    Runs program (8*mass bank n+8*r+1) (fieldAt n)
      (view (partialBank bank n) heap counter reference (remaining bank n) []) (ctl .done)
      (view bank heap counter reference [] []) :=by
  induction r generalizing n with
  | zero=>
    have hn:n=85:=by omega
    subst n
    simp only [mass_full,Nat.mul_zero,Nat.zero_add,partial_full,remaining_full]
    change Runs program 1 (ctl .eof) _ (ctl .done) _
    exact eof_run bank heap counter reference
  | succ r ih=>
    have hn:n<85:=by omega
    have hs:=field_run ⟨n,hn⟩ (partialBank bank n) heap counter reference (bank (I.role ⟨n,hn⟩))
      (remaining bank (n+1)) (partial_empty bank n hn)
    rw [partial_update bank n hn,next_at] at hs
    have ht:=ih (n+1) (by omega)
    have hh:=join hs ht
    rw [←remaining_cons bank n hn] at hh
    have hm:=mass_step bank n hn
    have hclock:8*mass bank n+8*(r+1)+1=
      (8*(bank (I.role ⟨n,hn⟩)).length+8)+(8*mass bank (n+1)+8*r+1):=by omega
    rw [hclock]
    change Runs program _ (ctl (.field ⟨n,hn⟩)) _ (ctl .done) _ at hh
    simpa only [fieldAt,hn,dite_eq_left] using hh
/-- Closed entire eighty-five-field trace from an ACTUALLY read record into the complete Fresh bank. -/
theorem fields_run (bank:F.Stack→List Bool) (heap counter reference:List Bool) :
    Runs program (8*mass bank 0+681) (ctl (.field 0))
      (view (fun _=>[]) heap counter reference (record bank) []) (ctl .done)
      (view bank heap counter reference [] []) :=by
  have h:=loop bank heap counter reference 0 85 (by omega)
  rw [partial_zero] at h
  have hc:8*mass bank 0+8*85+1=8*mass bank 0+681:=by omega
  rw [hc] at h
  have hz:fieldAt 0=ctl (.field 0):=by rfl
  rw [hz] at h
  simpa only [remaining,List.drop_zero,record] using h
end RiemannGaussian.SemiprimeD1StackFreshBankRestoreFields

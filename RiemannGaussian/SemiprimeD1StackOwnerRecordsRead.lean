/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOwnerRecordsCalls
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackOwnerRecordsRead
open SemiprimeD1StackOwnerRecords SemiprimeD1StackOwnerRecordsView SemiprimeD1StackOwnerRecordsCalls
open SemiprimeD1StackProcedureTrace (Runs runs_trans one_base)
open SemiprimeSourceHistogramKeyBits (frame)
/-- Actual field parse followed by consumption of the physically written valid bit. -/
theorem field_read (scopes:Bool) (s:S.Stack→List Bool) (keyBytes prefixBytes bankBytes hist out word tail pre:List Bool)
    (ho:if scopes then bankBytes=[] else keyBytes=[]) :
    Runs program (8*word.length+8) (.local (.field scopes))
      (data s (payload keyBytes prefixBytes bankBytes hist out) (rowAux (frame word tail) pre))
      (if scopes then .local .copyPrefix else .local (.field true))
      (data s (if scopes then payload keyBytes prefixBytes word hist out else payload word prefixBytes bankBytes hist out)
        (rowAux tail pre)) := by
  have htarget:(data s (payload keyBytes prefixBytes bankBytes hist out) (rowAux (frame word tail) pre))
      (if scopes then bank else key)=[]:=by
    cases scopes
    · change keyBytes=[];exact ho
    · change bankBytes=[];exact ho
  have hf:=field_call scopes (data s (payload keyBytes prefixBytes bankBytes hist out) (rowAux (frame word tail) pre))
    word tail rfl htarget rfl rfl
  let a:=rowAux tail pre
  let r:=if scopes then payload keyBytes prefixBytes word hist out else payload word prefixBytes bankBytes hist out
  have he:Function.update (Function.update (Function.update
      (data s (payload keyBytes prefixBytes bankBytes hist out) (rowAux (frame word tail) pre))
      (aux .reader) tail) (if scopes then bank else key) word) (aux .valid) [true]=
      data s r (Function.update a .valid [true]):=by
    cases scopes <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;>
      rw [update_aux] <;>
      have ha:Function.update (rowAux (frame word tail) pre) .reader tail=a:=by funext k;cases k <;> rfl
    all_goals rw [ha]
    · change Function.update (Function.update (data s _ a) (record _) word) (aux .valid) [true]=_
      rw [update_record,payload_key,update_aux];rfl
    · change Function.update (Function.update (data s _ a) (record _) word) (aux .valid) [true]=_
      rw [update_record,payload_bank,update_aux];rfl
  rw [he] at hf
  have hv:Runs program 1 (.local (.valid scopes)) (data s r (Function.update a .valid [true]))
      (if scopes then .local .copyPrefix else .local (.field true)) (data s r a):=by
    apply one_base program _ _ (.pop (aux .valid) (.local .abort) (.local .abort)
      (if scopes then .local .copyPrefix else .local (.field true))) _ _ rfl
    · simp only [SemiprimeD1StackBytecode.execute,data_aux,Function.update_same,
        SemiprimeD1StackBytecode.choose,List.head?_cons]
    · simp only [SemiprimeD1StackBytecode.execute,data_aux,Function.update_same,
        update_aux,Function.update_idem,List.tail_cons]
      have h:Function.update a .valid []=a:=by
        change Function.update a .valid (a .valid)=a
        exact Function.update_eq_self _ _
      rw [h]
  have h:=runs_trans program _ _ _ _ _ _ _ _ hf hv
  simpa only [r,a,show (8*word.length+7)+1=8*word.length+8 by omega] using h
/-- One actual tag and BOTH actual source-catalogue fields, never supplied operands. -/
theorem row_read (s:S.Stack→List Bool) (keyBytes bankBytes tail pre hist out:List Bool) :
    Runs program (8*keyBytes.length+8*bankBytes.length+17) (.local .loop)
      (data s (payload [] [] [] hist out) (rowAux (true::frame keyBytes (frame bankBytes tail)) pre))
      (.local .copyPrefix) (data s (payload keyBytes [] bankBytes hist out) (rowAux tail pre)) := by
  have hh:Runs program 1 (.local .loop)
      (data s (payload [] [] [] hist out) (rowAux (true::frame keyBytes (frame bankBytes tail)) pre))
      (.local (.field false))
      (data s (payload [] [] [] hist out) (rowAux (frame keyBytes (frame bankBytes tail)) pre)):=by
    apply one_base program _ _ (.pop (aux .reader) (.local .reverse) (.local .reverse) (.local (.field false))) _ _ rfl rfl
    simp only [SemiprimeD1StackBytecode.execute,data_aux,update_aux]
    congr 1;funext k;cases k <;> rfl
  have hk:=field_read false s [] [] [] hist out keyBytes (frame bankBytes tail) pre rfl
  have hb:=field_read true s keyBytes [] [] hist out bankBytes tail pre rfl
  have h:=runs_trans program _ _ _ _ _ _ _ _ hh (runs_trans program _ _ _ _ _ _ _ _ hk hb)
  simpa only [Bool.false_eq_true,ite_false,ite_true,show 1+((8*keyBytes.length+8)+(8*bankBytes.length+8))=
    8*keyBytes.length+8*bankBytes.length+17 by omega] using h
/-- Full retained caller prefix is copied before EVERY owner, preserving repeats/conflicts and suffix. -/
theorem prefix_copy (s:S.Stack→List Bool) (keyBytes bankBytes tail pre hist out:List Bool) :
    Runs program (5*pre.length+4) (.local .copyPrefix)
      (data s (payload keyBytes [] bankBytes hist out) (rowAux tail pre)) (.local .emit)
      (data s (payload keyBytes pre bankBytes hist out) (rowAux tail pre)) := by
  have h:=copy_call true (data s (payload keyBytes [] bankBytes hist out) (rowAux tail pre))
    (.local .copyPrefix) (.local .emit) rfl rfl
  change Runs program _ _ _ _ (Function.update _ (record _) (pre++[])) at h
  rw [List.append_nil,update_record,payload_prefix] at h
  exact h
end RiemannGaussian.SemiprimeD1StackOwnerRecordsRead

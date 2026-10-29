/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOwnerRecordsRead
import RiemannGaussian.SemiprimeD1StackPhysicalLoops
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackOwnerRecordsEmit
open SemiprimeD1StackOwnerRecords SemiprimeD1StackOwnerRecordsView SemiprimeD1StackOwnerRecordsRead
open SemiprimeD1StackProcedureTrace (Runs runs_trans)
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeD1OwnerPrefixBits (records)
namespace E
export SemiprimeD1StackOwnerRecordExecution (source_run timeBound)
export SemiprimeD1StackOwnerRecord (table)
end E
/-- ALL owner-table and ordinal work is physically cleared by the actual subprogram;
only its three deliberately retained operands and logger accumulators survive. -/
theorem done_payload (keyBytes:List Bool) (rows:List (List Bool×Bool)) (tail:List Bool)
    (words:List (List Bool)) (hs:words.length≤2) (hist out:List Bool) :
    (R.done keyBytes rows tail words hs hist out).data=
      payload keyBytes tail (vectorBits words)
        ((L.row (SemiprimeD1StackOwnerRecord.S.result words) (E.table keyBytes rows tail words hs)).reverse++hist) out:=by
  funext k;fin_cases k <;> rfl
/-- The actual34-role source consumes its actual parsed/copied operands and logs one row. -/
theorem record_call (s:S.Stack→List Bool) (a:Aux→List Bool) (keyBytes:List Bool)
    (rows:List (List Bool×Bool)) (tail:List Bool) (words:List (List Bool))
    (hs:words.length≤2) (hist out:List Bool) :
    ∃time≤E.timeBound keyBytes rows words hs+1,Runs program time (.local .emit)
      (data s (payload keyBytes (records rows tail) (vectorBits words) hist out) a)
      (.local .clearKey) (data s (R.done keyBytes rows tail words hs hist out).data a):=by
  obtain ⟨t,ht,hr⟩:=E.source_run keyBytes rows tail words hs hist out
  refine ⟨t+1,Nat.add_le_add_right ht 1,?_⟩
  apply SemiprimeD1StackProcedureInclusion.included_call program record Label.record record_injective
    R.program (.inl .start) (fun _=>rfl) (.local .emit) (.local .clearKey) rfl t
    (R.initial keyBytes (records rows tail) (vectorBits words) hist out)
    (R.done keyBytes rows tail words hs hist out) _ _ rfl rfl rfl rfl hr
  · exact ⟨fun _=>rfl,fun _ _=>rfl⟩
  · constructor
    · intro k;rfl
    · intro k hk;rcases k with k|k
      · rfl
      · rcases k with k|k
        · exact False.elim (hk k rfl)
        · rfl
/-- Actual key drain, including its real EOF transition. -/
theorem clear_key (s:S.Stack→List Bool) (a:Aux→List Bool) (keyBytes tail bankBytes hist out:List Bool) :
    Runs program (keyBytes.length+1) (.local .clearKey)
      (data s (payload keyBytes tail bankBytes hist out) a) (.local .clearTail)
      (data s (payload [] tail bankBytes hist out) a):=by
  let before:=data s (payload keyBytes tail bankBytes hist out) a
  have he:Function.update before key keyBytes=before:=by
    change Function.update before key (before key)=before
    exact Function.update_eq_self _ _
  have h:=SemiprimeD1StackPhysicalLoops.drain program (.local .clearKey) (.local .clearTail) key rfl before keyBytes
  rw [he] at h
  simpa only [before,key,update_record,payload_key] using h
theorem clear_tail (s:S.Stack→List Bool) (a:Aux→List Bool) (tail bankBytes hist out:List Bool) :
    Runs program (tail.length+1) (.local .clearTail)
      (data s (payload [] tail bankBytes hist out) a) (.local .clearBank)
      (data s (payload [] [] bankBytes hist out) a):=by
  let before:=data s (payload [] tail bankBytes hist out) a
  have he:Function.update before prefixReader tail=before:=by
    change Function.update before prefixReader (before prefixReader)=before
    exact Function.update_eq_self _ _
  have h:=SemiprimeD1StackPhysicalLoops.drain program (.local .clearTail) (.local .clearBank) prefixReader rfl before tail
  rw [he] at h
  simpa only [before,prefixReader,update_record,payload_prefix] using h
theorem clear_bank (s:S.Stack→List Bool) (a:Aux→List Bool) (bankBytes hist out:List Bool) :
    Runs program (bankBytes.length+1) (.local .clearBank)
      (data s (payload [] [] bankBytes hist out) a) (.local .loop)
      (data s (payload [] [] [] hist out) a):=by
  let before:=data s (payload [] [] bankBytes hist out) a
  have he:Function.update before bank bankBytes=before:=by
    change Function.update before bank (before bank)=before
    exact Function.update_eq_self _ _
  have h:=SemiprimeD1StackPhysicalLoops.drain program (.local .clearBank) (.local .loop) bank rfl before bankBytes
  rw [he] at h
  simpa only [before,bank,update_record,payload_bank] using h
/-- Complete actual three retained-operand cleanup; every other role was already physically cleared. -/
theorem clear_run (s:S.Stack→List Bool) (a:Aux→List Bool) (keyBytes tail bankBytes hist out:List Bool) :
    Runs program (keyBytes.length+tail.length+bankBytes.length+3) (.local .clearKey)
      (data s (payload keyBytes tail bankBytes hist out) a) (.local .loop)
      (data s (payload [] [] [] hist out) a):=by
  have h:=runs_trans program _ _ _ _ _ _ _ _ (clear_key s a keyBytes tail bankBytes hist out)
    (runs_trans program _ _ _ _ _ _ _ _ (clear_tail s a tail bankBytes hist out) (clear_bank s a bankBytes hist out))
  simpa only [show (keyBytes.length+1)+((tail.length+1)+(bankBytes.length+1))=
    keyBytes.length+tail.length+bankBytes.length+3 by omega] using h
end RiemannGaussian.SemiprimeD1StackOwnerRecordsEmit

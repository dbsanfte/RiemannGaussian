/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOwnerRecords
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackOwnerRecordsView
open SemiprimeD1StackOwnerRecords
/-- Actual owner-filter work roles alias no upstream source or outer loop word. -/
theorem record_injective :Function.Injective record:=Sum.inr_injective.comp Sum.inl_injective
/-- Actual private outer roles alias no source or filter role. -/
theorem aux_injective :Function.Injective aux:=Sum.inr_injective.comp Sum.inr_injective
/-- Literal reached filter-work projection. -/
theorem data_record (s:S.Stack→List Bool) (f:R.Stack→List Bool) (a:Aux→List Bool) (k:R.Stack) :
    data s f a (record k)=f k:=rfl
/-- Literal reached private metadata/reader/collector projection. -/
theorem data_aux (s:S.Stack→List Bool) (f:R.Stack→List Bool) (a:Aux→List Bool) (k:Aux) :
    data s f a (aux k)=a k:=rfl
/-- Exact physical filter-role update preserving the retained actual source and every outer word. -/
theorem update_record (s:S.Stack→List Bool) (f:R.Stack→List Bool) (a:Aux→List Bool) (k:R.Stack) (word:List Bool) :
    Function.update (data s f a) (record k) word=data s (Function.update f k word) a:=by
  funext j;rcases j with j|j
  · exact Function.update_of_ne (by intro h;cases h) _ _
  · rcases j with j|j
    · change Function.update (data s f a) (record k) word (record j)=(Function.update f k word) j
      simp only [Function.update_apply,data_record,record_injective.eq_iff]
    · exact Function.update_of_ne (by intro h;cases h) _ _
/-- Exact physical outer-role update preserving all original source/filter data. -/
theorem update_aux (s:S.Stack→List Bool) (f:R.Stack→List Bool) (a:Aux→List Bool) (k:Aux) (word:List Bool) :
    Function.update (data s f a) (aux k) word=data s f (Function.update a k word):=by
  funext j;rcases j with j|j
  · exact Function.update_of_ne (by intro h;cases h) _ _
  · rcases j with j|j
    · exact Function.update_of_ne (by intro h;cases h) _ _
    · change Function.update (data s f a) (aux k) word (aux j)=(Function.update a k word) j
      simp only [Function.update_apply,data_aux,aux_injective.eq_iff]
/-- Literal owner-record operand store; only bytes already parsed or physically copied. -/
def payload (key prefixBytes bank hist out : List Bool) : R.Stack→List Bool :=
  (R.initial key prefixBytes bank hist out).data
/-- Physical parsed key insertion affects no other operand or alias shadow. -/
theorem payload_key (key prefixBytes bank hist out word : List Bool) :
    Function.update (payload key prefixBytes bank hist out)
      (SemiprimeD1StackOwnerRecord.tableStack SemiprimeD1StackOwnerTable.query) word=
      payload word prefixBytes bank hist out :=by
  funext k;fin_cases k <;> rfl
theorem payload_prefix (key prefixBytes bank hist out word : List Bool) :
    Function.update (payload key prefixBytes bank hist out)
      (SemiprimeD1StackOwnerRecord.tableStack SemiprimeD1StackOwnerTable.reader) word=
      payload key word bank hist out :=by
  funext k;fin_cases k <;> rfl
theorem payload_bank (key prefixBytes bank hist out word : List Bool) :
    Function.update (payload key prefixBytes bank hist out) R.original word=
      payload key prefixBytes word hist out :=by
  funext k;fin_cases k <;> rfl
theorem payload_history (key prefixBytes bank hist out word : List Bool) :
    Function.update (payload key prefixBytes bank hist out) R.history word=
      payload key prefixBytes bank word out :=by
  funext k;fin_cases k <;> rfl
theorem payload_output (key prefixBytes bank hist out word : List Bool) :
    Function.update (payload key prefixBytes bank hist out) R.output word=
      payload key prefixBytes bank hist word :=by
  funext k;fin_cases k <;> rfl
end RiemannGaussian.SemiprimeD1StackOwnerRecordsView

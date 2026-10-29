/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryTagComplete
/-! # Complete actual search-answer restoration and cache retention
An actual hit really clears eleven unread/current words; exhausted searches
retain their already empty words. Both paths physically erase answer/counter/tag.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryTagCompleteView
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryTagComplete
namespace Log
export SemiprimeD1StackChildGroupFactoryWordLog (row)
end Log
/-- Every physical cache word outside actual early disposal, three search words and the answer history is retained. -/
theorem result_other (found:Bool) (before:Stack→List Bool) (position:List Bool) (k:Stack)
    (hf:∀j,Early.role j≠k) (ha:k≠aux .answerPosition) (hp:k≠aux .localPosition)
    (ht:k≠aux .tagWord) (hh:k≠aux .orderHistory):result found before position k=before k:=by
  simp only [result,Answer.result,Function.update_of_ne ht,Function.update_of_ne hp,
    Function.update_of_ne ha,Function.update_of_ne hh]
  cases found with
  | false=>exact Function.update_of_ne ha _ _
  | true=>
    change Early.result (copied before position) k=before k
    rw [Early.result_other _ _ hf]
    exact Function.update_of_ne ha _ _
/-- The actual answer word is physically empty after its real drain. -/
theorem result_answer (found:Bool) (before:Stack→List Bool) (position:List Bool):
    result found before position (aux .answerPosition)=[]:=rfl
/-- The actual binary local counter is physically empty after its real drain. -/
theorem result_local (found:Bool) (before:Stack→List Bool) (position:List Bool):
    result found before position (aux .localPosition)=[]:=rfl
/-- The actual old target tag is physically empty after its real drain. -/
theorem result_tag (found:Bool) (before:Stack→List Bool) (position:List Bool):
    result found before position (aux .tagWord)=[]:=rfl
/-- At a real hit, every one of the eleven actual unread/current tapes is physically erased. -/
theorem result_hit_role (before:Stack→List Bool) (position:List Bool) (j:Fin 11):
    result true before position (Early.role j)=[]:=by fin_cases j <;> rfl
/-- Exhausted-search finishing preserves the real work words that were already cleared by the actual search. -/
theorem result_missing_role (before:Stack→List Bool) (position:List Bool) (j:Fin 11):
    result false before position (Early.role j)=before (Early.role j):=by fin_cases j <;> rfl
/-- Exact computed binary index answer in actual original-port log order. -/
theorem result_orderHistory (found:Bool) (before:Stack→List Bool) (position:List Bool):
    result found before position (aux .orderHistory)=
      (Log.row position).reverse++before (aux .orderHistory):=by
  have hh:cleared found before position (aux .orderHistory)=before (aux .orderHistory):=by
    cases found with
    | false=>rfl
    | true=>
      change Early.result (copied before position) (aux .orderHistory)=before (aux .orderHistory)
      rw [Early.result_other _ _ (by intro j;fin_cases j <;> decide)]
      rfl
  change (Log.row position).reverse++cleared found before position (aux .orderHistory)=_
  rw [hh]
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryTagCompleteView

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryOldPortOne
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryTagSourceView
/-! # Complete actual original-port iteration restoration and ordered index meaning -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryOldPortOneView
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryOldPortOne
open SemiprimeBitArithmetic (bitValue)
namespace QV
export SemiprimeD1StackChildGroupFactoryTagSourceView (result_other result_answer result_local result_tag result_work result_orderHistory)
end QV
namespace Early
export SemiprimeD1StackChildGroupFactoryTagEarlyClear (role)
end Early
namespace PV
export SemiprimeD1StackChildGroupFactoryOldPortPickView
  (result_oldReader result_role result_clean result_skipped_tag)
end PV
namespace Position
export SemiprimeD1StackChildGroupFactoryTagLoopView (finalPosition)
end Position
namespace Log
export SemiprimeD1StackChildGroupFactoryWordLog (row)
end Log
/-- Full actual cache retention outside the original reader, query work and ordered answer log. -/
theorem result_other (before:Stack→List Bool) (buckets:List Buckets.Bucket) (p:Parse.Point) (tail target:List Bool) (k:Stack)
    (hf:∀j,Early.role j≠k) (ho:k≠aux .oldReader) (ha:k≠aux .answerPosition)
    (hp:k≠aux .localPosition) (ht:k≠aux .tagWord) (hh:k≠aux .orderHistory):
    result before buckets p tail target k=before k:=by
  have hraw:∀j,Cleanup.role j≠k:=by
    intro j
    fin_cases j
    · exact hf 4
    · exact hf 7
    · exact hf 8
  by_cases h:bitValue p.vertex=bitValue target
  · simp only [result,h,ite_true]
    rw [QV.result_other _ _ _ _ _ k hf ha hp ht hh]
    exact PV.result_other _ _ _ _ k hraw ho ht
  · simp only [result,h,ite_false]
    exact PV.result_other _ _ _ _ k hraw ho ht
/-- Actual original reader advances exactly one record, even when the query short-circuits early. -/
theorem result_oldReader (before:Stack→List Bool) (buckets:List Buckets.Bucket) (p:Parse.Point) (tail target:List Bool):
    result before buckets p tail target (aux .oldReader)=tail:=by
  by_cases h:bitValue p.vertex=bitValue target
  · simp only [result,h,ite_true]
    rw [QV.result_other _ _ _ _ _ _ (by intro j;fin_cases j <;> decide)
      (by decide) (by decide) (by decide) (by decide)]
    exact PV.result_oldReader _ _ _ _
  · simp only [result,h,ite_false]
    exact PV.result_oldReader _ _ _ _
/-- All eleven actual nested-reader/current-field/candidate roles are physically ready for the next old port. -/
theorem result_work (before:Stack→List Bool) (buckets:List Buckets.Bucket) (p:Parse.Point) (tail target:List Bool)
    (hh:∀k∈Header.cleanRoles,before k=[]) (hch:∀k∈Child.cleanRoles,before k=[])
    (ho:before (aux .outerReader)=[]) (hcan:before (aux .candidateTag)=[]) (j:Fin 11):
    result before buckets p tail target (Early.role j)=[]:=by
  have hh':∀k∈Header.cleanRoles,picked before p tail target k=[]:=PV.result_headerClean _ _ _ _ hh
  have hch':∀k∈Child.cleanRoles,picked before p tail target k=[]:=PV.result_childClean _ _ _ _ hch
  have ho':picked before p tail target (aux .outerReader)=[]:=
    (PV.result_other _ _ _ _ _ (by intro i;fin_cases i <;> decide) (by decide) (by decide)).trans ho
  have hc':picked before p tail target (aux .candidateTag)=[]:=
    (PV.result_other _ _ _ _ _ (by intro i;fin_cases i <;> decide) (by decide) (by decide)).trans hcan
  by_cases h:bitValue p.vertex=bitValue target
  · simp only [result,h,ite_true]
    exact QV.result_work _ _ _ _ _ hh' hch' hc' j
  · simp only [result,h,ite_false]
    fin_cases j
    · exact ho'
    · exact hh' (aux .childReader) (by simp [Header.cleanRoles])
    · exact hh' (aux .endpointReader) (by simp [Header.cleanRoles])
    · exact hch' (aux .rowBuffer) (by simp [Child.cleanRoles])
    · exact hch' (aux .ownerKey) (by simp [Child.cleanRoles])
    · exact hch' (aux .sourceKey) (by simp [Child.cleanRoles])
    · exact hch' (aux .slotWord) (by simp [Child.cleanRoles])
    · exact hch' (aux .edgeWord) (by simp [Child.cleanRoles])
    · exact hch' (aux .sideWord) (by simp [Child.cleanRoles])
    · exact hch' (aux .globalPosition) (by simp [Child.cleanRoles])
    · exact hc'
/-- Actual answer operand is physically fresh for the next old port. -/
theorem result_answer (before:Stack→List Bool) (buckets:List Buckets.Bucket) (p:Parse.Point) (tail target:List Bool)
    (ha:before (aux .answerPosition)=[]):result before buckets p tail target (aux .answerPosition)=[]:=by
  by_cases h:bitValue p.vertex=bitValue target
  · simp only [result,h,ite_true];exact QV.result_answer _ _ _ _ _
  · simp only [result,h,ite_false]
    exact (PV.result_other _ _ _ _ _ (by intro i;fin_cases i <;> decide) (by decide) (by decide)).trans ha
/-- Actual local counter is physically fresh for the next old port. -/
theorem result_local (before:Stack→List Bool) (buckets:List Buckets.Bucket) (p:Parse.Point) (tail target:List Bool)
    (hp:before (aux .localPosition)=[]):result before buckets p tail target (aux .localPosition)=[]:=by
  by_cases h:bitValue p.vertex=bitValue target
  · simp only [result,h,ite_true];exact QV.result_local _ _ _ _ _
  · simp only [result,h,ite_false]
    exact (PV.result_other _ _ _ _ _ (by intro i;fin_cases i <;> decide) (by decide) (by decide)).trans hp
/-- Actual target tag is physically fresh before acquiring the next original tag. -/
theorem result_tag (before:Stack→List Bool) (buckets:List Buckets.Bucket) (p:Parse.Point) (tail target:List Bool)
    (ht:before (aux .tagWord)=[]):result before buckets p tail target (aux .tagWord)=[]:=by
  by_cases h:bitValue p.vertex=bitValue target
  · simp only [result,h,ite_true];exact QV.result_tag _ _ _ _ _
  · simp only [result,h,ite_false]
    exact (PV.result_skipped_tag _ _ _ _ h).trans ht
/-- Physical binary answer word generated by this actual whole first-index query. -/
def answerWord (buckets:List Buckets.Bucket) (p:Parse.Point) (target:List Bool):List Bool:=
  Position.finalPosition buckets target (Build.rawTag p.edge p.side) []
/-- Exactly matching numeric old vertices emit one computed first-index word, in original old-port order. -/
theorem result_orderHistory (before:Stack→List Bool) (buckets:List Buckets.Bucket) (p:Parse.Point) (tail target:List Bool):
    result before buckets p tail target (aux .orderHistory)=
      (if bitValue p.vertex=bitValue target then (Log.row (answerWord buckets p target)).reverse else [])++before (aux .orderHistory):=by
  by_cases h:bitValue p.vertex=bitValue target
  · simp only [result,h,ite_true]
    rw [QV.result_orderHistory]
    rw [picked,PV.result_other _ _ _ _ _ (by intro j;fin_cases j <;> decide) (by decide) (by decide)]
    rfl
  · simp only [result,h,ite_false]
    rw [picked,PV.result_other _ _ _ _ _ (by intro j;fin_cases j <;> decide) (by decide) (by decide)]
    rfl
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryOldPortOneView

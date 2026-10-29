/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryTagSource
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryTagCompleteView
/-! # Exact whole-query restoration and actual ordered computed-index records
The real search outcome is derived from acquired bucket bytes. Eleven work
words are erased at a hit or proved exhausted; three local words are always
physically drained by the actual final source.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryTagSourceView
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryTagSource
namespace CV
export SemiprimeD1StackChildGroupFactoryTagCompleteView
  (result_other result_answer result_local result_tag result_hit_role result_missing_role result_orderHistory)
end CV
namespace Early
export SemiprimeD1StackChildGroupFactoryTagEarlyClear (role)
end Early
namespace LV
export SemiprimeD1StackChildGroupFactoryTagLoopView (result_clean result_headerClean result_candidate result_outerReader)
end LV
namespace Log
export SemiprimeD1StackChildGroupFactoryWordLog (row)
end Log
/-- Every actual cache/caller word outside eleven work tapes, three local words and the answer log is retained. -/
theorem result_other (before:Stack→List Bool) (buckets:List Buckets.Bucket) (target tag position:List Bool) (k:Stack)
    (hf:∀j,Early.role j≠k) (ha:k≠aux .answerPosition) (hp:k≠aux .localPosition)
    (ht:k≠aux .tagWord) (hh:k≠aux .orderHistory):result before buckets target tag position k=before k:=by
  rw [result,CV.result_other _ _ _ _ hf ha hp ht hh]
  have hraw:∀j,Cleanup.role j≠k:=by
    intro j
    fin_cases j
    · exact hf 4
    · exact hf 5
    · exact hf 6
    · exact hf 7
    · exact hf 8
    · exact hf 9
  have houter:=Ne.symm (hf 0)
  have hendpoint:=Ne.symm (hf 2)
  have hcan:=Ne.symm (hf 10)
  change k≠aux .outerReader at houter
  change k≠aux .endpointReader at hendpoint
  change k≠aux .candidateTag at hcan
  rw [searched,View.result_other _ _ _ _ _ k hraw hendpoint houter hcan hp]
  exact Function.update_of_ne houter _ _
/-- The physically copied computed answer is actually erased. -/
theorem result_answer (before:Stack→List Bool) (buckets:List Buckets.Bucket) (target tag position:List Bool):
    result before buckets target tag position (aux .answerPosition)=[]:=CV.result_answer _ _ _
/-- The physically incremented local counter is actually erased. -/
theorem result_local (before:Stack→List Bool) (buckets:List Buckets.Bucket) (target tag position:List Bool):
    result before buckets target tag position (aux .localPosition)=[]:=CV.result_local _ _ _
/-- The physically built original target tag is actually erased. -/
theorem result_tag (before:Stack→List Bool) (buckets:List Buckets.Bucket) (target tag position:List Bool):
    result before buckets target tag position (aux .tagWord)=[]:=CV.result_tag _ _ _
/-- All eleven actual nested-reader/current-field/candidate work tapes are ready for the next query. -/
theorem result_work (before:Stack→List Bool) (buckets:List Buckets.Bucket) (target tag position:List Bool)
    (hh:∀k∈Header.cleanRoles,before k=[]) (hz:∀k∈Parse.cleanRoles,before k=[])
    (hc:before (aux .candidateTag)=[]) (j:Fin 11):
    result before buckets target tag position (Early.role j)=[]:=by
  by_cases hf:Loop.found buckets target tag=true
  · rw [result,hf]
    exact CV.result_hit_role _ _ _
  · have hnf:Loop.found buckets target tag=false:=by
      cases hval:Loop.found buckets target tag with
      | false=>rfl
      | true=>exact False.elim (hf hval)
    rw [result,hnf,CV.result_missing_role]
    have hh':∀k∈Header.cleanRoles,copied before buckets k=[]:=by simpa [copied,Header.cleanRoles,aux,field] using hh
    have hz':∀k∈Parse.cleanRoles,copied before buckets k=[]:=by simpa [copied,Parse.cleanRoles,aux,field] using hz
    have hc':copied before buckets (aux .candidateTag)=[]:=by simpa [copied,aux] using hc
    have hheader:=LV.result_headerClean buckets (copied before buckets) target tag position hh' hnf
    have hchild:=LV.result_clean buckets (copied before buckets) target tag position hz' hnf
    have hcandidate:=LV.result_candidate buckets (copied before buckets) target tag position hc' hnf
    change Loop.result buckets (copied before buckets) target tag position (Early.role j)=[]
    fin_cases j
    · exact LV.result_outerReader _ _ _ _ _ hnf
    · exact hheader (aux .childReader) (by simp [Header.cleanRoles])
    · exact hheader (aux .endpointReader) (by simp [Header.cleanRoles])
    · exact hchild (aux .rowBuffer) (by simp [Parse.cleanRoles])
    · exact hchild (aux .ownerKey) (by simp [Parse.cleanRoles])
    · exact hchild (aux .sourceKey) (by simp [Parse.cleanRoles])
    · exact hchild (aux .slotWord) (by simp [Parse.cleanRoles])
    · exact hchild (aux .edgeWord) (by simp [Parse.cleanRoles])
    · exact hchild (aux .sideWord) (by simp [Parse.cleanRoles])
    · exact hchild (aux .globalPosition) (by simp [Parse.cleanRoles])
    · exact hcandidate
/-- Actual ordered binary index log, with the computed counter word and every previous original port retained. -/
theorem result_orderHistory (before:Stack→List Bool) (buckets:List Buckets.Bucket) (target tag position:List Bool):
    result before buckets target tag position (aux .orderHistory)=
      (Log.row (View.finalPosition buckets target tag position)).reverse++before (aux .orderHistory):=by
  rw [result,CV.result_orderHistory,searched,
    View.result_other _ _ _ _ _ _ (by intro j;fin_cases j <;> decide) (by decide) (by decide) (by decide) (by decide)]
  rfl
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryTagSourceView

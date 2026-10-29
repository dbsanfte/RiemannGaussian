/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketsSourceView
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryVertexBody
/-! # Actual post-bucket readiness for the whole all-vertex source
All twenty query words, arithmetic and twelve converter words are derived
from actual cleanup and retained initial emptiness, including zero packets.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketReady
open SemiprimeD1StackChildGroupFactoryRoles
namespace B
export SemiprimeD1StackChildGroupFactoryBucketsSource (result)
export SemiprimeD1StackChildGroupFactoryBucketsSourceView
  (Protected result_other result_clean result_reuse_word result_endpointReader result_histories)
end B
namespace Body
export SemiprimeD1StackChildGroupFactoryVertexBody (Ready)
end Body
namespace Work
export SemiprimeD1StackChildGroupFactoryOldPortsLoop (freshRole)
end Work
namespace Parse
export SemiprimeD1StackChildGroupFactoryBucketParse (Endpoint cleanRoles)
end Parse
/-- Actual whole completed bucket source restores precisely the next source's physical obligations. -/
theorem result_ready (before:Stack→List Bool) (packets:List (List Bool)) (es:List Parse.Endpoint)
    (position:List Bool) (hr:Body.Ready before) (hbh:before (aux .bucketHistory)=[]):
    Body.Ready (B.result before packets es position):=by
  have keep (k:Stack) (hk:B.Protected k) (hz:before k=[]):B.result before packets es position k=[]:=
    (B.result_other _ _ _ _ _ hk).trans hz
  have hc:∀k∈Parse.cleanRoles,before k=[]:=by
    intro k hk
    simp only [Parse.cleanRoles,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact hr.work (4:Fin 20) (by decide)
    · exact hr.work (5:Fin 20) (by decide)
    · exact hr.work (6:Fin 20) (by decide)
    · exact hr.work (7:Fin 20) (by decide)
    · exact hr.work (8:Fin 20) (by decide)
    · exact hr.work (3:Fin 20) (by decide)
    · exact hr.work (16:Fin 20) (by decide)
    · exact hr.work (17:Fin 20) (by decide)
  have hclean:=B.result_clean before packets es position hc
  constructor
  · intro j hj
    have hz:=hr.work j hj
    fin_cases j
    · exact keep _ (by
        constructor
        all_goals first | (intro k;fin_cases k <;> decide) | decide) hz
    · exact keep _ (by
        constructor
        all_goals first | (intro k;fin_cases k <;> decide) | decide) hz
    · exact B.result_endpointReader _ _ _ _ hz
    · exact hclean _ (by simp [Parse.cleanRoles,Work.freshRole])
    · exact hclean _ (by simp [Parse.cleanRoles,Work.freshRole])
    · exact hclean _ (by simp [Parse.cleanRoles,Work.freshRole])
    · exact hclean _ (by simp [Parse.cleanRoles,Work.freshRole])
    · exact hclean _ (by simp [Parse.cleanRoles,Work.freshRole])
    · exact hclean _ (by simp [Parse.cleanRoles,Work.freshRole])
    · exact (hj rfl).elim
    · exact keep _ (by
        constructor
        all_goals first | (intro k;fin_cases k <;> decide) | decide) hz
    · exact keep _ (by
        constructor
        all_goals first | (intro k;fin_cases k <;> decide) | decide) hz
    · exact keep _ (by
        constructor
        all_goals first | (intro k;fin_cases k <;> decide) | decide) hz
    · exact keep _ (by
        constructor
        all_goals first | (intro k;fin_cases k <;> decide) | decide) hz
    · exact B.result_reuse_word _ _ _ _ 0 hz
    · exact keep _ (by
        constructor
        all_goals first | (intro k;fin_cases k <;> decide) | decide) hz
    · exact hclean _ (by simp [Parse.cleanRoles,Work.freshRole])
    · exact hclean _ (by simp [Parse.cleanRoles,Work.freshRole])
    · exact keep _ (by
        constructor
        all_goals first | (intro k;fin_cases k <;> decide) | decide) hz
    · exact keep _ (by
        constructor
        all_goals first | (intro k;fin_cases k <;> decide) | decide) hz
  · intro k
    exact keep _ (by
      constructor
      all_goals first | (intro j;fin_cases j <;> cases k <;> decide) | (cases k <;> decide)) (hr.arithmetic_clean k)
  · intro k
    have h:=B.result_reuse_word before packets es position
      (SemiprimeD1StackChildGroupFactoryBucketConvertView.ordinalIndex k)
      (by rw [SemiprimeD1StackChildGroupFactoryBucketConvertView.ordinalIndex_role];exact hr.ordinal_clean k)
    simpa only [SemiprimeD1StackChildGroupFactoryBucketConvertView.ordinalIndex_role] using h
  · exact keep _ (by
      constructor
      all_goals first | (intro j;fin_cases j <;> decide) | decide) hr.oldReader_empty
  · exact B.result_reuse_word _ _ _ _ 2 hr.portBank_empty
  · exact (B.result_histories _ _ _ _ hbh hr.portHistory_empty).2
  · exact keep _ (by
      constructor
      all_goals first | (intro j;fin_cases j <;> decide) | decide) hr.orderBank_empty
  · exact keep _ (by
      constructor
      all_goals first | (intro j;fin_cases j <;> decide) | decide) hr.orderHistory_empty
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketReady

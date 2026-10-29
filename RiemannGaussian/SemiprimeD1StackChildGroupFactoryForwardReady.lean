/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryForwardBucketsSource
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryVertexBody
/-! # Actual forward catalogue bank satisfies the later all-vertex workspace ABI -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryForwardReady
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactory
namespace F
export SemiprimeD1StackChildGroupFactoryForwardSource (activation rows result)
end F
namespace A
export SemiprimeD1StackChildGroupFactoryActivationSource (result)
end A
namespace EV
export SemiprimeD1StackChildGroupFactoryEndpointSourceView (Protected result_clean)
end EV
namespace Source
export SemiprimeD1StackChildGroupFactoryForwardBucketsSource (forward_other)
end Source
namespace Parse
export SemiprimeD1StackChildGroupFactoryEndpointParse (Fields cleanRoles)
end Parse
namespace Body
export SemiprimeD1StackChildGroupFactoryVertexBody (Ready)
end Body
namespace Work
export SemiprimeD1StackChildGroupFactoryOldPortsLoop (freshRole)
end Work
/-- All later query, ordinal and arithmetic readiness comes from the actual completed forward source. -/
theorem result_ready (i:Inputs) (a coordinate:Nat) (ids:List (List Bool)) (fields:List Parse.Fields):
    Body.Ready (F.result i a coordinate ids fields):=by
  have keep (k:Stack) (hk:EV.Protected k) (hz:A.result i coordinate (F.activation a ids) k=[]):
      F.result i a coordinate ids fields k=[]:=(Source.forward_other _ _ _ _ _ _ hk).trans hz
  have hc:=EV.result_clean (A.result i coordinate (F.activation a ids)) (F.rows i a coordinate ids fields)
    (by simp [A.result,SemiprimeD1StackChildGroupFactoryActivation.data,input,Parse.cleanRoles,aux,field])
  constructor
  · intro j hj
    fin_cases j
    · exact keep _ (by
        constructor
        all_goals first | (intro k;fin_cases k <;> decide) | decide) rfl
    · exact hc _ (by simp [Parse.cleanRoles,Work.freshRole])
    · exact keep _ (by
        constructor
        all_goals first | (intro k;fin_cases k <;> decide) | decide) rfl
    · exact keep _ (by
        constructor
        all_goals first | (intro k;fin_cases k <;> decide) | decide) rfl
    · exact hc _ (by simp [Parse.cleanRoles,Work.freshRole])
    · exact hc _ (by simp [Parse.cleanRoles,Work.freshRole])
    · exact hc _ (by simp [Parse.cleanRoles,Work.freshRole])
    · exact hc _ (by simp [Parse.cleanRoles,Work.freshRole])
    · exact keep _ (by
        constructor
        all_goals first | (intro k;fin_cases k <;> decide) | decide) rfl
    · exact (hj rfl).elim
    · exact keep _ (by
        constructor
        all_goals first | (intro k;fin_cases k <;> decide) | decide) rfl
    · exact keep _ (by
        constructor
        all_goals first | (intro k;fin_cases k <;> decide) | decide) rfl
    · exact keep _ (by
        constructor
        all_goals first | (intro k;fin_cases k <;> decide) | decide) rfl
    · exact keep _ (by
        constructor
        all_goals first | (intro k;fin_cases k <;> decide) | decide) rfl
    · exact hc _ (by simp [Parse.cleanRoles,Work.freshRole])
    · exact hc _ (by simp [Parse.cleanRoles,Work.freshRole])
    · exact hc _ (by simp [Parse.cleanRoles,Work.freshRole])
    · exact hc _ (by simp [Parse.cleanRoles,Work.freshRole])
    · exact keep _ (by
        constructor
        all_goals first | (intro k;fin_cases k <;> decide) | decide) rfl
    · exact keep _ (by
        constructor
        all_goals first | (intro k;fin_cases k <;> decide) | decide) rfl
  · intro k
    apply keep _ ?_ rfl
    constructor
    all_goals first | (intro j;fin_cases j <;> cases k <;> decide) | (cases k <;> decide)
  · intro k
    apply keep _ ?_ rfl
    constructor
    all_goals first | (intro j;fin_cases j <;> cases k <;> decide) | (cases k <;> decide)
  · exact keep _ (by
      constructor
      all_goals first | (intro j;fin_cases j <;> decide) | decide) rfl
  · exact keep _ (by
      constructor
      all_goals first | (intro j;fin_cases j <;> decide) | decide) rfl
  · exact keep _ (by
      constructor
      all_goals first | (intro j;fin_cases j <;> decide) | decide) rfl
  · exact keep _ (by
      constructor
      all_goals first | (intro j;fin_cases j <;> decide) | decide) rfl
  · exact keep _ (by
      constructor
      all_goals first | (intro j;fin_cases j <;> decide) | decide) rfl
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryForwardReady

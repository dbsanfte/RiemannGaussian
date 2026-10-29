/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryReadyExecution
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryInputRetention
/-! # Every actual producer word and displaced input shadow survives Ready258
All143 selector/occurrence/inventory words are retained literally. The seven
aliased input words are proved retained by the real complete core source;
all other producer words are foreign physical data, never projected away.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryReadyRetention
namespace R
export SemiprimeD1StackChildGroupFactoryReady
  (Stack factory allocation selector occurrence inventory initial sourceInputs Header recover recover_factory)
end R
namespace Core
export SemiprimeD1StackChildGroupFactory (input Inputs)
end Core
namespace G
export SemiprimeD1StackChildGroupFactoryRoles (Stack Aux aux inputRole)
end G
namespace E
export SemiprimeD1StackChildGroupFactoryExecution (done result)
end E
namespace Input
export SemiprimeD1StackChildGroupFactoryInputRetention (sourceMark result_input)
end Input
open SemiprimeD1StackChildGroupFactoryReadyTrace
/-- All143 actual producer roles; the complete fresh115 allocation is disjoint. -/
def producer :R.Stack→Bool
  | .inr (.inr (.inr _))=>false
  | _=>true
/-- A core role can alias a producer only when it is one of the actual retained source inputs. -/
theorem factory_producer (j:G.Stack) (hj:producer (R.factory j)=true):Input.sourceMark j=true:=by
  rcases j with j|j|j|j|j|j
  all_goals first
    | cases hj
    | cases j <;> simp [SemiprimeD1StackChildGroupFactoryReady.factory,producer,Input.sourceMark,G.inputRole,
        SemiprimeD1StackChildGroupFactoryReady.environment,SemiprimeD1StackChildGroupFactoryReady.catalogue,
        SemiprimeD1StackChildGroupFactoryReady.owners,SemiprimeD1StackChildGroupFactoryReady.factors,
        SemiprimeD1StackChildGroupFactoryReady.pairs,SemiprimeD1StackChildGroupFactoryReady.placements,
        SemiprimeD1StackChildGroupFactoryReady.packets,R.selector,R.occurrence,R.inventory,R.allocation] at hj ⊢
/-- Any actually aliased input is unchanged by the full actual core program. -/
theorem core_input (i:Core.Inputs) (a coordinate:Nat) (ids packets:List (List Bool))
    (fields:List SemiprimeD1StackChildGroupFactoryEndpointParse.Fields) (j:G.Stack) (hj:Input.sourceMark j=true):
    E.result i a coordinate ids packets fields j=Core.input i j:=by
  rcases j with j|j|j|j|j|j
  all_goals first | cases hj | exact Input.result_input i a coordinate ids packets fields j hj
/-- EVERY actual producer word is retained, including the seven alias images and all unused/shadow maps. -/
theorem producer_retained (s:SemiprimeD1StackChildGroupFactoryReady.S.Stack→List Bool)
    (p:SemiprimeD1StackChildGroupFactoryReady.P.Stack→List Bool)
    (iv:SemiprimeD1StackChildGroupFactoryReady.I.Stack→List Bool) (h:R.Header)
    (a coordinate:Nat) (ids packets:List (List Bool))
    (fields:List SemiprimeD1StackChildGroupFactoryEndpointParse.Fields)
    (finish:C.State R.Stack SemiprimeD1StackChildGroupFactoryWiring.Label)
    (hr:Rel R.factory (R.initial s p iv h).data
      (E.done (R.sourceInputs s p iv h) a coordinate ids packets fields) finish)
    (k:R.Stack) (hk:producer k=true):finish.data k=(R.initial s p iv h).data k:=by
  classical
  by_cases hm:∃j,R.factory j=k
  · obtain ⟨j,hj⟩:=hm
    have hp:producer (R.factory j)=true:=by rw [hj];exact hk
    calc
      finish.data k=finish.data (R.factory j):=congrArg finish.data hj.symm
      _=E.result (R.sourceInputs s p iv h) a coordinate ids packets fields j:=hr.1.1 j
      _=Core.input (R.sourceInputs s p iv h) j:=core_input _ _ _ _ _ _ j (factory_producer j hp)
      _=(R.initial s p iv h).data (R.factory j):=(SemiprimeD1StackChildGroupFactoryReady.initial_projection _ _ _ _ j).symm
      _=(R.initial s p iv h).data k:=congrArg _ hj
  · exact hr.1.2 k (fun j he=>hm ⟨j,he⟩)
/-- Exact seven displaced physical input allocations remain counted and EMPTY. -/
def shadow :Fin 7→G.Aux
  | 0=>.environment | 1=>.catalogue | 2=>.owners | 3=>.factors
  | 4=>.occurrences | 5=>.placements | 6=>.packets
/-- No real instruction can address a displaced input shadow via the actual core inclusion. -/
theorem shadow_outside (i:Fin 7):∀j,R.factory j≠R.allocation (G.aux (shadow i)):=by
  intro j he
  have h:=congrArg R.recover he
  rw [R.recover_factory] at h
  change some j=some (G.aux (shadow i)) at h
  have hj:=Option.some.inj h
  subst j
  fin_cases i <;> cases he
/-- All seven unused input allocations stay physically empty at the true stopped ready boundary. -/
theorem shadow_empty (s:SemiprimeD1StackChildGroupFactoryReady.S.Stack→List Bool)
    (p:SemiprimeD1StackChildGroupFactoryReady.P.Stack→List Bool)
    (iv:SemiprimeD1StackChildGroupFactoryReady.I.Stack→List Bool) (h:R.Header)
    (a coordinate:Nat) (ids packets:List (List Bool))
    (fields:List SemiprimeD1StackChildGroupFactoryEndpointParse.Fields)
    (finish:C.State R.Stack SemiprimeD1StackChildGroupFactoryWiring.Label)
    (hr:Rel R.factory (R.initial s p iv h).data
      (E.done (R.sourceInputs s p iv h) a coordinate ids packets fields) finish) (i:Fin 7):
    finish.data (R.allocation (G.aux (shadow i)))=[]:=by
  rw [hr.1.2 _ (shadow_outside i)]
  fin_cases i <;> rfl
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryReadyRetention

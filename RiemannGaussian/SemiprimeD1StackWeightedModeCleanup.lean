/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackWeightedModeActivation
/-! # Actual recursive-return cleanup of every mutable weighted-tuple word -/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackWeightedModeCleanup
open SemiprimeD1StackWeightedMode SemiprimeD1StackWeightedModePrimitives SemiprimeD1StackWeightedModeView
open SemiprimeD1StackWeightedModeActivation (join)
open SemiprimeD1StackProcedureTrace
local notation "ctl" => (Sum.inl : Control→Label)
/-- Bytes actually consumed before a recursive return; foreign records/history are untouched. -/
def cleanupMass (v:Words) :Nat:=v.weights.length+v.budget.length+v.path.length+v.weight.length+
  v.exponent.length+v.subTodo.length+v.tuple.length+v.pathReader.length+v.valid.length
/-- Exactly the nine mutable physical words cleared by the recursive-return controller. -/
def cleaned (v:Words) :Words:=
  {v with weights:=[],budget:=[],path:=[],weight:=[],exponent:=[],subTodo:=[],tuple:=[],pathReader:=[],valid:=[]}
/-- One actual cleanup loop consumes its entire physical word and pays the empty pop. -/
theorem drain_one (v:Words) (i:Fin 9) :
    Runs program ((store v (cleared i)).length+1) (ctl (.cleanup i)) (store v) (cleanupNext i)
      (store (write v (cleared i) [])):=by
  simpa only [store_write] using drain_loop (.cleanup i) (cleanupNext i) (cleared i) rfl
    (store v) (store v (cleared i)) rfl
/-- The whole literal cleanup chain reaches actual ret only after all nine words are empty. -/
theorem cleanup_run (v:Words) :
    Runs program (cleanupMass v+9) (ctl (.cleanup 0)) (store v) (ctl .returning) (store (cleaned v)):=by
  let v1:Words:={v with weights:=[]}
  let v2:Words:={v1 with budget:=[]}
  let v3:Words:={v2 with path:=[]}
  let v4:Words:={v3 with weight:=[]}
  let v5:Words:={v4 with exponent:=[]}
  let v6:Words:={v5 with subTodo:=[]}
  let v7:Words:={v6 with tuple:=[]}
  let v8:Words:={v7 with pathReader:=[]}
  have h0:=drain_one v 0
  change Runs program (v.weights.length+1) _ _ _ (store v1) at h0
  have h1:=drain_one v1 1
  change Runs program (v.budget.length+1) _ _ _ (store v2) at h1
  have h2:=drain_one v2 2
  change Runs program (v.path.length+1) _ _ _ (store v3) at h2
  have h3:=drain_one v3 3
  change Runs program (v.weight.length+1) _ _ _ (store v4) at h3
  have h4:=drain_one v4 4
  change Runs program (v.exponent.length+1) _ _ _ (store v5) at h4
  have h5:=drain_one v5 5
  change Runs program (v.subTodo.length+1) _ _ _ (store v6) at h5
  have h6:=drain_one v6 6
  change Runs program (v.tuple.length+1) _ _ _ (store v7) at h6
  have h7:=drain_one v7 7
  change Runs program (v.pathReader.length+1) _ _ _ (store v8) at h7
  have h8:=drain_one v8 8
  change Runs program (v.valid.length+1) _ _ _ (store (cleaned v)) at h8
  have hh:=join h0 (join h1 (join h2 (join h3 (join h4 (join h5 (join h6 (join h7 h8)))))))
  have he:(v.weights.length+1)+((v.budget.length+1)+((v.path.length+1)+((v.weight.length+1)+
    ((v.exponent.length+1)+((v.subTodo.length+1)+((v.tuple.length+1)+((v.pathReader.length+1)+(v.valid.length+1))))))))=
    cleanupMass v+9:=by unfold cleanupMass;omega
  rw [he] at hh
  exact hh
end RiemannGaussian.SemiprimeD1StackWeightedModeCleanup

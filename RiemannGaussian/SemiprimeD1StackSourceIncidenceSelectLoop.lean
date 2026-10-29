/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectVariable
/-! # Complete actual unary-marker variable loop
Every true marker executes the complete real catalogue scan and winner commit.
The supplied physical input words are copied once; no advised selected prefix,
variable index, query value or loop clock participates in machine control.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectLoop
open SemiprimeD1StackSourceIncidenceSelect SemiprimeD1StackSourceIncidenceSelectPrimitives
open SemiprimeD1StackSourceIncidenceSelectView SemiprimeD1StackSourceIncidenceSelectVariable
open SemiprimeD1StackProcedureTrace
open SemiprimeD1TensorTapeCodec (vectorBits)
local notation "ctl" => Label.local
/-- Own sum of the actual full variable-step caps and the final physical empty-marker pop. -/
def loopClock (rows:List (List Bool×List Bool)) (square cube fourth:List Bool)
    (first:List Bool×List Bool) (entries:List (List Bool×List Bool)) :Nat→List (List Bool)→Nat
  | 0,_=>1
  | n+1,ids=>variableBound ids rows square cube fourth first entries+
      loopClock rows square cube fourth first entries n ((winnerPair ids rows square cube fourth first entries).1::ids)
/-- Every physically acquired marker causes one actual choice; final literal IDs equal the exact closed-score specification. -/
theorem loop_run (rows:List (List Bool×List Bool)) (square cube fourth owners factors:List Bool)
    (first:List Bool×List Bool) (entries:List (List Bool×List Bool)) (n:Nat) (ids:List (List Bool)) :
    ∃t ≤ loopClock rows square cube fourth first entries n ids,
      Runs program t (ctl .loopVariable)
        (clean ids [] (vectorBits ids) (SemiprimeD1StackOwnerLookup.records rows []) square cube fourth
          (SemiprimeD1StackOwnerLookup.records (first::entries) []) owners factors (List.replicate n true) [] [] [] [] [])
        (ctl .done)
        (clean (SemiprimeD1StackSourceIncidenceSelectScore.selected rows square cube fourth first.1 (entries.map Prod.fst)
          (List.replicate n true) ids) []
          (vectorBits (SemiprimeD1StackSourceIncidenceSelectScore.selected rows square cube fourth first.1 (entries.map Prod.fst)
            (List.replicate n true) ids))
          (SemiprimeD1StackOwnerLookup.records rows []) square cube fourth
          (SemiprimeD1StackOwnerLookup.records (first::entries) []) owners factors [] [] [] [] [] []) :=by
  induction n generalizing ids with
  | zero=>
    have h:=pop_run .loopVariable (ctl .done) (ctl .abort) (ctl .saveKey) (aux .todo)
      (clean ids [] (vectorBits ids) (SemiprimeD1StackOwnerLookup.records rows []) square cube fourth
        (SemiprimeD1StackOwnerLookup.records (first::entries) []) owners factors [] [] [] [] [] []) [] rfl rfl
    rw [clean_todo] at h
    exact ⟨1,Nat.le_refl _,h⟩
  | succ n ih=>
    obtain ⟨t0,ht0,h0⟩:=variable_run ids rows square cube fourth owners factors (List.replicate n true) first entries
    obtain ⟨t1,ht1,h1⟩:=ih ((winnerPair ids rows square cube fourth first entries).1::ids)
    have h:=join h0 h1
    refine ⟨t0+t1,Nat.add_le_add ht0 ht1,?_⟩
    simpa only [List.replicate_succ,SemiprimeD1StackSourceIncidenceSelectScore.selected,winnerPair_id] using h
end RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectLoop

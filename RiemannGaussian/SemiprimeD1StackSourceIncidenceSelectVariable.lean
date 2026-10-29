/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectScan
import RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectCommit
/-! # Complete actual variable step with one key snapshot and winner commitment
The actual unary marker is popped first. One physical current-key copy and one
physical catalogue copy precede the complete source scan and real commitment.
No dictionary snapshot, source replay or supplied winner enters this program.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectVariable
open SemiprimeD1StackSourceIncidenceSelect SemiprimeD1StackSourceIncidenceSelectPrimitives
open SemiprimeD1StackSourceIncidenceSelectView SemiprimeD1StackSourceIncidenceSelectScan
open SemiprimeD1StackSourceIncidenceSelectCommit SemiprimeD1StackProcedureTrace
open SemiprimeD1TensorTapeCodec (vectorBits)
namespace E
export SemiprimeD1StackSourceEnvironmentEncoding (variableKey)
end E
local notation "ctl" => Label.local
/-- Actual final cached pair of the complete first-plus-tail scan; no such pair is an input. -/
def winnerPair (ids:List (List Bool)) (rows:List (List Bool×List Bool))
    (square cube fourth:List Bool) (first:List Bool×List Bool) (entries:List (List Bool×List Bool)) :List Bool×List Bool :=
  scanBest ids rows square cube fourth (scored ids rows square cube fourth first) entries
/-- Own complete variable-step cap from the actual component calls and copied byte widths. -/
def variableBound (ids:List (List Bool)) (rows:List (List Bool×List Bool))
    (square cube fourth:List Bool) (first:List Bool×List Bool) (entries:List (List Bool×List Bool)) :Nat :=
  1+(5*(E.variableKey ids.length).length+4)+
    (5*(SemiprimeD1StackOwnerLookup.records (first::entries) []).length+4)+
    catalogueClock ids (vectorBits ids) rows square cube fourth first entries+
    commitBound ids (winnerPair ids rows square cube fourth first entries).1
      (winnerPair ids rows square cube fourth first entries).2
/-- One actual acquired marker causes exactly one full catalogue scan and one actual committed winner. -/
theorem variable_run (ids:List (List Bool)) (rows:List (List Bool×List Bool))
    (square cube fourth owners factors tokens:List Bool) (first:List Bool×List Bool)
    (entries:List (List Bool×List Bool)) :
    ∃t ≤ variableBound ids rows square cube fourth first entries,
      Runs program t (ctl .loopVariable)
        (clean ids [] (vectorBits ids) (SemiprimeD1StackOwnerLookup.records rows []) square cube fourth
          (SemiprimeD1StackOwnerLookup.records (first::entries) []) owners factors (true::tokens) [] [] [] [] [])
        (ctl .loopVariable)
        (clean ((winnerPair ids rows square cube fourth first entries).1::ids) []
          (vectorBits ((winnerPair ids rows square cube fourth first entries).1::ids))
          (SemiprimeD1StackOwnerLookup.records rows []) square cube fourth
          (SemiprimeD1StackOwnerLookup.records (first::entries) []) owners factors tokens [] [] [] [] []) :=by
  let stream:=SemiprimeD1StackOwnerLookup.records rows []
  let catalogue:=SemiprimeD1StackOwnerLookup.records (first::entries) []
  let key:=E.variableKey ids.length
  have h0:=pop_run .loopVariable (ctl .done) (ctl .abort) (ctl .saveKey) (aux .todo)
    (clean ids [] (vectorBits ids) stream square cube fourth catalogue owners factors (true::tokens) [] [] [] [] [])
    (true::tokens) rfl rfl
  change Runs program 1 _ _ _ (Function.update
    (clean ids [] (vectorBits ids) stream square cube fourth catalogue owners factors (true::tokens) [] [] [] [] [])
    (aux .todo) tokens) at h0
  rw [clean_todo] at h0
  have h1:=copy_call .saveKey .saveKey .copyCatalogue rfl
    (clean ids [] (vectorBits ids) stream square cube fourth catalogue owners factors tokens [] [] [] [] []) key [] rfl rfl rfl
  change Runs program _ _ _ _ (Function.update
    (clean ids [] (vectorBits ids) stream square cube fourth catalogue owners factors tokens [] [] [] [] [])
    (aux .savedKey) (key++[])) at h1
  rw [List.append_nil,clean_savedKey] at h1
  have h2:=copy_call .catalogue .copyCatalogue (.header true) rfl
    (clean ids [] (vectorBits ids) stream square cube fourth catalogue owners factors tokens [] key [] [] []) catalogue [] rfl rfl rfl
  change Runs program _ _ _ _ (Function.update
    (clean ids [] (vectorBits ids) stream square cube fourth catalogue owners factors tokens [] key [] [] [])
    (aux .reader) (catalogue++[])) at h2
  rw [List.append_nil,clean_reader] at h2
  obtain ⟨t3,ht3,h3⟩:=catalogue_run ids (vectorBits ids) rows square cube fourth catalogue owners factors tokens first entries
  obtain ⟨t4,ht4,h4⟩:=commit_run ids (winnerPair ids rows square cube fourth first entries).1
    (winnerPair ids rows square cube fourth first entries).2 stream square cube fourth catalogue owners factors tokens
  have h:=join (join (join (join h0 h1) h2) h3) h4
  refine ⟨_,?_,h⟩
  exact Nat.add_le_add (Nat.add_le_add_left ht3 _) ht4
/-- The physically retained winning ID is the exact native old first-on-tie winner for the same closed source score. -/
theorem winnerPair_id (ids:List (List Bool)) (rows:List (List Bool×List Bool))
    (square cube fourth:List Bool) (first:List Bool×List Bool) (entries:List (List Bool×List Bool)) :
    (winnerPair ids rows square cube fourth first entries).1=
      SemiprimeD1StackSourceIncidenceSelectScore.winner rows square cube fourth ids first.1 (entries.map Prod.fst) :=
  scanBest_seed ids rows square cube fourth first.1 entries
end RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectVariable

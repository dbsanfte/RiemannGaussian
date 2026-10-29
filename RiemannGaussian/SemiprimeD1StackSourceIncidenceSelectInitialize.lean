/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectCalls
import RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectView
/-! # Actual once-only initialization and paid variable marker acquisition
No dictionary, selected prefix, numeric variable count or advised iteration
marker word enters the source. Both actual unary input words are copied with
preservation; their physically acquired marker concatenation drives the loop.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectInitialize
open SemiprimeD1StackSourceIncidenceSelect SemiprimeD1StackSourceIncidenceSelectPrimitives
open SemiprimeD1StackSourceIncidenceSelectView SemiprimeD1StackSourceIncidenceSelectCalls
open SemiprimeD1StackProcedureTrace
local notation "ctl" => Label.local
/-- Actual one-time empty-prefix and dictionary initialization, retaining the exact seven input words. -/
theorem initialize_run (stream catalogue square cube fourth owners factors:List Bool) :
    Runs program 4 (ctl .start) (initial stream catalogue square cube fourth owners factors).data
      (ctl .copyOwners) (clean [] [] [false] stream square cube fourth catalogue owners factors [] [] [] [] [] []) :=by
  let before:=(initial stream catalogue square cube fourth owners factors).data
  have h0:=push_run .start (ctl .initialize) selected false before rfl
  let mid:=Function.update before selected [false]
  change Runs program 1 _ _ _ mid at h0
  have hi:∀k,mid (environmentStack k)=
      (SemiprimeD1StackSourceEnvironmentExecution.initializeReady [] [] [false]).data k:=by
    intro k
    rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  have h1:=initialize_call mid [] [] [false] hi
  have he:withEnvironment mid (SemiprimeD1StackSourceEnvironmentExecution.initializeDone [] [] [false]).data=
      clean [] [] [false] stream square cube fourth catalogue owners factors [] [] [] [] [] []:=by
    funext k
    rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k
        · rcases k with k|k <;> cases k <;> rfl
        · cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
  rw [he] at h1
  exact join h0 h1
/-- All marker bytes are acquired by the actual two preserving copies; no native total count controls the program. -/
theorem prepare_run (stream catalogue square cube fourth:List Bool) (n F:Nat) :
    Runs program (5*(n+F)+12) (ctl .start)
      (initial stream catalogue square cube fourth (List.replicate n true) (List.replicate F true)).data
      (ctl .loopVariable)
      (clean [] [] [false] stream square cube fourth catalogue (List.replicate n true) (List.replicate F true)
        (List.replicate (n+F) true) [] [] [] [] []) :=by
  let owners:=List.replicate n true
  let factors:=List.replicate F true
  have h0:=initialize_run stream catalogue square cube fourth owners factors
  have h1:=copy_call .owners .copyOwners .copyFactors rfl
    (clean [] [] [false] stream square cube fourth catalogue owners factors [] [] [] [] [] []) owners [] rfl rfl rfl
  change Runs program _ _ _ _ (Function.update
    (clean [] [] [false] stream square cube fourth catalogue owners factors [] [] [] [] [] [])
    (aux .todo) (owners++[])) at h1
  rw [List.append_nil,clean_todo] at h1
  have h2:=copy_call .factors .copyFactors .loopVariable rfl
    (clean [] [] [false] stream square cube fourth catalogue owners factors owners [] [] [] [] []) factors owners rfl rfl rfl
  change Runs program _ _ _ _ (Function.update
    (clean [] [] [false] stream square cube fourth catalogue owners factors owners [] [] [] [] [])
    (aux .todo) (factors++owners)) at h2
  rw [clean_todo] at h2
  have h:=join (join h0 h1) h2
  have he:factors++owners=List.replicate (n+F) true:=by
    rw [←List.replicate_add,Nat.add_comm]
  have ht:4+(5*owners.length+4)+(5*factors.length+4)=5*(n+F)+12:=by
    dsimp only [owners,factors]
    simp only [List.length_replicate]
    omega
  simpa only [he,ht,owners,factors] using h
end RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectInitialize

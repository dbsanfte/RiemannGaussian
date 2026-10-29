/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectCalls
import RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectView
/-! # Actual committed winner extension and newest-first selected-vector framing
The physically retained winning ID is copied to the shared environment, really
extended at the saved current key and framed onto the old selected vector. Every
candidate/snapshot/incumbent/score word is physically drained before iteration.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectCommit
open SemiprimeD1StackSourceIncidenceSelect SemiprimeD1StackSourceIncidenceSelectPrimitives
open SemiprimeD1StackSourceIncidenceSelectView SemiprimeD1StackSourceIncidenceSelectCalls
open SemiprimeD1StackProcedureTrace
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeSourceHistogramKeyBits (frame)
namespace E
export SemiprimeD1StackSourceEnvironmentEncoding (variableKey)
end E
local notation "ctl" => Label.local
/-- Own complete commit cap, including the real environment return, real Frame and all byte drains. -/
def commitBound (ids:List (List Bool)) (id savedScore:List Bool) :Nat :=
  200*(id.length+(E.variableKey ids.length).length+savedScore.length+1)
/-- The same source physically commits the exact winner and advances only after every private word is clear. -/
theorem commit_run (ids:List (List Bool))
    (id savedScore stream square cube fourth catalogue owners factors todo:List Bool) :
    ∃t ≤ commitBound ids id savedScore,
      Runs program t (ctl .copyWinner)
        (clean ids [] (vectorBits ids) stream square cube fourth catalogue owners factors todo []
          (E.variableKey ids.length) id savedScore [])
        (ctl .loopVariable)
        (clean (id::ids) [] (vectorBits (id::ids)) stream square cube fourth catalogue owners factors todo [] [] [] [] []) :=by
  let pfx:=vectorBits ids
  let key:=E.variableKey ids.length
  have h0:=copy_call .winner .copyWinner .commit rfl
    (clean ids [] pfx stream square cube fourth catalogue owners factors todo [] key id savedScore []) id [] rfl rfl rfl
  change Runs program _ _ _ _ (Function.update
    (clean ids [] pfx stream square cube fourth catalogue owners factors todo [] key id savedScore []) candidate (id++[])) at h0
  rw [List.append_nil,clean_chosen] at h0
  let before:=clean ids id pfx stream square cube fourth catalogue owners factors todo [] key id savedScore []
  obtain ⟨t1,ht1,h1⟩:=extend_call .commit .frameWinner rfl before ids id [] pfx (fun _=>rfl)
  have he:withEnvironment before (SemiprimeD1StackSourceEnvironmentExecution.extendDone ids id [] pfx).data=
      clean (id::ids) id pfx stream square cube fourth catalogue owners factors todo [] key id savedScore []:=by
    funext k
    rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k
        · rcases k with k|k <;> cases k <;> rfl
        · cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
  rw [he] at h1
  have h2:=frame_call .frameWinner .prefixTag rfl
    (clean (id::ids) id pfx stream square cube fourth catalogue owners factors todo [] key id savedScore []) id pfx rfl rfl rfl
  change Runs program _ _ _ _ (Function.update
    (clean (id::ids) id pfx stream square cube fourth catalogue owners factors todo [] key id savedScore []) selected (frame id pfx)) at h2
  rw [clean_pfx] at h2
  have h3:=push_run .prefixTag (ctl .clearCommittedChosen) selected true
    (clean (id::ids) id (frame id pfx) stream square cube fourth catalogue owners factors todo [] key id savedScore []) rfl
  change Runs program 1 _ _ _ (Function.update
    (clean (id::ids) id (frame id pfx) stream square cube fourth catalogue owners factors todo [] key id savedScore []) selected
    (true::frame id pfx)) at h3
  rw [clean_pfx] at h3
  have h4:=drain_loop .clearCommittedChosen (ctl .clearSavedKey) candidate rfl
    (clean (id::ids) id (true::frame id pfx) stream square cube fourth catalogue owners factors todo [] key id savedScore []) id rfl
  rw [clean_chosen] at h4
  have h5:=drain_loop .clearSavedKey (ctl .clearWinnerID) (aux .savedKey) rfl
    (clean (id::ids) [] (true::frame id pfx) stream square cube fourth catalogue owners factors todo [] key id savedScore []) key rfl
  rw [clean_savedKey] at h5
  have h6:=drain_loop .clearWinnerID (ctl .clearWinnerScore) (aux .bestID) rfl
    (clean (id::ids) [] (true::frame id pfx) stream square cube fourth catalogue owners factors todo [] [] id savedScore []) id rfl
  rw [clean_bestID] at h6
  have h7:=drain_loop .clearWinnerScore (ctl .loopVariable) (aux .bestScore) rfl
    (clean (id::ids) [] (true::frame id pfx) stream square cube fourth catalogue owners factors todo [] [] [] savedScore []) savedScore rfl
  rw [clean_bestScore] at h7
  have h:=join (join (join (join (join (join (join h0 h1) h2) h3) h4) h5) h6) h7
  refine ⟨_,?_,h⟩
  change t1 ≤ 101*(id.length+key.length+1)+1 at ht1
  change _ ≤ 200*(id.length+key.length+savedScore.length+1)
  omega
end RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectCommit

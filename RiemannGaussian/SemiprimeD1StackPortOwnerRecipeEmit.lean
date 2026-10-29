/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPortOwnerRecipeCalls
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
namespace RiemannGaussian.SemiprimeD1StackPortOwnerRecipeEmit
open SemiprimeD1StackPortOwnerRecipe SemiprimeD1StackPortOwnerRecipeSpec SemiprimeD1StackPortOwnerRecipeCalls
open SemiprimeD1StackProcedureTrace (Runs one_base runs_trans)
open SemiprimeSourceHistogramKeyBits (frame)
/-- The actual classifier consumes only its copied tag counter. -/
def ready (p:Counters) : Stack→List Bool := Function.update (prepared p) (reg .tagReader) []
/-- Actual scalar field word selected from the computed physical cache. -/
def word (p:Counters) (recipe:Recipe) (part:Fin 6) : List Bool := ready p (fields recipe part)
/-- Literal six-field output suffix at every actual framing stage. -/
def suffix (p:Counters) (recipe:Recipe) (count:ℕ) : List Bool :=
  if count=0 then [true]
  else if count=1 then frame (word p recipe 5) [true]
  else if count=2 then frame (word p recipe 4) (frame (word p recipe 5) [true])
  else if count=3 then frame (word p recipe 3) (frame (word p recipe 4) (frame (word p recipe 5) [true]))
  else if count=4 then frame (word p recipe 2) (frame (word p recipe 3) (frame (word p recipe 4) (frame (word p recipe 5) [true])))
  else if count=5 then frame (word p recipe 1) (frame (word p recipe 2) (frame (word p recipe 3) (frame (word p recipe 4) (frame (word p recipe 5) [true]))))
  else frame (word p recipe 0) (frame (word p recipe 1) (frame (word p recipe 2) (frame (word p recipe 3) (frame (word p recipe 4) (frame (word p recipe 5) [true])))))
/-- Actual per-field output update, retaining all acquired input and intermediate words. -/
def store (p:Counters) (recipe:Recipe) (count:ℕ) : Stack→List Bool :=
  Function.update (ready p) (aux .output) (suffix p recipe count)
/-- Literal continuation after a field call. -/
def next (recipe:Recipe) (part:Fin 6) : Label :=
  if h:part.val<5 then .local (.emit recipe ⟨part.val+1,by omega⟩) else .local .halt
/-- All six actual sources avoid both physical key output and its scratch. -/
theorem fields_not_output : ∀recipe:Recipe,∀part:Fin 6,fields recipe part≠aux .output := by decide
/-- Literal framing accumulator equation at each of the six static stages. -/
theorem suffix_step (p:Counters) (recipe:Recipe) (part:Fin 6) :
    frame (word p recipe ⟨5-part.val,by omega⟩) (suffix p recipe part.val)=suffix p recipe (part.val+1) := by
  fin_cases part <;> rfl
/-- One complete real Frame call, retaining actual scalar inputs and every other cache. -/
theorem field_run (p:Counters) (recipe:Recipe) (part:Fin 6) :
    Runs program (6*(word p recipe ⟨5-part.val,by omega⟩).length+5)
      (.local (.emit recipe part)) (store p recipe part.val)
      (next recipe part) (store p recipe (part.val+1)) := by
  have hs:store p recipe part.val (aux .frameScratch)=[]:=by
    simp [store,ready,prepared,atStage,aux,reg,Function.update]
  have h:=frame_call recipe part (store p recipe part.val) (.local (.emit recipe part)) (next recipe part) hs rfl
  have hw:store p recipe part.val (fields recipe ⟨5-part.val,by omega⟩)=word p recipe ⟨5-part.val,by omega⟩:=by
    exact Function.update_of_ne (fields_not_output recipe _) _ _
  have ho:store p recipe part.val (aux .output)=suffix p recipe part.val:=Function.update_self _ _ _
  rw [hw,ho,suffix_step] at h
  change Runs program _ _ _ _ (Function.update (Function.update (ready p) (aux .output)
    (suffix p recipe part.val)) (aux .output) (suffix p recipe (part.val+1))) at h
  rw [Function.update_idem] at h
  exact h
/-- Literal total actual field payload retained in the computed key. -/
def mass (p:Counters) (recipe:Recipe) : ℕ :=
  (word p recipe 0).length+(word p recipe 1).length+(word p recipe 2).length+
  (word p recipe 3).length+(word p recipe 4).length+(word p recipe 5).length
/-- All six actual preserving Frame calls, in their literal reverse field order. -/
theorem fields_run (p:Counters) (recipe:Recipe) :
    Runs program (6*mass p recipe+30) (.local (.emit recipe 0)) (store p recipe 0)
      (.local .halt) (store p recipe 6) := by
  have h0:=field_run p recipe 0
  have h1:=field_run p recipe 1
  have h2:=field_run p recipe 2
  have h3:=field_run p recipe 3
  have h4:=field_run p recipe 4
  have h5:=field_run p recipe 5
  have h:=runs_trans program _ _ _ _ _ _ _ _ h0
    (runs_trans program _ _ _ _ _ _ _ _ h1 (runs_trans program _ _ _ _ _ _ _ _ h2
      (runs_trans program _ _ _ _ _ _ _ _ h3 (runs_trans program _ _ _ _ _ _ _ _ h4 h5))))
  have ht:(6*(word p recipe 5).length+5)+((6*(word p recipe 4).length+5)+
      ((6*(word p recipe 3).length+5)+((6*(word p recipe 2).length+5)+
        ((6*(word p recipe 1).length+5)+(6*(word p recipe 0).length+5)))))=6*mass p recipe+30:=by
    unfold mass
    omega
  change Runs program ((6*(word p recipe 5).length+5)+((6*(word p recipe 4).length+5)+
      ((6*(word p recipe 3).length+5)+((6*(word p recipe 2).length+5)+
        ((6*(word p recipe 1).length+5)+(6*(word p recipe 0).length+5))))))
    (.local (.emit recipe 0)) (store p recipe 0) (.local .halt) (store p recipe 6) at h
  rw [ht] at h
  exact h
/-- The actual compact sentinel is pushed into the formerly empty output. -/
theorem sentinel_run (p:Counters) (recipe:Recipe) :
    Runs program 1 (.local (.begin recipe)) (ready p) (.local (.emit recipe 0)) (store p recipe 0) := by
  apply one_base program _ _ (.push (aux .output) true (.local (.emit recipe 0))) _ _ rfl rfl
  have ho:ready p (aux .output)=[]:=by rfl
  change Function.update (ready p) (aux .output) (true::ready p (aux .output))=_
  rw [ho]
  rfl
/-- Actual sentinel and all six field calls, before the final physical halt. -/
theorem emit_run (p:Counters) (recipe:Recipe) :
    Runs program (6*mass p recipe+31) (.local (.begin recipe)) (ready p)
      (.local .halt) (store p recipe 6) := by
  have h:=runs_trans program _ _ _ _ _ _ _ _ (sentinel_run p recipe) (fields_run p recipe)
  simpa only [show 1+(6*mass p recipe+30)=6*mass p recipe+31 by omega] using h
end RiemannGaussian.SemiprimeD1StackPortOwnerRecipeEmit

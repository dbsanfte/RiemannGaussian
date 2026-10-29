/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceSelectedKeysView
/-! # One final chronological vector reversal and exact arbitrary-query restoration -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceSelectedKeysFinish
open SemiprimeD1StackSourceSelectedKeys SemiprimeD1StackSourceSelectedKeysEncoding
open SemiprimeD1StackSourceSelectedKeysPrimitives SemiprimeD1StackSourceSelectedKeysView
open SemiprimeD1StackProcedureTrace
/-- Full physical stopped bank with an actually produced arbitrary output word. -/
def resultWith (i:Inputs) (out:List Bool) :Stack→List Bool :=Function.update (data (environment i) (tape i)) (aux .output) out
/-- Actual EOF check, false output seed, one complete reversal, paid query restoration and saved-query drain. -/
def finishTime (i:Inputs) (hist:List Bool) :Nat :=2*hist.length+6*i.query.length+10
/-- Actual final reversal retains original forward key order, restores all25cache fields and clears every private scratch. -/
theorem finish_run (i:Inputs) (hist:List Bool) :
    Runs program (finishTime i hist) .eof (view i [] [] [] [] [] [] [] [] [] [] hist []) .done
      (resultWith i (hist.reverse++[false])) :=by
  have h0:=peek_run .eof .seed .abort .abort (aux .reader) (view i [] [] [] [] [] [] [] [] [] [] hist []) [] rfl rfl
  have h1:=push_run .seed .reverseFinish (aux .output) false (view i [] [] [] [] [] [] [] [] [] [] hist []) rfl
  change Runs program 1 _ _ _ (Function.update (view i [] [] [] [] [] [] [] [] [] [] hist []) (aux .output) [false]) at h1
  rw [update_out] at h1
  have h2:=reverse_call .finish .reverseFinish .restoreQuery rfl (view i [] [] [] [] [] [] [] [] [] [] hist [false]) hist [false] rfl rfl
  change Runs program _ _ _ _ (Function.update (Function.update
    (view i [] [] [] [] [] [] [] [] [] [] hist [false]) (aux .history) []) (aux .output) (hist.reverse++[false])) at h2
  rw [update_hist,update_out] at h2
  have h3:=copy_call .restoreQuery .restoreQuery .clearSavedQuery rfl
    (view i [] [] [] [] [] [] [] [] [] [] [] (hist.reverse++[false])) rfl rfl
  change Runs program (5*i.query.length+4) _ _ _ (Function.update
    (view i [] [] [] [] [] [] [] [] [] [] [] (hist.reverse++[false])) query i.query) at h3
  rw [update_q] at h3
  have h4:=drain_loop .clearSavedQuery .done (aux .savedQuery) rfl
    (view i i.query [] [] [] [] [] [] [] [] [] [] (hist.reverse++[false])) i.query rfl
  have he:Function.update (view i i.query [] [] [] [] [] [] [] [] [] [] (hist.reverse++[false])) (aux .savedQuery) []=
      resultWith i (hist.reverse++[false]):=by
    funext k
    rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k <;> cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
  rw [he] at h4
  have h:=join (join (join (join h0 h1) h2) h3) h4
  have ht:1+1+(2*hist.length+3)+(5*i.query.length+4)+(i.query.length+1)=finishTime i hist:=by unfold finishTime;omega
  simpa only [ht,SemiprimeD1StackBytecode.choose,List.head?_nil] using h
end RiemannGaussian.SemiprimeD1StackSourceSelectedKeysFinish

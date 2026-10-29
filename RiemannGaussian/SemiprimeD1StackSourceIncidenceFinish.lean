/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceIncidenceLoopView
/-! # Actual source EOF, original-query restoration and complete final private cleanup -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceIncidenceFinish
open SemiprimeD1StackSourceIncidence SemiprimeD1StackSourceIncidenceEncoding
open SemiprimeD1StackSourceIncidencePrimitives SemiprimeD1StackSourceIncidenceLoopView
open SemiprimeD1StackProcedureTrace
/-- Full47-word physical result with an actually computed arbitrary accumulator. -/
def resultWith (i:Inputs) (acc:List Bool) :Stack→List Bool :=
  Function.update (data (environment i) (tape i) i.square i.cube i.fourth) (aux .total) acc
/-- Actual EOF/copy/drain suffix cost; the final whole halt is paid by the caller theorem. -/
def finishTime (i:Inputs) :Nat :=6*i.query.length+6
/-- The SAME literal program physically restores the exact arbitrary incoming query and clears its saved copy. -/
theorem finish_run (i:Inputs) (acc:List Bool) :
    Runs program (finishTime i) .outerEOF (bank i [] [] [] [] [] [] [] [] [] [] acc) .done (resultWith i acc) :=by
  have h0:=peek_run .outerEOF .restoreQuery .abort .abort (aux .outerReader)
    (bank i [] [] [] [] [] [] [] [] [] [] acc) [] rfl rfl
  have h1:=copy_call .restoreQuery .restoreQuery .clearSavedQuery rfl
    (bank i [] [] [] [] [] [] [] [] [] [] acc) rfl rfl
  change Runs program (5*i.query.length+4) _ _ _
    (Function.update (bank i [] [] [] [] [] [] [] [] [] [] acc) query i.query) at h1
  have h2:=drain_loop .clearSavedQuery .done (aux .savedQuery) rfl
    (Function.update (bank i [] [] [] [] [] [] [] [] [] [] acc) query i.query) i.query rfl
  have he:Function.update (Function.update (bank i [] [] [] [] [] [] [] [] [] [] acc) query i.query)
      (aux .savedQuery) []=resultWith i acc:=by
    funext k
    rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k <;> cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
  rw [he] at h2
  have h:=join (join h0 h1) h2
  have ht:1+(5*i.query.length+4)+(i.query.length+1)=finishTime i:=by unfold finishTime;omega
  simpa only [ht,SemiprimeD1StackBytecode.choose,List.head?_nil] using h
end RiemannGaussian.SemiprimeD1StackSourceIncidenceFinish

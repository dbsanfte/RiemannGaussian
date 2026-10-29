/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackTransformSelectorsBounds
import RiemannGaussian.SemiprimeD1VertexCatalogueEncoding
import RiemannGaussian.SemiprimeD1StackPublicScaleFinite
/-! # Actual selector singletons for every original constructor and direction -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
namespace RiemannGaussian.SemiprimeD1StackTransformSelectorsOriginal
open SemiprimeD1StackTransformSelectors SemiprimeD1StackTransformSelectorsExecution
open SemiprimeD1VertexCatalogueEncoding (transformCode)
open SemiprimeD1StackPublicScaleFinite (selector)
/-- Every authoritative original transform code lies in the actual three-code control. -/
theorem transform_code_lt (tr : SemiprimeMacroGraph.Transform) : transformCode tr<3 :=by
  rcases tr with side|terminal
  · fin_cases side <;> decide
  · cases terminal;decide
/-- The physically decoded bit is exactly the frozen original inverse selector. -/
theorem inverse_original (tr : SemiprimeMacroGraph.Transform) : (transformCode tr==2)=selector tr :=by
  rcases tr with side|terminal
  · fin_cases side <;> decide
  · cases terminal;rfl
/-- Original first-transform tag1 physically constructs false stage and the
correct inverse singleton for ALL three original transform directions. -/
theorem first_source_run (tr : SemiprimeMacroGraph.Transform) (oldStage oldInverse : List Bool) :
    C.run program (timeBound [true] (List.replicate (transformCode tr) true) oldStage oldInverse)
      (initial [true] (List.replicate (transformCode tr) true) oldStage oldInverse)=
      some (done [true] (List.replicate (transformCode tr) true) false (selector tr)) :=by
  have h:=source_run 1 ⟨transformCode tr,transform_code_lt tr⟩ false rfl oldStage oldInverse
  rw [inverse_original] at h
  exact h
/-- Original scale tag2 physically constructs the inverse selector; its unused
stage is false and no selector value is initialized by the caller. -/
theorem scale_source_run (tr : SemiprimeMacroGraph.Transform) (oldStage oldInverse : List Bool) :
    C.run program (timeBound [true,true] (List.replicate (transformCode tr) true) oldStage oldInverse)
      (initial [true,true] (List.replicate (transformCode tr) true) oldStage oldInverse)=
      some (done [true,true] (List.replicate (transformCode tr) true) false (selector tr)) :=by
  have h:=source_run 2 ⟨transformCode tr,transform_code_lt tr⟩ false rfl oldStage oldInverse
  rw [inverse_original] at h
  exact h
/-- Original second-transform tag3 physically constructs true stage and the
correct inverse singleton, preserving both original source fields. -/
theorem second_source_run (tr : SemiprimeMacroGraph.Transform) (oldStage oldInverse : List Bool) :
    C.run program (timeBound [true,true,true] (List.replicate (transformCode tr) true) oldStage oldInverse)
      (initial [true,true,true] (List.replicate (transformCode tr) true) oldStage oldInverse)=
      some (done [true,true,true] (List.replicate (transformCode tr) true) true (selector tr)) :=by
  have h:=source_run 3 ⟨transformCode tr,transform_code_lt tr⟩ true rfl oldStage oldInverse
  rw [inverse_original] at h
  exact h
end RiemannGaussian.SemiprimeD1StackTransformSelectorsOriginal

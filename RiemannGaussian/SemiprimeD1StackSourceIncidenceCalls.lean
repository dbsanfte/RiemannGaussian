/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceIncidenceView
/-! # Actual key comparison, marked lookup and finite status emission traces -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceIncidenceCalls
open SemiprimeD1StackSourceIncidence SemiprimeD1StackSourceIncidencePrimitives
open SemiprimeD1StackSourceIncidenceView SemiprimeD1StackProcedureTrace
open SemiprimeD1StackSourceIncidenceSpec (Status possible drop)
/-- Proof-side name for one physically parsed key; the program obtains it only through real copies. -/
def endpoint (words:Aux→List Bool) (side:Bool) (kind:Edge) :List Bool :=
  Sum.elim (fun _=>[]) words (key side kind)
/-- Two paid preserving copies and the SAME real numeric comparator preserve every retained input byte. -/
theorem keys_run (ids:List (List Bool)) (chosen pfx:List Bool) (words:Aux→List Bool) (kind:Edge)
    (hc:words .copyScratch=[]) (hs:words .eqScratch=[]) :
    Runs program ((5*(endpoint words false kind).length+4)+(5*(endpoint words true kind).length+4)+
      (SemiprimeD1StackWordEqualExecution.executionTime (endpoint words false kind) (endpoint words true kind)+1))
      (.edgeStart kind) (view ids chosen pfx words [] [] [] [] [] []) (.keysEqual kind)
      (view ids chosen pfx words [] [] []
        [decide (SemiprimeBitArithmetic.bitValue (endpoint words false kind)=
          SemiprimeBitArithmetic.bitValue (endpoint words true kind))] [] []) :=by
  have h0:=copy_call (.keyLeft kind) (.edgeStart kind) (.edgeRight kind) rfl
    (view ids chosen pfx words [] [] [] [] [] []) rfl hc
  change Runs program (5*(view ids chosen pfx words [] [] [] [] [] [] (key false kind)).length+4)
    (.edgeStart kind) _ (.edgeRight kind)
    (Function.update (view ids chosen pfx words [] [] [] [] [] []) (aux .eqLeft)
      (view ids chosen pfx words [] [] [] [] [] [] (key false kind))) at h0
  rw [key_projection,update_left] at h0
  change Runs program _ _ _ _ (view ids chosen pfx words [] (endpoint words false kind) [] [] [] []) at h0
  have h1:=copy_call (.keyRight kind) (.edgeRight kind) (.compareKeys kind) rfl
    (view ids chosen pfx words [] (endpoint words false kind) [] [] [] []) rfl hc
  change Runs program (5*(view ids chosen pfx words [] (endpoint words false kind) [] [] [] [] (key true kind)).length+4)
    (.edgeRight kind) _ (.compareKeys kind)
    (Function.update (view ids chosen pfx words [] (endpoint words false kind) [] [] [] []) (aux .eqRight)
      (view ids chosen pfx words [] (endpoint words false kind) [] [] [] [] (key true kind))) at h1
  rw [key_projection,update_right] at h1
  change Runs program _ _ _ _
    (view ids chosen pfx words [] (endpoint words false kind) (endpoint words true kind) [] [] []) at h1
  have h2:=equal_call (.compareKeys kind) (.keysEqual kind) rfl
    (view ids chosen pfx words [] (endpoint words false kind) (endpoint words true kind) [] [] []) hs rfl
  change Runs program _ _ _ _
    (Function.update (Function.update (Function.update
      (view ids chosen pfx words [] (endpoint words false kind) (endpoint words true kind) [] [] [])
        (aux .eqLeft) []) (aux .eqRight) []) (aux .eqOutput)
      [decide (SemiprimeBitArithmetic.bitValue (endpoint words false kind)=
        SemiprimeBitArithmetic.bitValue (endpoint words true kind))]) at h2
  rw [update_left,update_right,update_comparison] at h2
  exact join (join h0 h1) h2
/-- A computed finite outcome is physically pushed as two actual Bool bytes before returning. -/
theorem status_run (ids:List (List Bool)) (chosen pfx:List Bool) (words:Aux→List Bool) (status:Status) :
    Runs program 2 (.status status) (view ids chosen pfx words [] [] [] [] [] []) .edgeReturn
      (view ids chosen pfx words [] [] [] [possible status,drop status] [] []) :=by
  have h0:=push_run (.status status) (.statusPossible status) (aux .eqOutput) (drop status)
    (view ids chosen pfx words [] [] [] [] [] []) rfl
  change Runs program 1 _ _ _ (Function.update (view ids chosen pfx words [] [] [] [] [] []) (aux .eqOutput) [drop status]) at h0
  rw [update_comparison] at h0
  have h1:=push_run (.statusPossible status) .edgeReturn (aux .eqOutput) (possible status)
    (view ids chosen pfx words [] [] [] [drop status] [] []) rfl
  change Runs program 1 _ _ _
    (Function.update (view ids chosen pfx words [] [] [] [drop status] [] []) (aux .eqOutput) [possible status,drop status]) at h1
  rw [update_comparison] at h1
  exact join h0 h1
/-- Exact complete environment call in the larger47-role bank; saved ID operands and all caller words survive. -/
theorem lookup_view (ids:List (List Bool)) (chosen pfx:List Bool) (words:Aux→List Bool)
    (kind:Edge) (side:Bool) (q left right:List Bool) :
    ∃t≤201*(q.length+1)*((Env.dictionary ids).length+1)+1,
      Runs program t (.lookup kind side) (view ids chosen pfx words q left right [] [] []) (.readFound kind side)
        (view ids chosen pfx words q left right [] [decide (SemiprimeBitArithmetic.bitValue q < ids.length)]
          (if SemiprimeBitArithmetic.bitValue q < ids.length then
            SemiprimeSourceHistogramPrefix.expected ids (SemiprimeBitArithmetic.bitValue q) else [])) :=by
  obtain ⟨t,ht,hr⟩:=lookup_call kind side (view ids chosen pfx words q left right [] [] []) ids chosen q pfx
    (environment_projection ids chosen pfx words q left right [])
  refine ⟨t,ht,?_⟩
  have he:Sum.elim (SemiprimeD1StackSourceEnvironmentExecution.lookupDone ids chosen q pfx).data
      (fun k=>view ids chosen pfx words q left right [] [] [] (aux k))=
      view ids chosen pfx words q left right [] [decide (SemiprimeBitArithmetic.bitValue q < ids.length)]
        (if SemiprimeBitArithmetic.bitValue q < ids.length then
          SemiprimeSourceHistogramPrefix.expected ids (SemiprimeBitArithmetic.bitValue q) else []):=by
    funext k
    rcases k with k|k
    · rfl
    · cases k <;> rfl
  rw [he] at hr
  exact hr
end RiemannGaussian.SemiprimeD1StackSourceIncidenceCalls

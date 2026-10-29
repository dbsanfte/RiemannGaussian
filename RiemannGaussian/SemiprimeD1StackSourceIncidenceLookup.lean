/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceIncidenceCalls
/-! # Paid query copies, actual presence reads, explicit fixed-ID saves and cleanup -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceIncidenceLookup
open SemiprimeD1StackSourceIncidence SemiprimeD1StackSourceIncidencePrimitives
open SemiprimeD1StackSourceIncidenceView SemiprimeD1StackSourceIncidenceCalls
open SemiprimeD1StackProcedureTrace
/-- Each actual endpoint query is physically copied, looked up and retained until its own cleanup. -/
theorem lookup_stage (ids:List (List Bool)) (chosen pfx:List Bool) (words:Aux→List Bool)
    (kind:Edge) (side:Bool) (left right:List Bool) (hc:words .copyScratch=[]) :
    ∃t≤201*((endpoint words side kind).length+1)*((Env.dictionary ids).length+1)+
        5*(endpoint words side kind).length+5,
      Runs program t (.copyQuery kind side) (view ids chosen pfx words [] left right [] [] []) (.readFound kind side)
        (view ids chosen pfx words (endpoint words side kind) left right []
          [decide (SemiprimeBitArithmetic.bitValue (endpoint words side kind) < ids.length)]
          (if SemiprimeBitArithmetic.bitValue (endpoint words side kind) < ids.length then
            SemiprimeSourceHistogramPrefix.expected ids (SemiprimeBitArithmetic.bitValue (endpoint words side kind)) else [])) :=by
  have h0:=copy_call (.query kind side) (.copyQuery kind side) (.lookup kind side) rfl
    (view ids chosen pfx words [] left right [] [] []) rfl hc
  change Runs program (5*(view ids chosen pfx words [] left right [] [] [] (key side kind)).length+4)
    (.copyQuery kind side) _ (.lookup kind side)
    (Function.update (view ids chosen pfx words [] left right [] [] []) query
      (view ids chosen pfx words [] left right [] [] [] (key side kind))) at h0
  rw [key_projection,update_q] at h0
  change Runs program (5*(endpoint words side kind).length+4) _ _ _
    (view ids chosen pfx words (endpoint words side kind) left right [] [] []) at h0
  obtain ⟨t,ht,h1⟩:=lookup_view ids chosen pfx words kind side (endpoint words side kind) left right
  exact ⟨_,by omega,join h0 h1⟩
/-- The actual found singleton is consumed into a finite branch; an empty ID is never used as a presence test. -/
theorem found_pop (ids:List (List Bool)) (chosen pfx:List Bool) (words:Aux→List Bool)
    (kind:Edge) (side present:Bool) (q left right returned:List Bool) :
    Runs program 1 (.readFound kind side) (view ids chosen pfx words q left right [] [present] returned)
      (if present then .copyID kind side else .clearID kind side false)
      (view ids chosen pfx words q left right [] [] returned) :=by
  have h:=pop_run (.readFound kind side) .abort (.clearID kind side false) (.copyID kind side) found
    (view ids chosen pfx words q left right [] [present] returned) [present] rfl rfl
  change Runs program 1 _ _ _ (Function.update (view ids chosen pfx words q left right [] [present] returned) found []) at h
  rw [update_present] at h
  cases present <;> exact h
/-- The first actual fixed ID is saved directly in equality.left before any second lookup. -/
theorem save_first (ids:List (List Bool)) (chosen pfx:List Bool) (words:Aux→List Bool)
    (kind:Edge) (q right returned:List Bool) (hc:words .copyScratch=[]) :
    Runs program (5*returned.length+4) (.copyID kind false) (view ids chosen pfx words q [] right [] [] returned)
      (.clearID kind false true) (view ids chosen pfx words q returned right [] [] returned) :=by
  have h:=copy_call (.id false) (.copyID kind false) (.clearID kind false true) rfl
    (view ids chosen pfx words q [] right [] [] returned) rfl hc
  change Runs program _ _ _ _
    (Function.update (view ids chosen pfx words q [] right [] [] returned) (aux .eqLeft) returned) at h
  rw [update_left] at h
  exact h
/-- The second actual fixed ID is copied into equality.right, preserving the first saved physical ID. -/
theorem save_second (ids:List (List Bool)) (chosen pfx:List Bool) (words:Aux→List Bool)
    (kind:Edge) (q left returned:List Bool) (hc:words .copyScratch=[]) :
    Runs program (5*returned.length+4) (.copyID kind true) (view ids chosen pfx words q left [] [] [] returned)
      (.clearID kind true true) (view ids chosen pfx words q left returned [] [] returned) :=by
  have h:=copy_call (.id true) (.copyID kind true) (.clearID kind true true) rfl
    (view ids chosen pfx words q left [] [] [] returned) rfl hc
  change Runs program _ _ _ _
    (Function.update (view ids chosen pfx words q left [] [] [] returned) (aux .eqRight) returned) at h
  rw [update_right] at h
  exact h
/-- Both actual lookup output and actual query are fully physically drained between lookups. -/
theorem cleanup (ids:List (List Bool)) (chosen pfx:List Bool) (words:Aux→List Bool)
    (kind:Edge) (side present:Bool) (q left right returned:List Bool) :
    Runs program ((returned.length+1)+(q.length+1)) (.clearID kind side present)
      (view ids chosen pfx words q left right [] [] returned) (.afterLookup kind side present)
      (view ids chosen pfx words [] left right [] [] []) :=by
  have h0:=drain_loop (.clearID kind side present) (.clearQuery kind side present) idOutput rfl
    (view ids chosen pfx words q left right [] [] returned) returned rfl
  rw [update_returned] at h0
  have h1:=drain_loop (.clearQuery kind side present) (.afterLookup kind side present) query rfl
    (view ids chosen pfx words q left right [] [] []) q rfl
  rw [update_q] at h1
  exact join h0 h1
end RiemannGaussian.SemiprimeD1StackSourceIncidenceLookup

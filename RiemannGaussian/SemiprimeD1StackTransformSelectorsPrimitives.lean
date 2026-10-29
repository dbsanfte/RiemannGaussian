/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackTransformSelectors
/-! # Paid original-field copies, physical drains and Boolean selector pushes -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
namespace RiemannGaussian.SemiprimeD1StackTransformSelectorsPrimitives
open SemiprimeD1StackTransformSelectors SemiprimeD1StackProcedureTrace
/-- Consecutive actual fragments of this same fixed source compose. -/
theorem compose {m n : Nat} {pc mid next : Label} {before middle after : Stack→List Bool}
    (h : Runs program m pc before mid middle) (g : Runs program n mid middle next after) :
    Runs program (m+n) pc before next after :=runs_trans program _ _ _ _ _ _ _ _ h g
/-- Exact actual reader update, retaining all six other physical words. -/
theorem update_tagReader (a b c d e f word : List Bool) :
    Function.update (data a b c d e f) .tagReader word=data a b word d e f :=by
  funext k;cases k <;> rfl
/-- Exact actual transform-reader update. -/
theorem update_transformReader (a b c d e f word : List Bool) :
    Function.update (data a b c d e f) .transformReader word=data a b c word e f :=by
  funext k;cases k <;> rfl
/-- Exact actual stage-selector update. -/
theorem update_stage (a b c d e f word : List Bool) :
    Function.update (data a b c d e f) .stage word=data a b c d word f :=by
  funext k;cases k <;> rfl
/-- Exact actual inverse-selector update. -/
theorem update_inverse (a b c d e f word : List Bool) :
    Function.update (data a b c d e f) .inverse word=data a b c d e word :=by
  funext k;cases k <;> rfl
/-- Every stale selector cell and its EOF are actually consumed. -/
theorem clear_stage (tag tr oldStage oldInverse : List Bool) :
    Runs program (oldStage.length+1) .start (data tag tr [] [] oldStage oldInverse)
      .clearInverse (data tag tr [] [] [] oldInverse) :=by
  have h:=SemiprimeD1StackPhysicalLoops.drain program .start .clearInverse .stage rfl
    (data tag tr [] [] oldStage oldInverse) oldStage
  rw [update_stage,update_stage] at h
  exact h
/-- Every stale inverse-selector cell and its EOF are actually consumed. -/
theorem clear_inverse (tag tr oldInverse : List Bool) :
    Runs program (oldInverse.length+1) .clearInverse (data tag tr [] [] [] oldInverse)
      .copyTag (data tag tr [] [] [] []) :=by
  have h:=SemiprimeD1StackPhysicalLoops.drain program .clearInverse .copyTag .inverse rfl
    (data tag tr [] [] [] oldInverse) oldInverse
  rw [update_inverse,update_inverse] at h
  exact h
/-- Actual preserving constructor copy, with three disjoint physical operands. -/
theorem copy_tag (tag tr : List Bool) :
    Runs program (5*tag.length+4) .copyTag (data tag tr [] [] [] []) (.tag 0) (data tag tr tag [] [] []) :=by
  apply included_call program (copyStack false) (Label.copy false) (copy_injective false)
    SemiprimeD1StackCopy.code 0 (fun _=>rfl) .copyTag (.tag 0) rfl (5*tag.length+3)
    (SemiprimeD1StackCopy.state 0 none tag [] []) (SemiprimeD1StackCopy.done tag (tag++[]))
  · rfl
  · rfl
  · exact SemiprimeD1StackCopy.copy_words tag [] none
  · constructor
    · intro k;fin_cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k;fin_cases k <;> simp only [copyStack,
        SemiprimeD1StackCopy.done,SemiprimeD1StackCopy.payload,List.append_nil] <;> rfl
    · intro k hk
      cases k with
      | tag|transform|transformReader|scratch|stage|inverse=>rfl
      | tagReader=>exact (hk 1 rfl).elim
/-- Actual preserving coord0 copy, after the constructor was physically decoded. -/
theorem copy_transform (tag tr : List Bool) (second : Bool) :
    Runs program (5*tr.length+4) (.copyTransform second) (data tag tr [] [] [] [])
      (.transform second 0) (data tag tr [] tr [] []) :=by
  apply included_call program (copyStack true) (Label.copy true) (copy_injective true)
    SemiprimeD1StackCopy.code 0 (fun _=>rfl) (.copyTransform second) (.transform second 0) rfl (5*tr.length+3)
    (SemiprimeD1StackCopy.state 0 none tr [] []) (SemiprimeD1StackCopy.done tr (tr++[]))
  · rfl
  · rfl
  · exact SemiprimeD1StackCopy.copy_words tr [] none
  · constructor
    · intro k;fin_cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k;fin_cases k <;> simp only [copyStack,
        SemiprimeD1StackCopy.done,SemiprimeD1StackCopy.payload,List.append_nil] <;> rfl
    · intro k hk
      cases k with
      | tag|transform|tagReader|scratch|stage|inverse=>rfl
      | transformReader=>exact (hk 1 rfl).elim
/-- ONLY after both decoded fields are validated, two literal pushes create
the actual singleton Boolean stage/inverse words. -/
theorem emit (tag tr : List Bool) (second inverse : Bool) :
    Runs program 2 (.emitStage second inverse) (data tag tr [] [] [] [])
      .done (data tag tr [] [] [second] [inverse]) :=by
  have h0:Runs program 1 (.emitStage second inverse) (data tag tr [] [] [] [])
      (.emitInverse inverse) (data tag tr [] [] [second] []):=by
    apply one_base program _ _ (.push .stage second (.emitInverse inverse)) _ _ rfl
    · rfl
    · exact update_stage _ _ _ _ _ _ _
  have h1:Runs program 1 (.emitInverse inverse) (data tag tr [] [] [second] [])
      .done (data tag tr [] [] [second] [inverse]):=by
    apply one_base program _ _ (.push .inverse inverse .done) _ _ rfl
    · rfl
    · exact update_inverse _ _ _ _ _ _ _
  exact compose h0 h1
end RiemannGaussian.SemiprimeD1StackTransformSelectorsPrimitives

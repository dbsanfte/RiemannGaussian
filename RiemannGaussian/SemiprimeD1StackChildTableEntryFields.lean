/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildTableEntryScalar
/-! # Actual individual coefficient parser and physical vector loop views -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildTableEntryFields
open SemiprimeD1StackChildTableEntry SemiprimeD1StackChildTableEntryEncoding
open SemiprimeD1StackChildTableEntryView SemiprimeD1StackChildTableEntryPrimitives
open SemiprimeD1StackChildTableEntryScalar SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
namespace Link
export SemiprimeD1StackMultiplierLink (DataRel data_update)
end Link
local notation "ctl"=>Label.local
/-- Clean retained gather/lookup/reducer boundary; the table reader is an actual physical vector cursor. -/
def view (old child:J.Stack→List Bool) (assignment path reader:List Bool) (w:Words):Stack→List Bool:=
  bank old child (G.contents [] assignment [] [] [] path) (T.contents [] [] [] [] reader) (scalarBank [] []) (words w)
/-- One lookup-reader update changes no task, scratch or unused shadow word. -/
theorem tree_reader (reader xs:List Bool):
    Function.update (T.contents [] [] [] [] reader) .output xs=T.contents [] [] [] [] xs:=by
  funext k;cases k <;> rfl
/-- One complete real Field call acquires the next coefficient and actual validity singleton. -/
theorem field_call (old child:J.Stack→List Bool) (assignment path word tail:List Bool) (w:Words):
    Runs program (8*word.length+7) (ctl .parse)
      (view old child assignment path (frame word tail) {w with coefficient:=[],valid:=[],scratch:=[]})
      (ctl .valid) (view old child assignment path tail {w with coefficient:=word,valid:=[true],scratch:=[]}):=by
  let before:=view old child assignment path (frame word tail) {w with coefficient:=[],valid:=[],scratch:=[]}
  let start:=SemiprimeD1TensorTapeFieldBytecode.initial (frame word tail) []
  let stop:SemiprimeD1StackBytecode.State F.Stack F.Label:=
    ⟨none,none,Sum.elim (SemiprimeD1TensorTapeFieldMachine.contents tail [] word) (fun _=>[true])⟩
  have hin:Link.DataRel fieldStack before start.store before:=by
    constructor
    · intro k;rcases k with k|k <;> cases k <;> rfl
    · intro k _;rfl
  have h0:=Link.data_update fieldStack field_injective before start.store before hin (.inl .input) tail
  have h1:=Link.data_update fieldStack field_injective before _ _ h0 (.inl .output) word
  have h2:=Link.data_update fieldStack field_injective before _ _ h1 (.inr ()) [true]
  have he:Function.update (Function.update (Function.update start.store (.inl .input) tail) (.inl .output) word)
      (.inr ()) [true]=stop.store:=by funext k;rcases k with k|k <;> cases k <;> rfl
  rw [he] at h2
  change Link.DataRel fieldStack before stop.store
    (Function.update (Function.update (Function.update before (treeAllocation .output) tail) (aux .coefficient) word) (aux .valid) [true]) at h2
  dsimp only [before,view] at h2
  rw [update_tree,tree_reader,update_aux,words_update,update_aux,words_update] at h2
  exact included_call program fieldStack Label.field field_injective F.code (F.active .tagPop (none,false)) (fun _=>rfl)
    (ctl .parse) (ctl .valid) rfl (8*word.length+6) start stop before _ rfl rfl
    (SemiprimeD1TensorTapeFieldBytecode.framed_run word tail []) hin h2
/-- Validity is genuinely consumed; only the acquired coefficient remains. -/
theorem field_read (old child:J.Stack→List Bool) (assignment path word tail:List Bool) (w:Words):
    Runs program (8*word.length+8) (ctl .parse)
      (view old child assignment path (frame word tail) {w with coefficient:=[],valid:=[],scratch:=[]})
      (ctl .oldCount) (view old child assignment path tail {w with coefficient:=word,valid:=[],scratch:=[]}):=by
  have h0:=field_call old child assignment path word tail w
  let v:Words:={w with coefficient:=word,valid:=[true],scratch:=[]}
  have h1:=pop_run .valid (ctl .abort) (ctl .abort) (ctl .oldCount) (aux .valid)
    (view old child assignment path tail v) [true] rfl rfl
  change Runs program 1 _ _ _ (Function.update (view old child assignment path tail v) (aux .valid) []) at h1
  dsimp only [view] at h1
  rw [update_aux,words_update] at h1
  have h:=join h0 h1
  convert h using 1 <;> rfl
end RiemannGaussian.SemiprimeD1StackChildTableEntryFields

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceSelectionAcquirePrimitives
/-! # Seven actual input transfers from the REAL occurrence and alphabet sources -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceSelectionAcquireSelectorInput
open SemiprimeD1StackSourceSelectionAcquire SemiprimeD1StackSourceSelectionAcquireView
open SemiprimeD1StackSourceSelectionAcquirePrimitives SemiprimeD1StackProcedureTrace
local notation "ctl" => Label.local
/-- Entire physical63-role selector input after seven real preserving copies. -/
def selectorReady (occurrences:Occ.Stack→List Bool) (alphabet:Alpha.Stack→List Bool) :Select.Stack→List Bool :=
  (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (fun _=>[]) (Select.queryStack (SemiprimeD1StackSourceIncidence.aux .source)) (occurrences .output)) (Select.aux .catalogue) (alphabet (Alpha.aux .output))) (Select.queryStack (SemiprimeD1StackSourceIncidence.aux .square)) (alphabet (Alpha.aux .square))) (Select.queryStack (SemiprimeD1StackSourceIncidence.aux .cube)) (alphabet (Alpha.aux .cube))) (Select.queryStack (SemiprimeD1StackSourceIncidence.aux .fourth)) (alphabet (Alpha.aux .fourth))) (Select.aux .owners) (occurrences .number)) (Select.aux .factors) (occurrences .factors))
/-- Exact seven-copy source clock, including every actual restore loop and return. -/
def selectorCopyTime (occurrences:Occ.Stack→List Bool) (alphabet:Alpha.Stack→List Bool) :Nat :=
  5*((occurrences .output).length+(alphabet (Alpha.aux .output)).length+(alphabet (Alpha.aux .square)).length+(alphabet (Alpha.aux .cube)).length+(alphabet (Alpha.aux .fourth)).length+(occurrences .number).length+(occurrences .factors).length)+28
/-- Complete real input transfer preserves all other acquired154-role component words. -/
theorem selector_input_run (occurrences:Occ.Stack→List Bool) (alphabet:Alpha.Stack→List Bool)
    (keys:Keys.Stack→List Bool) :
    Runs program (selectorCopyTime occurrences alphabet) (ctl (.copy .occurrences))
      (data occurrences alphabet (fun _=>[]) keys []) (ctl .select)
      (data occurrences alphabet (selectorReady occurrences alphabet) keys []) :=by
  let s0:Select.Stack→List Bool:=fun _=>[]
  let s1:=Function.update s0 (Select.queryStack (SemiprimeD1StackSourceIncidence.aux .source)) (occurrences .output)
  let s2:=Function.update s1 (Select.aux .catalogue) (alphabet (Alpha.aux .output))
  let s3:=Function.update s2 (Select.queryStack (SemiprimeD1StackSourceIncidence.aux .square)) (alphabet (Alpha.aux .square))
  let s4:=Function.update s3 (Select.queryStack (SemiprimeD1StackSourceIncidence.aux .cube)) (alphabet (Alpha.aux .cube))
  let s5:=Function.update s4 (Select.queryStack (SemiprimeD1StackSourceIncidence.aux .fourth)) (alphabet (Alpha.aux .fourth))
  let s6:=Function.update s5 (Select.aux .owners) (occurrences .number)
  let s7:=Function.update s6 (Select.aux .factors) (occurrences .factors)
  have h0:=copy_call .occurrences (data occurrences alphabet s0 keys []) (occurrences .output) [] rfl rfl rfl
  simp only [List.append_nil] at h0
  change Runs program (5*(occurrences .output).length+4) _ _ _
    (Function.update (data occurrences alphabet s0 keys []) (selectorStack (Select.queryStack (SemiprimeD1StackSourceIncidence.aux .source))) (occurrences .output)) at h0
  rw [data_selector] at h0
  have h1:=copy_call .catalogue (data occurrences alphabet s1 keys []) (alphabet (Alpha.aux .output)) [] rfl rfl rfl
  simp only [List.append_nil] at h1
  change Runs program (5*(alphabet (Alpha.aux .output)).length+4) _ _ _
    (Function.update (data occurrences alphabet s1 keys []) (selectorStack (Select.aux .catalogue)) (alphabet (Alpha.aux .output))) at h1
  rw [data_selector] at h1
  have h2:=copy_call .square (data occurrences alphabet s2 keys []) (alphabet (Alpha.aux .square)) [] rfl rfl rfl
  simp only [List.append_nil] at h2
  change Runs program (5*(alphabet (Alpha.aux .square)).length+4) _ _ _
    (Function.update (data occurrences alphabet s2 keys []) (selectorStack (Select.queryStack (SemiprimeD1StackSourceIncidence.aux .square))) (alphabet (Alpha.aux .square))) at h2
  rw [data_selector] at h2
  have h3:=copy_call .cube (data occurrences alphabet s3 keys []) (alphabet (Alpha.aux .cube)) [] rfl rfl rfl
  simp only [List.append_nil] at h3
  change Runs program (5*(alphabet (Alpha.aux .cube)).length+4) _ _ _
    (Function.update (data occurrences alphabet s3 keys []) (selectorStack (Select.queryStack (SemiprimeD1StackSourceIncidence.aux .cube))) (alphabet (Alpha.aux .cube))) at h3
  rw [data_selector] at h3
  have h4:=copy_call .fourth (data occurrences alphabet s4 keys []) (alphabet (Alpha.aux .fourth)) [] rfl rfl rfl
  simp only [List.append_nil] at h4
  change Runs program (5*(alphabet (Alpha.aux .fourth)).length+4) _ _ _
    (Function.update (data occurrences alphabet s4 keys []) (selectorStack (Select.queryStack (SemiprimeD1StackSourceIncidence.aux .fourth))) (alphabet (Alpha.aux .fourth))) at h4
  rw [data_selector] at h4
  have h5:=copy_call .owners (data occurrences alphabet s5 keys []) (occurrences .number) [] rfl rfl rfl
  simp only [List.append_nil] at h5
  change Runs program (5*(occurrences .number).length+4) _ _ _
    (Function.update (data occurrences alphabet s5 keys []) (selectorStack (Select.aux .owners)) (occurrences .number)) at h5
  rw [data_selector] at h5
  have h6:=copy_call .factors (data occurrences alphabet s6 keys []) (occurrences .factors) [] rfl rfl rfl
  simp only [List.append_nil] at h6
  change Runs program (5*(occurrences .factors).length+4) _ _ _
    (Function.update (data occurrences alphabet s6 keys []) (selectorStack (Select.aux .factors)) (occurrences .factors)) at h6
  rw [data_selector] at h6
  have h:=(join (join (join (join (join (join h0 h1) h2) h3) h4) h5) h6)
  change Runs program _ _ _ (ctl .select) _ at h
  change Runs program _ _ _ _ (data occurrences alphabet s7 keys [])
  convert h using 1
  unfold selectorCopyTime
  omega
end RiemannGaussian.SemiprimeD1StackSourceSelectionAcquireSelectorInput


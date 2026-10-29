/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceSelectionAcquirePrimitives
/-! # Four actual stopped-selector cache/source transfers before the real key reader -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceSelectionAcquireKeyInput
open SemiprimeD1StackSourceSelectionAcquire SemiprimeD1StackSourceSelectionAcquireView
open SemiprimeD1StackSourceSelectionAcquirePrimitives SemiprimeD1StackProcedureTrace
local notation "ctl" => Label.local
/-- Full39-role key-reader bank after the dictionary/key/prefix/source physical copies. -/
def keyReady (selector:Select.Stack→List Bool) :Keys.Stack→List Bool :=
  (Function.update (Function.update (Function.update (Function.update (fun _=>[]) (Keys.environmentStack (Env.aux .dictionary)) (selector Select.dictionary)) (Keys.environmentStack (Env.aux .nextKey)) (selector Select.nextKey)) (Keys.environmentStack (Env.aux .prefix)) (selector Select.selected)) (Keys.aux .source) (selector (Select.queryStack (SemiprimeD1StackSourceIncidence.aux .source))))
/-- Exact four-copy clock, retaining the original complete selected cache and occurrence source. -/
def keyCopyTime (selector:Select.Stack→List Bool) :Nat :=
  5*((selector Select.dictionary).length+(selector Select.nextKey).length+(selector Select.selected).length+(selector (Select.queryStack (SemiprimeD1StackSourceIncidence.aux .source))).length)+16
/-- All four actual cache/source handoffs preserve every other acquired154-role component word. -/
theorem key_input_run (occurrences:Occ.Stack→List Bool) (alphabet:Alpha.Stack→List Bool)
    (selector:Select.Stack→List Bool) :
    Runs program (keyCopyTime selector) (ctl (.copy .dictionary))
      (data occurrences alphabet selector (fun _=>[]) []) (ctl .keys)
      (data occurrences alphabet selector (keyReady selector) []) :=by
  let k0:Keys.Stack→List Bool:=fun _=>[]
  let k1:=Function.update k0 (Keys.environmentStack (Env.aux .dictionary)) (selector Select.dictionary)
  let k2:=Function.update k1 (Keys.environmentStack (Env.aux .nextKey)) (selector Select.nextKey)
  let k3:=Function.update k2 (Keys.environmentStack (Env.aux .prefix)) (selector Select.selected)
  let k4:=Function.update k3 (Keys.aux .source) (selector (Select.queryStack (SemiprimeD1StackSourceIncidence.aux .source)))
  have h0:=copy_call .dictionary (data occurrences alphabet selector k0 []) (selector Select.dictionary) [] rfl rfl rfl
  simp only [List.append_nil] at h0
  change Runs program (5*(selector Select.dictionary).length+4) _ _ _
    (Function.update (data occurrences alphabet selector k0 []) (keyStack (Keys.environmentStack (Env.aux .dictionary))) (selector Select.dictionary)) at h0
  rw [data_keys] at h0
  have h1:=copy_call .nextKey (data occurrences alphabet selector k1 []) (selector Select.nextKey) [] rfl rfl rfl
  simp only [List.append_nil] at h1
  change Runs program (5*(selector Select.nextKey).length+4) _ _ _
    (Function.update (data occurrences alphabet selector k1 []) (keyStack (Keys.environmentStack (Env.aux .nextKey))) (selector Select.nextKey)) at h1
  rw [data_keys] at h1
  have h2:=copy_call .prefix (data occurrences alphabet selector k2 []) (selector Select.selected) [] rfl rfl rfl
  simp only [List.append_nil] at h2
  change Runs program (5*(selector Select.selected).length+4) _ _ _
    (Function.update (data occurrences alphabet selector k2 []) (keyStack (Keys.environmentStack (Env.aux .prefix))) (selector Select.selected)) at h2
  rw [data_keys] at h2
  have h3:=copy_call .keySource (data occurrences alphabet selector k3 []) (selector (Select.queryStack (SemiprimeD1StackSourceIncidence.aux .source))) [] rfl rfl rfl
  simp only [List.append_nil] at h3
  change Runs program (5*(selector (Select.queryStack (SemiprimeD1StackSourceIncidence.aux .source))).length+4) _ _ _
    (Function.update (data occurrences alphabet selector k3 []) (keyStack (Keys.aux .source)) (selector (Select.queryStack (SemiprimeD1StackSourceIncidence.aux .source)))) at h3
  rw [data_keys] at h3
  have h:=(join (join (join h0 h1) h2) h3)
  change Runs program _ _ _ (ctl .keys) _ at h
  change Runs program _ _ _ _ (data occurrences alphabet selector k4 [])
  convert h using 1
  unfold keyCopyTime
  omega
end RiemannGaussian.SemiprimeD1StackSourceSelectionAcquireKeyInput


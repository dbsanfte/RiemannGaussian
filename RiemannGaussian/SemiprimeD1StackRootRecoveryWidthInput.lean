/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootRecoveryWidthPrimitives
/-! # Actual exponent/incidence-count transfers with the retained source scratch -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootRecoveryWidthInput
open SemiprimeD1StackRootRecoveryWidth SemiprimeD1StackRootRecoveryWidthView
open SemiprimeD1StackRootRecoveryWidthPrimitives SemiprimeD1StackProcedureTrace
local notation "ctl" => Label.local
/-- Only the literal next source's two input fields are populated. -/
def widthReady (root:R.Stack→List Bool) :W.Stack→List Bool :=
  Function.update (Function.update (fun _=>[])
    (W.aux .a) (root O.exponentRole))
    (W.aux .m) (root O.edgesRole)
/-- The two actual writes yield exactly the next real source's honest physical input bank. -/
theorem widthReady_input (root:R.Stack→List Bool) :widthReady root=
    (W.initial (root O.exponentRole) (root O.edgesRole)).data :=by
  funext k
  rcases k with k|k
  · rfl
  · cases k <;> rfl
/-- Both restoring copies pay every actual metadata byte and both real returns. -/
def widthCopyTime (root:R.Stack→List Bool) :Nat :=
  5*((root O.exponentRole).length+(root O.edgesRole).length)+8
/-- The original producer bank is retained literally, including its reused scratch restored to empty. -/
theorem width_input_run (root:R.Stack→List Bool) (hs:root R.copyScratch=[]) :
    Runs program (widthCopyTime root) (ctl (.copy .exponent)) (data root (fun _=>[]))
      (ctl .width) (data root (widthReady root)) :=by
  let s0:W.Stack→List Bool:=fun _=>[]
  let s1:=Function.update s0 (W.aux .a) (root O.exponentRole)
  let s2:=Function.update s1 (W.aux .m) (root O.edgesRole)
  have h0:=copy_call .exponent (data root s0) (root O.exponentRole) [] rfl rfl hs
  simp only [List.append_nil] at h0
  change Runs program _ _ _ _ (Function.update (data root s0)
    (widthStack (W.aux .a)) (root O.exponentRole)) at h0
  rw [data_width] at h0
  have h1:=copy_call .edges (data root s1) (root O.edgesRole) [] rfl rfl hs
  simp only [List.append_nil] at h1
  change Runs program _ _ _ _ (Function.update (data root s1)
    (widthStack (W.aux .m)) (root O.edgesRole)) at h1
  rw [data_width] at h1
  have h:=join h0 h1
  change Runs program _ _ _ (ctl .width) _ at h
  change Runs program _ _ _ _ (data root s2)
  convert h using 1
  unfold widthCopyTime
  omega
end RiemannGaussian.SemiprimeD1StackRootRecoveryWidthInput

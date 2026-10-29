/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryCleanup
/-! # Actual final exhaustive cleanup, success status and true halt
This source executes every real cleanup label before pushing success and
halting. Caller returns and all 115 physical words are accounted for.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryFinish
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryWiring
open SemiprimeD1StackChildGroupFactory SemiprimeD1StackChildGroupFactoryPrimitives
open SemiprimeD1StackProcedureTrace
namespace Clean
export SemiprimeD1StackChildGroupFactoryCleanup (result mass source_trace)
end Clean
/-- The success bit is physically pushed only after its old word was drained. -/
def result (before:Stack→List Bool):Stack→List Bool:=
  Function.update (Clean.result false before) (aux .success) [true]
/-- All actual jumps, all word drains, the literal push and final halt are paid. -/
def timeBound (before:Stack→List Bool):Nat:=115*(Clean.mass before+1)+3
/-- Actual final source, for arbitrary real saved return frames and stale flags. -/
theorem source_run (before:Stack→List Bool):
    ∃t≤timeBound before,∀frames (start:C.State Stack Label),
      At (.local 15 13) before frames start→
      C.run program t start=some (⟨none,none,none,result before,frames⟩:C.State Stack Label):=by
  have h0:=jump_run (.local 15 13) (.clear false 0) before rfl
  obtain ⟨x,hx,h1⟩:=Clean.source_trace false before
  have h2:=push_run accept (.local 15 17) (aux .success) true (Clean.result false before) rfl
  have he:(Clean.result false before) (aux .success)=[]:=rfl
  rw [he] at h2
  change Runs program 1 accept _ (.local 15 17) (result before) at h2
  have hwhole:=join h0 (join h1 h2)
  refine ⟨1+(x+1)+1,?_,?_⟩
  · dsimp only [timeBound];omega
  · intro frames start hs
    obtain ⟨mid,hm,hat⟩:=hwhole frames start hs
    have hh:=halt_run program (.local 15 17) rfl (result before) frames mid hat
    rw [SemiprimeD1StackReturnLink.run_add,hm,Option.bind_some,hh]
/-- Actual retained inputs and outputs survive the complete finishing source. -/
theorem result_retained (before:Stack→List Bool) (k:Stack)
    (hk:retained false k=true) (hs:k≠aux .success):result before k=before k:=by
  simp only [result,Function.update_of_ne hs,Clean.result,hk,ite_true]
/-- Every unretained private word, including unused shadows, is empty at halt. -/
theorem result_private (before:Stack→List Bool) (k:Stack)
    (hk:retained false k=false) (hs:k≠aux .success):result before k=[]:=by
  simp only [result,Function.update_of_ne hs,Clean.result,hk,Bool.false_eq_true,ite_false]
/-- Literal success flag at the actual stopped boundary. -/
theorem result_success (before:Stack→List Bool):result before (aux .success)=[true]:=Function.update_self _ _ _
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryFinish

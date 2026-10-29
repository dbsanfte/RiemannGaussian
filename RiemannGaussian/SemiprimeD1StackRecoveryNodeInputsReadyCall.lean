/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryNodeInputsEncoding
import RiemannGaussian.SemiprimeD1StackRecoveryNodeInputsAffineReady
/-! # Real same-program ready call from an ACTUAL acquired Grid bank without Grid replay -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryNodeInputsReadyCall
open SemiprimeD1StackRecoveryNodeInputs SemiprimeD1StackRecoveryNodeInputsInventory
open SemiprimeD1StackRecoveryNodeInputsEncoding SemiprimeD1StackProcedureTrace
/-- Actual Grid-cache ready entry executes actual q/affine work and its real return, with no supplied q/array answer. -/
theorem ready_call (a M u : ℕ) (selected : Fin (2^(a+1))) (t width : List Bool)
    (ht : SemiprimeBitArithmetic.bitValue t=selected.val) :
    ∃s≤SemiprimeD1StackRecoveryNodeInputsAffineReady.timeBound a M u selected t width+1,
      Runs program s (ctl .readyGrid) (gridReady a M u selected t width).data
        (ctl .inverse) (afterAffine a M u selected t width) := by
  obtain ⟨s,hs,hr⟩:=SemiprimeD1StackRecoveryNodeInputsAffineReady.source_run a M u selected t width ht
  refine ⟨s+1,Nat.add_le_add_right hs 1,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program affine affineLabel affine_injective A.program
    (.local .ready) (fun _=>rfl) (ctl .readyGrid) (ctl .inverse) rfl s
    (SemiprimeD1StackRecoveryNodeInputsAffineReady.initial a M u selected t width)
    (SemiprimeD1StackRecoveryAffineEncoding.done a M u selected t width) _ _ rfl rfl rfl rfl hr
  · exact ⟨fun _=>rfl,fun _ _=>rfl⟩
  · constructor
    · intro k;rfl
    · intro k hk;rcases k with k|k
      · exact (hk k rfl).elim
      · rfl
end RiemannGaussian.SemiprimeD1StackRecoveryNodeInputsReadyCall

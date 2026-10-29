/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryNodeInputsEncoding
/-! # Three real whole-source calls with exact direct-alias input lineage and actual returns -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryNodeInputsCalls
open SemiprimeD1StackRecoveryNodeInputs SemiprimeD1StackRecoveryNodeInputsInventory
open SemiprimeD1StackRecoveryNodeInputsEncoding SemiprimeD1StackProcedureTrace
namespace V
export SemiprimeD1StackRecoveryNodeInputsView (empty inverse_initial powers_initial)
end V
/-- ACTUAL affine source includes exactly one whole Grid call and acquires q/denominator internally. -/
theorem affine_call (a M u : ℕ) (selected : Fin (2^(a+1))) (t width : List Bool)
    (ht : SemiprimeBitArithmetic.bitValue t=selected.val) :
    ∃s≤SemiprimeD1StackRecoveryAffineExecution.timeBound a M u selected t width+1,
      Runs program s (ctl .start)
        (input (List.replicate a true) (List.replicate M true) (List.replicate u true) t width)
        (ctl .inverse) (afterAffine a M u selected t width) := by
  obtain ⟨s,hs,hr⟩:=SemiprimeD1StackRecoveryAffineExecution.source_run a M u selected t width ht
  refine ⟨s+1,Nat.add_le_add_right hs 1,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program affine affineLabel affine_injective A.program
    (.local .start) (fun _=>rfl) (ctl .start) (ctl .inverse) rfl s
    (A.initial (List.replicate a true) (List.replicate M true) (List.replicate u true) t width)
    (SemiprimeD1StackRecoveryAffineEncoding.done a M u selected t width) _ _ rfl rfl rfl rfl hr
  · exact ⟨fun _=>rfl,fun _ _=>rfl⟩
  · constructor
    · intro k;rfl
    · intro k hk;rcases k with k|k
      · exact (hk k rfl).elim
      · rfl
/-- The ENTIRE real inverse uses actual acquired affine-array/q/W aliases, preserving ALL112 old words. -/
theorem inverse_call (a M u : ℕ) (selected : Fin (2^(a+1))) (t width : List Bool) :
    ∃s≤SemiprimeD1StackNormalizedInverseBounds.polynomial (E.array a M u selected width) (E.retained a M u selected) width+1,
      Runs program s (ctl .inverse) (afterAffine a M u selected t width)
        (ctl .powers) (afterInverse a M u selected t width) := by
  let den:=E.array a M u selected width
  let q:=E.retained a M u selected
  let before:=afterAffine a M u selected t width
  have hin:=V.inverse_initial (E.result a M u selected t width)
    (SemiprimeD1StackNormalizedInverse.tape den) (List.replicate q true) width
    (rational_image a M u selected t width) (denominator_image a M u selected t width) (q_image a M u selected t width)
  obtain ⟨s,hs,hr⟩:=SemiprimeD1StackNormalizedInverseBounds.source_run_bounded den q width
  refine ⟨s+1,Nat.add_le_add_right hs 1,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program inverse inverseLabel inverse_injective I.program
    (I.ctl .start) (fun _=>rfl) (ctl .inverse) (ctl .powers) rfl s
    (I.initial (SemiprimeD1StackNormalizedInverse.tape den) (List.replicate q true) width)
    (SemiprimeD1StackNormalizedInverseEncoding.done den q width) _ _ rfl rfl rfl rfl hr hin
  have ho:=SemiprimeD1StackMultiplierLink.data_update inverse inverse_injective before
    (I.input (SemiprimeD1StackNormalizedInverse.tape den) (List.replicate q true) width) before hin
    (I.aux .output) (inverseTape a M u selected width)
  exact ho
/-- The real powers source reads the SAME retained Grid argument/q/W; no argument/grid/source replay occurs. -/
theorem powers_call (a M u : ℕ) (selected : Fin (2^(a+1))) (t width : List Bool) :
    ∃s≤SemiprimeD1StackRecoveryPowersExecution.timeBound (argument a M u selected width) width (E.retained a M u selected)+1,
      Runs program s (ctl .powers) (afterInverse a M u selected t width)
        (ctl .done) (result a M u selected t width) := by
  let arg:=argument a M u selected width
  let q:=E.retained a M u selected
  let before:=afterInverse a M u selected t width
  have hin:=V.powers_initial (E.result a M u selected t width) (inverseTape a M u selected width)
    (SemiprimeD1StackRecoveryPowersSpec.signed arg) arg.denominator (List.replicate q true) width
    (rational_image a M u selected t width) (argument_signed a M u selected t width)
    (argument_den a M u selected t width) (q_image a M u selected t width)
  obtain ⟨s,hs,hr⟩:=SemiprimeD1StackRecoveryPowersExecution.source_run arg q width
  refine ⟨s+1,Nat.add_le_add_right hs 1,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program powers powersLabel powers_injective P.program
    (.local .start) (fun _=>rfl) (ctl .powers) (ctl .done) rfl s
    (P.initial (SemiprimeD1StackRecoveryPowersSpec.signed arg) arg.denominator (List.replicate q true) width)
    (SemiprimeD1StackRecoveryPowersEncoding.done arg q width) _ _ rfl rfl rfl rfl hr hin
  have ho:=SemiprimeD1StackMultiplierLink.data_update powers powers_injective before
    (P.input (SemiprimeD1StackRecoveryPowersSpec.signed arg) arg.denominator (List.replicate q true) width) before hin
    (P.aux .output) (powerTape a M u selected width)
  exact ho
end RiemannGaussian.SemiprimeD1StackRecoveryNodeInputsCalls

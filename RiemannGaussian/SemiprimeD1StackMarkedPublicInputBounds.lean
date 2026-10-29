/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackMarkedPublicInputCost
/-! # SAME finite machine's whole marked-coefficient time certificate -/
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 262144
set_option maxRecDepth 32768
namespace RiemannGaussian.SemiprimeD1StackMarkedPublicInputBounds
open SemiprimeD1StackMarkedPublicInput SemiprimeD1StackMarkedPublicInputEncoding
open SemiprimeD1StackMarkedPublicInputExecution SemiprimeD1StackMarkedPublicInputCost
/-- Whole source has a fixed quadratic in its actual physical source words. -/
theorem source_run_bounded (bits raw indexWord : List Bool) (side : Bool) (hb : bits≠[]) :
    ∃ t ≤ polynomial bits raw indexWord,
      SemiprimeD1StackCalls.run program t (initial bits raw indexWord [side])=
        some (done bits raw indexWord side) := by
  obtain ⟨t,ht,hr⟩ := source_run bits raw indexWord side hb
  exact ⟨t,ht.trans (runBound_le bits raw indexWord),hr⟩
/-- Genuine compiled execution, including every actual call/return and final halt. -/
noncomputable def machineSource (bits raw indexWord : List Bool) (side : Bool) (hb : bits≠[]) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial bits raw indexWord [side]))
      (some (SemiprimeD1StackCalls.configuration (done bits raw indexWord side)))
      (polynomial bits raw indexWord) := by
  apply SemiprimeD1StackCalls.evalsCorrect
    (checker (.inl SemiprimeD1StackPublicInputWidth.original)) (aux .output) (ctl .start) program
  let h := source_run_bounded bits raw indexWord side hb
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
end RiemannGaussian.SemiprimeD1StackMarkedPublicInputBounds


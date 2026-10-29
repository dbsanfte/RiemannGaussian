/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackEuclidGCDSetup
import RiemannGaussian.SemiprimeD1StackEuclidGCDLoop
/-! # Whole two-original-word source, exact compact GCD and its own physical clock -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackEuclidGCDExecution
open SemiprimeD1StackEuclidGCD SemiprimeD1StackEuclidGCDEncoding SemiprimeD1StackEuclidGCDSpec
open SemiprimeD1StackEuclidGCDSetup SemiprimeD1StackEuclidGCDLoop
open SemiprimeD1StackProcedureTrace
/-- Own whole-source instruction count: actual input preparation, actual loop and actual final halt. -/
def runBound (left right:List Bool) :Nat:=setupTime left right+
  loopTime (fuelLength left right) left (SemiprimeD1StackSourceEnvironmentEncoding.normalize right)+1
/-- Same fixed program produces all result bytes internally and preserves both original words and all real outer returns. -/
theorem source_trace (left right:List Bool) :
    Runs program (runBound left right-1) .start (input left right) .done (result left right) :=by
  have h0:=setup_run left right
  have h1:=loop_run (fuelLength left right) left right left
    (SemiprimeD1StackSourceEnvironmentEncoding.normalize right) (answer_stopped left right)
  exact SemiprimeD1StackEuclidGCDPrimitives.join h0 h1
/-- Actual terminal halt clears both flags and every genuine return cell; no answer or fuel is supplied. -/
theorem source_run (left right:List Bool) :
    SemiprimeD1StackCalls.run program (runBound left right) (initial left right)=some (done left right) :=by
  obtain ⟨finish,hfin,hAt⟩:=source_trace left right [] (initial left right) ⟨rfl,rfl,rfl⟩
  have he:runBound left right=(runBound left right-1)+1:=by unfold runBound;omega
  rw [he,SemiprimeD1StackReturnLink.run_add,hfin,Option.bind_some]
  exact halt_run program .done rfl (result left right) [] finish hAt
/-- Genuine fixed eighteen-role finite machine, with the same complete input-only source clock. -/
noncomputable def gcdInTime (left right:List Bool) :
    StateTransition.EvalsToInTime machine.step (SemiprimeD1StackCalls.configuration (initial left right))
      (some (SemiprimeD1StackCalls.configuration (done left right))) (runBound left right) :=by
  apply SemiprimeD1StackCalls.evalsCorrect (aux .left) (aux .output) .start program
  exact ⟨⟨runBound left right,source_run left right⟩,le_rfl⟩
/-- Entire stopped bank contains the exact compact normalization of legacy GCD and both original inputs. -/
theorem output_legacy (left right:List Bool) :
    (done left right).data (aux .output)=
      SemiprimeD1StackSourceEnvironmentEncoding.normalize (SemiprimeBitGcd.gcdBits left right).bits:=
  answer_legacy_bits left right
/-- The actual stopped word has the exact mathematical GCD value for arbitrary input padding. -/
theorem output_value (left right:List Bool) :
    SemiprimeBitArithmetic.bitValue ((done left right).data (aux .output))=
      (SemiprimeBitArithmetic.bitValue left).gcd (SemiprimeBitArithmetic.bitValue right):=
  answer_value left right
end RiemannGaussian.SemiprimeD1StackEuclidGCDExecution

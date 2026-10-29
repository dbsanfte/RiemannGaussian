/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1BinaryBootstrap
import RiemannGaussian.SemiprimeMacroEntryExecution

/-! # Original public-input meaning of the executed bootstrap
This connects the actual preserved binary input and acquired width to the
literal existing public configuration parameters. It does not execute the
remaining transform/radix/normalizer/graph constructors as machine operations.
-/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1BinaryBootstrapPublic
open SemiprimeD1BinaryBootstrap SemiprimeBitArithmetic SemiprimeMacroParameters

/-- Physically acquired width is the exact original public bitLength on canonical input. -/
theorem public_width (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) :
    ((done bits).store Stack.width).length=bitLength (bitValue bits) := by
  simpa only [done,payload,List.length_replicate,bitLength] using canonical_width bits hc

/-- The preserved original input is unchanged and the public zero test is physically returned. -/
theorem public_input_flags (bits:List Bool) :
    (done bits).store Stack.input=bits ∧
      (done bits).store Stack.nonzero=[(SemiprimeBitDivision.nonzeroBits bits).nonzero] := by
  exact ⟨rfl,congrArg List.singleton (seenOne_eq_nonzeroBits bits)⟩

/-- An actual original-input machine certificate expressed in the SAME public bitLength,
with no supplied width, zero predicate or decoded natural input. -/
def originalInTime (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) :
    StateTransition.EvalsToInTime machine.step (Turing.initList machine bits)
      (some (SemiprimeD1StackBytecode.configuration
        (⟨none,none,payload bits [] (List.replicate (bitLength (bitValue bits)) true)
          [(SemiprimeBitDivision.nonzeroBits bits).nonzero]⟩:
          SemiprimeD1StackBytecode.State Stack Label))) (5*bitLength (bitValue bits)+4) := by
  have h:=bootstrapInTime bits
  have hw:bits.length=bitLength (bitValue bits):=canonical_width bits hc
  simpa only [done,hw,seenOne_eq_nonzeroBits] using h

/-- Every original public shape field consumes the width acquired by this actual scan.
The equalities are a semantic consumer bridge, not a machine-cost claim for those constructors. -/
theorem public_configuration_dimensions (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits)
    (hN:0<bitValue bits) :
    let ell:=((done bits).store Stack.width).length
    let config:=SemiprimeMacroEntryExecution.executablePublicConfig (bitValue bits) hN
    config.r=firstAxis ell ∧ config.t=secondAxis ell ∧ config.digits=digitCount ell ∧
      config.bits=radixBits ell ∧ config.depth=macroDepth ell := by
  dsimp only
  rw [public_width bits hc]
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

/-- Canonical original-input storage is polynomial in the SAME public bitLength. -/
theorem original_space (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits)
    (fuel:ℕ) (cfg:machine.Cfg)
    (hr:(fun cfg=>cfg.bind machine.step)^[fuel] (some (Turing.initList machine bits))=some cfg) :
    (cfg.stk Stack.input).length+(cfg.stk Stack.reverse).length+
      (cfg.stk Stack.width).length+(cfg.stk Stack.nonzero).length ≤21*(bitLength (bitValue bits)+1) := by
  have h:=machine_space bits fuel cfg hr
  have hw:bits.length=bitLength (bitValue bits):=canonical_width bits hc
  simpa only [hw] using h
end RiemannGaussian.SemiprimeD1BinaryBootstrapPublic

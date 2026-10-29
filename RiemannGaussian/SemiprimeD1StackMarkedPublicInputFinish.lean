/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackMarkedPublicInputCopies
/-! # Uniform actual2ell template fit and physical cleanup -/
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 262144
set_option maxRecDepth 32768
namespace RiemannGaussian.SemiprimeD1StackMarkedPublicInputFinish
open SemiprimeD1StackMarkedPublicInput SemiprimeD1StackMarkedPublicInputEncoding
open SemiprimeD1StackMarkedPublicInputCopies SemiprimeD1StackMarkedPublicInputCalls
open SemiprimeD1StackMarkedPublicInputPrimitives SemiprimeD1StackProcedureTrace
/-- Paid template cache selected from the actual stopped checker. -/
def ellAt (p : P.Stack → List Bool) : List Bool :=
  p (.inl (.inl SemiprimeD1StackPublicInputWidth.widthKey))
/-- Whole actual uniform fit/cleanup clock, including all calls and real returns. -/
def finishTime (p : P.Stack → List Bool) (reader digit radix operand : List Bool) : Nat :=
  (5*(ellAt p).length+4)+(5*(ellAt p).length+4)+
  (SemiprimeD1StackWordFitExecution.totalTime operand (ellAt p++ellAt p)+1)+
  (reader.length+1)+(digit.length+1)+(radix.length+1)
/-- Invalid, unmarked and marked operands all reach this SAME real fitter and
all helper words are physically cleared afterward. -/
theorem finish_run (p : P.Stack → List Bool) (reader digit radix side operand : List Bool) :
    Runs program (finishTime p reader digit radix operand) (ctl .widthA)
      (data p {reader := reader, digit := digit, radix := radix, side := side, shifted := operand})
      (ctl .done) (data p {side := side, template := ellAt p++ellAt p, output := SemiprimeD1StackWordFitExecution.result operand (ellAt p++ellAt p)}) := by
  let w0 : Work := {reader := reader, digit := digit, radix := radix, side := side, shifted := operand}
  let w1 : Work := {w0 with template := ellAt p}
  let w2 : Work := {w0 with template := ellAt p++ellAt p}
  let result := SemiprimeD1StackWordFitExecution.result operand (ellAt p++ellAt p)
  let w3 : Work := {reader := reader, digit := digit, radix := radix, side := side, template := ellAt p++ellAt p, output := result}
  let w4 : Work := {w3 with reader := []}
  let w5 : Work := {w4 with digit := []}
  have h0 := width_copy p w0 .widthA .widthB rfl
  dsimp only [w0] at h0
  simp only [List.append_nil] at h0
  have h1 := width_copy p w1 .widthB .fit rfl
  have h2 := fit_call p w2
  have h3 := drain_loop .clearRaw (ctl .clearWord) (word 0) rfl (data p w3) reader rfl
  rw [update_reader] at h3
  have h4 := drain_loop .clearWord (ctl .clearRadix) (word 4) rfl (data p w4) digit rfl
  rw [update_digit] at h4
  have h5 := drain_loop .clearRadix (ctl .done) (product .multiplicand) rfl (data p w5) radix rfl
  rw [update_radix] at h5
  have hh := join (join (join (join (join h0 h1) h2) h3) h4) h5
  exact hh
end RiemannGaussian.SemiprimeD1StackMarkedPublicInputFinish


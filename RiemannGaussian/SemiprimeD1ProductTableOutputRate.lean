/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackProductTableOriginal
/-! # Whole-family product-table acquisition is quasilinear in actual output
For m ACTUALLY emitted old-codec Boolean cells, the SAME fixed N-only machine
takes at most10^30*m*(Nat.size m)^6 transitions. Original input acquisition,
every leaf's arithmetic/cleanup and final output construction are included.
This is a local-table compiler component, not a whole collision/factor query.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1ProductTableOutputRate
open SemiprimeD1StackProductTable SemiprimeD1StackProductTableSpec SemiprimeD1StackProductTableExecution
open SemiprimeD1TensorTapeCodec (tape)
/-- Every leaf contributes at least four real output cells, even at zero. -/
theorem tree_length_lower (bits front : List Bool) (n : ℕ) :4*2^n≤(tape (tree bits front n)).length := by
  induction n generalizing front with
  | zero=>
    have he:tape (tree bits front 0)=SemiprimeD1BooleanTreeStream.leafBytes (answer bits front):=
      (SemiprimeD1BooleanTreeStream.leafBytes_original _).symm
    rw [he]
    cases answer bits front <;> decide
  | succ n ih=>
    have hl:=ih (front++[false])
    have hr:=ih (front++[true])
    change 4*2^(n+1)≤(true::(tape (tree bits (front++[false]) n)++tape (tree bits (front++[true]) n))).length
    simp only [List.length_cons,List.length_append,pow_succ]
    omega
/-- The actual dyadic stopping rule bounds original width by arity squared;
thus the complete polynomial preprocessing cost becomes only a log-output factor. -/
theorem input_le_arity_square (bits : List Bool) :bits.length+1≤(arity bits+1)^2 := by
  let R:=SemiprimeMacroParameters.transformLength bits.length
  have hr:R≤arity bits := by
    unfold arity
    rw [SemiprimeD1StackPublicProductBounds.cached_length]
    change R≤3*(R+1)
    omega
  have hs:R^2≤(arity bits)^2:=Nat.pow_le_pow_left hr 2
  have hl:16*bits.length≤R^2:=SemiprimeMacroParameters.transform_square_lower bits.length
  nlinarith
/-- The actual output has at least as many cells as its real assignment leaves. -/
theorem leaves_le_output (bits : List Bool) :2^(arity bits)≤(outputTape bits).length := by
  have h:=tree_length_lower bits [] (arity bits)
  change 4*2^(arity bits)≤(outputTape bits).length at h
  omega
/-- Actual original assignment arity is at most the binary bitlength of the
already materialized output cell count, with no size oracle in the program. -/
theorem arity_le_output_size (bits : List Bool) :arity bits+1≤Nat.size (outputTape bits).length := by
  have hl:=leaves_le_output bits
  have hs:=Nat.lt_size_self (outputTape bits).length
  by_contra hn
  have ha:Nat.size (outputTape bits).length≤arity bits := by omega
  have hp:=Nat.pow_le_pow_right (by decide : 1≤(2:ℕ)) ha
  omega
/-- Explicit quasilinear bound in ACTUAL output cells and its binary bitlength.
All quantities below occur only in proofs, never as supplied control/data. -/
def outputBound (bits : List Bool) : ℕ :=
  1000000000000000000000000000000*(Nat.size (outputTape bits).length)^6*(outputTape bits).length
/-- Complete own original-N source clock is O(m log^6 m) for the ENTIRE family. -/
theorem runBound_le_outputBound (bits : List Bool) :
    SemiprimeD1StackProductTableBounds.runBound bits≤outputBound bits := by
  have h3:=Nat.pow_le_pow_left (input_le_arity_square bits) 3
  rw [←pow_mul] at h3
  change (bits.length+1)^3≤(arity bits+1)^6 at h3
  have hs:=Nat.pow_le_pow_left (arity_le_output_size bits) 6
  have hp: (bits.length+1)^3≤(Nat.size (outputTape bits).length)^6:=h3.trans hs
  exact Nat.mul_le_mul (Nat.mul_le_mul_left _ hp) (leaves_le_output bits)
/-- Genuine SAME finite-machine execution from N ONLY with the whole-family
quasilinear-output clock, including every acquisition/cleanup/output step. -/
noncomputable def machineOutputBound (bits : List Bool) (hb : bits≠[]) :
    StateTransition.EvalsToInTime machine.step (Turing.initList machine bits)
      (some (SemiprimeD1StackCalls.configuration (done bits))) (outputBound bits) := by
  have h:=SemiprimeD1StackProductTableBounds.machineTable bits hb
  exact ⟨h.toEvalsTo,h.steps_le_m.trans (runBound_le_outputBound bits)⟩
end RiemannGaussian.SemiprimeD1ProductTableOutputRate

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackBinarySquareRootStorage
/-! # Universal original-binary square-root correctness, bit time and all-word space
The original input is the sole physical operand. All powers, trials, verdicts
and the compact root are acquired by the SAME literal finite program.
Packed factor-count/sum extraction and the final factor-recovery caller remain
separate joins; this source is the binary square-root primitive only.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackBinarySquareRootOriginal
open scoped BigOperators
open SemiprimeD1StackBinarySquareRoot SemiprimeD1StackBinarySquareRootEncoding
open SemiprimeD1StackBinarySquareRootExecution SemiprimeD1StackBinarySquareRootStorage
open SemiprimeBitArithmetic SemiprimeSourceCompactBits
/-- Original binary D is retained verbatim, even for padded zero/input words. -/
theorem retained_input (bits : List Bool) : (done bits).data originalInput=bits := rfl
/-- The descending power is actually consumed and its final borrowed trim storage cleared. -/
theorem power_empty (bits : List Bool) : (done bits).data power=[] := rfl
/-- The internal raw root is physically consumed by the actual final reversal. -/
theorem root_empty (bits : List Bool) : (done bits).data (aux .root)=[] := rfl
/-- Every one of the eighteen actual private arithmetic roles is empty at halt. -/
theorem private_empty (bits : List Bool) (i : Fin 18) : (done bits).data (clearStack i)=[] := by
  fin_cases i <;> rfl
/-- Output correctness is universal; no compactness, positivity, square or factoring advice is supplied. -/
theorem output_value (bits : List Bool) :
    bitValue ((done bits).data (aux .output))=Nat.sqrt (bitValue bits) :=
  SemiprimeD1StackBinarySquareRootArithmetic.output_value bits
/-- Actual final byte output is compact, including the empty representation of zero. -/
theorem output_compact (bits : List Bool) : Compact ((done bits).data (aux .output)) :=
  SemiprimeD1StackBinarySquareRootArithmetic.output_compact bits
/-- Ordinary integer square-root inequalities hold for the ACTUAL stopped output. -/
theorem output_bounds (bits : List Bool) :
    (bitValue ((done bits).data (aux .output)))^2 ≤ bitValue bits ∧
      bitValue bits < (bitValue ((done bits).data (aux .output))+1)^2 := by
  rw [output_value]
  exact ⟨Nat.sqrt_le' _,Nat.lt_succ_sqrt' _⟩
/-- Original-binary acquisition, exact sqrt and its OWN fixed quartic bit-time bound. -/
theorem source_original (bits : List Bool) :
    ∃t ≤ 100000000*(bits.length+1)^4,
      SemiprimeD1StackCalls.run program t (initial bits)=some (done bits) ∧
      (done bits).data originalInput=bits ∧
      bitValue ((done bits).data (aux .output))=Nat.sqrt (bitValue bits) ∧
      Compact ((done bits).data (aux .output)) := by
  obtain ⟨t,ht,hr⟩:=source_run_bounded bits
  exact ⟨t,ht,hr,retained_input bits,output_value bits,output_compact bits⟩
/-- Genuine Turing.initList binary-input machine, with the SAME proved actual quartic clock. -/
noncomputable def machineOriginal (bits : List Bool) :
    StateTransition.EvalsToInTime machine.step (Turing.initList machine bits)
      (some (SemiprimeD1StackCalls.configuration (done bits))) (100000000*(bits.length+1)^4) := by
  rw [initial_eq]
  apply SemiprimeD1StackCalls.evalsCorrect originalInput (aux .output) (ctl .start) program
  let h:=source_run_bounded bits
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
/-- All33 words and actual saved-return cells are paid at EVERY actual compiled prefix. -/
theorem original_prefix_cells (bits : List Bool) (fuel : ℕ) (cfg : machine.Cfg)
    (hp : (fun q => q.bind machine.step)^[fuel] (some (Turing.initList machine bits))=some cfg) :
    (∑k : Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤ 10000000000*(bits.length+1)^4 :=
  machine_prefix_cells bits fuel cfg hp
end RiemannGaussian.SemiprimeD1StackBinarySquareRootOriginal

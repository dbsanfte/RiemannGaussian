/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicScaleDot
/-! # Actual computed-status branch, output-word extraction and integer equality -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 4096
namespace RiemannGaussian.SemiprimeD1StackPublicScaleTail
open SemiprimeD1StackPublicScale SemiprimeD1StackPublicScaleState SemiprimeD1StackPublicScaleDot
open SemiprimeD1StackPublicScalePrimitives SemiprimeD1StackProcedureTrace SemiprimeBitArithmetic
/-- Actual acquired-vector guard, never a supplied status. -/
def flag (bits raw : List Bool) : Bool := SemiprimeD1StackPublicScaleMeaning.guard (cached bits) (inputWord bits raw)
/-- Exact physical data after popping the ACTUAL dot status. -/
def branched (bits raw stride frequency : List Bool) (inverse : Bool) (j k : ℕ) : Stack→List Bool :=
  Function.update (evaluated bits raw stride frequency inverse j k) (dotStack I.status) []
/-- Exact real WordBlock input/output updates, not an advised extracted word. -/
def readData (bits raw stride frequency : List Bool) (inverse : Bool) (j k : ℕ) : Stack→List Bool :=
  let data:=branched bits raw stride frequency inverse j k
  Function.update (Function.update data (blockStack 0) ((data (blockStack 0)).drop (data (blockStack 1)).length))
    (blockStack 4) (SemiprimeD1StackWordBlockExecution.result (data (blockStack 0)) (data (blockStack 1)))
/-- Actual final comparison bit on the actual extracted words. -/
def equalAnswer (bits raw stride frequency : List Bool) (inverse : Bool) (j k : ℕ) : Bool :=
  let data:=readData bits raw stride frequency inverse j k
  decide (bitValue (data (equalStack .left))=bitValue (data (equalStack .right)))
/-- Complete final physical store, retaining the raw/cache fields actually read
on that branch; true path consumes both compared words, false path skips them. -/
def finalData (bits raw stride frequency : List Bool) (inverse : Bool) (j k : ℕ) : Stack→List Bool :=
  if flag bits raw then
    Function.update (Function.update (Function.update (readData bits raw stride frequency inverse j k)
      (equalStack .left) []) (equalStack .right) []) (equalStack .output)
        [equalAnswer bits raw stride frequency inverse j k]
  else Function.update (branched bits raw stride frequency inverse j k) (auxRole .output) [false]
/-- Budget for the actually selected tail, paying BOTH tails as an allowance. -/
def tailBudget (bits raw stride frequency : List Bool) (inverse : Bool) (j k : ℕ) : ℕ :=
  1+1+(SemiprimeD1StackWordBlockExecution.totalTime (cached bits)+1)+
    (SemiprimeD1StackWordEqualExecution.executionTime
      (readData bits raw stride frequency inverse j k (equalStack .left))
      (readData bits raw stride frequency inverse j k (equalStack .right))+1)
/-- Actual status pop chooses reject versus actual output-word acquisition. -/
theorem branch_run (bits raw stride frequency : List Bool) (inverse : Bool) (j k : ℕ) :
    Runs program 1 .branch (evaluated bits raw stride frequency inverse j k)
      (if flag bits raw then .readOutput else .reject) (branched bits raw stride frequency inverse j k) := by
  have h:=pop .branch .bad .reject .readOutput (dotStack I.status) rfl (evaluated bits raw stride frequency inverse j k)
  rw [status_value] at h
  change Runs program 1 .branch (evaluated bits raw stride frequency inverse j k)
    (SemiprimeD1StackBytecode.choose .bad .reject .readOutput (some (flag bits raw)))
    (branched bits raw stride frequency inverse j k) at h
  cases he : flag bits raw <;> simpa only [he,SemiprimeD1StackBytecode.choose,Bool.false_eq_true,ite_false,ite_true] using h
/-- The actual output block has the original acquired template, not a width answer. -/
theorem branch_modulus (bits raw stride frequency : List Bool) (inverse : Bool) (j k : ℕ) :
    branched bits raw stride frequency inverse j k (blockStack 1)=cached bits := rfl
/-- Actual WordBlock call reads the real suffix, preserving its remaining bytes. -/
theorem output_call (bits raw stride frequency : List Bool) (inverse : Bool) (j k : ℕ) :
    Runs program (SemiprimeD1StackWordBlockExecution.totalTime (cached bits)+1) .readOutput
      (branched bits raw stride frequency inverse j k) .equal (readData bits raw stride frequency inverse j k) :=
  block_call _ rfl rfl rfl
/-- Actual equality consumes actual physical words and returns its singleton bit. -/
theorem comparison_call (bits raw stride frequency : List Bool) (inverse : Bool) (j k : ℕ) :
    Runs program (SemiprimeD1StackWordEqualExecution.executionTime
      (readData bits raw stride frequency inverse j k (equalStack .left))
      (readData bits raw stride frequency inverse j k (equalStack .right))+1)
      .equal (readData bits raw stride frequency inverse j k) .done
      (Function.update (Function.update (Function.update (readData bits raw stride frequency inverse j k)
        (equalStack .left) []) (equalStack .right) []) (equalStack .output)
          [equalAnswer bits raw stride frequency inverse j k]) := equal_call _ rfl rfl
/-- Complete actual branch and integer comparison. No status, guard truth,
output word, comparison answer or component clock is assumed. -/
theorem tail_run (bits raw stride frequency : List Bool) (inverse : Bool) (j k : ℕ) :
    ∃t≤tailBudget bits raw stride frequency inverse j k,
      Runs program t .branch (evaluated bits raw stride frequency inverse j k) .done
        (finalData bits raw stride frequency inverse j k) := by
  have h:=branch_run bits raw stride frequency inverse j k
  cases he : flag bits raw with
  | false=>
    have h0 : Runs program 1 .branch (evaluated bits raw stride frequency inverse j k) .reject
        (branched bits raw stride frequency inverse j k) := by simpa only [he,Bool.false_eq_true,ite_false] using h
    have h1:=push .reject .done (auxRole .output) false rfl (branched bits raw stride frequency inverse j k)
    have hz : branched bits raw stride frequency inverse j k (auxRole .output)=[] := rfl
    rw [hz] at h1
    refine ⟨2,by unfold tailBudget;omega,?_⟩
    simpa only [finalData,he,Bool.false_eq_true,ite_false] using runs_trans program 1 1 _ _ _ _ _ _ h0 h1
  | true=>
    have h0 : Runs program 1 .branch (evaluated bits raw stride frequency inverse j k) .readOutput
        (branched bits raw stride frequency inverse j k) := by simpa only [he,ite_true] using h
    have h1:=output_call bits raw stride frequency inverse j k
    have h2:=comparison_call bits raw stride frequency inverse j k
    have hh:=runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ h0 h1) h2
    refine ⟨1+(SemiprimeD1StackWordBlockExecution.totalTime (cached bits)+1)+
      (SemiprimeD1StackWordEqualExecution.executionTime
        (readData bits raw stride frequency inverse j k (equalStack .left))
        (readData bits raw stride frequency inverse j k (equalStack .right))+1),?_,?_⟩
    · unfold tailBudget;omega
    · simpa only [finalData,he,ite_true] using hh
end RiemannGaussian.SemiprimeD1StackPublicScaleTail

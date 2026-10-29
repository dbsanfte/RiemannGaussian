/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootPhaseGrid
/-! # Exact acquired-root views and chronological binary grid specification -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootPhaseGridEncoding
open SemiprimeD1StackRootPhaseGrid
/-- Original active-test value specifies an ACTUALLY acquired root output bit. -/
def active (bits:List Bool) : Bool :=SemiprimeD1RecursiveCounter.activeTest
  (SemiprimeD1StackRootRecursiveControlEncoding.scaleValue bits)
  (SemiprimeD1StackRootRecursiveControlEncoding.lambdaValue bits) 0
  (SemiprimeD1StackRootRecursiveControlEncoding.edgeValue bits)
/-- Original cumulative root exponent; never a supplied word/width/count. -/
def exponentValue (bits:List Bool) : Nat :=SemiprimeD1Schedule.exponent
  (SemiprimeD1StackRootRecursiveControlEncoding.lambdaValue bits) 0
/-- Exact framed chronological list produced by the real wrapped binary increments. -/
def grid (a:Nat) : List Bool :=SemiprimeD1TensorTapeCodec.vectorBits
  (SemiprimeD1StackAssignmentOrder.assignments (2^(a+1)) (List.replicate (a+1) false))
/-- Actual retained-root/new-work view used only in execution proofs. -/
def view (root:R.Stack→List Bool) (word counts work out:List Bool) : Stack→List Bool :=
  data root (A.data word [] [] [] out) counts work
/-- Prepared boundary occurs only after the entire N-only root acquisition. -/
def prepared (root:R.Stack→List Bool) : Stack→List Bool :=view root [] [] [] []
/-- Every acquired count byte has been consumed to produce an actual binary zero word. -/
def ready (root:R.Stack→List Bool) (a:Nat) : Stack→List Bool :=
  view root (List.replicate (a+1) false) [] [] []
/-- Exact conditional output: inactive is physically EMPTY, active is the actual full vector. -/
def finished (root:R.Stack→List Bool) (verdict:Bool) (a:Nat) : Stack→List Bool :=
  view root [] [] [] (if verdict then grid a else [])
/-- Real complete original-input final payload retains every119 source word. -/
def result (bits:List Bool) : Stack→List Bool :=finished (R.result bits) (active bits) (exponentValue bits)
/-- Actual final halt has no pending auxiliary flag or return frame. -/
def done (bits:List Bool) : C.State Stack Label :=⟨none,none,none,result bits,[]⟩
/-- The physical source guard is the original branch, without a supplied evaluator. -/
theorem acquired_guard (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) :
    R.result bits R.output=[active bits] :=SemiprimeD1StackRootRecursiveControlOriginal.verdict_original bits hc
/-- The shared physical source exponent is the exact original acquired unary word. -/
theorem acquired_exponent (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) :
    R.result bits (R.sourceStack SemiprimeD1StackRootParameters.exponent)=List.replicate (exponentValue bits) true :=by
  exact (SemiprimeD1StackRootRecursiveControlOriginal.source_preserved bits SemiprimeD1StackRootParameters.exponent).trans
    (SemiprimeD1StackRootParametersOriginal.exponent_original bits hc)
/-- All119 actual root roles survive the entire conditional enumeration. -/
theorem root_preserved (bits:List Bool) (k:R.Stack) : result bits (rootStack k)=R.result bits k :=rfl
/-- The original binary input is retained byte for byte. -/
theorem input_preserved (bits:List Bool) : result bits originalInput=bits :=
  SemiprimeD1StackRootRecursiveControlOriginal.input_preserved bits
/-- No unary2^a object is ever prepared: the executing zero word has exactly a+1 binary digits. -/
theorem ready_word_length (root:R.Stack→List Bool) (a:Nat) :
    (ready root a (enumStack .word)).length=a+1 :=List.length_replicate
/-- Actual input to the conditional stage is the retained source and seven empty new words. -/
theorem afterRoot_eq (bits:List Bool) : afterRoot bits=prepared (R.result bits) :=by
  funext k;cases k with
  | inl k=>rfl
  | inr k=>cases k with
    | inl k=>cases k <;> rfl
    | inr i=>rfl
end RiemannGaussian.SemiprimeD1StackRootPhaseGridEncoding

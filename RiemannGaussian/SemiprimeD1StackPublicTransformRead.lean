/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicTransformQuery
/-! # Actual normalized-product/output read and streaming comparison
No output-word getter, query result, equality truth or component clock is an
executing argument. All bytes come from actual included procedures/caches.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackPublicTransformRead
open SemiprimeD1StackPublicTransform SemiprimeD1StackPublicTransformState
open SemiprimeD1StackPublicTransformWords SemiprimeD1StackPublicTransformGuards
open SemiprimeD1StackPublicTransformMetadata SemiprimeD1StackPublicTransformLoopState
open SemiprimeD1StackPublicTransformPrimitives SemiprimeD1StackPublicTransformQuery
open SemiprimeD1StackProcedureTrace SemiprimeBitArithmetic
open SemiprimeD1StackUnaryDivmod (unary)
open SemiprimeD1TensorTapeCodec (vectorBits)
/-- Actual normalized modular residue, correctness specification only. -/
def productWord (bits raw : List Bool) (second inverse : Bool) (k : ℕ) : List Bool :=
  SemiprimeD1StackResidueMulExecution.residue (normalizer bits second inverse) (dotWord bits raw second inverse k) (cached bits)
/-- Actual output-vector query result, proved by REAL sequential parsing below. -/
def outputWord (bits raw : List Bool) (second : Bool) (k : ℕ) : List Bool := ((outputs (rootData bits) raw second)[k]?).getD []
/-- The actual normalized result is physically copied into the comparator. -/
def productCopied (bits raw : List Bool) (second inverse : Bool) (k : ℕ) : Parts := copied (multiplied bits raw second inverse k) .productResult
/-- Actual numeric multiplier output work is physically drained. -/
def productCleared (bits raw : List Bool) (second inverse : Bool) (k : ℕ) : Parts := set (productCopied bits raw second inverse k) (.multiply M.output) []
/-- Actual query index is copied from the actual remaining-counter tape. -/
def indexReady (bits raw : List Bool) (second inverse : Bool) (k : ℕ) : Parts := copied (productCleared bits raw second inverse k) .index
/-- Actual reader result state, after physical cache scan and all skipped fields. -/
def readDone (bits raw : List Bool) (second inverse : Bool) (k : ℕ) : Parts :=
  {indexReady bits raw second inverse k with reader:=(SemiprimeD1StackJetRead.store
    (vectorBits (outputs (rootData bits) raw second)) [] [] [] [] (outputWord bits raw second k) [] [])}
/-- The actual read output is physically copied, not supplied to equality. -/
def outputCopied (bits raw : List Bool) (second inverse : Bool) (k : ℕ) : Parts := copied (readDone bits raw second inverse k) .outputWord
/-- Every actual read-result byte is physically drained before reader reuse. -/
def outputCleared (bits raw : List Bool) (second inverse : Bool) (k : ℕ) : Parts := set (outputCopied bits raw second inverse k) (.read .output) []
/-- Actual integer equality answer on the two ACTUAL included-procedure outputs. -/
def queryAnswer (bits raw : List Bool) (second inverse : Bool) (k : ℕ) : Bool :=
  decide (bitValue (productWord bits raw second inverse k)=bitValue (outputWord bits raw second k))
/-- Actual completed comparator store, with the computed Boolean present. -/
def compared (bits raw : List Bool) (second inverse : Bool) (k : ℕ) : Parts :=
  {outputCleared bits raw second inverse k with equality:=SemiprimeD1StackAdder.store [] [] [] [queryAnswer bits raw second inverse k]}
/-- The returned equality bit is actually popped for loop/reject control. -/
def popped (bits raw : List Bool) (second inverse : Bool) (k : ℕ) : Parts := set (compared bits raw second inverse k) (.equal .output) []
/-- Actual modular result copy, including full source preservation/restoration. -/
theorem copy_product (bits raw : List Bool) (second inverse : Bool) (k : ℕ) :
    Runs program (5*(productWord bits raw second inverse k).length+4) .copyProduct (data (multiplied bits raw second inverse k))
      .clearProduct (data (productCopied bits raw second inverse k)) :=
  copy_run .productResult .copyProduct .clearProduct rfl (multiplied bits raw second inverse k) rfl rfl
/-- Actual multiplier-result work is fully popped before the next query. -/
theorem clear_product (bits raw : List Bool) (second inverse : Bool) (k : ℕ) :
    Runs program ((productWord bits raw second inverse k).length+1) .clearProduct (data (productCopied bits raw second inverse k))
      .copyIndex (data (productCleared bits raw second inverse k)) := by
  have h:=drain .clearProduct .copyIndex (.multiply M.output) rfl (data (productCopied bits raw second inverse k))
  have hv : data (productCopied bits raw second inverse k) (.multiply M.output)=productWord bits raw second inverse k := rfl
  rw [hv,←data_set] at h;exact h
/-- ACTUAL counter bytes are copied into the sequential reader's physical index. -/
theorem copy_index (bits raw : List Bool) (second inverse : Bool) (k : ℕ) :
    Runs program (5*(unary k).length+4) .copyIndex (data (productCleared bits raw second inverse k))
      .readOutput (data (indexReady bits raw second inverse k)) :=
  copy_run .index .copyIndex .readOutput rfl (productCleared bits raw second inverse k) rfl rfl
/-- Reader cache/index/work are exactly the real parser input. -/
theorem reader_initial (bits raw : List Bool) (second inverse : Bool) (k : ℕ) :
    (indexReady bits raw second inverse k).reader=SemiprimeD1StackJetRead.store
      (vectorBits (outputs (rootData bits) raw second)) [] (unary k) [] [] [] [] [] := by
  funext q;cases q <;> rfl
/-- WHOLE actual output read pays every copied/scanned/skipped field and clears
query/work; no index getter or output-word/count answer is supplied. -/
theorem read_call (bits raw : List Bool) (second inverse : Bool) (k : ℕ) :
    Runs program (SemiprimeD1StackJetReadExecution.totalTime (unary k) (outputs (rootData bits) raw second)+1)
      .readOutput (data (indexReady bits raw second inverse k)) .copyOutput (data (readDone bits raw second inverse k)) := by
  apply SemiprimeD1StackProcedureCallsTrace.included_call program Stack.read Label.read
    (by intro i j h;exact Stack.read.inj h) J.program .start (fun _=>rfl) .readOutput .copyOutput rfl
    (SemiprimeD1StackJetReadExecution.totalTime (unary k) (outputs (rootData bits) raw second))
    (SemiprimeD1StackJetRead.state (some .start) none none (vectorBits (outputs (rootData bits) raw second)) [] (unary k) [] [] [] [] [])
    (SemiprimeD1StackJetRead.state none none none (vectorBits (outputs (rootData bits) raw second)) [] [] [] [] (outputWord bits raw second k) [] [])
    _ _ rfl rfl rfl rfl (by simpa only [unary,List.length_replicate,outputWord] using
      SemiprimeD1StackJetReadExecution.source_run (unary k) (outputs (rootData bits) raw second))
  · constructor
    · intro q;exact congrFun (reader_initial bits raw second inverse k) q
    · intro q _;rfl
  · constructor
    · intro q;rfl
    · intro q hq;cases q <;> first | rfl | exact (hq _ rfl).elim
/-- Actual output read bytes enter the comparator through a REAL copy. -/
theorem copy_output (bits raw : List Bool) (second inverse : Bool) (k : ℕ) :
    Runs program (5*(outputWord bits raw second k).length+4) .copyOutput (data (readDone bits raw second inverse k))
      .clearOutput (data (outputCopied bits raw second inverse k)) :=
  copy_run .outputWord .copyOutput .clearOutput rfl (readDone bits raw second inverse k) rfl rfl
/-- Entire read result is physically popped after its preserving copy. -/
theorem clear_output (bits raw : List Bool) (second inverse : Bool) (k : ℕ) :
    Runs program ((outputWord bits raw second k).length+1) .clearOutput (data (outputCopied bits raw second inverse k))
      .compare (data (outputCleared bits raw second inverse k)) := by
  have h:=drain .clearOutput .compare (.read .output) rfl (data (outputCopied bits raw second inverse k))
  have hv : data (outputCopied bits raw second inverse k) (.read .output)=outputWord bits raw second k := rfl
  rw [hv,←data_set] at h;exact h
/-- Actual compared operands and scratch are exact after physical read/copies. -/
theorem equality_initial (bits raw : List Bool) (second inverse : Bool) (k : ℕ) :
    (outputCleared bits raw second inverse k).equality=SemiprimeD1StackAdder.store
      (productWord bits raw second inverse k) (outputWord bits raw second k) [] [] := by
  funext q;cases q <;> rfl
/-- WHOLE real numeric comparison: unequal zero-padding is handled by the actual
streaming program; neither equality nor operand canonicality is a premise. -/
theorem compare_call (bits raw : List Bool) (second inverse : Bool) (k : ℕ) :
    Runs program (SemiprimeD1StackWordEqualExecution.executionTime (productWord bits raw second inverse k) (outputWord bits raw second k)+1)
      .compare (data (outputCleared bits raw second inverse k)) .branchEqual (data (compared bits raw second inverse k)) := by
  apply included_call program Stack.equal Label.equal (by intro i j h;exact Stack.equal.inj h) E.code .loop
    (fun _=>rfl) .compare .branchEqual rfl
    (SemiprimeD1StackWordEqualExecution.executionTime (productWord bits raw second inverse k) (outputWord bits raw second k))
    (SemiprimeD1StackWordEqual.state (some .loop) none (productWord bits raw second inverse k) (outputWord bits raw second k) [])
    (SemiprimeD1StackWordEqual.state none none [] [] [queryAnswer bits raw second inverse k]) _ _ rfl rfl
    (SemiprimeD1StackWordEqualExecution.source_run _ _ none)
  · constructor
    · intro q;exact congrFun (equality_initial bits raw second inverse k) q
    · intro q _;rfl
  · constructor
    · intro q;rfl
    · intro q hq;cases q <;> first | rfl | exact (hq _ rfl).elim
/-- Actual Boolean pop decides the next iteration or rejection, not supplied truth. -/
theorem compare_branch (bits raw : List Bool) (second inverse : Bool) (k : ℕ) :
    Runs program 1 .branchEqual (data (compared bits raw second inverse k))
      (if queryAnswer bits raw second inverse k then .loop else .reject) (data (popped bits raw second inverse k)) := by
  have h:=pop .branchEqual .bad .reject .loop (.equal .output) rfl (data (compared bits raw second inverse k))
  have hv : data (compared bits raw second inverse k) (.equal .output)=[queryAnswer bits raw second inverse k] := rfl
  rw [hv,←data_set] at h
  cases he : queryAnswer bits raw second inverse k <;>
    simpa only [popped,he,List.head?_cons,List.tail_cons,SemiprimeD1StackBytecode.choose,Bool.false_eq_true,ite_true,ite_false] using h
end RiemannGaussian.SemiprimeD1StackPublicTransformRead

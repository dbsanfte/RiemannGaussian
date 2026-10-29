/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPackedRootInput
/-! # Complete physical bank views for the actual marked-root input join -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPackedRootInputEncoding
open SemiprimeD1StackPackedRootInput
open SemiprimeBitArithmetic (bitValue)
/-- Actual full2270 result, including every old map and rational width. -/
def rootResult (bits : List Bool) (hN : 0<bitValue bits) : R.Stack→List Bool :=
  (SemiprimeD1StackRootPacketInventoryEncoding.done bits hN).data
/-- Every actually computed new207 marked-source word is retained. -/
def markedResult (bits : List Bool) (hN : 0<bitValue bits) (k : Private) : List Bool :=
  (SemiprimeD1StackMarkedRootRecordsExecution.done bits hN).data (.inr k)
/-- Actual complete newly acquired28-word context bank. -/
def contextResult (bits : List Bool) : J.Stack→List Bool :=
  (SemiprimeD1StackPackedRootContextEncoding.done bits).data
/-- Boundary after the real2270 source, with all235 new words still empty. -/
def rootReady (bits : List Bool) (hN : 0<bitValue bits) : Stack→List Bool :=
  bank (rootResult bits hN) (fun _ => []) (fun _ => [])
/-- Boundary after actual ready2011, retaining the entire original2270 bank. -/
def markedReady (bits : List Bool) (hN : 0<bitValue bits) : Stack→List Bool :=
  bank (rootResult bits hN) (markedResult bits hN) (fun _ => [])
/-- Honest context front door, after the real restoring N copy. -/
def contextReady (bits : List Bool) (hN : 0<bitValue bits) : Stack→List Bool :=
  bank (rootResult bits hN) (markedResult bits hN) (J.input bits)
/-- Complete exact2505-word result of all actual calls. -/
def result (bits : List Bool) (hN : 0<bitValue bits) : Stack→List Bool :=
  bank (rootResult bits hN) (markedResult bits hN) (contextResult bits)
/-- True halt has no transient flag and no residual real return cells. -/
def done (bits : List Bool) (hN : 0<bitValue bits) : C.State Stack Label :=
  ⟨none,none,none,result bits hN,[]⟩
/-- Exact update to one actual context operand, preserving both other complete banks. -/
theorem bank_context (root : R.Stack→List Bool) (marked : Private→List Bool) (context : J.Stack→List Bool)
    (k : J.Stack) (xs : List Bool) :
    Function.update (bank root marked context) (contextStack k) xs=
      bank root marked (Function.update context k xs) := by
  dsimp only [bank,contextStack]
  rw [Sum.update_elim_inr,Sum.update_elim_inr]
/-- The SINGLE physical N copy forms exactly the real context source's initial word bank. -/
theorem contextReady_copy (bits : List Bool) (hN : 0<bitValue bits) :
    Function.update (markedReady bits hN) (contextStack J.originalInput) bits=contextReady bits hN := by
  unfold markedReady contextReady
  rw [bank_context]
  apply congrArg (bank (rootResult bits hN) (markedResult bits hN))
  funext k
  rw [SemiprimeD1StackPackedRootContextStorage.input_single]
  by_cases h : k=J.originalInput
  · subst k
    simp only [Function.update_self,ite_true]
  · simp only [Function.update_of_ne h,h,ite_false]
/-- The actual N handoff reads precisely the retained original binary input. -/
theorem marked_N (bits : List Bool) (hN : 0<bitValue bits) :
    markedReady bits hN originalInput=bits := SemiprimeD1PackedRootRetained.retained_N bits hN
/-- The real restoring scratch remains empty after the marked ready continuation. -/
theorem marked_scratch (bits : List Bool) (hN : 0<bitValue bits) :
    markedReady bits hN (rootStack R.copyScratch)=[] := SemiprimeD1PackedRootRetained.scratch_empty bits hN
/-- All original2270 physical words are retained through both new acquisitions. -/
theorem root_retained (bits : List Bool) (hN : 0<bitValue bits) (k : R.Stack) :
    result bits hN (rootStack k)=rootResult bits hN k := rfl
/-- Every new207 marked-source word is retained after the actual context call. -/
theorem marked_retained (bits : List Bool) (hN : 0<bitValue bits) (k : Private) :
    result bits hN (.inr (.inl k))=markedResult bits hN k := rfl
/-- All28 actual new-precision context words survive the enclosing halt. -/
theorem context_retained (bits : List Bool) (hN : 0<bitValue bits) (k : J.Stack) :
    result bits hN (contextStack k)=contextResult bits k := rfl
end RiemannGaussian.SemiprimeD1StackPackedRootInputEncoding

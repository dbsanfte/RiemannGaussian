/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootRecoveryWidthCalls
import RiemannGaussian.SemiprimeD1StackRootRecoveryWidthInput
/-! # Actual stopped original-input metadata supplies both physical width operands -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootRecoveryWidthEncoding
open SemiprimeD1StackRootRecoveryWidth SemiprimeD1StackRootRecoveryWidthInput
open SemiprimeBitArithmetic (bitValue)
/-- Actual whole stopped original-input producer, retaining all2139 words. -/
def rootDone (bits:List Bool) (hN:0 < bitValue bits):C.State R.Stack R.Label:=
  SemiprimeD1StackRootPacketPaddingEncoding.done bits hN
/-- Actual width source stop from precisely the two physically computed metadata values. -/
def widthDone (bits:List Bool):C.State W.Stack W.Label:=
  SemiprimeD1StackRecoveryWidthEncoding.done (O.originalA bits) (O.originalM bits)
/-- Both complete actual banks are retained at the enclosing halt. -/
def result (bits:List Bool) (hN:0 < bitValue bits):Stack→List Bool:=
  data (rootDone bits hN).data (widthDone bits).data
/-- Actual whole2211-role true halt, with both flags and genuine returns cleared. -/
def done (bits:List Bool) (hN:0 < bitValue bits):C.State Stack Label:=⟨none,none,none,result bits hN,[]⟩
/-- Reused scratch is derived empty from the SAME complete stopped root source. -/
theorem root_scratch (bits:List Bool) (hN:0 < bitValue bits):(rootDone bits hN).data R.copyScratch=[]:=by
  have h0:=SemiprimeD1StackRootPacketPaddingExecution.root_retained bits hN
    SemiprimeD1StackRootSelectionAcquire.copyScratch
  exact h0.trans (SemiprimeD1StackRootPacketPaddingEncoding.root_scratch bits hN)
/-- Actual paid metadata transfers form the honest whole width-source initial bank. -/
theorem widthReady_original (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0 < bitValue bits):
    widthReady (rootDone bits hN).data=
      (W.initial (List.replicate (O.originalA bits) true) (List.replicate (O.originalM bits) true)).data:=by
  rw [widthReady_input]
  change (W.initial ((SemiprimeD1StackRootPacketPaddingEncoding.done bits hN).data O.exponentRole)
    ((SemiprimeD1StackRootPacketPaddingEncoding.done bits hN).data O.edgesRole)).data=_
  rw [SemiprimeD1StackRecoveryWidthOriginal.root_exponent bits hc hN,
    SemiprimeD1StackRecoveryWidthOriginal.root_edges bits hN]
  rfl
/-- Both actual source clocks, both acquired-word copies, two real calls and true halt are paid. -/
def timeBound (bits:List Bool) (hN:0 < bitValue bits):Nat:=
  SemiprimeD1StackRootPacketPaddingBounds.runBound bits+widthCopyTime (rootDone bits hN).data+
    SemiprimeD1StackRecoveryWidthBounds.polynomial (O.originalA bits) (O.originalM bits)+3
end RiemannGaussian.SemiprimeD1StackRootRecoveryWidthEncoding

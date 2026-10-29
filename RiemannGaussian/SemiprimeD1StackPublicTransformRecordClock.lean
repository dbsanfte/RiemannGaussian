/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicTransformRecordBounds
import RiemannGaussian.SemiprimeD1StackStaticRecordClock
/-! # Closed concrete actual transform-record clock from physical scope metadata -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackPublicTransformRecordClock
open SemiprimeD1StackPublicTransformRecord SemiprimeD1StackPublicTransformRecordExecution
/-- Fixed degree-eighteen polynomial per physically acquired scalar, plus paid
binary-to-unary ordinal conversion and every original tensor framing byte. -/
def runBound (bits : List Bool) (_second _inverse : Bool) (words : List (List Bool)) (M : Nat) : Nat :=
  SemiprimeD1StackPublicTransformTableBounds.runBound bits words+
    110*(words.length+1)*(M+1)+21*2^words.length+20
/-- The complete actual own source clock, without native report transport. -/
theorem timeBound_le (bits : List Bool) (second inverse : Bool) (words : List (List Bool)) (M : Nat)
    (hl : ∀w∈words,w.length≤M) (hv : ∀w∈words,SemiprimeBitArithmetic.bitValue w≤M) :
    timeBound bits second inverse words≤runBound bits second inverse words M := by
  have h:=SemiprimeD1StackStaticRecordClock.timeBound_le I.static (I.inputTemplate bits second inverse)
    words (T.answer bits second inverse) (T.budget bits) M hl hv
  have ht:=SemiprimeD1StackPublicTransformTableBounds.timeBound_le bits second inverse words
  change SemiprimeD1StackStaticTableBounds.runBound I.static (I.inputTemplate bits second inverse)
    words (T.budget bits)≤_ at ht
  change timeBound bits second inverse words≤_ at h
  unfold runBound
  omega
/-- Every real static-table/scoping/logging transition obeys this closed bound. -/
theorem source_run_bounded (bits : List Bool) (second inverse : Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<SemiprimeBitArithmetic.bitValue bits) (words : List (List Bool))
    (M : Nat) (hl : ∀w∈words,w.length≤M) (hv : ∀w∈words,SemiprimeBitArithmetic.bitValue w≤M)
    (hist out : List Bool) :
    ∃t≤runBound bits second inverse words M,SemiprimeD1StackCalls.run program t
      (initial bits second inverse (SemiprimeD1TensorTapeCodec.vectorBits words) hist out)=
      some (done bits second inverse words hist out) := by
  obtain ⟨t,ht,hr⟩:=source_run bits second inverse hc hN words hist out
  exact ⟨t,ht.trans (timeBound_le bits second inverse words M hl hv),hr⟩
end RiemannGaussian.SemiprimeD1StackPublicTransformRecordClock

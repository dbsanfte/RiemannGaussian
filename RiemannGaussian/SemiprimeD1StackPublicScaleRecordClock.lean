/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicScaleRecordBounds
import RiemannGaussian.SemiprimeD1StackStaticRecordClock
/-! # Closed concrete actual scale-record clock from physical scope metadata -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackPublicScaleRecordClock
open SemiprimeD1StackPublicScaleRecord SemiprimeD1StackPublicScaleRecordExecution
/-- Fixed degree-sixteen polynomial per physically acquired scalar, plus paid
binary-to-unary ordinal conversion and every original tensor framing byte. -/
def runBound (bits stride frequency : List Bool) (_inverse : Bool) (words : List (List Bool)) (M : Nat) : Nat :=
  SemiprimeD1StackPublicScaleTableBounds.runBound bits stride frequency words+
    110*(words.length+1)*(M+1)+21*2^words.length+20
/-- The complete actual own source clock, without native report transport. -/
theorem timeBound_le (bits stride frequency : List Bool) (inverse : Bool) (words : List (List Bool)) (M : Nat)
    (hl : ∀w∈words,w.length≤M) (hv : ∀w∈words,SemiprimeBitArithmetic.bitValue w≤M) :
    timeBound bits stride frequency inverse words≤runBound bits stride frequency inverse words M := by
  have h:=SemiprimeD1StackStaticRecordClock.timeBound_le I.static (I.inputTemplate bits stride frequency inverse)
    words (T.answer bits stride frequency inverse) (T.budget bits stride frequency) M hl hv
  have ht:=SemiprimeD1StackPublicScaleTableBounds.timeBound_le bits stride frequency inverse words
  change SemiprimeD1StackStaticTableBounds.runBound I.static (I.inputTemplate bits stride frequency inverse)
    words (T.budget bits stride frequency)≤_ at ht
  change timeBound bits stride frequency inverse words≤_ at h
  unfold runBound
  omega
/-- Every real static-table/scoping/logging transition obeys this closed bound. -/
theorem source_run_bounded (bits stride frequency : List Bool) (inverse : Bool) (hj : stride=SemiprimeD1StackUnaryDivmod.unary stride.length)
    (hk : frequency=SemiprimeD1StackUnaryDivmod.unary frequency.length)
    (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<SemiprimeBitArithmetic.bitValue bits) (words : List (List Bool))
    (M : Nat) (hl : ∀w∈words,w.length≤M) (hv : ∀w∈words,SemiprimeBitArithmetic.bitValue w≤M)
    (hist out : List Bool) :
    ∃t≤runBound bits stride frequency inverse words M,SemiprimeD1StackCalls.run program t
      (initial bits stride frequency inverse (SemiprimeD1TensorTapeCodec.vectorBits words) hist out)=
      some (done bits stride frequency inverse words hist out) := by
  obtain ⟨t,ht,hr⟩:=source_run bits stride frequency inverse hj hk hc hN words hist out
  exact ⟨t,ht.trans (timeBound_le bits stride frequency inverse words M hl hv),hr⟩
end RiemannGaussian.SemiprimeD1StackPublicScaleRecordClock

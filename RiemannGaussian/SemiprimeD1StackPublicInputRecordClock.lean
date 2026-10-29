/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicInputRecordBounds
import RiemannGaussian.SemiprimeD1StackStaticRecordClock
/-! # Closed concrete actual input-record clock from physical scope metadata -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackPublicInputRecordClock
open SemiprimeD1StackPublicInputRecord SemiprimeD1StackPublicInputRecordExecution
/-- Fixed quadratic polynomial per physically acquired scalar, plus paid
binary-to-unary ordinal conversion and every original tensor framing byte. -/
def runBound (bits indexWord : List Bool) (words : List (List Bool)) (M : Nat) : Nat :=
  SemiprimeD1StackPublicInputTableBounds.runBound bits indexWord words+
    110*(words.length+1)*(M+1)+21*2^words.length+20
/-- The complete actual own source clock, without native report transport. -/
theorem timeBound_le (bits indexWord : List Bool) (words : List (List Bool)) (M : Nat)
    (hl : ∀w∈words,w.length≤M) (hv : ∀w∈words,SemiprimeBitArithmetic.bitValue w≤M) :
    timeBound bits indexWord words≤runBound bits indexWord words M := by
  have h:=SemiprimeD1StackStaticRecordClock.timeBound_le I.static (I.inputTemplate bits indexWord)
    words (T.answer bits indexWord) (T.budget bits indexWord) M hl hv
  have ht:=SemiprimeD1StackPublicInputTableBounds.timeBound_le bits indexWord words
  change SemiprimeD1StackStaticTableBounds.runBound I.static (I.inputTemplate bits indexWord)
    words (T.budget bits indexWord)≤_ at ht
  change timeBound bits indexWord words≤_ at h
  unfold runBound
  omega
/-- Every real static-table/scoping/logging transition obeys this closed bound. -/
theorem source_run_bounded (bits indexWord : List Bool) (hb : bits≠[]) (words : List (List Bool))
    (M : Nat) (hl : ∀w∈words,w.length≤M) (hv : ∀w∈words,SemiprimeBitArithmetic.bitValue w≤M)
    (hist out : List Bool) :
    ∃t≤runBound bits indexWord words M,SemiprimeD1StackCalls.run program t
      (initial bits indexWord (SemiprimeD1TensorTapeCodec.vectorBits words) hist out)=
      some (done bits indexWord words hist out) := by
  obtain ⟨t,ht,hr⟩:=source_run bits indexWord hb words hist out
  exact ⟨t,ht.trans (timeBound_le bits indexWord words M hl hv),hr⟩
end RiemannGaussian.SemiprimeD1StackPublicInputRecordClock

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackStaticRecordBounds
/-! # Explicit source clock from the same acquired bytes and checker trace -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeD1StackStaticRecordClock
open SemiprimeD1StackStaticRecord SemiprimeD1StackStaticRecordExecution
variable {K L : Type} [DecidableEq K] [Fintype K] (s : T.Static K L)
omit [DecidableEq K] [Fintype K] in
/-- Actual unary scope bytes include every zero ordinal and framing delimiter. -/
theorem ports_length (words : List (List Bool)) (M : Nat)
    (hv : ∀w∈words,SemiprimeBitArithmetic.bitValue w≤M) :
    (S.result words).length≤words.length*(2*M+2)+1 := by
  have h:=SemiprimeD1StackPortOrdinalStreamBounds.bank_length
    (SemiprimeD1StackPortOrdinalStreamExecution.unaryWords words) M (by
      intro w hw
      obtain ⟨v,hv',rfl⟩:=List.mem_map.mp hw
      simpa only [List.length_replicate] using hv v hv')
  simpa only [S.result,SemiprimeD1StackPortOrdinalStreamExecution.unaryWords,List.length_map] using h
omit [DecidableEq K] in
/-- Same complete source clock: static-checker whole-table bit time, actual
scope width/value conversion and one copy of every literal tensor byte. -/
theorem timeBound_le (template : K→List Bool) (words : List (List Bool))
    (answer : List Bool→Bool) (budget : Nat→Nat) (M : Nat)
    (hl : ∀w∈words,w.length≤M) (hv : ∀w∈words,SemiprimeBitArithmetic.bitValue w≤M) :
    timeBound s template words answer budget≤
      SemiprimeD1StackStaticTableBounds.runBound s template words budget+
        110*(words.length+1)*(M+1)+21*2^words.length+20 := by
  have ht:=SemiprimeD1StackStaticTableBounds.timeBound_le s template words answer budget
  have hs:=SemiprimeD1StackPortOrdinalStreamBounds.timeBound_le words M hl hv
  have hp:=ports_length words M hv
  have hb:=SemiprimeD1StackStaticTableBounds.tree_length answer [] words.length
  change (SemiprimeD1StackStaticTableExecution.outputTape answer words).length+1≤7*2^words.length at hb
  unfold timeBound R.recordTime
  nlinarith
end RiemannGaussian.SemiprimeD1StackStaticRecordClock

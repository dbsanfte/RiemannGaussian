/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPortOrdinalStreamComponents
import RiemannGaussian.SemiprimeD1StackDigitBankSpec
/-! # Whole physical binary-ID stream conversion -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackPortOrdinalStreamExecution
open SemiprimeD1StackPortOrdinalStream SemiprimeD1StackPortOrdinalStreamComponents
open SemiprimeD1StackProcedureTrace
open SemiprimeD1StackDigitBankSpec (entries entries_vectorBits)
open SemiprimeSourceHistogramKeyBits (frame)
local notation "ctl" => SemiprimeD1StackPortOrdinalStream.Label.control
/-- Exact metadata-only converted words, never a runtime supplier. -/
def unaryWords (words:List (List Bool)) : List (List Bool) :=
  words.map fun w=>List.replicate (SemiprimeBitArithmetic.bitValue w) true
/-- Every parser, unary conversion, logger and cleanup is retained. -/
def loopBudget : List (List Bool)→Nat
  | [] => 1
  | w::ws => 21*SemiprimeBitArithmetic.bitValue w+14*w.length+40+loopBudget ws
/-- The actual EOF-controlled loop processes every record, including zero IDs. -/
theorem loop_run (words:List (List Bool)) (bank hist:List Bool) :
    ∃t≤loopBudget words,Runs program t (ctl .next)
      (data bank (SemiprimeD1TensorTapeCodec.vectorBits words) [] [] [] hist [])
      (ctl .finish) (data bank [] [] [] [] ((entries (unaryWords words)).reverse++hist) []) := by
  induction words generalizing hist with
  | nil =>
    refine ⟨1,le_refl _,?_⟩
    simp only [unaryWords,List.map_nil,entries,List.reverse_nil,List.nil_append]
    apply one_base program (ctl .next) (ctl .finish)
      (.pop .reader (ctl .finish) (ctl .finish) (ctl .parse)) _ _ rfl
    · rfl
    · funext k;cases k <;> rfl
  | cons w ws ih =>
    let tail:=SemiprimeD1TensorTapeCodec.vectorBits ws
    let u:=List.replicate (SemiprimeBitArithmetic.bitValue w) true
    let nextHist:=(true::frame u []).reverse++hist
    have h0 : Runs program 1 (ctl .next)
        (data bank (SemiprimeD1TensorTapeCodec.vectorBits (w::ws)) [] [] [] hist [])
        (ctl .parse) (data bank (frame w tail) [] [] [] hist []) := by
      apply one_base program (ctl .next) (ctl .parse)
        (.pop .reader (ctl .finish) (ctl .finish) (ctl .parse)) _ _ rfl
      · rfl
      · funext k;cases k <;> rfl
    have h1:=field_call bank w tail hist
    have h2:=clear_valid bank tail w hist
    obtain ⟨a,ha,h3⟩:=unary_call bank tail w hist
    obtain ⟨b,hb,h4⟩:=log_call bank tail u hist
    have h5:=clear_unary bank tail u nextHist
    obtain ⟨t,ht,h6⟩:=ih nextHist
    have h:=runs_trans program _ _ _ _ _ _ _ _
      (runs_trans program _ _ _ _ _ _ _ _
        (runs_trans program _ _ _ _ _ _ _ _
          (runs_trans program _ _ _ _ _ _ _ _
            (runs_trans program _ _ _ _ _ _ _ _
              (runs_trans program _ _ _ _ _ _ _ _ h0 h1) h2) h3) h4) h5) h6
    refine ⟨1+(8*w.length+7)+1+a+b+(u.length+1)+t,?_,?_⟩
    · have hu:u.length=SemiprimeBitArithmetic.bitValue w:=List.length_replicate
      simp only [loopBudget]
      omega
    · simpa only [unaryWords,List.map_cons,entries,List.reverse_append,List.append_assoc] using h


/-- Explicit whole trace allowance includes the final physical log reversal. -/
def timeBound (words:List (List Bool)) : Nat :=
  5*(SemiprimeD1TensorTapeCodec.vectorBits words).length+loopBudget words+
    2*(entries (unaryWords words)).length+7
/-- Exact halt keeps the original binary bank and clears every private role. -/
def done (words:List (List Bool)) : C.State Stack Label :=
  ⟨none,none,none,data (SemiprimeD1TensorTapeCodec.vectorBits words) [] [] [] [] []
    (SemiprimeD1StackPortOrdinalStream.result words),[]⟩
/-- Closed actual stream execution; neither decoded ports nor unary answers enter. -/
theorem source_run (words:List (List Bool)) :
    ∃t≤timeBound words,SemiprimeD1StackCalls.run program t
      (initial (SemiprimeD1TensorTapeCodec.vectorBits words))=some (done words) := by
  let bank:=SemiprimeD1TensorTapeCodec.vectorBits words
  let encoded:=entries (unaryWords words)
  have h0:=copy_call bank
  obtain ⟨m,hm,h1⟩:=loop_run words bank []
  simp only [List.append_nil] at h1
  have h2 : Runs program 1 (ctl .finish) (data bank [] [] [] [] encoded.reverse [])
      (ctl .reverse) (data bank [] [] [] [] encoded.reverse [false]) := by
    apply one_base program (ctl .finish) (ctl .reverse) (.push .output false (ctl .reverse)) _ _ rfl
    · rfl
    · funext k;cases k <;> rfl
  have h3:=reverse_run encoded.reverse bank [false]
  simp only [List.length_reverse,List.reverse_reverse] at h3
  have h:=runs_trans program _ _ _ _ _ _ _ _
    (runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ h0 h1) h2) h3
  obtain ⟨finish,hr,ho⟩:=h [] (initial bank) ⟨rfl,by funext k;cases k <;> rfl,rfl⟩
  have he:=halt_run program (ctl .done) rfl
    (data bank [] [] [] [] [] (encoded++[false])) [] finish ho
  refine ⟨(5*bank.length+4)+m+1+(2*encoded.length+1)+1,?_,?_⟩
  · change (5*bank.length+4)+m+1+(2*encoded.length+1)+1 ≤
      5*bank.length+loopBudget words+2*encoded.length+7
    omega
  · rw [SemiprimeD1StackReturnLink.run_add,hr,Option.bind_some,he]
    have hvec:encoded++[false]=SemiprimeD1StackPortOrdinalStream.result words := entries_vectorBits _
    rw [hvec]
    rfl
end RiemannGaussian.SemiprimeD1StackPortOrdinalStreamExecution

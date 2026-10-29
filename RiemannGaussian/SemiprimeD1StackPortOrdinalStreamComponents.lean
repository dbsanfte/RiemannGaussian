/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPortOrdinalStream
import RiemannGaussian.SemiprimeD1StackPhysicalLoops
/-! # Actual component calls for binary ordinal stream conversion -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackPortOrdinalStreamComponents
open SemiprimeD1StackPortOrdinalStream SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
open SemiprimeD1StackProcedureTrace (runs_trans)
local notation "ctl" => SemiprimeD1StackPortOrdinalStream.Label.control
/-- Clean loop payload; all included private scratch is physically empty. -/
def data (bank reader word valid unary hist out:List Bool) : Stack→List Bool
  | .bank => bank | .reader => reader | .word => word | .valid => valid
  | .unary => unary | .history => hist | .output => out | _ => []
/-- The actual parser reads one field, including a zero-length field. -/
theorem field_call (bank word tail hist:List Bool) :
    Runs program (8*word.length+7) (ctl .parse) (data bank (frame word tail) [] [] [] hist [])
      (ctl .clearValid) (data bank tail word [true] [] hist []) := by
  apply included_call program fieldStack Label.field fieldStack_injective Field.code
    (Field.active .tagPop (none,false)) (fun _=>rfl) (ctl .parse) (ctl .clearValid) rfl
    (8*word.length+6) (Field.initial (frame word tail) [])
    (⟨none,none,Sum.elim (SemiprimeD1TensorTapeFieldMachine.contents tail [] word) (fun _=>[true])⟩:
      SemiprimeD1StackBytecode.State Field.Stack Field.Label)
    (data bank (frame word tail) [] [] [] hist []) (data bank tail word [true] [] hist [])
  · rfl
  · rfl
  · exact SemiprimeD1TensorTapeFieldBytecode.framed_run word tail []
  · constructor
    · intro k;cases k with
      | inl k => cases k <;> rfl
      | inr k => cases k;rfl
    · intro k _;rfl
  · constructor
    · intro k;cases k with
      | inl k => cases k <;> rfl
      | inr k => cases k;rfl
    · intro k hk;cases k <;> first
        | rfl
        | exact False.elim (hk (.inl .input) rfl)
        | exact False.elim (hk (.inl .output) rfl)
        | exact False.elim (hk (.inl .scratch) rfl)
        | exact False.elim (hk (.inr ()) rfl)
/-- Actual binary-to-unary conversion, retaining no native decoded answer. -/
theorem unary_call (bank tail word hist:List Bool) :
    ∃m≤7*SemiprimeBitArithmetic.bitValue word+6*word.length+4,
      Runs program m (ctl .convert) (data bank tail word [] [] hist []) (ctl .log)
        (data bank tail [] [] (List.replicate (SemiprimeBitArithmetic.bitValue word) true) hist []) := by
  let t:=2*word.length+1+SemiprimeD1StackUnaryCounterExecution.loopTime word.reverse 0
  refine ⟨t+1,by have h:=SemiprimeD1StackUnaryCounterExecution.source_time word;omega,?_⟩
  apply included_call program unaryStack Label.unary unaryStack_injective Unary.code .reverse
    (fun _=>rfl) (ctl .convert) (ctl .log) rfl t
    (SemiprimeD1StackUnaryCounter.state (some .reverse) none word [] [] [])
    (SemiprimeD1StackUnaryCounter.state none none [] [] []
      (List.replicate (SemiprimeBitArithmetic.bitValue word) true))
    (data bank tail word [] [] hist [])
    (data bank tail [] [] (List.replicate (SemiprimeBitArithmetic.bitValue word) true) hist [])
  · rfl
  · rfl
  · exact SemiprimeD1StackUnaryCounterExecution.source_run word
  · constructor
    · intro k;cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k;cases k <;> rfl
    · intro k hk;cases k <;> first
        | rfl
        | exact False.elim (hk .left rfl)
        | exact False.elim (hk .right rfl)
        | exact False.elim (hk .scratch rfl)
        | exact False.elim (hk .output rfl)


/-- The original binary vector is physically copied and retained. -/
theorem copy_call (bank:List Bool) :
    Runs program (5*bank.length+4) (ctl .start) (data bank [] [] [] [] [] [])
      (ctl .next) (data bank bank [] [] [] [] []) := by
  apply included_call program copyStack Label.copy copyStack_injective SemiprimeD1StackCopy.code 0
    (fun _=>rfl) (ctl .start) (ctl .next) rfl (5*bank.length+3)
    (SemiprimeD1StackCopy.state 0 none bank [] []) (SemiprimeD1StackCopy.done bank bank)
    (data bank [] [] [] [] [] []) (data bank bank [] [] [] [] [])
  · rfl
  · rfl
  · simpa only [List.append_nil] using SemiprimeD1StackCopy.copy_words bank [] none
  · constructor
    · intro k;fin_cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k;fin_cases k <;> rfl
    · intro k hk;cases k <;> first
        | rfl
        | exact False.elim (hk 1 rfl)
/-- Empty unary words are logged as genuine empty vector fields. -/
theorem log_call (bank tail word hist:List Bool) :
    ∃m≤6*(2*word.length+3)+1,Runs program m (ctl .log)
      (data bank tail [] [] word hist []) (ctl .clearUnary)
      (data bank tail [] [] word ((true::frame word []).reverse++hist) []) := by
  obtain ⟨m,hm,hr⟩:=SemiprimeD1StackAssignmentBody.body_run word hist
  refine ⟨m+1,by omega,?_⟩
  apply included_call program bodyStack Label.body bodyStack_injective Body.code Body.entry
    (fun _=>rfl) (ctl .log) (ctl .clearUnary) rfl m
    (⟨some Body.entry,none,SemiprimeD1StackAssignmentBody.contents word [] hist⟩:
      SemiprimeD1StackBytecode.State Body.Stack Body.Label)
    (⟨none,none,SemiprimeD1StackAssignmentBody.contents word [] ((true::frame word []).reverse++hist)⟩:
      SemiprimeD1StackBytecode.State Body.Stack Body.Label)
    (data bank tail [] [] word hist [])
    (data bank tail [] [] word ((true::frame word []).reverse++hist) [])
  · rfl
  · rfl
  · exact hr
  · constructor
    · intro k;cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k;cases k <;> rfl
    · intro k hk;cases k <;> first
        | rfl
        | exact False.elim (hk .history rfl)

/-- Clear the physically written parser-valid bit before conversion. -/
theorem clear_valid (bank tail word hist:List Bool) :
    Runs program 1 (ctl .clearValid) (data bank tail word [true] [] hist [])
      (ctl .convert) (data bank tail word [] [] hist []) := by
  apply one_base program (ctl .clearValid) (ctl .convert)
    (.pop .valid (ctl .convert) (ctl .convert) (ctl .convert)) _ _ rfl
  · rfl
  · funext k;cases k <;> rfl
/-- Physically clear the restored unary word after it has been logged. -/
theorem clear_unary (bank tail word hist:List Bool) :
    Runs program (word.length+1) (ctl .clearUnary) (data bank tail [] [] word hist [])
      (ctl .next) (data bank tail [] [] [] hist []) := by
  have h:=SemiprimeD1StackPhysicalLoops.drain program (ctl .clearUnary) (ctl .next) Stack.unary rfl
    (data bank tail [] [] [] hist []) word
  have hi : Function.update (data bank tail [] [] [] hist []) Stack.unary word=
      data bank tail [] [] word hist [] := by
    funext k;cases k <;> simp [Function.update,data]
  have ho : Function.update (data bank tail [] [] [] hist []) Stack.unary []=
      data bank tail [] [] [] hist [] := Function.update_eq_self _ _
  rw [hi,ho] at h
  exact h
/-- One physical reversal restores the original record ordering. -/
theorem reverse_run (hist bank out:List Bool) :
    Runs program (2*hist.length+1) (ctl .reverse) (data bank [] [] [] [] hist out)
      (ctl .done) (data bank [] [] [] [] [] (hist.reverse++out)) := by
  induction hist generalizing out with
  | nil =>
    apply one_base program (ctl .reverse) (ctl .done)
      (.pop .history (ctl .done) (ctl (.emit false)) (ctl (.emit true))) _ _ rfl
    · rfl
    · funext k;cases k <;> rfl
  | cons b hist ih =>
    have h0 : Runs program 1 (ctl .reverse) (data bank [] [] [] [] (b::hist) out)
        (ctl (.emit b)) (data bank [] [] [] [] hist out) := by
      apply one_base program (ctl .reverse) (ctl (.emit b))
        (.pop .history (ctl .done) (ctl (.emit false)) (ctl (.emit true))) _ _ rfl
      · cases b <;> rfl
      · funext k;cases k <;> rfl
    have h1 : Runs program 1 (ctl (.emit b)) (data bank [] [] [] [] hist out)
        (ctl .reverse) (data bank [] [] [] [] hist (b::out)) := by
      apply one_base program (ctl (.emit b)) (ctl .reverse) (.push .output b (ctl .reverse)) _ _ rfl
      · rfl
      · funext k;cases k <;> rfl
    have h:=runs_trans program _ _ _ _ _ _ _ _
      (runs_trans program _ _ _ _ _ _ _ _ h0 h1) (ih (b::out))
    simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append,
      show (1+1)+(2*hist.length+1)=2*(hist.length+1)+1 by omega] using h
end RiemannGaussian.SemiprimeD1StackPortOrdinalStreamComponents

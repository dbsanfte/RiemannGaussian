/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1TensorTapeFieldMachine

/-! # Actual finite-stack execution of the existing framed-field parser
The correctness target is the literal KeyBits.split used by TensorTape parsing.
Transition counts refer to the actual fixed Mathlib TM2 program.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RiemannGaussian.SemiprimeD1TensorTapeFieldExecution
open Turing Turing.TM2 SemiprimeD1TensorTapeFieldMachine
open SemiprimeSourceHistogramKeyBits

/-- A false framing tag is consumed, setting only the finite valid flag. -/
theorem tag_false (v : Registers) (xs rev out : List Bool) :
    step (config (some .tagPop) v (false::xs) rev out)=
      some (config (some .tagBranch) (some false,true) xs rev out) := by
  simp [SemiprimeD1TensorTapeFieldMachine.step,program,config,contents,TM2.step,TM2.stepAux]

/-- A true framing tag requests one actual data bit. -/
theorem tag_true (v : Registers) (xs rev out : List Bool) :
    step (config (some .tagPop) v (true::xs) rev out)=
      some (config (some .tagBranch) (some true,false) xs rev out) := by
  simp [SemiprimeD1TensorTapeFieldMachine.step,program,config,contents,TM2.step,TM2.stepAux]

/-- EOF is tested physically and records invalid termination. -/
theorem tag_nil (v : Registers) (rev out : List Bool) :
    step (config (some .tagPop) v [] rev out)=
      some (config (some .tagBranch) (none,false) [] rev out) := by
  simp [SemiprimeD1TensorTapeFieldMachine.step,program,config,contents,TM2.step,TM2.stepAux]

/-- Fixed finite tag-control branch. -/
theorem branch_tag_true (xs rev out : List Bool) :
    step (config (some .tagBranch) (some true,false) xs rev out)=
      some (config (some .dataPop) (some true,false) xs rev out) := by
  rfl

/-- False tags transition to the actual reversing copy loop. -/
theorem branch_tag_false (xs rev out : List Bool) :
    step (config (some .tagBranch) (some false,true) xs rev out)=
      some (config (some .reversePop) (some false,true) xs rev out) := by rfl

/-- EOF also transitions to reversing, with invalid status retained. -/
theorem branch_tag_nil (rev out : List Bool) :
    step (config (some .tagBranch) (none,false) [] rev out)=
      some (config (some .reversePop) (none,false) [] rev out) := by rfl

/-- Actual data-bit pop; no whole word is read in a primitive. -/
theorem data_cons (v : Registers) (b : Bool) (xs rev out : List Bool) :
    step (config (some .dataPop) v (b::xs) rev out)=
      some (config (some .dataBranch) (some b,false) xs rev out) := by
  simp [SemiprimeD1TensorTapeFieldMachine.step,program,config,contents,TM2.step,TM2.stepAux]

/-- A missing data bit is invalid, including a dangling true tag. -/
theorem data_nil (v : Registers) (rev out : List Bool) :
    step (config (some .dataPop) v [] rev out)=
      some (config (some .dataBranch) (none,false) [] rev out) := by
  simp [SemiprimeD1TensorTapeFieldMachine.step,program,config,contents,TM2.step,TM2.stepAux]

/-- Available data uses the fixed copy instruction. -/
theorem branch_data (b : Bool) (xs rev out : List Bool) :
    step (config (some .dataBranch) (some b,false) xs rev out)=
      some (config (some .dataPush) (some b,false) xs rev out) := by rfl

/-- Missing data exits to the actual copy-reversal loop. -/
theorem branch_data_nil (rev out : List Bool) :
    step (config (some .dataBranch) (none,false) [] rev out)=
      some (config (some .reversePop) (none,false) [] rev out) := by rfl

/-- Each copied bit is an actual single-symbol stack push. -/
theorem push_data (b : Bool) (xs rev out : List Bool) :
    step (config (some .dataPush) (some b,false) xs rev out)=
      some (config (some .tagPop) (some b,false) xs (b::rev) out) := by
  simp [SemiprimeD1TensorTapeFieldMachine.step,program,config,contents,TM2.step,TM2.stepAux]

/-- The reverse loop pops exactly one actual bit. -/
theorem reverse_cons (v : Registers) (b : Bool) (xs rev out : List Bool) :
    step (config (some .reversePop) v xs (b::rev) out)=
      some (config (some .reverseBranch) (some b,v.2) xs rev out) := by
  simp [SemiprimeD1TensorTapeFieldMachine.step,program,config,contents,TM2.step,TM2.stepAux]

/-- The empty reverse stack is tested physically. -/
theorem reverse_nil (v : Registers) (xs out : List Bool) :
    step (config (some .reversePop) v xs [] out)=
      some (config (some .reverseBranch) (none,v.2) xs [] out) := by
  simp [SemiprimeD1TensorTapeFieldMachine.step,program,config,contents,TM2.step,TM2.stepAux]

/-- A reverse-loop data bit selects the fixed output-push label. -/
theorem branch_reverse (b valid : Bool) (xs rev out : List Bool) :
    step (config (some .reverseBranch) (some b,valid) xs rev out)=
      some (config (some .reversePush) (some b,valid) xs rev out) := by rfl

/-- A completed reverse loop halts, retaining the finite valid flag and tape suffix. -/
theorem branch_reverse_nil (valid : Bool) (xs out : List Bool) :
    step (config (some .reverseBranch) (none,valid) xs [] out)=
      some (config none (none,valid) xs [] out) := by rfl

/-- Forward output is produced by actual one-bit stack pushes. -/
theorem push_reverse (b valid : Bool) (xs rev out : List Bool) :
    step (config (some .reversePush) (some b,valid) xs rev out)=
      some (config (some .reversePop) (some b,valid) xs rev (b::out)) := by
  simp [SemiprimeD1TensorTapeFieldMachine.step,program,config,contents,TM2.step,TM2.stepAux]

/-- Reversing is an actual pop/branch/push loop, paying every copied output bit. -/
theorem reverse_exec (v : Registers) (xs rev out : List Bool) :
    Executes (3*rev.length+2) (config (some .reversePop) v xs rev out)
      (config none (none,v.2) xs [] (rev.reverse++out)) := by
  induction rev generalizing v out with
  | nil =>
    exact Executes.next (reverse_nil v xs out)
      (Executes.next (branch_reverse_nil v.2 xs out) (Executes.refl _))
  | cons b rev ih =>
    have head : Executes 3 (config (some .reversePop) v xs (b::rev) out)
        (config (some .reversePop) (some b,v.2) xs rev (b::out)) :=
      Executes.next (reverse_cons v b xs rev out)
        (Executes.next (branch_reverse b v.2 xs rev out)
          (Executes.next (push_reverse b v.2 xs rev out) (Executes.refl _)))
    have all:=head.trans (ih (some b,v.2) (b::out))
    simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append,
      Nat.mul_add,Nat.mul_one,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using all

/-- One actual framed data pair uses five fixed machine transitions. -/
theorem pair_exec (v : Registers) (b : Bool) (xs rev out : List Bool) :
    Executes 5 (config (some .tagPop) v (true::b::xs) rev out)
      (config (some .tagPop) (some b,false) xs (b::rev) out) :=
  Executes.next (tag_true v (b::xs) rev out)
    (Executes.next (branch_tag_true (b::xs) rev out)
      (Executes.next (data_cons (some true,false) b xs rev out)
        (Executes.next (branch_data b xs rev out)
          (Executes.next (push_data b xs rev out) (Executes.refl _)))))

/-- Actual tag/EOF path count, a proof measure rather than a machine register. -/
def fieldSteps : List Bool → ℕ
  | [] => 4
  | false::_ => 4
  | true::[] => 6
  | true::_::xs => 8+fieldSteps xs

/-- The complete actual machine computes the existing parser on every tape,
including missing tags/data, while preserving the exact unconsumed suffix. -/
theorem parse_exec (xs : List Bool) (v : Registers) (rev out : List Bool) :
    Executes (3*rev.length+fieldSteps xs) (config (some .tagPop) v xs rev out)
      (config none (none,(split xs).valid) (split xs).rest []
        (rev.reverse++(split xs).first++out)) := by
  induction xs using split.induct generalizing v rev out with
  | case1 =>
    have head : Executes 2 (config (some .tagPop) v [] rev out)
        (config (some .reversePop) (none,false) [] rev out) :=
      Executes.next (tag_nil v rev out)
        (Executes.next (branch_tag_nil rev out) (Executes.refl _))
    have all:=head.trans (reverse_exec (none,false) [] rev out)
    convert all using 1 <;>
      simp only [fieldSteps,split,List.append_nil]
    all_goals omega
  | case2 ys =>
    have head : Executes 2 (config (some .tagPop) v (false::ys) rev out)
        (config (some .reversePop) (some false,true) ys rev out) :=
      Executes.next (tag_false v ys rev out)
        (Executes.next (branch_tag_false ys rev out) (Executes.refl _))
    have all:=head.trans (reverse_exec (some false,true) ys rev out)
    convert all using 1 <;>
      simp only [fieldSteps,split,List.append_nil]
    all_goals omega
  | case3 =>
    have head : Executes 4 (config (some .tagPop) v [true] rev out)
        (config (some .reversePop) (none,false) [] rev out) :=
      Executes.next (tag_true v [] rev out)
        (Executes.next (branch_tag_true [] rev out)
          (Executes.next (data_nil (some true,false) rev out)
            (Executes.next (branch_data_nil rev out) (Executes.refl _))))
    have all:=head.trans (reverse_exec (none,false) [] rev out)
    convert all using 1 <;>
      simp only [fieldSteps,split,List.append_nil]
    all_goals omega
  | case4 b xs ih =>
    have all:=(pair_exec v b xs rev out).trans (ih (some b,false) (b::rev) out)
    convert all using 1 <;>
      simp only [fieldSteps,split,List.length_cons,List.reverse_cons,List.append_assoc,
        List.singleton_append,Nat.mul_add,Nat.mul_one]
    all_goals omega

/-- Actual transition count is linear even for malformed input and arbitrary tails. -/
theorem fieldSteps_le (xs : List Bool) : fieldSteps xs ≤ 4*xs.length+6 := by
  induction xs using split.induct with
  | case1 => decide
  | case2 ys => simp only [fieldSteps,List.length_cons];omega
  | case3 => decide
  | case4 b xs ih => simp only [fieldSteps,List.length_cons];omega

/-- Exact framed-field outputs use literal Boolean stacks and finite status only. -/
def final (xs : List Bool) : Cfg Alphabet PC Registers :=
  config none (none,(split xs).valid) (split xs).rest [] (split xs).first

/-- Mathlib actual-time certificate for the executed parser, not a scalar-cost annotation. -/
def splitInTime (xs : List Bool) :
    StateTransition.EvalsToInTime SemiprimeD1TensorTapeFieldMachine.step
      (config (some .tagPop) (none,false) xs [] []) (some (final xs)) (4*xs.length+6) := by
  have h:=parse_exec xs (none,false) [] []
  simp only [List.length_nil,Nat.mul_zero,Nat.zero_add,List.reverse_nil,List.nil_append,List.append_nil] at h
  exact ⟨h.inTime.toEvalsTo,fieldSteps_le xs⟩

/-- On the actual TensorTape coefficient-field layout, both payload and tail are exact. -/
theorem actual_field (word tail : List Bool) :
    (final (frame word tail)).stk Stack.output=word ∧
      (final (frame word tail)).stk Stack.input=tail ∧
      (final (frame word tail)).var.2=true := by
  have h:=split_frame word tail
  exact ⟨h.1,h.2.1,h.2.2⟩

end RiemannGaussian.SemiprimeD1TensorTapeFieldExecution

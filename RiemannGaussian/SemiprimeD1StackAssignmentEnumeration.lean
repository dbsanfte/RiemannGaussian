/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackAssignmentLoopExecution
import RiemannGaussian.SemiprimeD1StackAssignmentOrder
import Mathlib.Tactic.Linarith

/-! # Exact executed assignment enumeration before physical overflow
The fixed program calls its literal logging/restoration body and actual lowered
incrementer. This proof joins the whole loop, not an assumed body/count callback.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace RiemannGaussian.SemiprimeD1StackAssignmentEnumeration
open SemiprimeD1StackAssignmentLoop SemiprimeD1StackAssignmentLoopExecution
open SemiprimeD1StackAssignmentOrder
open SemiprimeD1StackIncrement (wrapped overflow)
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeSourceHistogramKeyBits (frame)
local notation "ctl" => SemiprimeD1StackAssignmentLoop.control

/-- Exact concatenation of the physically logged vector entry. -/
theorem log_cons (word history output : List Bool) (tail : List (List Bool)) :
    (((true::frame word []).reverse++history).reverse++vectorBits tail)++output=
      (history.reverse++vectorBits (word::tail))++output := by
  have hf : frame word (vectorBits tail)=frame word []++vectorBits tail := by
    simpa using SemiprimeD1TensorTapeVectorMachine.frame_append word [] (vectorBits tail)
  simp [vectorBits,hf,List.reverse_append,List.append_assoc]

/-- Actual loop time budget; original word/history dimensions only. -/
def budget (word history : List Bool) : ℕ :=
  100*(word.length+1)*remaining word+2*history.length+10

/-- The whole actual loop executes exactly the before-overflow assignment catalogue.
Each induction step executes the included body and actual incrementer once. -/
theorem loop_run_from (R : ℕ) (word history output : List Bool)
    (flag : Option Bool) (returned : Option Label) (frames : List Label)
    (hR : remaining word=R) :
    ∃m≤budget word history,C.run code m
      (state (ctl .bodyCall) flag returned word [] [] history output frames)=
      some ⟨none,none,none,data [] [] [] []
        ((history.reverse++vectorBits (assignments R word))++output),frames⟩ := by
  induction R using Nat.strong_induction_on generalizing word history flag returned with
  | h R ih =>
    have hpos := remaining_pos word
    let logged := (true::frame word []).reverse++history
    obtain ⟨m1,hm1,f1,r1,hbody⟩ := body_call word history output flag returned frames
    change C.run code m1 (state (ctl .bodyCall) flag returned word [] [] history output frames)=
      some (state (ctl .incCall) f1 r1 word [] [] logged output frames) at hbody
    obtain ⟨m2,hm2,f2,r2,hinc⟩ := increment_call word logged output f1 r1 frames
    cases ho : overflow word with
    | true =>
      have hlast := overflow_remaining word ho
      have hRone : R=1 := by omega
      have hend := finish_run (wrapped word) logged output f2 r2 frames
      have hinc' : C.run code m2 (state (ctl .incCall) f1 r1 word [] [] logged output frames)=
          some (state (ctl .afterInc) f2 r2 [] [] (true::wrapped word) logged output frames) := by
        simpa only [ho] using hinc
      have hr := run_trans hbody (run_trans hinc' hend)
      refine ⟨m1+(m2+((wrapped word).length+2*logged.length+7)),?_,?_⟩
      · unfold budget
        simp only [SemiprimeD1StackIncrement.wrapped_length] at hm1 hm2 ⊢
        dsimp [logged]
        simp only [List.length_append,List.length_reverse,List.length_cons,
          SemiprimeSourceHistogramKeyBits.frame_length,List.length_nil]
        rw [hlast]
        nlinarith
      · rw [hRone]
        simpa only [assignments,vectorBits] using hr.trans
          (congrArg some (congrArg (fun xs => (⟨none,none,none,data [] [] [] [] xs,frames⟩ : C.State Stack Label))
            (by simpa [logged,vectorBits,List.append_assoc] using log_cons word history output [])))
    | false =>
      have hstep := remaining_step word ho
      have hsmall : remaining (wrapped word)<R := by omega
      obtain ⟨m3,hm3,hrest⟩ := ih (remaining (wrapped word)) hsmall
        (wrapped word) logged none r2 rfl
      have hinc' : C.run code m2 (state (ctl .incCall) f1 r1 word [] [] logged output frames)=
          some (state (ctl .afterInc) f2 r2 [] [] (false::wrapped word) logged output frames) := by
        simpa only [ho] using hinc
      have hcontinue := continue_run (wrapped word) logged output f2 r2 frames
      have hr := run_trans hbody (run_trans hinc' (run_trans hcontinue hrest))
      refine ⟨m1+(m2+(4*(wrapped word).length+3+m3)),?_,?_⟩
      · unfold budget at hm3 ⊢
        simp only [SemiprimeD1StackIncrement.wrapped_length] at hm3 ⊢
        dsimp [logged] at hm3
        simp only [List.length_append,List.length_reverse,List.length_cons,
          SemiprimeSourceHistogramKeyBits.frame_length,List.length_nil] at hm3
        nlinarith
      · have heq : R=remaining (wrapped word)+1 := by omega
        rw [heq]
        exact hr.trans (congrArg some (congrArg
          (fun xs => (⟨none,none,none,data [] [] [] [] xs,frames⟩ : C.State Stack Label))
          (by simpa only [logged,assignments] using
            log_cons word history output (assignments (remaining (wrapped word)) (wrapped word)))))

/-- Closed original-word endpoint, with no supplied iteration count or body. -/
theorem loop_run (word history output : List Bool) (flag : Option Bool)
    (returned : Option Label) (frames : List Label) :
    ∃m≤budget word history,C.run code m
      (state (ctl .bodyCall) flag returned word [] [] history output frames)=
      some ⟨none,none,none,data [] [] [] []
        ((history.reverse++vectorBits (assignments (remaining word) word))++output),frames⟩ :=
  loop_run_from (remaining word) word history output flag returned frames rfl

/-- Physical zero-word input enumerates exactly 2^width actual original assignments. -/
theorem zero_run (width : ℕ) :
    ∃m≤100*(width+1)*2^width+10,C.run code m
      (state (ctl .bodyCall) none none (List.replicate width false) [] [] [] [])=
      some ⟨none,none,none,data [] [] [] []
        (vectorBits (assignments (2^width) (List.replicate width false))),[]⟩ := by
  simpa [budget,zero_remaining] using loop_run (List.replicate width false) [] [] none none []

end RiemannGaussian.SemiprimeD1StackAssignmentEnumeration

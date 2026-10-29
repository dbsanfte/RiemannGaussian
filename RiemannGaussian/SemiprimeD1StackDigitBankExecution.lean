/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackDigitBankComponents
import RiemannGaussian.SemiprimeD1StackDigitBankSpec

/-! # Actual EOF-driven acquisition of every original radix digit
The fixed program has no fuel, requested digit count or evaluator input. The
proof bounds its physical EOF loop and its actual copied/framed byte history.
-/
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackDigitBankExecution
open SemiprimeD1StackDigitBank SemiprimeD1StackProcedureTrace
open SemiprimeD1StackDigitBankComponents SemiprimeD1StackDigitBankSpec
open SemiprimeSourceHistogramKeyBits (frame)

/-- A proof-side bound on the actual loop, including every real body call. -/
def loopBudget (W : ℕ) (width : List Bool) (fuel : ℕ) : ℕ :=
  (21*width.length+5*W+40)*fuel+1

/-- Actual EOF-loop trace for arbitrary existing reverse history. Every
existential time is obtained from literal component executions. -/
theorem loop_run (originalWord width : List Bool) (hw : width≠[]) (W fuel : ℕ)
    (word hist : List Bool) (hW : word.length ≤ W) (hf : word.length ≤ fuel) :
    ∃time ≤ loopBudget W width fuel,
      Runs program time (SemiprimeD1StackDigitBank.control .loop) (store originalWord word width [] hist [])
        (SemiprimeD1StackDigitBank.control .finish)
          (store originalWord [] width [] ((entries (blocks width fuel word)).reverse++hist) []) := by
  induction fuel generalizing word hist with
  | zero =>
    have he : word=[] := List.length_eq_zero_iff.mp (by omega)
    subst word
    refine ⟨1,by simp only [loopBudget,Nat.mul_zero,Nat.zero_add];omega,?_⟩
    simpa only [blocks,entries,List.reverse_nil,List.nil_append] using loop_empty originalWord width hist
  | succ fuel ih =>
    cases word with
    | nil =>
      refine ⟨1,by unfold loopBudget;omega,?_⟩
      simpa only [blocks,entries,List.reverse_nil,List.nil_append] using loop_empty originalWord width hist
    | cons b word =>
      let input:=b::word
      let digit:=SemiprimeD1StackDigitBlockExecution.result input width
      let nextHistory:=(true::frame digit []).reverse++hist
      have hs : (input.drop width.length).length < input.length := drop_progress width hw b word
      have htailW : (input.drop width.length).length ≤ W := hs.le.trans hW
      have htailFuel : (input.drop width.length).length ≤ fuel := by
        change input.length ≤ fuel+1 at hf
        omega
      obtain ⟨t,ht,hloop⟩:=ih (input.drop width.length) nextHistory htailW htailFuel
      obtain ⟨m,hm,hlog⟩:=log_call originalWord (input.drop width.length) width digit hist
      have h0:=loop_nonempty originalWord b word width hist
      have h1:=block_call originalWord input width hist
      have h3:=clear_block_run digit originalWord (input.drop width.length) width nextHistory
      have h01:=runs_trans program _ _ _ _ _ _ _ _ h0 h1
      have h012:=runs_trans program _ _ _ _ _ _ _ _ h01 hlog
      have h0123:=runs_trans program _ _ _ _ _ _ _ _ h012 h3
      have hall:=runs_trans program _ _ _ _ _ _ _ _ h0123 hloop
      refine ⟨1+(SemiprimeD1StackDigitBlockExecution.totalTime input width+1)+m+(digit.length+1)+t,?_,?_⟩
      · let K:=21*width.length+5*W+40
        have hd : digit.length ≤ width.length := block_length input width
        have hb:=SemiprimeD1StackDigitBlockExecution.totalTime_le input width
        have hr : 1+(SemiprimeD1StackDigitBlockExecution.totalTime input width+1)+m+(digit.length+1) ≤ K := by
          dsimp only [K]
          change input.length ≤ W at hW
          omega
        calc
          _ ≤ K+(K*fuel+1) := Nat.add_le_add hr ht
          _ = loopBudget W width (fuel+1) := by unfold loopBudget;dsimp only [K];ring
      · simpa only [input,digit,nextHistory,blocks,entries,List.reverse_append,List.append_assoc] using hall

/-- Encoded bank produced by the actual source loop, not an input to it. -/
def result (word width : List Bool) : List Bool :=
  SemiprimeD1TensorTapeCodec.vectorBits (blocks width word.length word)

/-- Whole-program quadratic budget, including original-input copy, all block
and frame calls, cleanup and final physical reversal. -/
def timeBound (word width : List Bool) : ℕ := 100*(word.length+1)*(word.length+width.length+1)

/-- Full actual bank trace preserves original binary N/cache and clears every
reader/work/history/return cell. No digit/count answer or callback is supplied. -/
theorem source_run (word width : List Bool) (hw : width≠[]) :
    ∃time ≤ timeBound word width,
      C.run program time
        (⟨some (SemiprimeD1StackDigitBank.control .start),none,none,store word [] width [] [] [],[]⟩:C.State Stack Label)=
        some (⟨none,none,none,store word [] width [] [] (result word width),[]⟩:C.State Stack Label) := by
  obtain ⟨m,hm,hloop⟩:=loop_run word width hw word.length word.length word [] le_rfl le_rfl
  simp only [List.append_nil] at hloop
  let encoded:=entries (blocks width word.length word)
  have h0:=start_run word width hw
  have h1:=copy_call word width
  have h3:=finish_run word width encoded.reverse
  have h4:=reverse_run encoded.reverse word width [false]
  simp only [List.reverse_reverse] at h4
  have h01:=runs_trans program _ _ _ _ _ _ _ _ h0 h1
  have h012:=runs_trans program _ _ _ _ _ _ _ _ h01 hloop
  have h0123:=runs_trans program _ _ _ _ _ _ _ _ h012 h3
  have h01234:=runs_trans program _ _ _ _ _ _ _ _ h0123 h4
  obtain ⟨finish,hfinish,hout⟩:=h01234 []
    (⟨some (SemiprimeD1StackDigitBank.control .start),none,none,store word [] width [] [] [],[]⟩:C.State Stack Label)
    ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program (SemiprimeD1StackDigitBank.control .done) rfl
    (store word [] width [] [] (encoded++[false])) [] finish hout
  refine ⟨1+(5*word.length+4)+m+1+(2*encoded.reverse.length+1)+1,?_,?_⟩
  · have he:=entries_blocks_length width word.length word
    change encoded.length ≤ word.length*(2*width.length+2) at he
    simp only [List.length_reverse]
    unfold loopBudget at hm
    unfold timeBound
    nlinarith [Nat.zero_le (word.length*width.length),Nat.zero_le (word.length^2)]
  · rw [SemiprimeD1StackReturnLink.run_add,hfinish,Option.bind_some,hh]
    have he : encoded++[false]=result word width := entries_vectorBits _
    rw [he]

/-- A proof-side time witness for the actual deterministic program. Choosing a
proved trace length is not an instruction or result supplier in that program. -/
noncomputable def sourceBank (word width : List Bool) (hw : width≠[]) :
    StateTransition.EvalsToInTime (C.step program)
      (⟨some (SemiprimeD1StackDigitBank.control .start),none,none,store word [] width [] [] [],[]⟩:C.State Stack Label)
      (some (⟨none,none,none,store word [] width [] [] (result word width),[]⟩:C.State Stack Label))
      (timeBound word width) := by
  let h:=source_run word width hw
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩

/-- Actual fixed finite-machine bank certificate. Only live original N, width
cache and acquired vector remain; all scratch and real return frames are empty. -/
noncomputable def machineBank (word width : List Bool) (hw : width≠[]) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration
        (⟨some (SemiprimeD1StackDigitBank.control .start),none,none,store word [] width [] [] [],[]⟩:C.State Stack Label))
      (some (SemiprimeD1StackCalls.configuration
        (⟨none,none,none,store word [] width [] [] (result word width),[]⟩:C.State Stack Label)))
      (timeBound word width) :=
  SemiprimeD1StackCalls.evalsCorrect original output (SemiprimeD1StackDigitBank.control .start) program _ _ _
    (sourceBank word width hw)

end RiemannGaussian.SemiprimeD1StackDigitBankExecution

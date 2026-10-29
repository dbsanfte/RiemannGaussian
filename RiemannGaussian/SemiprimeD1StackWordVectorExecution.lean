/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackWordVectorComponents
import RiemannGaussian.SemiprimeD1StackWordVectorSpec

/-! # Closed physical acquisition of a whole assignment word vector
The counter is copied from its actual cache and popped. Every iteration is the
literal proved WordBlock, logger and cleanup; a single final reversal emits the
original order. No selected word, grouping function or body verdict is supplied.
-/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackWordVectorExecution
open SemiprimeD1StackWordVector SemiprimeD1StackWordVectorComponents SemiprimeD1StackWordVectorSpec
open SemiprimeD1StackProcedureTrace
open SemiprimeD1StackDigitBankSpec (entries entries_vectorBits)
open SemiprimeSourceHistogramKeyBits (frame)
local notation "ctl" => SemiprimeD1StackWordVector.Label.control

/-- Actual closed loop allowance includes every complete word/logger call. -/
def loopBudget (width count : List Bool) : ℕ := (23*width.length+29)*count.length+1
/-- Near-output-linear allowance in raw input and physically emitted word cells. -/
def timeBound (word width count : List Bool) : ℕ :=
  100*(word.length+(count.length+1)*(width.length+1)+1)
/-- Physical acquired output vector; this is never an operand of the program. -/
def result (word width count : List Bool) : List Bool :=
  SemiprimeD1TensorTapeCodec.vectorBits (blocks width count.length word)
/-- Exact actual halt retains original input, unread suffix and both caches. -/
def done (word width count : List Bool) : C.State Stack Label :=
  ⟨none,none,none,store word (word.drop (count.length*width.length)) width count [] [] [] (result word width count),[]⟩

/-- Whole counted acquisition loop, including zero width, EOF padding and all
original bit values. The actual counter words are not required to be unary true. -/
theorem loop_run (word reader width count todo hist : List Bool) :
    ∃t ≤ loopBudget width todo,Runs program t (ctl .loop) (store word reader width count todo [] hist [])
      (ctl .finish) (store word (reader.drop (todo.length*width.length)) width count [] []
        ((entries (blocks width todo.length reader)).reverse++hist) []) := by
  induction todo generalizing reader hist with
  | nil =>
    refine ⟨1,le_refl _,?_⟩
    simp only [List.length_nil,Nat.zero_mul,List.drop_zero,blocks,entries,List.reverse_nil,List.nil_append]
    apply one_base program (ctl .loop) (ctl .finish)
      (.pop remaining (ctl .finish) (ctl .blockCall) (ctl .blockCall)) _ _ rfl
    · rfl
    · funext k
      rcases k with k|k
      · rfl
      · fin_cases k <;> rfl
  | cons b todo ih =>
    let block:=SemiprimeD1StackWordBlockExecution.result reader width
    let nextHistory:=(true::frame block []).reverse++hist
    obtain ⟨t,ht,hloop⟩:=ih (reader.drop width.length) nextHistory
    have h0 : Runs program 1 (ctl .loop) (store word reader width count (b::todo) [] hist [])
        (ctl .blockCall) (store word reader width count todo [] hist []) := by
      apply one_base program (ctl .loop) (ctl .blockCall)
        (.pop remaining (ctl .finish) (ctl .blockCall) (ctl .blockCall)) _ _ rfl
      · cases b <;> rfl
      · funext k
        rcases k with k|k
        · rfl
        · fin_cases k <;> rfl
    have h1:=block_call word reader width count todo hist
    obtain ⟨m,hm,h2⟩:=log_call word (reader.drop width.length) width count todo block hist
    have h3:=clear_block word (reader.drop width.length) width count todo block nextHistory
    have h:=runs_trans program _ _ _ _ _ _ _ _
      (runs_trans program _ _ _ _ _ _ _ _
        (runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ h0 h1) h2) h3) hloop
    refine ⟨1+(SemiprimeD1StackWordBlockExecution.totalTime width+1)+m+(block.length+1)+t,?_,?_⟩
    · have hb : block.length=width.length := SemiprimeD1StackWordBlockExecution.result_length reader width
      have htime:=SemiprimeD1StackWordBlockBounds.totalTime_eq width
      have hlocal : 1+(SemiprimeD1StackWordBlockExecution.totalTime width+1)+m+(block.length+1) ≤ 23*width.length+29 := by omega
      calc
        _ ≤ (23*width.length+29)+((23*width.length+29)*todo.length+1) := Nat.add_le_add hlocal ht
        _ = loopBudget width (b::todo) := by simp only [loopBudget,List.length_cons];ring
    · simpa only [List.length_cons,blocks,entries,block,nextHistory,List.reverse_append,List.append_assoc,drop_next] using h

/-- COMPLETE actual raw-assignment-to-word-vector source, with all physical
input/count copies and complete block/log/reverse work paid exactly once. -/
theorem source_run (word width count : List Bool) :
    ∃t ≤ timeBound word width count,C.run program t (initial word width count)=some (done word width count) := by
  have h0:=copy_input word width count
  have h1:=copy_count word word width count
  obtain ⟨m,hm,h2⟩:=loop_run word word width count count []
  simp only [List.append_nil] at h2
  let encoded:=entries (blocks width count.length word)
  have h3:=finish_run word (word.drop (count.length*width.length)) width count encoded.reverse
  have h4:=reverse_run encoded.reverse word (word.drop (count.length*width.length)) width count [false]
  simp only [List.length_reverse,List.reverse_reverse] at h4
  have h:=runs_trans program _ _ _ _ _ _ _ _
    (runs_trans program _ _ _ _ _ _ _ _
      (runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ h0 h1) h2) h3) h4
  obtain ⟨finish,hr,ho⟩:=h [] (initial word width count) ⟨rfl,rfl,rfl⟩
  have he:=halt_run program (ctl .done) rfl
    (store word (word.drop (count.length*width.length)) width count [] [] [] (encoded++[false])) [] finish ho
  refine ⟨(5*word.length+4)+(5*count.length+4)+m+1+(2*encoded.length+1)+1,?_,?_⟩
  · have hlen:=entries_length width count.length word
    change encoded.length=count.length*(2*width.length+2) at hlen
    unfold loopBudget at hm
    unfold timeBound
    rw [hlen]
    nlinarith [Nat.zero_le (count.length*width.length)]
  · rw [SemiprimeD1StackReturnLink.run_add,hr,Option.bind_some,he]
    have hvec : encoded++[false]=result word width count := entries_vectorBits _
    rw [hvec]
    rfl

end RiemannGaussian.SemiprimeD1StackWordVectorExecution

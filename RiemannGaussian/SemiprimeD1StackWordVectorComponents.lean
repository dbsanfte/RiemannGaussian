/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackWordVector

/-! # Actual input copying, closed word extraction, logging and reversal
Every supplied component trace is the literal fixed included program. No block,
record, metadata value or grouping body is an execution premise.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackWordVectorComponents
open SemiprimeD1StackWordVector SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
local notation "ctl" => SemiprimeD1StackWordVector.Label.control

/-- Acquire the disposable assignment reader by a real preserving copy. -/
theorem copy_input (word width count : List Bool) :
    Runs program (5*word.length+4) (ctl .start) (store word [] width count [] [] [] [])
      (ctl .copyCount) (store word word width count [] [] [] []) := by
  apply included_call program (copyStack false) (Label.copy false) (copyStack_injective false)
    SemiprimeD1StackCopy.code 0 (fun _=>rfl) (ctl .start) (ctl .copyCount) rfl (5*word.length+3)
    (SemiprimeD1StackCopy.state 0 none word [] []) (SemiprimeD1StackCopy.done word word)
    (store word [] width count [] [] [] []) (store word word width count [] [] [] [])
  · rfl
  · rfl
  · simpa only [List.append_nil] using SemiprimeD1StackCopy.copy_words word [] none
  · constructor
    · intro k;fin_cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k;fin_cases k <;> rfl
    · intro k hk
      rcases k with k|k
      · fin_cases k <;> first | rfl | exact False.elim (hk 1 rfl)
      · rfl

/-- Acquire the complete physical loop counter by a real preserving copy. -/
theorem copy_count (word reader width count : List Bool) :
    Runs program (5*count.length+4) (ctl .copyCount) (store word reader width count [] [] [] [])
      (ctl .loop) (store word reader width count count [] [] []) := by
  apply included_call program (copyStack true) (Label.copy true) (copyStack_injective true)
    SemiprimeD1StackCopy.code 0 (fun _=>rfl) (ctl .copyCount) (ctl .loop) rfl (5*count.length+3)
    (SemiprimeD1StackCopy.state 0 none count [] []) (SemiprimeD1StackCopy.done count count)
    (store word reader width count [] [] [] []) (store word reader width count count [] [] [])
  · rfl
  · rfl
  · simpa only [List.append_nil] using SemiprimeD1StackCopy.copy_words count [] none
  · constructor
    · intro k;fin_cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k;fin_cases k <;> rfl
    · intro k hk
      rcases k with k|k
      · rfl
      · fin_cases k <;> first | rfl | exact False.elim (hk 1 rfl)

/-- The COMPLETE actual raw block program preserves every unread assignment bit. -/
theorem block_call (word reader width count todo hist : List Bool) :
    Runs program (SemiprimeD1StackWordBlockExecution.totalTime width+1)
      (ctl .blockCall) (store word reader width count todo [] hist []) (ctl .logCall)
      (store word (reader.drop width.length) width count todo
        (SemiprimeD1StackWordBlockExecution.result reader width) hist []) := by
  apply SemiprimeD1StackProcedureCallsTrace.included_call program Sum.inl Label.block Sum.inl_injective
    Block.program .start (fun _=>rfl) (ctl .blockCall) (ctl .logCall) rfl
    (SemiprimeD1StackWordBlockExecution.totalTime width) (Block.initial reader width)
    (SemiprimeD1StackWordBlockExecution.done reader width)
    (store word reader width count todo [] hist [])
    (store word (reader.drop width.length) width count todo
      (SemiprimeD1StackWordBlockExecution.result reader width) hist [])
  · rfl
  · rfl
  · rfl
  · rfl
  · exact SemiprimeD1StackWordBlockExecution.source_run reader width
  · constructor
    · intro k;rfl
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk
      rcases k with k|k
      · exact False.elim (hk k rfl)
      · rfl

/-- Actual fixed logger emits the reverse of one complete framed vector entry,
retaining the full raw word including high zero padding. -/
theorem log_call (word reader width count todo block hist : List Bool) :
    ∃m ≤ 6*(2*block.length+3)+1,Runs program m (ctl .logCall)
      (store word reader width count todo block hist []) (ctl .clearBlock)
      (store word reader width count todo block ((true::frame block []).reverse++hist) []) := by
  obtain ⟨m,hm,hr⟩:=Body.body_run block hist
  refine ⟨m+1,by omega,?_⟩
  apply included_call program bodyStack Label.body bodyStack_injective Body.code Body.entry
    (fun _=>rfl) (ctl .logCall) (ctl .clearBlock) rfl m
    (⟨some Body.entry,none,Body.contents block [] hist⟩:
      SemiprimeD1StackBytecode.State Body.Stack Body.Label)
    (⟨none,none,Body.contents block [] ((true::frame block []).reverse++hist)⟩:
      SemiprimeD1StackBytecode.State Body.Stack Body.Label)
    (store word reader width count todo block hist [])
    (store word reader width count todo block ((true::frame block []).reverse++hist) [])
  · rfl
  · rfl
  · exact hr
  · constructor
    · intro k;cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k;cases k <;> rfl
    · intro k hk
      rcases k with k|k
      · rfl
      · fin_cases k <;> first | rfl | exact False.elim (hk .history rfl)

/-- The preserved per-word output is physically cleared before the next block. -/
theorem clear_block (word reader width count todo block hist : List Bool) :
    Runs program (block.length+1) (ctl .clearBlock) (store word reader width count todo block hist [])
      (ctl .loop) (store word reader width count todo [] hist []) := by
  have h:=SemiprimeD1StackPhysicalLoops.drain program (ctl .clearBlock) (ctl .loop) (.inl 4) rfl
    (store word reader width count todo [] hist []) block
  have hi : Function.update (store word reader width count todo [] hist []) (.inl 4) block=
      store word reader width count todo block hist [] := by
    funext k
    rcases k with k|k
    · fin_cases k <;> simp [Function.update,store,Block.store]
    · simp [Function.update,store]
  have ho : Function.update (store word reader width count todo [] hist []) (.inl 4) []=
      store word reader width count todo [] hist [] := Function.update_eq_self _ _
  rw [hi,ho] at h
  exact h

/-- The vector nil terminator is an actual emitted bit. -/
theorem finish_run (word reader width count hist : List Bool) :
    Runs program 1 (ctl .finish) (store word reader width count [] [] hist [])
      (ctl .reverse) (store word reader width count [] [] hist [false]) := by
  apply one_base program (ctl .finish) (ctl .reverse) (.push output false (ctl .reverse)) _ _ rfl
  · rfl
  · funext k;rcases k with k|k
    · rfl
    · fin_cases k <;> rfl

/-- One physical reversal restores chronological word and within-word bit order. -/
theorem reverse_run (hist word reader width count out : List Bool) :
    Runs program (2*hist.length+1) (ctl .reverse) (store word reader width count [] [] hist out)
      (ctl .done) (store word reader width count [] [] [] (hist.reverse++out)) := by
  induction hist generalizing out with
  | nil =>
    apply one_base program (ctl .reverse) (ctl .done)
      (.pop history (ctl .done) (ctl (.emit false)) (ctl (.emit true))) _ _ rfl
    · rfl
    · funext k;rcases k with k|k
      · rfl
      · fin_cases k <;> rfl
  | cons b hist ih =>
    have h0 : Runs program 1 (ctl .reverse) (store word reader width count [] [] (b::hist) out)
        (ctl (.emit b)) (store word reader width count [] [] hist out) := by
      apply one_base program (ctl .reverse) (ctl (.emit b))
        (.pop history (ctl .done) (ctl (.emit false)) (ctl (.emit true))) _ _ rfl
      · cases b <;> rfl
      · funext k;rcases k with k|k
        · rfl
        · fin_cases k <;> rfl
    have h1 : Runs program 1 (ctl (.emit b)) (store word reader width count [] [] hist out)
        (ctl .reverse) (store word reader width count [] [] hist (b::out)) := by
      apply one_base program (ctl (.emit b)) (ctl .reverse) (.push output b (ctl .reverse)) _ _ rfl
      · rfl
      · funext k;rcases k with k|k
        · rfl
        · fin_cases k <;> rfl
    have h:=runs_trans program _ _ _ _ _ _ _ _
      (runs_trans program _ _ _ _ _ _ _ _ h0 h1) (ih (b::out))
    simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append,
      show (1+1)+(2*hist.length+1)=2*(hist.length+1)+1 by omega] using h

end RiemannGaussian.SemiprimeD1StackWordVectorComponents

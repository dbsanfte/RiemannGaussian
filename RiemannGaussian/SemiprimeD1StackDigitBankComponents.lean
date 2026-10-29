/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackDigitBank

/-! # Actual streaming digit-bank component executions
Each statement below is a trace of the literal enclosing program, including
nested block calls, physical logging and reversal. No digit/body evaluator or
count/cost answer is accepted by the executing program.
-/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackDigitBankComponents
open SemiprimeD1StackDigitBank SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)

/-- A positive physical width selects the actual initial-copy call. -/
theorem start_run (word width : List Bool) (hw : width≠[]) :
    Runs program 1 (SemiprimeD1StackDigitBank.control .start) (store word [] width [] [] [])
      (SemiprimeD1StackDigitBank.control .copyInput) (store word [] width [] [] []) := by
  apply one_base program (SemiprimeD1StackDigitBank.control .start) (SemiprimeD1StackDigitBank.control .copyInput)
    (.peek (.inl .width) (SemiprimeD1StackDigitBank.control .done) (SemiprimeD1StackDigitBank.control .copyInput) (SemiprimeD1StackDigitBank.control .copyInput))
    (store word [] width [] [] []) (store word [] width [] [] []) rfl
  · cases width with
    | nil => exact False.elim (hw rfl)
    | cons b width => cases b <;> rfl
  · rfl

/-- Copy the original binary integer once, preserving the original and cache. -/
theorem copy_call (word width : List Bool) :
    Runs program (5*word.length+4) (SemiprimeD1StackDigitBank.control .copyInput) (store word [] width [] [] [])
      (SemiprimeD1StackDigitBank.control .loop) (store word word width [] [] []) := by
  apply included_call program copyStack copyLabel copyStack_injective SemiprimeD1StackCopy.code 0
    (fun _=>rfl) (SemiprimeD1StackDigitBank.control .copyInput) (SemiprimeD1StackDigitBank.control .loop) rfl (5*word.length+3)
    (SemiprimeD1StackCopy.state 0 none word [] []) (SemiprimeD1StackCopy.done word word)
    (store word [] width [] [] []) (store word word width [] [] [])
  · rfl
  · rfl
  · simpa only [List.append_nil] using SemiprimeD1StackCopy.copy_words word [] none
  · constructor
    · intro k;fin_cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k;fin_cases k <;> rfl
    · intro k hk
      have hr:=hk 1
      rcases k with k|k
      · cases k <;> simp_all [store,copyStack,original,SemiprimeD1StackDigitBlock.store]
      · rfl

/-- The nonempty reader is tested by a real peek, leaving its first bit intact. -/
theorem loop_nonempty (originalWord : List Bool) (b : Bool) (reader width hist : List Bool) :
    Runs program 1 (SemiprimeD1StackDigitBank.control .loop) (store originalWord (b::reader) width [] hist [])
      (SemiprimeD1StackDigitBank.control .blockCall) (store originalWord (b::reader) width [] hist []) := by
  apply one_base program (SemiprimeD1StackDigitBank.control .loop) (SemiprimeD1StackDigitBank.control .blockCall)
    (.peek (.inl .input) (SemiprimeD1StackDigitBank.control .finish) (SemiprimeD1StackDigitBank.control .blockCall) (SemiprimeD1StackDigitBank.control .blockCall))
    (store originalWord (b::reader) width [] hist []) (store originalWord (b::reader) width [] hist []) rfl
  · cases b <;> rfl
  · rfl

/-- EOF is acquired from the actual reader, not from a supplied digit count. -/
theorem loop_empty (originalWord width hist : List Bool) :
    Runs program 1 (SemiprimeD1StackDigitBank.control .loop) (store originalWord [] width [] hist [])
      (SemiprimeD1StackDigitBank.control .finish) (store originalWord [] width [] hist []) := by
  apply one_base program (SemiprimeD1StackDigitBank.control .loop) (SemiprimeD1StackDigitBank.control .finish)
    (.peek (.inl .input) (SemiprimeD1StackDigitBank.control .finish) (SemiprimeD1StackDigitBank.control .blockCall) (SemiprimeD1StackDigitBank.control .blockCall))
    (store originalWord [] width [] hist []) (store originalWord [] width [] hist []) rfl
  · rfl
  · rfl

/-- The actual nested Copy/prefix/trim block code executes inside the bank,
preserving original N, cached width, outer frames and current reverse log. -/
theorem block_call (originalWord reader width hist : List Bool) :
    Runs program (SemiprimeD1StackDigitBlockExecution.totalTime reader width+1)
      (SemiprimeD1StackDigitBank.control .blockCall) (store originalWord reader width [] hist [])
      (SemiprimeD1StackDigitBank.control .logCall) (store originalWord (reader.drop width.length) width
        (SemiprimeD1StackDigitBlockExecution.result reader width) hist []) := by
  apply SemiprimeD1StackProcedureCallsTrace.included_call program Sum.inl blockLabel Sum.inl_injective
    Block.program .start (fun _=>rfl) (SemiprimeD1StackDigitBank.control .blockCall) (SemiprimeD1StackDigitBank.control .logCall) rfl
    (SemiprimeD1StackDigitBlockExecution.totalTime reader width)
    (⟨some .start,none,none,SemiprimeD1StackDigitBlock.store reader width [] [] [] [] [] [],[]⟩:
      C.State Block.Stack Block.Label)
    (⟨none,none,none,SemiprimeD1StackDigitBlock.store (reader.drop width.length) width [] [] [] [] []
      (SemiprimeD1StackDigitBlockExecution.result reader width),[]⟩:C.State Block.Stack Block.Label)
    (store originalWord reader width [] hist [])
    (store originalWord (reader.drop width.length) width (SemiprimeD1StackDigitBlockExecution.result reader width) hist [])
  · rfl
  · rfl
  · rfl
  · rfl
  · exact SemiprimeD1StackDigitBlockExecution.source_run reader width
  · constructor
    · intro k;rfl
    · intro k hk
      rcases k with k|k
      · exact False.elim (hk k rfl)
      · rfl
  · constructor
    · intro k;rfl
    · intro k hk
      rcases k with k|k
      · exact False.elim (hk k rfl)
      · rfl

/-- Actual finite body code physically logs the block; the existential trace
length is obtained from its already proved literal execution, not advised. -/
theorem log_call (originalWord reader width block hist : List Bool) :
    ∃m ≤ 6*(2*block.length+3)+1,
      Runs program m (SemiprimeD1StackDigitBank.control .logCall) (store originalWord reader width block hist [])
        (SemiprimeD1StackDigitBank.control .clearBlock) (store originalWord reader width block ((true::frame block []).reverse++hist) []) := by
  obtain ⟨m,hm,hr⟩:=SemiprimeD1StackAssignmentBody.body_run block hist
  refine ⟨m+1,by omega,?_⟩
  apply included_call program bodyStack bodyLabel bodyStack_injective Body.code Body.entry
    (fun _=>rfl) (SemiprimeD1StackDigitBank.control .logCall) (SemiprimeD1StackDigitBank.control .clearBlock) rfl m
    (⟨some Body.entry,none,SemiprimeD1StackAssignmentBody.contents block [] hist⟩:
      B.State Body.Stack Body.Label)
    (⟨none,none,SemiprimeD1StackAssignmentBody.contents block [] ((true::frame block []).reverse++hist)⟩:
      B.State Body.Stack Body.Label)
    (store originalWord reader width block hist [])
    (store originalWord reader width block ((true::frame block []).reverse++hist) [])
  · rfl
  · rfl
  · exact hr
  · constructor
    · intro k;cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k;cases k <;> rfl
    · intro k hk
      have hh:=hk .history
      rcases k with k|k
      · rfl
      · fin_cases k <;> simp_all [store,bodyStack,history]

/-- Every copied block cell is physically cleared before the next reader test. -/
theorem clear_block_run (block originalWord reader width hist : List Bool) :
    Runs program (block.length+1) (SemiprimeD1StackDigitBank.control .clearBlock) (store originalWord reader width block hist [])
      (SemiprimeD1StackDigitBank.control .loop) (store originalWord reader width [] hist []) := by
  induction block with
  | nil =>
    apply one_base program (SemiprimeD1StackDigitBank.control .clearBlock) (SemiprimeD1StackDigitBank.control .loop)
      (.pop (.inl .output) (SemiprimeD1StackDigitBank.control .loop) (SemiprimeD1StackDigitBank.control .clearBlock) (SemiprimeD1StackDigitBank.control .clearBlock))
      (store originalWord reader width [] hist []) (store originalWord reader width [] hist []) rfl
    · rfl
    · funext k
      rcases k with k|k
      · cases k <;> rfl
      · rfl
  | cons b block ih =>
    have h0 : Runs program 1 (SemiprimeD1StackDigitBank.control .clearBlock) (store originalWord reader width (b::block) hist [])
        (SemiprimeD1StackDigitBank.control .clearBlock) (store originalWord reader width block hist []) := by
      apply one_base program (SemiprimeD1StackDigitBank.control .clearBlock) (SemiprimeD1StackDigitBank.control .clearBlock)
        (.pop (.inl .output) (SemiprimeD1StackDigitBank.control .loop) (SemiprimeD1StackDigitBank.control .clearBlock) (SemiprimeD1StackDigitBank.control .clearBlock))
        (store originalWord reader width (b::block) hist []) (store originalWord reader width block hist []) rfl
      · cases b <;> rfl
      · funext k
        rcases k with k|k
        · cases k <;> rfl
        · rfl
    have hh:=runs_trans program _ _ _ _ _ _ _ _ h0 ih
    convert hh using 1
    simp only [List.length_cons]
    omega

/-- The vector terminator is an actual output push. -/
theorem finish_run (originalWord width hist : List Bool) :
    Runs program 1 (SemiprimeD1StackDigitBank.control .finish) (store originalWord [] width [] hist [])
      (SemiprimeD1StackDigitBank.control .reverse) (store originalWord [] width [] hist [false]) := by
  apply one_base program (SemiprimeD1StackDigitBank.control .finish) (SemiprimeD1StackDigitBank.control .reverse)
    (.push output false (SemiprimeD1StackDigitBank.control .reverse)) (store originalWord [] width [] hist [])
      (store originalWord [] width [] hist [false]) rfl
  · rfl
  · funext k
    rcases k with k|k
    · rfl
    · fin_cases k <;> rfl

/-- Every reverse-log bit is physically popped and pushed into chronological order. -/
theorem reverse_run (hist originalWord width out : List Bool) :
    Runs program (2*hist.length+1) (SemiprimeD1StackDigitBank.control .reverse) (store originalWord [] width [] hist out)
      (SemiprimeD1StackDigitBank.control .done) (store originalWord [] width [] [] (hist.reverse++out)) := by
  induction hist generalizing out with
  | nil =>
    apply one_base program (SemiprimeD1StackDigitBank.control .reverse) (SemiprimeD1StackDigitBank.control .done)
      (.pop history (SemiprimeD1StackDigitBank.control .done) (SemiprimeD1StackDigitBank.control (.emit false)) (SemiprimeD1StackDigitBank.control (.emit true)))
      (store originalWord [] width [] [] out) (store originalWord [] width [] [] out) rfl
    · rfl
    · funext k
      rcases k with k|k
      · rfl
      · fin_cases k <;> rfl
  | cons b hist ih =>
    have h0 : Runs program 1 (SemiprimeD1StackDigitBank.control .reverse) (store originalWord [] width [] (b::hist) out)
        (SemiprimeD1StackDigitBank.control (.emit b)) (store originalWord [] width [] hist out) := by
      apply one_base program (SemiprimeD1StackDigitBank.control .reverse) (SemiprimeD1StackDigitBank.control (.emit b))
        (.pop history (SemiprimeD1StackDigitBank.control .done) (SemiprimeD1StackDigitBank.control (.emit false)) (SemiprimeD1StackDigitBank.control (.emit true)))
        (store originalWord [] width [] (b::hist) out) (store originalWord [] width [] hist out) rfl
      · cases b <;> rfl
      · funext k
        rcases k with k|k
        · rfl
        · fin_cases k <;> rfl
    have h1 : Runs program 1 (SemiprimeD1StackDigitBank.control (.emit b)) (store originalWord [] width [] hist out)
        (SemiprimeD1StackDigitBank.control .reverse) (store originalWord [] width [] hist (b::out)) := by
      apply one_base program (SemiprimeD1StackDigitBank.control (.emit b)) (SemiprimeD1StackDigitBank.control .reverse) (.push output b (SemiprimeD1StackDigitBank.control .reverse))
        (store originalWord [] width [] hist out) (store originalWord [] width [] hist (b::out)) rfl
      · rfl
      · funext k
        rcases k with k|k
        · rfl
        · fin_cases k <;> rfl
    have h2:=ih (b::out)
    have hh:=runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ h0 h1) h2
    simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
    convert hh using 1
    simp only [List.length_cons]
    omega

end RiemannGaussian.SemiprimeD1StackDigitBankComponents

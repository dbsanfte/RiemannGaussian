/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicInputState
import RiemannGaussian.SemiprimeD1StackProcedureInclusion
/-! # Actual included calls inside the closed PublicInput52 program -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxSize 8192
set_option maxRecDepth 32768
namespace RiemannGaussian.SemiprimeD1StackPublicInputComponents
open SemiprimeD1StackPublicInput SemiprimeD1StackPublicInputState
open SemiprimeD1StackProcedureTrace (Runs)
/-- H37 executes ONCE inside this caller, from original N and physical index only. -/
theorem acquire_call (bits raw indexWord : List Bool) (hb : bits≠[]) :
    ∃t≤SemiprimeD1StackPublicInputWidthExecution.timeBound bits indexWord,
      Runs program (t+1) .start (initial bits raw indexWord).data .copyRaw (ready bits raw indexWord) := by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackPublicInputWidthExecution.source_run bits indexWord hb
  refine ⟨t,ht,?_⟩
  apply SemiprimeD1StackProcedureInclusion.included_call program Sum.inl Label.header Sum.inl_injective
    H.program .start (fun _=>rfl) .start .copyRaw rfl t
    (SemiprimeD1StackPublicInputWidth.initial bits indexWord)
    (SemiprimeD1StackPublicInputWidthExecution.done bits indexWord)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact hr
  · constructor
    · intro k; rfl
    · intro k hk; rfl
  · constructor
    · intro k; rfl
    · intro k hk
      rcases k with k|k
      · exact (hk k rfl).elim
      · rcases k with k|k
        · fin_cases k <;> rfl
        · rcases k with k|k
          · rcases k with k|k <;> cases k <;> rfl
          · rcases k with k|k <;> cases k <;> rfl
/-- Real preserving raw-assignment copy, including its actual call and return. -/
theorem copy_raw_call (bits raw indexWord : List Bool) :
    Runs program (5*raw.length+4) .copyRaw (ready bits raw indexWord) .block (afterCopy bits raw indexWord) := by
  apply SemiprimeD1StackProcedureFragments.included_call program (copyStack 0) (Label.copy 0) (copy_injective 0)
    SemiprimeD1StackCopy.code 0 (fun _=>rfl) .copyRaw .block rfl (5*raw.length+3)
    (SemiprimeD1StackCopy.state 0 none raw [] []) (SemiprimeD1StackCopy.done raw raw)
  · rfl
  · rfl
  · simpa only [List.append_nil] using SemiprimeD1StackCopy.copy_words raw [] none
  · constructor
    · intro k; fin_cases k <;> rfl
    · intro k hk; rfl
  · constructor
    · intro k; fin_cases k <;> rfl
    · intro k hk
      rcases k with k|k
      · rfl
      · rcases k with k|k
        · fin_cases k <;> first | rfl | exact (hk 1 rfl).elim
        · rcases k with k|k
          · rcases k with k|k <;> cases k <;> rfl
          · rcases k with k|k <;> cases k <;> rfl
/-- Actual block extraction uses the SAME retained public modulus-width template. -/
theorem block_call (bits raw indexWord : List Bool) :
    Runs program (SemiprimeD1StackWordBlockExecution.totalTime (M.cached bits)+1)
      .block (afterCopy bits raw indexWord) .activity (afterBlock bits raw indexWord) := by
  apply SemiprimeD1StackProcedureInclusion.included_call program blockStack Label.extract block_injective
    B.program SemiprimeD1StackWordFit.Label.start (fun _=>rfl) .block .activity rfl _
    (SemiprimeD1StackWordBlock.initial raw (M.cached bits))
    (SemiprimeD1StackWordBlockExecution.done raw (M.cached bits))
  · rfl
  · rfl
  · rfl
  · rfl
  · exact SemiprimeD1StackWordBlockExecution.source_run raw (M.cached bits)
  · constructor
    · intro k; fin_cases k <;> rfl
    · intro k hk; rfl
  · constructor
    · intro k; fin_cases k <;> rfl
    · intro k hk
      rcases k with k|k
      · rfl
      · rcases k with k|k
        · fin_cases k <;> first | rfl | exact (hk 0 rfl).elim | exact (hk 4 rfl).elim
        · rcases k with k|k
          · rcases k with k|k <;> cases k <;> rfl
          · rcases k with k|k <;> cases k <;> rfl
/-- The two actual word-preserving copies share this literal inclusion; only the
code's fixed entry/return labels vary, never a runtime source/evaluator. -/
theorem copy_word_call (pc next : Label) (hcall : program pc=.call (.copy 1 0) next)
    (h : H.Stack→List Bool) (raw reader word : List Bool) :
    Runs program (5*word.length+4) pc (store h raw reader word [] [] [])
      next (store h raw reader word word [] []) := by
  apply SemiprimeD1StackProcedureFragments.included_call program (copyStack 1) (Label.copy 1) (copy_injective 1)
    SemiprimeD1StackCopy.code 0 (fun _=>rfl) pc next hcall (5*word.length+3)
    (SemiprimeD1StackCopy.state 0 none word [] []) (SemiprimeD1StackCopy.done word word)
  · rfl
  · rfl
  · simpa only [List.append_nil] using SemiprimeD1StackCopy.copy_words word [] none
  · constructor
    · intro k; fin_cases k <;> rfl
    · intro k hk; rfl
  · constructor
    · intro k; fin_cases k <;> rfl
    · intro k hk
      rcases k with k|k
      · rfl
      · rcases k with k|k
        · fin_cases k <;> rfl
        · rcases k with k|k
          · rcases k with k|k
            · cases k <;> first | rfl | exact (hk 1 rfl).elim
            · rfl
          · rcases k with k|k <;> cases k <;> rfl
/-- Actual strict comparison consumes BOTH physical operands and clears its
subtractor workspace; only the actual borrow answer remains. -/
theorem less_call (pc next : Label) (hcall : program pc=.call (.less .start) next)
    (bits indexWord raw reader word left bd : List Bool) :
    Runs program (SemiprimeD1StackWordLessExecution.totalTime left bd+1) pc
      (store (header bits indexWord bd) raw reader word left [] []) next
      (store (header bits indexWord []) raw reader word []
        [SemiprimeD1StackWordLessExecution.answer left bd] []) := by
  apply SemiprimeD1StackProcedureInclusion.included_call program lessStack Label.less less_injective
    L.program .start (fun _=>rfl) pc next hcall _
    (SemiprimeD1StackWordLess.initial left bd) (SemiprimeD1StackWordLessExecution.done left bd)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact SemiprimeD1StackWordLessExecution.source_run left bd
  · constructor
    · intro k; rcases k with k|k <;> cases k <;> rfl
    · intro k hk; rfl
  · constructor
    · intro k; rcases k with k|k <;> cases k <;> rfl
    · intro k hk
      rcases k with k|k
      · by_cases he:k=H.output
        · subst k;exact (hk (.inl .right) rfl).elim
        · simp [store,header,he]
      · rcases k with k|k
        · rfl
        · rcases k with k|k
          · rcases k with k|k
            · cases k <;> first | rfl | exact (hk (.inl .left) rfl).elim
            · exact (hk (.inr ()) rfl).elim
          · rfl
/-- Actual numeric-zero equality consumes its word and clears operand/scratch
cells; no decoded zero predicate is supplied to its code. -/
theorem equal_call (pc next : Label) (hcall : program pc=.call (.equality .loop) next)
    (h : H.Stack→List Bool) (raw reader word : List Bool) :
    Runs program (SemiprimeD1StackWordEqualExecution.executionTime word []+1) pc
      (store h raw reader word [] [] []) next
      (store h raw reader [] [] [decide (SemiprimeBitArithmetic.bitValue word=0)] []) := by
  apply SemiprimeD1StackProcedureFragments.included_call program equalStack Label.equality equal_injective
    E.code .loop (fun _=>rfl) pc next hcall _
    (SemiprimeD1StackWordEqual.state (some .loop) none word [] [])
    (SemiprimeD1StackWordEqual.state none none [] [] [decide (SemiprimeBitArithmetic.bitValue word=0)])
  · rfl
  · rfl
  · exact SemiprimeD1StackWordEqualExecution.source_run word [] none
  · constructor
    · intro k; cases k <;> rfl
    · intro k hk; rfl
  · constructor
    · intro k; cases k <;> rfl
    · intro k hk
      rcases k with k|k
      · rfl
      · rcases k with k|k
        · fin_cases k <;> first | rfl | exact (hk .left rfl).elim
        · rcases k with k|k
          · rcases k with k|k
            · rfl
            · exact (hk .output rfl).elim
          · rfl

end RiemannGaussian.SemiprimeD1StackPublicInputComponents

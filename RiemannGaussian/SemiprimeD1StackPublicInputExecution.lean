/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicInputBranches
/-! # Closed actual source execution of the whole PublicInput52 checker
Only original bits/raw/index and bits≠[] enter the final endpoint. Every bound,
word, guard, test and flag is acquired by the literal Core52 procedures.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 2200000
set_option maxRecDepth 32768
namespace RiemannGaussian.SemiprimeD1StackPublicInputExecution
open SemiprimeD1StackPublicInput SemiprimeD1StackPublicInputState
open SemiprimeD1StackPublicInputComponents SemiprimeD1StackPublicInputControl SemiprimeD1StackPublicInputBranches
open SemiprimeD1StackProcedureFragments (Runs)
/-- Generous derived local bound; no component-cost answer is an input. -/
def bodyBound (bits raw indexWord : List Bool) : ℕ :=
  100*((M.word bits raw).length+(M.actualBound bits indexWord).length+3)
/-- Complete actual source budget: H37 ONCE, raw Copy, WordBlock, all concrete
comparison/flag branches and cleanup, their actual calls/returns and final halt. -/
def timeBound (bits raw indexWord : List Bool) : ℕ :=
  (SemiprimeD1StackPublicInputWidthExecution.timeBound bits indexWord+1)+(5*raw.length+4)+
    (SemiprimeD1StackWordBlockExecution.totalTime (M.cached bits)+1)+bodyBound bits raw indexWord+1
/-- Actual active/inactive execution, closed under all computed branch values;
none is supplied as a runtime operand, truth advice or cost premise. -/
theorem body_run (bits raw indexWord : List Bool) :
    ∃t≤bodyBound bits raw indexWord,Runs program t .activity
      (store (header bits indexWord (M.actualBound bits indexWord)) raw (suffix bits raw) (M.word bits raw) [] [] [])
      .done (store (header bits indexWord []) raw (suffix bits raw) [] [] [] [M.expected bits raw indexWord]) := by
  have hactivity:=activity_peek bits indexWord raw (suffix bits raw) (M.word bits raw)
  by_cases ha:0<SemiprimeD1StackInputWidthExecution.width (SemiprimeD1StackPublicInputWidthExecution.cache bits indexWord)
  · have h0 : Runs program 1 .activity
        (store (header bits indexWord (M.actualBound bits indexWord)) raw (suffix bits raw) (M.word bits raw) [] [] [])
        .guardCopy (store (header bits indexWord (M.actualBound bits indexWord)) raw (suffix bits raw) (M.word bits raw) [] [] []) := by
      simpa only [ha,ite_true] using hactivity
    have h1:=copy_word_call .guardCopy .guard rfl (header bits indexWord (M.actualBound bits indexWord))
      raw (suffix bits raw) (M.word bits raw)
    have h2:=less_call .guard .readGuard rfl bits indexWord raw (suffix bits raw) (M.word bits raw)
      (M.word bits raw) (M.actualBound bits indexWord)
    have h3:=read_comparison .readGuard .bad (fun b=>if b then Label.indexCase else .write false) rfl
      (header bits indexWord []) raw (suffix bits raw) (M.word bits raw)
      (SemiprimeD1StackWordLessExecution.answer (M.word bits raw) (M.actualBound bits indexWord))
    have hp:=SemiprimeD1StackProcedureFragments.Runs.trans h0
      (SemiprimeD1StackProcedureFragments.Runs.trans h1
        (SemiprimeD1StackProcedureFragments.Runs.trans h2 h3))
    have hl:=SemiprimeD1StackWordLessExecution.totalTime_le (M.word bits raw) (M.actualBound bits indexWord)
    by_cases hg:SemiprimeD1StackWordLessExecution.answer (M.word bits raw) (M.actualBound bits indexWord)=true
    · have hprefix : Runs program (1+((5*(M.word bits raw).length+4)+
          ((SemiprimeD1StackWordLessExecution.totalTime (M.word bits raw) (M.actualBound bits indexWord)+1)+1)))
          .activity (store (header bits indexWord (M.actualBound bits indexWord)) raw (suffix bits raw) (M.word bits raw) [] [] [])
          .indexCase (store (header bits indexWord []) raw (suffix bits raw) (M.word bits raw) [] [] []) := by
        simpa only [hg,ite_true] using hp
      obtain ⟨t,ht,hrest⟩:=index_tail bits raw indexWord
      have hh:=hprefix.trans hrest
      refine ⟨(1+((5*(M.word bits raw).length+4)+
        ((SemiprimeD1StackWordLessExecution.totalTime (M.word bits raw) (M.actualBound bits indexWord)+1)+1)))+t,?_,?_⟩
      · unfold bodyBound
        omega
      · have hv : flagRule bits raw indexWord=M.expected bits raw indexWord := by
          simp only [SemiprimeD1StackPublicInputMeaning.expected,ha,ite_true,hg,Bool.true_and,flagRule]
        rw [←hv]
        exact hh
    · have hn:SemiprimeD1StackWordLessExecution.answer (M.word bits raw) (M.actualBound bits indexWord)=false :=
        by cases h:SemiprimeD1StackWordLessExecution.answer (M.word bits raw) (M.actualBound bits indexWord) <;> simp_all
      have hprefix : Runs program (1+((5*(M.word bits raw).length+4)+
          ((SemiprimeD1StackWordLessExecution.totalTime (M.word bits raw) (M.actualBound bits indexWord)+1)+1)))
          .activity (store (header bits indexWord (M.actualBound bits indexWord)) raw (suffix bits raw) (M.word bits raw) [] [] [])
          (.write false) (store (header bits indexWord []) raw (suffix bits raw) (M.word bits raw) [] [] []) := by
        simpa only [hn,Bool.false_eq_true,ite_false] using hp
      have hrest:=write_finish bits indexWord [] raw (suffix bits raw) (M.word bits raw) false
      have hh:=hprefix.trans hrest
      refine ⟨(1+((5*(M.word bits raw).length+4)+
        ((SemiprimeD1StackWordLessExecution.totalTime (M.word bits raw) (M.actualBound bits indexWord)+1)+1)))+
        ((M.word bits raw).length+0+3),?_,?_⟩
      · unfold bodyBound
        omega
      · have hv : false=M.expected bits raw indexWord := by
          simp only [SemiprimeD1StackPublicInputMeaning.expected,ha,ite_true,hn,Bool.false_and]
        rw [←hv]
        exact hh
  · have h0 : Runs program 1 .activity
        (store (header bits indexWord (M.actualBound bits indexWord)) raw (suffix bits raw) (M.word bits raw) [] [] [])
        .zero (store (header bits indexWord (M.actualBound bits indexWord)) raw (suffix bits raw) (M.word bits raw) [] [] []) := by
      simpa only [ha,ite_false] using hactivity
    have h1:=equal_call .zero .readZero rfl (header bits indexWord (M.actualBound bits indexWord))
      raw (suffix bits raw) (M.word bits raw)
    have h2:=zero_finish bits indexWord (M.actualBound bits indexWord) raw (suffix bits raw)
      (decide (SemiprimeBitArithmetic.bitValue (M.word bits raw)=0))
    have hh:=SemiprimeD1StackProcedureFragments.Runs.trans h0
      (SemiprimeD1StackProcedureFragments.Runs.trans h1 h2)
    refine ⟨1+((SemiprimeD1StackWordEqualExecution.executionTime (M.word bits raw) []+1)+
      ((M.actualBound bits indexWord).length+4)),?_,?_⟩
    · have he:=SemiprimeD1StackWordEqualExecution.executionTime_le (M.word bits raw) []
      simp only [List.length_nil] at he
      unfold bodyBound
      omega
    · have hv : decide (SemiprimeBitArithmetic.bitValue (M.word bits raw)=0)=M.expected bits raw indexWord := by
        simp only [SemiprimeD1StackPublicInputMeaning.expected,ha,ite_false]
      rw [←hv]
      exact hh

/-- WHOLE closed actual checker. No computed width/word/guard/verdict/clock
premise is admitted; every source and comparison executes inside this code. -/
theorem source_run (bits raw indexWord : List Bool) (hb : bits≠[]) :
    ∃t≤timeBound bits raw indexWord,C.run program t (initial bits raw indexWord)=
      some (SemiprimeD1StackPublicInputState.done bits raw indexWord) := by
  obtain ⟨a,ha,h0⟩:=acquire_call bits raw indexWord hb
  have h1:=copy_raw_call bits raw indexWord
  have h2:=block_call bits raw indexWord
  obtain ⟨b,hbTime,hbody⟩:=body_run bits raw indexWord
  have h3 : Runs program b .activity (afterBlock bits raw indexWord) .done
      (SemiprimeD1StackPublicInputState.done bits raw indexWord).data := by
    simpa only [afterBlock,header_acquired,SemiprimeD1StackPublicInputState.done] using hbody
  have hh:=SemiprimeD1StackProcedureFragments.Runs.trans h0
    (SemiprimeD1StackProcedureFragments.Runs.trans h1
      (SemiprimeD1StackProcedureFragments.Runs.trans h2 h3))
  obtain ⟨finish,hfinish,hAt⟩:=hh [] (initial bits raw indexWord) ⟨rfl,rfl,rfl⟩
  refine ⟨(a+1)+((5*raw.length+4)+((SemiprimeD1StackWordBlockExecution.totalTime (M.cached bits)+1)+b))+1,?_,?_⟩
  · unfold timeBound
    omega
  · rw [SemiprimeD1StackReturnLink.run_add,hfinish,Option.bind_some]
    rcases hAt with ⟨hpc,hd,hframes⟩
    change C.step program finish=some (SemiprimeD1StackPublicInputState.done bits raw indexWord)
    simp [C.step,SemiprimeD1StackCalls.step,hpc,program,C.execute,SemiprimeD1StackCalls.execute,hd,hframes,
      SemiprimeD1StackPublicInputState.done]
end RiemannGaussian.SemiprimeD1StackPublicInputExecution

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicInputControl
/-! # Actual first/nonfirst flag branches of PublicInput52 -/
set_option autoImplicit false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 1800000
set_option maxRecDepth 32768
namespace RiemannGaussian.SemiprimeD1StackPublicInputBranches
open SemiprimeD1StackPublicInput SemiprimeD1StackPublicInputState
open SemiprimeD1StackPublicInputComponents SemiprimeD1StackPublicInputControl
open SemiprimeD1StackProcedureFragments (Runs)
/-- Proof-side exact flag verdict; NEVER a runtime argument or evaluator. -/
def flagRule (bits raw indexWord : List Bool) : Bool :=
  decide (M.rawFlag bits raw= !(if indexWord.isEmpty then
    SemiprimeD1StackWordLessExecution.answer (M.word bits raw) [false,true]
    else decide (SemiprimeBitArithmetic.bitValue (M.word bits raw)=0)))
/-- Actual computed test pop, flag peek, result push and ALL cleanup. -/
theorem test_finish (bits indexWord raw reader word : List Bool) (test : Bool) :
    Runs program (word.length+5) .readTest
      (store (header bits indexWord []) raw reader word [] [test] []) .done
      (store (header bits indexWord []) raw reader [] [] []
        [decide (reader.head?.getD false= !test)]) := by
  have h0:=read_comparison .readTest .bad Label.flag rfl (header bits indexWord []) raw reader word test
  have h1:=flag_peek test (header bits indexWord []) raw reader word
  have h2:=write_finish bits indexWord [] raw reader word ((!test)==reader.head?.getD false)
  have h:=h0.trans (h1.trans h2)
  simpa only [List.length_nil,SemiprimeD1StackPublicInputMeaning.flag_orientation,
    Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
/-- Actual inactive zero result pop and complete residual-bound cleanup. -/
theorem zero_finish (bits indexWord bd raw reader : List Bool) (test : Bool) :
    Runs program (bd.length+4) .readZero
      (store (header bits indexWord bd) raw reader [] [] [test] []) .done
      (store (header bits indexWord []) raw reader [] [] [] [test]) := by
  have h0:=read_comparison .readZero .bad Label.write rfl (header bits indexWord bd) raw reader [] test
  have h1:=write_finish bits indexWord bd raw reader [] test
  simpa only [List.length_nil,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h0.trans h1
/-- Both first/nonfirst branches execute concrete comparators. No zero/nonzero,
less-than-two, flag or component-time answer is supplied. -/
theorem index_tail (bits raw indexWord : List Bool) :
    ∃t≤40*((M.word bits raw).length+3),Runs program t .indexCase
      (store (header bits indexWord []) raw (suffix bits raw) (M.word bits raw) [] [] []) .done
      (store (header bits indexWord []) raw (suffix bits raw) [] [] [] [flagRule bits raw indexWord]) := by
  have hindex:=index_peek bits indexWord raw (suffix bits raw) (M.word bits raw)
  by_cases hi:indexWord.isEmpty=true
  · have h0 : Runs program 1 .indexCase
        (store (header bits indexWord []) raw (suffix bits raw) (M.word bits raw) [] [] []) .firstCopy
        (store (header bits indexWord []) raw (suffix bits raw) (M.word bits raw) [] [] []) := by
      simpa only [hi,ite_true] using hindex
    have h1:=copy_word_call .firstCopy .twoHigh rfl (header bits indexWord []) raw (suffix bits raw) (M.word bits raw)
    have h2:=push_two bits indexWord raw (suffix bits raw) (M.word bits raw)
    have h3:=less_call .firstCheck .readTest rfl bits indexWord raw (suffix bits raw) (M.word bits raw)
      (M.word bits raw) [false,true]
    have h4:=test_finish bits indexWord raw (suffix bits raw) (M.word bits raw)
      (SemiprimeD1StackWordLessExecution.answer (M.word bits raw) [false,true])
    have hh:=SemiprimeD1StackProcedureFragments.Runs.trans h0
      (SemiprimeD1StackProcedureFragments.Runs.trans h1
        (SemiprimeD1StackProcedureFragments.Runs.trans h2
          (SemiprimeD1StackProcedureFragments.Runs.trans h3 h4)))
    refine ⟨1+((5*(M.word bits raw).length+4)+(2+
      ((SemiprimeD1StackWordLessExecution.totalTime (M.word bits raw) [false,true]+1)+
        ((M.word bits raw).length+5)))),?_,?_⟩
    · have hb:=SemiprimeD1StackWordLessExecution.totalTime_le (M.word bits raw) [false,true]
      simp only [List.length_cons,List.length_nil] at hb
      omega
    · have hv : decide ((suffix bits raw).head?.getD false=
          !SemiprimeD1StackWordLessExecution.answer (M.word bits raw) [false,true])=flagRule bits raw indexWord := by
        unfold flagRule
        apply decide_eq_decide.mpr
        simp only [hi,ite_true,M.rawFlag,suffix]
      rw [←hv]
      exact hh
  · have hn:indexWord.isEmpty=false:=by cases h:indexWord.isEmpty <;> simp_all
    have h0 : Runs program 1 .indexCase
        (store (header bits indexWord []) raw (suffix bits raw) (M.word bits raw) [] [] []) .nonzero
        (store (header bits indexWord []) raw (suffix bits raw) (M.word bits raw) [] [] []) := by
      simpa only [hn,Bool.false_eq_true,ite_false] using hindex
    have h1:=equal_call .nonzero .readTest rfl (header bits indexWord []) raw (suffix bits raw) (M.word bits raw)
    have h2:=test_finish bits indexWord raw (suffix bits raw) []
      (decide (SemiprimeBitArithmetic.bitValue (M.word bits raw)=0))
    have hh:=SemiprimeD1StackProcedureFragments.Runs.trans h0
      (SemiprimeD1StackProcedureFragments.Runs.trans h1 h2)
    refine ⟨1+((SemiprimeD1StackWordEqualExecution.executionTime (M.word bits raw) []+1)+(0+5)),?_,?_⟩
    · have hb:=SemiprimeD1StackWordEqualExecution.executionTime_le (M.word bits raw) []
      simp only [List.length_nil] at hb
      omega
    · have hv : decide ((suffix bits raw).head?.getD false=
          !decide (SemiprimeBitArithmetic.bitValue (M.word bits raw)=0))=flagRule bits raw indexWord := by
        unfold flagRule
        apply decide_eq_decide.mpr
        simp only [hn,Bool.false_eq_true,ite_false,M.rawFlag,suffix]
      rw [←hv]
      exact hh
end RiemannGaussian.SemiprimeD1StackPublicInputBranches

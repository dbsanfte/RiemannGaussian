/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceKeyFrequencyCounter
import RiemannGaussian.SemiprimeD1StackSourceKeyFrequencyCalls
import RiemannGaussian.SemiprimeD1StackSourceKeyFrequencyEncoding
/-! # Actual compact frequency increment and strict maximum replacement -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceKeyFrequencyMaximum
open SemiprimeD1StackSourceKeyFrequency SemiprimeD1StackSourceKeyFrequencyEncoding
open SemiprimeD1StackSourceKeyFrequencyPrimitives SemiprimeD1StackSourceKeyFrequencyCalls
open SemiprimeD1StackSourceKeyFrequencyCounter SemiprimeD1StackProcedureTrace
/-- Both copies, real subtractor/borrow, optional old-maximum drain/copy and actual Boolean pop are paid. -/
def maximumClock (maximum count:List Bool) :Nat :=
  5*maximum.length+4+(5*count.length+4)+SemiprimeD1StackWordLessExecution.totalTime maximum count+2+
    if SemiprimeD1StackWordLessExecution.answer maximum count then maximum.length+1+5*count.length+4 else 0
/-- Only actual byte comparison determines replacement; equal maxima retain the existing word. -/
theorem maximum_run (src reader raw count:List Bool) (s:Summary) :
    Runs program (maximumClock s.maximum count) .copyMaximum
      (bank {loopWords src reader s with raw:=raw,query:=encoded raw,count:=count}) .frameCount
      (bank {loopWords src reader s with raw:=raw,query:=encoded raw,count:=count,maximum:=nextMaximum s.maximum count}) :=by
  let w0:Words:={loopWords src reader s with raw:=raw,query:=encoded raw,count:=count}
  let w1:Words:={w0 with left:=s.maximum}
  let w2:Words:={w1 with right:=count}
  let answer:=SemiprimeD1StackWordLessExecution.answer s.maximum count
  let w3:Words:={w2 with left:=[],right:=[],discard:=[answer]}
  let w4:Words:={w3 with discard:=[]}
  have h0:=copy_call .maxLeft .copyMaximum .copyCount rfl (bank w0) s.maximum [] rfl rfl rfl
  change Runs program (5*s.maximum.length+4) .copyMaximum (bank w0) .copyCount (Function.update (bank w0) (lookupStack (.inl .left)) (s.maximum++[])) at h0
  rw [List.append_nil,update_left] at h0
  change Runs program (5*s.maximum.length+4) .copyMaximum (bank w0) .copyCount (bank w1) at h0
  have h1:=copy_call .countRight .copyCount .compare rfl (bank w1) count [] rfl rfl rfl
  change Runs program (5*count.length+4) .copyCount (bank w1) .compare (Function.update (bank w1) (lookupStack (.inl .right)) (count++[])) at h1
  rw [List.append_nil,update_right] at h1
  change Runs program (5*count.length+4) .copyCount (bank w1) .compare (bank w2) at h1
  have h2:=less_call (bank w2) s.maximum count (by intro k;rcases k with k|k <;> cases k <;> rfl)
  rw [update_left,update_right,update_discard] at h2
  change Runs program (SemiprimeD1StackWordLessExecution.totalTime s.maximum count+1) .compare (bank w2) .readMaximum (bank w3) at h2
  have h3:=pop_run .readMaximum .abort .frameCount .clearMaximum (lookupStack (.inr .discard)) (bank w3) [answer] rfl rfl
  rw [update_discard] at h3
  by_cases ha:answer=true
  · have hl:SemiprimeD1StackBytecode.choose Label.abort Label.frameCount Label.clearMaximum [answer].head?=Label.clearMaximum:=by rw [ha];rfl
    rw [hl] at h3
    change Runs program 1 .readMaximum (bank w3) .clearMaximum (bank w4) at h3
    have h4:=drain_loop .clearMaximum .saveMaximum (aux .maximum) rfl (bank w4) s.maximum rfl
    rw [update_maximum] at h4
    have h5:=copy_call .newMaximum .saveMaximum .frameCount rfl (bank {w4 with maximum:=[]}) count [] rfl rfl rfl
    change Runs program (5*count.length+4) .saveMaximum (bank {w4 with maximum:=[]}) .frameCount (Function.update (bank {w4 with maximum:=[]}) (aux .maximum) (count++[])) at h5
    rw [List.append_nil,update_maximum] at h5
    have h:=join (join (join (join (join h0 h1) h2) h3) h4) h5
    simp only [maximumClock,nextMaximum,show SemiprimeD1StackWordLessExecution.answer s.maximum count=true from ha,ite_true]
    convert h using 1 <;> first | omega | rfl
  · have haf:answer=false:=Bool.eq_false_iff.mpr ha
    have hl:SemiprimeD1StackBytecode.choose Label.abort Label.frameCount Label.clearMaximum [answer].head?=Label.frameCount:=by rw [haf];rfl
    rw [hl] at h3
    change Runs program 1 .readMaximum (bank w3) .frameCount (bank w4) at h3
    have h:=join (join (join h0 h1) h2) h3
    simp only [maximumClock,nextMaximum,show SemiprimeD1StackWordLessExecution.answer s.maximum count=false from haf,
      Bool.false_eq_true,ite_false,Nat.add_zero]
    convert h using 1; first | omega | rfl
/-- Real reusable compact-counter entry and its real local return are part of the whole row. -/
theorem successor_run (src reader raw:List Bool) (s:Summary) :
    ∃q≤40*((read s.rows raw).length+1)+2,Runs program q .successor
      (bank {loopWords src reader s with raw:=raw,query:=encoded raw,oldCount:=read s.rows raw}) .copyMaximum
      (bank {loopWords src reader s with raw:=raw,query:=encoded raw,count:=nextCount s.rows raw}) :=by
  let w:Words:={loopWords src reader s with raw:=raw,query:=encoded raw,oldCount:=read s.rows raw}
  obtain ⟨q,hq,hr⟩:=counter_run (bank w) (read s.rows raw) rfl rfl rfl rfl rfl rfl rfl
  rw [update_oldCount,update_count] at hr
  refine ⟨q+2,by omega,?_⟩
  exact local_call .successor .increment .copyMaximum rfl q _ _ hr
end RiemannGaussian.SemiprimeD1StackSourceKeyFrequencyMaximum

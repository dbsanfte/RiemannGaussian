/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceEnvironmentPrimitives
import RiemannGaussian.SemiprimeD1StackSourceEnvironmentEncoding
/-! # Same-source actual compact key increment, overflow and cleanup -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceEnvironmentCounter
open SemiprimeD1StackSourceEnvironment SemiprimeD1StackSourceEnvironmentPrimitives
open SemiprimeD1StackSourceEnvironmentEncoding SemiprimeD1StackProcedureTrace
local notation "ctl" => Label.local
/-- Only the actually popped overflow bit selects the one literal high carry write. -/
theorem carry_run (carry:Bool) (before:Stack→List Bool) :
    Runs program 1 (ctl (.counterCarry carry)) before (ctl .trimCounter)
      (if carry then Function.update before (aux .trimScratch) (true::before (aux .trimScratch)) else before) :=by
  cases carry
  · exact one_base program _ _ (.jump (ctl .trimCounter)) _ _ rfl rfl rfl
  · exact push_run (.counterCarry true) (ctl .trimCounter) (aux .trimScratch) true before rfl
/-- Real increment, physical overflow pop/reverse/carry and real trim; every other caller word is retained. -/
theorem counter_run (before:Stack→List Bool) (word:List Bool)
    (hw:before (aux .nextKey)=word) (hn:before (aux .incNext)=[])
    (hi:before (aux .incScratch)=[]) (ht:before (aux .trimScratch)=[])
    (hc:before (aux .copyWork)=[]) (hf:before (aux .frameScratch)=[]) :
    ∃q≤40*(word.length+1),Runs program q (ctl .increment) before (ctl .clearMarked)
      (Function.update before (aux .nextKey) (successor word)) :=by
  let carry:=SemiprimeD1StackIncrement.overflow word
  let wrapped:=SemiprimeD1StackIncrement.wrapped word
  let b0:=Function.update (Function.update before (aux .nextKey) []) (aux .incNext) (carry::wrapped)
  let b1:=Function.update b0 (aux .incNext) wrapped
  let b2:=Function.update (Function.update b1 (aux .incNext) []) (aux .trimScratch) wrapped.reverse
  let b3:=if carry then Function.update b2 (aux .trimScratch) (true::b2 (aux .trimScratch)) else b2
  obtain ⟨a,ha,h0⟩:=increment_call before word hw hi hn
  change Runs program a _ _ _ b0 at h0
  have h1:=pop_run .popOverflow (ctl .abort) (ctl (.reverseCounter false)) (ctl (.reverseCounter true))
    (aux .incNext) b0 (carry::wrapped) rfl rfl
  have hlab:SemiprimeD1StackBytecode.choose (ctl .abort) (ctl (.reverseCounter false)) (ctl (.reverseCounter true))
      (carry::wrapped).head?=ctl (.reverseCounter carry):=by cases carry <;> rfl
  rw [hlab] at h1
  change Runs program 1 _ b0 (ctl (.reverseCounter carry)) b1 at h1
  have h2:=reverse_call .counter (.reverseCounter carry) (.counterCarry carry) rfl b1 wrapped [] rfl
    (by simpa [b1,b0,reverseStack,aux,Function.update] using ht)
  simp only [List.append_nil] at h2
  change Runs program (2*wrapped.length+3) _ b1 _ b2 at h2
  have h3:=carry_run carry b2
  change Runs program 1 _ b2 _ b3 at h3
  have hscratch:b3 (aux .trimScratch)=successorScratch word:=by
    dsimp only [b3,b2,b1,b0,carry,wrapped,successorScratch]
    split <;> rfl
  have h4:=trim_call .counter .trimCounter .clearMarked rfl b3 (successorScratch word) []
    (by cases hb:carry <;> simpa [b3,b2,b1,b0,hb,trimStack,aux,Function.update] using hc)
    (by cases hb:carry <;> simpa [b3,b2,b1,b0,hb,trimStack,aux,Function.update] using hf) hscratch
    (by dsimp only [b3];split <;> rfl)
  simp only [List.append_nil] at h4
  have he:Function.update (Function.update b3 (trimStack .counter .scratch) []) (trimStack .counter .output)
      (SemiprimeD1StackReduceExecution.trimReverse (successorScratch word))=
      Function.update before (aux .nextKey) (successor word):=by
    change Function.update (Function.update b3 (aux .trimScratch) []) (aux .nextKey) (successor word)=_
    funext k
    cases hb:carry <;> rcases k with k|k
    · simp [b3,hb,b2,b1,b0,aux,Function.update]
    · cases k <;> simp [b3,hb,b2,b1,b0,aux,Function.update]
      all_goals first | exact hn | exact ht
    · simp [b3,hb,b2,b1,b0,aux,Function.update]
    · cases k <;> simp [b3,hb,b2,b1,b0,aux,Function.update]
      all_goals first | exact hn | exact ht
  rw [he] at h4
  have h:=join (join (join (join h0 h1) h2) h3) h4
  refine ⟨_,?_,h⟩
  have htrim:=SemiprimeD1StackReduceExecution.trimTime_le (successorScratch word)
  have hlen:(successorScratch word).length≤word.length+1:=by
    unfold successorScratch
    split <;> simp only [List.length_cons,List.length_reverse,SemiprimeD1StackIncrement.wrapped_length] <;> omega
  have hwrap:wrapped.length=word.length:=SemiprimeD1StackIncrement.wrapped_length word
  omega
end RiemannGaussian.SemiprimeD1StackSourceEnvironmentCounter

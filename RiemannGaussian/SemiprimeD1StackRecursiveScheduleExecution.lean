/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecursiveSchedule

/-! # Same-program conditional guard/successor execution with real nested returns -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
namespace RiemannGaussian.SemiprimeD1StackRecursiveScheduleExecution
open SemiprimeD1StackRecursiveSchedule SemiprimeD1StackProcedureTrace
local notation "ctl" => (Sum.inl : Control→Label)
/-- Actual trace concatenation for this single fixed front-end program. -/
theorem join {m n:Nat} {pc mid next:Label} {before between after:Stack→List Bool}
    (h:Runs program m pc before mid between) (g:Runs program n mid between next after) :
    Runs program (m+n) pc before next after :=
  runs_trans program m n pc mid next before between after h g
/-- The included actual guard acquires its verdict and clears all private work. -/
theorem guard_call (a:List Bool) (v:SemiprimeD1StackScheduleActive.Param→Nat) :
    ∃t≤200*(A.volume v+1),Runs program (t+1) (ctl .start) (initial a v).data
      (ctl .branch) (ready a v) := by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackScheduleActiveExecution.source_run v
  refine ⟨t,ht,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program guardStack guardLabel
    Sum.inl_injective A.program (.inl (.left .leaf)) (fun _=>rfl)
    (ctl .start) (ctl .branch) rfl t (A.start v) (A.done v) _ _ rfl rfl rfl rfl hr
  · constructor
    · intro k;rfl
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk;cases k with
      | inl k=>exact (hk k rfl).elim
      | inr k=>rfl
/-- The included real successor reads the guard's retained level stack directly. -/
theorem successor_call (a:List Bool) (v:SemiprimeD1StackScheduleActive.Param→Nat) :
    Runs program (S.runTime a (A.unaryWords v .levels)+1) (ctl .successor) (ready a v)
      (ctl .done) (afterSuccessor a v) := by
  apply SemiprimeD1StackProcedureCallsTrace.included_call program successorStack successorLabel
    successor_injective S.program (.inl .start) (fun _=>rfl) (ctl .successor) (ctl .done) rfl
    (S.runTime a (A.unaryWords v .levels)) (S.initial a (A.unaryWords v .levels))
    (S.done a (A.unaryWords v .levels)) _ _ rfl rfl rfl rfl
    (SemiprimeD1StackScheduleSuccessorExecution.source_run a (A.unaryWords v .levels))
  · constructor
    · intro k
      exact payload_successor (A.done v).data (S.initial a (A.unaryWords v .levels)).data rfl k
    · intro k _;rfl
  · constructor
    · intro k
      exact payload_successor (A.done v).data (S.result a (A.unaryWords v .levels)) rfl k
    · intro k hk;cases k with
      | inl k=>rfl
      | inr k=>cases k <;> first
          | rfl
          | exact False.elim (hk .nextLevels rfl)
          | exact False.elim (hk .nextExponent rfl)
/-- A real physical peek chooses whether any child metadata is constructed. -/
theorem branch_run (a:List Bool) (v:SemiprimeD1StackScheduleActive.Param→Nat) (b:Bool)
    (hb:A.answer v=b) :
    Runs program 1 (ctl .branch) (ready a v)
      (ctl (if b then Control.successor else Control.done)) (ready a v) := by
  apply one_base program (ctl .branch) _
    (.peek (guardStack .output) (ctl .done) (ctl .done) (ctl .successor)) _ _ rfl
  · cases b <;> simp [SemiprimeD1StackBytecode.execute,SemiprimeD1StackBytecode.choose,
      ready,payload,guardStack,SemiprimeD1StackScheduleActiveExecution.done,
      SemiprimeD1StackScheduleActive.data,hb]
  · rfl
/-- The guard and optional successor execute in one program and share one own clock. -/
theorem source_trace (a:List Bool) (v:SemiprimeD1StackScheduleActive.Param→Nat) :
    ∃t,t+1≤runBound a v ∧ Runs program t (ctl .start) (initial a v).data
      (ctl .done) (result a v) := by
  obtain ⟨t,ht,hg⟩:=guard_call a v
  cases hb:A.answer v with
  | false=>
    have hp:=branch_run a v false hb
    simp only [Bool.false_eq_true,ite_false] at hp
    have h:=join hg hp
    refine ⟨(t+1)+1,?_,?_⟩
    · unfold runBound;omega
    · simpa only [result,hb,Bool.false_eq_true,ite_false] using h
  | true=>
    have hp:=branch_run a v true hb
    simp only [ite_true] at hp
    have h:=join (join hg hp) (successor_call a v)
    refine ⟨((t+1)+1)+(S.runTime a (A.unaryWords v .levels)+1),?_,?_⟩
    · have hs:=SemiprimeD1StackScheduleSuccessorBounds.runTime_le a (A.unaryWords v .levels)
      have hu:=SemiprimeD1StackScheduleActiveBounds.parameter_le v .levels
      simp only [A.unaryWords,List.length_replicate] at hs
      simp only [A.unaryWords]
      unfold runBound
      omega
    · simpa only [result,hb,ite_true] using h
/-- Complete same-program run, including the literal final halt. -/
theorem source_run (a:List Bool) (v:SemiprimeD1StackScheduleActive.Param→Nat) :
    ∃t≤runBound a v,SemiprimeD1StackCalls.run program t (initial a v)=some (done a v) := by
  obtain ⟨t,ht,h⟩:=source_trace a v
  obtain ⟨finish,hf,hs⟩:=h [] (initial a v) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program (ctl .done) rfl (result a v) [] finish hs
  refine ⟨t+1,ht,?_⟩
  rw [SemiprimeD1StackReturnLink.run_add,hf,Option.bind_some]
  exact hh
end RiemannGaussian.SemiprimeD1StackRecursiveScheduleExecution

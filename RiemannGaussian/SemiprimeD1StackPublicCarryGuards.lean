/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicCarryAcquire
/-! # Three ACTUAL copied-operand guards and computed branch
No coefficient/carry canonicality, comparison answer or branch verdict is an
executing input or a hypothesis of the completed public carry pipeline.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 4096
namespace RiemannGaussian.SemiprimeD1StackPublicCarryGuards
open SemiprimeD1StackPublicCarry SemiprimeD1StackPublicCarryState SemiprimeD1StackPublicCarryPrimitives
open SemiprimeD1StackProcedureTrace
/-- Exact actual copy/comparison/pop count of one guard. -/
def guardBudget (context : T.Stack→List Bool) (raw : List Bool) (k : Fin 3) : ℕ :=
  (5*(word context raw k).length+4)+(5*(SemiprimeD1StackPublicCarryState.guardBound context k).length+4)+
    (SemiprimeD1StackWordLessExecution.totalTime (word context raw k) (SemiprimeD1StackPublicCarryState.guardBound context k)+1)+1
/-- Each physical guard preserves all source caches, uses actual fresh copies,
and consumes the actual returned Boolean to choose the next controller label. -/
theorem guard_run (context : T.Stack→List Bool) (raw : List Bool) (k : Fin 3) :
    Runs program (guardBudget context raw k) (.guardOperand k) (view context (ready context raw))
      (if guardAnswer context raw k then afterGuard k else .reject) (view context (ready context raw)) := by
  let p:=ready context raw
  let w:=word context raw k
  let b:=SemiprimeD1StackPublicCarryState.guardBound context k
  let p1:=set p .blockOut w
  let p2:=set p1 .blockCount b
  let p3:=set (set (set p2 .blockOut []) .blockCount []) .valid [guardAnswer context raw k]
  have hw : copied context p (.operand k)=w := by fin_cases k <;> rfl
  have h0:=copy_call (.operand k) (.guardOperand k) (.guardBound k) rfl context p rfl rfl
  rw [hw] at h0
  change Runs program (5*w.length+4) (.guardOperand k) (view context p) (.guardBound k) (view context p1) at h0
  have hb : copied context p1 (.guardBound k)=b := by fin_cases k <;> rfl
  have h1:=copy_call (.guardBound k) (.guardBound k) (.compare k) rfl context p1 rfl rfl
  rw [hb] at h1
  change Runs program (5*b.length+4) (.guardBound k) (view context p1) (.compare k) (view context p2) at h1
  have h2 : Runs program (SemiprimeD1StackWordLessExecution.totalTime w b+1) (.compare k)
      (view context p2) (.tested k) (view context p3) := less_call k context p2 rfl rfl rfl
  have h3:=pop_aux (.tested k) .bad .reject (afterGuard k) .valid rfl context p3
  change Runs program 1 (.tested k) (view context p3)
    (SemiprimeD1StackBytecode.choose .bad .reject (afterGuard k) (some (guardAnswer context raw k)))
    (view context p) at h3
  have hchoose : SemiprimeD1StackBytecode.choose Label.bad Label.reject (afterGuard k)
      (some (guardAnswer context raw k))=(if guardAnswer context raw k then afterGuard k else .reject) := by
    cases guardAnswer context raw k <;> rfl
  rw [hchoose] at h3
  exact runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ h0 h1) h2) h3
/-- Conjunction of actual computed guard bits; not supplied branch advice. -/
def allGuards (context : T.Stack→List Bool) (raw : List Bool) : Bool :=
  guardAnswer context raw 0 && (guardAnswer context raw 1 && guardAnswer context raw 2)
/-- A common allowance pays all actually visited guards, including real copies. -/
def guardsBudget (context : T.Stack→List Bool) (raw : List Bool) : ℕ :=
  guardBudget context raw 0+guardBudget context raw 1+guardBudget context raw 2
/-- Exact short-circuit guard execution and selected branch. No ordering/guard
truth is assumed: both success and every early rejected branch are proved. -/
theorem guards_run (context : T.Stack→List Bool) (raw : List Bool) :
    ∃t ≤ guardsBudget context raw,Runs program t (.guardOperand 0) (view context (ready context raw))
      (if allGuards context raw then .frame 3 else .reject) (view context (ready context raw)) := by
  have h0:=guard_run context raw 0
  cases hg0 : guardAnswer context raw 0 with
  | false=>
    have h0' : Runs program (guardBudget context raw 0) (.guardOperand 0) (view context (ready context raw))
        .reject (view context (ready context raw)) := by simpa only [hg0,Bool.false_eq_true,ite_false] using h0
    refine ⟨guardBudget context raw 0,?_,?_⟩
    · unfold guardsBudget;omega
    · simpa only [allGuards,hg0,Bool.false_and,Bool.false_eq_true,ite_false] using h0'
  | true=>
    have h0' : Runs program (guardBudget context raw 0) (.guardOperand 0) (view context (ready context raw))
        (.guardOperand 1) (view context (ready context raw)) := by simpa [hg0,afterGuard] using h0
    have h1:=guard_run context raw 1
    cases hg1 : guardAnswer context raw 1 with
    | false=>
      have h1' : Runs program (guardBudget context raw 1) (.guardOperand 1) (view context (ready context raw))
          .reject (view context (ready context raw)) := by simpa only [hg1,Bool.false_eq_true,ite_false] using h1
      have h:=runs_trans program _ _ _ _ _ _ _ _ h0' h1'
      refine ⟨guardBudget context raw 0+guardBudget context raw 1,?_,?_⟩
      · unfold guardsBudget;omega
      · simpa only [allGuards,hg0,hg1,Bool.true_and,Bool.false_and,Bool.false_eq_true,ite_false] using h
    | true=>
      have h1' : Runs program (guardBudget context raw 1) (.guardOperand 1) (view context (ready context raw))
          (.guardOperand 2) (view context (ready context raw)) := by simpa [hg1,afterGuard] using h1
      have h2:=guard_run context raw 2
      cases hg2 : guardAnswer context raw 2 with
      | false=>
        have h2' : Runs program (guardBudget context raw 2) (.guardOperand 2) (view context (ready context raw))
            .reject (view context (ready context raw)) := by simpa only [hg2,Bool.false_eq_true,ite_false] using h2
        have h:=runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ h0' h1') h2'
        refine ⟨guardsBudget context raw,le_rfl,?_⟩
        simpa only [guardsBudget,allGuards,hg0,hg1,hg2,Bool.true_and,Bool.false_eq_true,ite_false] using h
      | true=>
        have h2' : Runs program (guardBudget context raw 2) (.guardOperand 2) (view context (ready context raw))
            (.frame 3) (view context (ready context raw)) := by simpa [hg2,afterGuard] using h2
        have h:=runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ h0' h1') h2'
        refine ⟨guardsBudget context raw,le_rfl,?_⟩
        simpa only [guardsBudget,allGuards,hg0,hg1,hg2,Bool.true_and,ite_true] using h
/-- The complete actual verdict is precisely the guard conjunction AND INTEGER equation. -/
theorem answer_split (context : T.Stack→List Bool) (raw : List Bool) :
    answer context raw=(allGuards context raw && equationAnswer context raw) := by
  simp only [answer,allGuards,Bool.and_assoc]
end RiemannGaussian.SemiprimeD1StackPublicCarryGuards

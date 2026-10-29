/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicCarryEquation
/-! # Closed physical carry body, with computed guards and integer verdict
The context below is a proof view of already acquired physical stacks. It is
not an executing lookup, producer, expected-answer or clock argument.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 4096
namespace RiemannGaussian.SemiprimeD1StackPublicCarryExecution
open SemiprimeD1StackPublicCarry SemiprimeD1StackPublicCarryState
open SemiprimeD1StackPublicCarryAcquire SemiprimeD1StackPublicCarryGuards
open SemiprimeD1StackPublicCarryEquation SemiprimeD1StackProcedureTrace
/-- Full actual three-word parser transition count. -/
def parseBudget (context : T.Stack→List Bool) (raw : List Bool) : ℕ :=
  8*(coefficient context raw).length+9+(8*(previous context raw).length+9)+
    (8*(next context raw).length+9)+1
/-- An allowance for the actually taken branch, paying every real component. -/
def bodyBudget (context : T.Stack→List Bool) (raw : List Bool) : ℕ :=
  3+(SemiprimeD1StackWordVectorExecution.timeBound raw (width context) three+1)+
  parseBudget context raw+(5*(width context).length+6)+guardsBudget context raw+
  (1+clearBudget context raw)+(framesBudget context raw+clearBudget context raw+equationBudget context raw)
/-- Complete executable body: raw assignment acquisition, actual guards, and the
actual integer equation. Neither successful guards nor a verdict are premises. -/
theorem body_run (context : T.Stack→List Bool) (raw : List Bool) :
    ∃t ≤ bodyBudget context raw,Runs program t (.seed 0) (view context (rawPayload raw))
      .done (view context (clean context raw (answer context raw))) := by
  obtain ⟨tv,hv,rv⟩:=vector_call context raw
  obtain ⟨tg,hg,rg⟩:=guards_run context raw
  have pre:=runs_trans program _ _ _ _ _ _ _ _
    (runs_trans program _ _ _ _ _ _ _ _
      (runs_trans program _ _ _ _ _ _ _ _ (seed_run context raw) rv)
      (parse_run context raw)) (bound_run context raw)
  have all:=runs_trans program _ _ _ _ _ _ _ _ pre rg
  cases ha : allGuards context raw with
  | false=>
    have all' : Runs program (3+tv+parseBudget context raw+(5*(width context).length+6)+tg)
        (.seed 0) (view context (rawPayload raw)) .reject (view context (ready context raw)) := by
      simpa only [parseBudget,ha,Bool.false_eq_true,ite_false] using all
    have done:=runs_trans program _ _ _ _ _ _ _ _ all' (reject_run context raw)
    refine ⟨3+tv+parseBudget context raw+(5*(width context).length+6)+tg+(1+clearBudget context raw),?_,?_⟩
    · unfold bodyBudget;omega
    · simpa only [answer_split,ha,Bool.false_and] using done
  | true=>
    have all' : Runs program (3+tv+parseBudget context raw+(5*(width context).length+6)+tg)
        (.seed 0) (view context (rawPayload raw)) (.frame 3) (view context (ready context raw)) := by
      simpa only [parseBudget,ha,ite_true] using all
    have done:=runs_trans program _ _ _ _ _ _ _ _ all' (success_run context raw)
    refine ⟨3+tv+parseBudget context raw+(5*(width context).length+6)+tg+
      (framesBudget context raw+clearBudget context raw+equationBudget context raw),?_,?_⟩
    · unfold bodyBudget;omega
    · simpa only [answer_split,ha,Bool.true_and] using done
/-- The actually acquired original-public physical cache, not a supplied context. -/
def actualContext (bits index : List Bool) : T.Stack→List Bool :=
  (SemiprimeD1StackPublicTargetExecution.done bits index).data
/-- The complete clean halt retains the original acquisition and raw assignment. -/
def done (bits raw index : List Bool) : C.State Stack Label :=
  ⟨none,none,none,view (actualContext bits index)
    (clean (actualContext bits index) raw (answer (actualContext bits index) raw)),[]⟩
/-- Original metadata and target acquisition executes ONCE before grouping. -/
theorem target_call (bits raw index : List Bool) (hb : bits≠[]) :
    ∃t ≤ SemiprimeD1StackPublicTargetBounds.timeBound bits index+1,
      Runs program t .start (initial bits raw index).data (.seed 0)
        (view (actualContext bits index) (rawPayload raw)) := by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackPublicTargetBounds.source_run_bounded bits index hb
  refine ⟨t+1,Nat.add_le_add_right ht 1,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program Sum.inl Label.target Sum.inl_injective
    T.program .start (fun _=>rfl) .start (.seed 0) rfl t
    (T.initial bits index) (SemiprimeD1StackPublicTargetExecution.done bits index)
    _ _ rfl rfl rfl rfl hr
  · constructor
    · intro k;rfl
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk;rcases k with k|k
      · exact (hk k rfl).elim
      · rfl
/-- Actual whole-program allowance, including both real calls and final halt. -/
def timeBound (bits raw index : List Bool) : ℕ :=
  SemiprimeD1StackPublicTargetBounds.timeBound bits index+bodyBudget (actualContext bits index) raw+2
/-- CLOSED original-binary acquisition → raw three-word acquisition → physical
canonicality guards → physical INTEGER equation. No prepared operand/target,
metadata answer, guard, expected verdict, source or component clock is supplied. -/
theorem source_run (bits raw index : List Bool) (hb : bits≠[]) :
    ∃t ≤ timeBound bits raw index,
      C.run program t (initial bits raw index)=some (done bits raw index) := by
  obtain ⟨t,ht,h0⟩:=target_call bits raw index hb
  obtain ⟨u,hu,h1⟩:=body_run (actualContext bits index) raw
  obtain ⟨finish,hfinish,hout⟩:=(runs_trans program _ _ _ _ _ _ _ _ h0 h1) []
    (initial bits raw index) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program .done rfl
    (view (actualContext bits index) (clean (actualContext bits index) raw
      (answer (actualContext bits index) raw))) [] finish hout
  refine ⟨t+u+1,?_,?_⟩
  · unfold timeBound;omega
  · rw [SemiprimeD1StackReturnLink.run_add,hfinish,Option.bind_some,hh]
    rfl
end RiemannGaussian.SemiprimeD1StackPublicCarryExecution

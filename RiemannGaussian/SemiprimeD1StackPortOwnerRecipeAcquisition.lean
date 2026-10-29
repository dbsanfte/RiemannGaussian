/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPortOwnerRecipePrepare
import RiemannGaussian.SemiprimeD1StackPortOwnerRecipeModes
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
namespace RiemannGaussian.SemiprimeD1StackPortOwnerRecipeAcquisition
open SemiprimeD1StackPortOwnerRecipe SemiprimeD1StackPortOwnerRecipeSpec
open SemiprimeD1StackPortOwnerRecipePrepare SemiprimeD1StackPortOwnerRecipeModes
open SemiprimeD1StackProcedureTrace (Runs runs_refl runs_trans)
/-- Static preparation continuation used only in the trace proof. -/
def entry (count:ℕ) : Label :=
  if h:count<41 then .local (.prepare ⟨count,h⟩) else .local (.classify 0)
/-- The chronological sum of ACTUAL primitive call bounds, never a source operand. -/
def remainingBudget (p:Counters) : ℕ→ℕ→ℕ
  | 0,_=>0
  | fuel+1,count=>if h:count<41 then stepTime p ⟨count,h⟩+remainingBudget p fuel (count+1) else 0
/-- Every real preparation stage executes from its exact acquired predecessor store. -/
theorem suffix_run (p:Counters) (fuel count:ℕ) (hc:count+fuel=41) :
    ∃time≤remainingBudget p fuel count,Runs program time (entry count) (atStage p count)
      (.local (.classify 0)) (prepared p) := by
  induction fuel generalizing count with
  | zero=>
    have he:count=41:=by omega
    subst count
    exact ⟨0,le_rfl,runs_refl program _ _⟩
  | succ fuel ih=>
    have hcount:count<41:=by omega
    have hn:count+1+fuel=41:=by omega
    obtain ⟨time,ht,hr⟩:=ih (count+1) hn
    let j:Fin 41:=⟨count,hcount⟩
    obtain ⟨stepTime,hstepTime,hstep⟩:=prepare_step p j
    have hnext:nextPrepare j=entry (count+1):=by
      by_cases hh:count<40
      · have hsucc:count+1<41:=by omega
        simp [nextPrepare,entry,j,hh,hsucc]
      · have he:count=40:=by omega
        subst count
        rfl
    rw [hnext] at hstep
    have h:=runs_trans program _ _ _ _ _ _ _ _ hstep hr
    refine ⟨stepTime+time,?_,?_⟩
    · simp only [remainingBudget,dite_eq_left hcount]
      exact Nat.add_le_add hstepTime ht
    · have hentry:entry count=.local (.prepare j):=by simp [entry,hcount,j]
      rw [hentry]
      exact h
/-- ACTUAL original-counter literal-tag/arithmetic acquisition, including every included call. -/
theorem acquisition_run (p:Counters) :
    ∃time≤406+remainingBudget p 41 0,Runs program time (.local .start) (input (words p))
      (.local (.classify 0)) (prepared p) := by
  obtain ⟨m,hm,hr⟩:=modes_run p
  obtain ⟨n,hn,hs⟩:=suffix_run p 41 0 rfl
  change Runs program n (.local (.prepare 0)) (atStage p 0) (.local (.classify 0)) (prepared p) at hs
  exact ⟨m+n,Nat.add_le_add hm hn,runs_trans program _ _ _ _ _ _ _ _ hr hs⟩
end RiemannGaussian.SemiprimeD1StackPortOwnerRecipeAcquisition

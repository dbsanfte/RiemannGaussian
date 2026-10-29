/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPortOwnerRecipeCalls
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
namespace RiemannGaussian.SemiprimeD1StackPortOwnerRecipeModes
open SemiprimeD1StackPortOwnerRecipe SemiprimeD1StackPortOwnerRecipeSpec SemiprimeD1StackPortOwnerRecipeCalls
open SemiprimeD1StackProcedureTrace (Runs one_base runs_refl runs_trans)
open SemiprimeD1StackUnaryDivmod (unary)
/-- Actual source starts every literal mode cache empty, including mode zero. -/
theorem mode_initial (p:Counters) : input (words p)=atMode p 0 := by
  funext k
  rcases k with k|k
  · rfl
  · rcases k with k|k
    · cases k with
      | mode j=>
        by_cases h:j.val=0
        · simp [input,atMode,h,unary]
        · have hj:j≠0:=by intro he;exact h (congrArg Fin.val he)
          simp [input,atMode,hj]
      | _=>rfl
    · rfl
/-- A physically pushed next marker installs precisely the next literal mode word. -/
theorem mode_update (p:Counters) (j:Fin 9) :
    Function.update (atMode p j.val) (reg (.mode ⟨j.val+1,by omega⟩)) (unary (j.val+1))=
      atMode p (j.val+1) := by
  funext k
  rcases k with k|k
  · simp [atMode,reg,Function.update]
  · rcases k with k|k
    · cases k with
      | mode i=>
        by_cases he:i=⟨j.val+1,by omega⟩
        · subst i
          simp [atMode,reg,Function.update]
        · have hv:i.val≠j.val+1:=by intro h;exact he (Fin.ext h)
          have hc:i.val≤j.val+1 ↔ i.val≤j.val:=by omega
          simp [atMode,reg,Function.update,he,hc]
      | _=>simp [atMode,reg,Function.update]
    · simp [atMode,reg,Function.update]
/-- All literal mode tags have been physically acquired before any coordinate arithmetic. -/
theorem modes_ready (p:Counters) : atMode p 9=atStage p 0 := by
  funext k
  rcases k with k|k
  · rfl
  · rcases k with k|k
    · cases k with
      | mode j=>
        have hj:j.val≤9:=by omega
        simp [atMode,atStage,cached,hj]
      | _=>rfl
    · rfl
/-- Static continuation of the literal mode-word builder. -/
def nextMode (j:Fin 9) : Label :=
  if h:j.val<8 then .local (.modeCopy ⟨j.val+1,by omega⟩) else .local (.prepare 0)
/-- Real preserving copy followed by its real one-marker push. -/
theorem mode_step (p:Counters) (j:Fin 9) :
    Runs program (5*j.val+5) (.local (.modeCopy j)) (atMode p j.val)
      (nextMode j) (atMode p (j.val+1)) := by
  have hc:=copy_call (.mode j) (atMode p j.val) (.local (.modeCopy j)) (.local (.modePush j)) rfl rfl
  have hsource:(atMode p j.val) (copyOperands (.mode j)).1=unary j.val:=by
    simp [atMode,copyOperands,reg]
  have hdest:(atMode p j.val) (copyOperands (.mode j)).2=[]:=by
    simp [atMode,copyOperands,reg]
  rw [hsource,hdest,List.append_nil] at hc
  let copied:=Function.update (atMode p j.val) (reg (.mode ⟨j.val+1,by omega⟩)) (unary j.val)
  change Runs program (5*(unary j.val).length+4) (.local (.modeCopy j)) (atMode p j.val)
    (.local (.modePush j)) copied at hc
  have hp:Runs program 1 (.local (.modePush j)) copied (nextMode j) (atMode p (j.val+1)):=by
    apply one_base program (.local (.modePush j)) (nextMode j)
      (.push (reg (.mode ⟨j.val+1,by omega⟩)) true (nextMode j)) copied _ rfl rfl
    change Function.update copied (reg (.mode ⟨j.val+1,by omega⟩))
      (true::copied (reg (.mode ⟨j.val+1,by omega⟩)))=_
    dsimp [copied]
    rw [Function.update_self,Function.update_idem]
    rw [show true::unary j.val=unary (j.val+1) from (SemiprimeD1StackUnaryDivmod.unary_succ j.val).symm]
    exact mode_update p j
  have h:=runs_trans program _ _ _ _ _ _ _ _ hc hp
  simpa only [unary,List.length_replicate,show 5*j.val+4+1=5*j.val+5 by omega] using h
/-- Proof-side label for the remaining literal mode constructor suffix. -/
def modeEntry (n:ℕ) : Label :=
  if h:n<9 then .local (.modeCopy ⟨n,h⟩) else .local (.prepare 0)
/-- All nine real mode copies/pushes execute, without a supplied literal-tag bank. -/
theorem modes_suffix (p:Counters) (fuel count:ℕ) (hc:count+fuel=9) :
    ∃time≤45*fuel,Runs program time (modeEntry count) (atMode p count)
      (.local (.prepare 0)) (atMode p 9) := by
  induction fuel generalizing count with
  | zero=>
    have he:count=9:=by omega
    subst count
    exact ⟨0,le_rfl,runs_refl program _ _⟩
  | succ fuel ih=>
    have hcount:count<9:=by omega
    have hn:count+1+fuel=9:=by omega
    obtain ⟨time,ht,hr⟩:=ih (count+1) hn
    let j:Fin 9:=⟨count,hcount⟩
    have hstep:=mode_step p j
    have hnext:nextMode j=modeEntry (count+1):=by
      by_cases hh:count<8
      · have hsucc:count+1<9:=by omega
        simp [nextMode,modeEntry,j,hh,hsucc]
      · have he:count=8:=by omega
        subst count
        rfl
    rw [hnext] at hstep
    have h:=runs_trans program _ _ _ _ _ _ _ _ hstep hr
    refine ⟨(5*count+5)+time,by omega,?_⟩
    have hentry:modeEntry count=.local (.modeCopy j):=by simp [modeEntry,hcount,j]
    rw [hentry]
    exact h
/-- Literal first jump plus all physical tag construction, ending at preparation stage zero. -/
theorem modes_run (p:Counters) :
    ∃time≤406,Runs program time (.local .start) (input (words p)) (.local (.prepare 0)) (atStage p 0) := by
  obtain ⟨time,ht,hr⟩:=modes_suffix p 9 0 rfl
  have hz:Runs program 1 (.local .start) (input (words p)) (.local (.modeCopy 0)) (input (words p)):=by
    apply one_base program _ _ (.jump (.local (.modeCopy 0))) _ _ rfl rfl
    rfl
  rw [mode_initial] at hz
  change Runs program time (.local (.modeCopy 0)) (atMode p 0) (.local (.prepare 0)) (atMode p 9) at hr
  rw [modes_ready] at hr
  have h:=runs_trans program _ _ _ _ _ _ _ _ hz hr
  rw [←mode_initial] at h
  exact ⟨1+time,by omega,h⟩
end RiemannGaussian.SemiprimeD1StackPortOwnerRecipeModes

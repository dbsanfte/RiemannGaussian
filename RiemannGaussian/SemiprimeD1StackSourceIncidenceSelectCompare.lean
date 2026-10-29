/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectPrimitives
/-! # Real paid strict comparison of the acquired and retained score words
Only actual preserving copies feed the real five-role WordLess source. Its
computed Boolean is physically popped; the whole other bank, including both
actual candidate/score words and every caller return, survives this fragment.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectCompare
open SemiprimeD1StackSourceIncidenceSelect SemiprimeD1StackSourceIncidenceSelectPrimitives
open SemiprimeD1StackProcedureTrace
local notation "ctl" => Label.local
/-- Complete63-role comparison bank; all other60 words retain their actual prior values. -/
def view (retained:Stack→List Bool) (left right result:List Bool) :Stack→List Bool :=
  fun k=>if k=aux .compareLeft then left else if k=aux .compareRight then right
    else if k=aux .compareOutput then result else retained k
/-- One actual left comparison update preserves every other physical stack. -/
theorem update_left (retained:Stack→List Bool) (left right result word:List Bool) :
    Function.update (view retained left right result) (aux .compareLeft) word=view retained word right result :=by
  funext k
  rcases k with k|k
  · rfl
  · cases k <;> rfl
/-- One actual right comparison update preserves every other physical stack. -/
theorem update_right (retained:Stack→List Bool) (left right result word:List Bool) :
    Function.update (view retained left right result) (aux .compareRight) word=view retained left word result :=by
  funext k
  rcases k with k|k
  · rfl
  · cases k <;> rfl
/-- One actual result comparison update preserves every other physical stack. -/
theorem update_result (retained:Stack→List Bool) (left right result word:List Bool) :
    Function.update (view retained left right result) (aux .compareOutput) word=view retained left right word :=by
  funext k
  rcases k with k|k
  · rfl
  · cases k <;> rfl
/-- A later candidate is compared ONLY by actual source words, with no supplied score-order Boolean. -/
theorem compare_run (retained:Stack→List Bool) (newScore oldScore:List Bool)
    (hn:retained score=newScore) (ho:retained (aux .bestScore)=oldScore)
    (hc:retained (aux .copyScratch)=[]) (hs:retained (aux .compareScratch)=[])
    (hd:retained (aux .discard)=[]) :
    Runs program (5*newScore.length+5*oldScore.length+
        SemiprimeD1StackWordLessExecution.totalTime newScore oldScore+10)
      (ctl (.acquired false)) (view retained [] [] [])
      (ctl (if SemiprimeD1StackWordLessExecution.answer newScore oldScore then .clearBestID else .clearScore))
      (view retained [] [] []) :=by
  have h0:=copy_call .scoreOperand (.acquired false) .copyBestOperand rfl
    (view retained [] [] []) newScore [] hn rfl hc
  change Runs program _ _ _ _
    (Function.update (view retained [] [] []) (aux .compareLeft) (newScore++[])) at h0
  rw [List.append_nil,update_left] at h0
  have h1:=copy_call .bestOperand .copyBestOperand .compare rfl
    (view retained newScore [] []) oldScore [] ho rfl hc
  change Runs program _ _ _ _
    (Function.update (view retained newScore [] []) (aux .compareRight) (oldScore++[])) at h1
  rw [List.append_nil,update_right] at h1
  have h2:=less_call (view retained newScore oldScore []) newScore oldScore rfl rfl hs hd rfl
  rw [update_left,update_right,update_result] at h2
  have h3:=pop_run .compared (ctl .abort) (ctl .clearScore) (ctl .clearBestID) (aux .compareOutput)
    (view retained [] [] [SemiprimeD1StackWordLessExecution.answer newScore oldScore])
    [SemiprimeD1StackWordLessExecution.answer newScore oldScore] rfl rfl
  change Runs program 1 _ _ _ (Function.update
    (view retained [] [] [SemiprimeD1StackWordLessExecution.answer newScore oldScore]) (aux .compareOutput) []) at h3
  rw [update_result] at h3
  have hp:SemiprimeD1StackBytecode.choose (ctl .abort) (ctl .clearScore) (ctl .clearBestID)
      [SemiprimeD1StackWordLessExecution.answer newScore oldScore].head?=
      ctl (if SemiprimeD1StackWordLessExecution.answer newScore oldScore then .clearBestID else .clearScore):=by
    cases SemiprimeD1StackWordLessExecution.answer newScore oldScore <;> rfl
  rw [hp] at h3
  have h:=join (join (join h0 h1) h2) h3
  have ht:(5*newScore.length+4)+(5*oldScore.length+4)+
      (SemiprimeD1StackWordLessExecution.totalTime newScore oldScore+1)+1=
      5*newScore.length+5*oldScore.length+SemiprimeD1StackWordLessExecution.totalTime newScore oldScore+10:=by omega
  simpa only [ht] using h
/-- The actual paid comparison costs a fixed linear function of physical score byte widths. -/
theorem compare_time_le (newScore oldScore:List Bool) :
    5*newScore.length+5*oldScore.length+SemiprimeD1StackWordLessExecution.totalTime newScore oldScore+10 ≤
      22*(newScore.length+oldScore.length+1) :=by
  have h:=SemiprimeD1StackWordLessExecution.totalTime_le newScore oldScore
  omega
/-- A clean comparison view restores exactly the original complete caller bank. -/
theorem view_empty (retained:Stack→List Bool) (hl:retained (aux .compareLeft)=[])
    (hr:retained (aux .compareRight)=[]) (ho:retained (aux .compareOutput)=[]) :
    view retained [] [] []=retained :=by
  funext k
  by_cases h0:k=aux .compareLeft
  · subst k
    simp only [view,ite_true]
    exact hl.symm
  · by_cases h1:k=aux .compareRight
    · subst k
      simp only [view,h0,ite_false,ite_true]
      exact hr.symm
    · by_cases h2:k=aux .compareOutput
      · subst k
        simp only [view,h0,h1,ite_false,ite_true]
        exact ho.symm
      · simp only [view,h0,h1,h2,ite_false]
end RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectCompare

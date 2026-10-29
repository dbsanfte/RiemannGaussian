/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectView
import RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectCompare
/-! # Actual first-score caching and strict incumbent replacement
The first candidate is saved by finite control even when its ID and score are
both zero. Every later replacement uses only the real comparator's strict bit;
ties preserve both original incumbent words. Every erased score is drained.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectIncumbent
open SemiprimeD1StackSourceIncidenceSelect SemiprimeD1StackSourceIncidenceSelectPrimitives
open SemiprimeD1StackSourceIncidenceSelectView SemiprimeD1StackProcedureTrace
local notation "ctl" => Label.local
/-- Real copies cache the exact candidate and its actual acquired score without recomputation. -/
theorem save_run (pc scorePC:Control)
    (hc:program (ctl pc)=.call (.copier .bestID 0) (ctl scorePC))
    (hs:program (ctl scorePC)=.call (.copier .bestScore 0) (ctl .clearScore))
    (ids:List (List Bool))
    (id pfx stream square cube fourth catalogue owners factors todo reader savedKey newScore:List Bool) :
    Runs program (5*id.length+5*newScore.length+8) (ctl pc)
      (clean ids id pfx stream square cube fourth catalogue owners factors todo reader savedKey [] [] newScore)
      (ctl .clearScore)
      (clean ids id pfx stream square cube fourth catalogue owners factors todo reader savedKey id newScore newScore) :=by
  have h0:=copy_call .bestID pc scorePC hc
    (clean ids id pfx stream square cube fourth catalogue owners factors todo reader savedKey [] [] newScore)
    id [] rfl rfl rfl
  change Runs program _ _ _ _ (Function.update
    (clean ids id pfx stream square cube fourth catalogue owners factors todo reader savedKey [] [] newScore)
      (aux .bestID) (id++[])) at h0
  rw [List.append_nil,clean_bestID] at h0
  have h1:=copy_call .bestScore scorePC .clearScore hs
    (clean ids id pfx stream square cube fourth catalogue owners factors todo reader savedKey id [] newScore)
    newScore [] rfl rfl rfl
  change Runs program _ _ _ _ (Function.update
    (clean ids id pfx stream square cube fourth catalogue owners factors todo reader savedKey id [] newScore)
      (aux .bestScore) (newScore++[])) at h1
  rw [List.append_nil,clean_bestScore] at h1
  have h:=join h0 h1
  have ht:(5*id.length+4)+(5*newScore.length+4)=5*id.length+5*newScore.length+8:=by omega
  simpa only [ht] using h
/-- The just-acquired score word is physically drained before the temporary dictionary is rolled back. -/
theorem clear_score (ids:List (List Bool))
    (id pfx stream square cube fourth catalogue owners factors todo reader savedKey bestID bestScore newScore:List Bool) :
    Runs program (newScore.length+1) (ctl .clearScore)
      (clean ids id pfx stream square cube fourth catalogue owners factors todo reader savedKey bestID bestScore newScore)
      (ctl .rollbackTag)
      (clean ids id pfx stream square cube fourth catalogue owners factors todo reader savedKey bestID bestScore []) :=by
  have h:=drain_loop .clearScore (ctl .rollbackTag) score rfl
    (clean ids id pfx stream square cube fourth catalogue owners factors todo reader savedKey bestID bestScore newScore)
    newScore rfl
  rw [clean_total] at h
  exact h
/-- First-candidate status is explicit finite control; zero words cannot be mistaken for uninitialized state. -/
theorem first_run (ids:List (List Bool))
    (id pfx stream square cube fourth catalogue owners factors todo reader savedKey newScore:List Bool) :
    Runs program (5*id.length+6*newScore.length+9) (ctl (.acquired true))
      (clean ids id pfx stream square cube fourth catalogue owners factors todo reader savedKey [] [] newScore)
      (ctl .rollbackTag)
      (clean ids id pfx stream square cube fourth catalogue owners factors todo reader savedKey id newScore []) :=by
  have h0:=save_run (.acquired true) .saveFirstScore rfl rfl ids id pfx stream square cube fourth catalogue owners factors todo reader savedKey newScore
  have h1:=clear_score ids id pfx stream square cube fourth catalogue owners factors todo reader savedKey id newScore newScore
  have h:=join h0 h1
  have ht:(5*id.length+5*newScore.length+8)+(newScore.length+1)=5*id.length+6*newScore.length+9:=by omega
  simpa only [ht] using h
/-- A computed strict improvement pays both incumbent drains and both real replacement copies. -/
theorem better_run (ids:List (List Bool))
    (id pfx stream square cube fourth catalogue owners factors todo reader savedKey oldID oldScore newScore:List Bool) :
    Runs program (oldID.length+oldScore.length+5*id.length+6*newScore.length+11) (ctl .clearBestID)
      (clean ids id pfx stream square cube fourth catalogue owners factors todo reader savedKey oldID oldScore newScore)
      (ctl .rollbackTag)
      (clean ids id pfx stream square cube fourth catalogue owners factors todo reader savedKey id newScore []) :=by
  have h0:=drain_loop .clearBestID (ctl .clearBestScore) (aux .bestID) rfl
    (clean ids id pfx stream square cube fourth catalogue owners factors todo reader savedKey oldID oldScore newScore) oldID rfl
  rw [clean_bestID] at h0
  have h1:=drain_loop .clearBestScore (ctl .saveBetterID) (aux .bestScore) rfl
    (clean ids id pfx stream square cube fourth catalogue owners factors todo reader savedKey [] oldScore newScore) oldScore rfl
  rw [clean_bestScore] at h1
  have h2:=save_run .saveBetterID .saveBetterScore rfl rfl ids id pfx stream square cube fourth catalogue owners factors todo reader savedKey newScore
  have h3:=clear_score ids id pfx stream square cube fourth catalogue owners factors todo reader savedKey id newScore newScore
  have h:=join (join (join h0 h1) h2) h3
  have ht:(oldID.length+1)+(oldScore.length+1)+(5*id.length+5*newScore.length+8)+(newScore.length+1)=
      oldID.length+oldScore.length+5*id.length+6*newScore.length+11:=by omega
  simpa only [ht] using h
/-- Every later actual acquired score returns the exact strict-update pair, retaining the incumbent on all ties. -/
theorem later_run (ids:List (List Bool))
    (id pfx stream square cube fourth catalogue owners factors todo reader savedKey oldID oldScore newScore:List Bool) :
    ∃t ≤ 100*(id.length+newScore.length+oldID.length+oldScore.length+1),
      Runs program t (ctl (.acquired false))
        (clean ids id pfx stream square cube fourth catalogue owners factors todo reader savedKey oldID oldScore newScore)
        (ctl .rollbackTag)
        (clean ids id pfx stream square cube fourth catalogue owners factors todo reader savedKey
          (SemiprimeD1StackSourceIncidenceSelectSpec.scoredPick (oldID,oldScore) (id,newScore)).1
          (SemiprimeD1StackSourceIncidenceSelectSpec.scoredPick (oldID,oldScore) (id,newScore)).2 []) :=by
  let before:=clean ids id pfx stream square cube fourth catalogue owners factors todo reader savedKey oldID oldScore newScore
  have h0:=SemiprimeD1StackSourceIncidenceSelectCompare.compare_run before newScore oldScore rfl rfl rfl rfl rfl
  rw [SemiprimeD1StackSourceIncidenceSelectCompare.view_empty before rfl rfl rfl] at h0
  have ht:=SemiprimeD1StackSourceIncidenceSelectCompare.compare_time_le newScore oldScore
  have hp:=SemiprimeD1StackSourceIncidenceSelectSpec.real_less_pick (oldID,oldScore) (id,newScore)
  cases hb:SemiprimeD1StackWordLessExecution.answer newScore oldScore with
  | false=>
    have h1:=clear_score ids id pfx stream square cube fourth catalogue owners factors todo reader savedKey oldID oldScore newScore
    simp only [hb,Bool.false_eq_true,ite_false] at h0 hp
    rw [←hp]
    refine ⟨_,by omega,join h0 h1⟩
  | true=>
    have h1:=better_run ids id pfx stream square cube fourth catalogue owners factors todo reader savedKey oldID oldScore newScore
    simp only [hb,ite_true] at h0 hp
    rw [←hp]
    refine ⟨_,by omega,join h0 h1⟩
end RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectIncumbent

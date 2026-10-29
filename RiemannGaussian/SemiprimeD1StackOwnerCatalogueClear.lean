/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOwnerCatalogueEmit
import RiemannGaussian.SemiprimeD1StackPhysicalLoops
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 131072
namespace RiemannGaussian.SemiprimeD1StackOwnerCatalogueClear
open SemiprimeD1StackOwnerCatalogue SemiprimeD1StackOwnerCatalogueSource
open SemiprimeD1StackOwnerCatalogueFields
open SemiprimeD1StackProcedureTrace (Runs runs_trans)
/-- Fixed mathematical inverse to the physical 47-role cleanup order. -/
def workRank : RecipeWork→Fin 47
  | .inl (.mode i)=>⟨i.val,by omega⟩
  | .inl .rt=>10
  | .inl .width=>11
  | .inl .qa=>12
  | .inl .ma=>13
  | .inl .qb=>14
  | .inl .mb=>15
  | .inl .tc=>16
  | .inl .rc=>17
  | .inl .pbc=>18
  | .inl .aminus=>19
  | .inl .bminus=>20
  | .inl .dminus=>21
  | .inl .bplus=>22
  | .inl .slot10=>23
  | .inl .slot11=>24
  | .inl .slot12=>25
  | .inl .wd=>26
  | .inl .slot13f=>27
  | .inl .slot13t=>28
  | .inl .slot14t=>29
  | .inl .slot14f=>30
  | .inl .wb=>31
  | .inl .divInput=>32
  | .inl .testLeft=>33
  | .inl .testLimit=>34
  | .inl .smallA=>35
  | .inl .ltArt=>36
  | .inl .ltNext=>37
  | .inl .tagReader=>38
  | .inr .copyScratch=>39
  | .inr .multiplier=>40
  | .inr .productScratch=>41
  | .inr .maddScratch=>42
  | .inr .divCopy=>43
  | .inr .divScratch=>44
  | .inr .frameScratch=>45
  | .inr .output=>46
/-- Every work role is physically visited exactly once. -/
theorem workRole_rank (k:RecipeWork) : workRole (workRank k)=k := by
  rcases k with k|k
  · cases k with
    | mode i=>fin_cases i <;> decide
    | _=>decide
  · cases k <;> decide
/-- The mathematical rank agrees with each actual static cleanup call. -/
theorem rank_workRole (part:Fin 47) : workRank (workRole part)=part := by
  fin_cases part <;> decide
/-- The actual arithmetic work after n literal cleanup roles have been erased. -/
def workCleared (w:RecipeWork→List Bool) (n:Nat) (k:RecipeWork) : List Bool :=
  if (workRank k).val<n then [] else w k
/-- An actual drain changes precisely the next role in the cleanup order. -/
theorem workCleared_step (w:RecipeWork→List Bool) (part:Fin 47) :
    Function.update (workCleared w part.val) (workRole part) []=workCleared w (part.val+1) := by
  funext k
  by_cases hk:k=workRole part
  · subst k;simp only [Function.update_same,workCleared,rank_workRole,Nat.lt_succ_self,ite_true]
  · have hn:(workRank k).val≠part.val:=by
      intro h;have he:workRank k=part:=Fin.ext h
      have hrole:=workRole_rank k
      rw [he] at hrole
      exact hk hrole.symm
    simp only [Function.update_of_ne hk,workCleared]
    split <;> split <;> simp_all <;> omega
/-- No arithmetic payload is discarded without its real pop trace. -/
theorem workCleared_end (w:RecipeWork→List Bool) : workCleared w 47=fun _=>[] := by
  funext k;exact ite_eq_left (workRank k).isLt
/-- Static actual continuation following a work-role EOF pop. -/
def workNext (part:Fin 47) : Label :=
  if h:part.val<46 then .local (.clearRecipe ⟨part.val+1,by omega⟩) else .local (.clearCache 0)
/-- Actual one-role erasure, including the final EOF pop. -/
theorem work_call (s:S.Stack→List Bool) (w:RecipeWork→List Bool) (f:Fin 7→List Bool)
    (a:Aux→List Bool) (part:Fin 47) :
    Runs program ((w (workRole part)).length+1) (.local (.clearRecipe part))
      (data s (workCleared w part.val) f a) (workNext part)
      (data s (workCleared w (part.val+1)) f a) := by
  let before:=data s (workCleared w part.val) f a
  have hv:before (work (workRole part))=w (workRole part):=by
    simp only [before,data_work,workCleared,rank_workRole,Nat.lt_irrefl,ite_false]
  have hi:Function.update before (work (workRole part)) (w (workRole part))=before:=by
    rw [←hv];exact Function.update_eq_self _ _
  have h:=SemiprimeD1StackPhysicalLoops.drain program (.local (.clearRecipe part))
    (workNext part) (work (workRole part)) rfl before (w (workRole part))
  rw [hi] at h
  simpa only [before,update_work,workCleared_step] using h
/-- Exact static position within all 47 actual cleanup loops. -/
def workPC (n:Nat) : Label :=
  if h:n<47 then .local (.clearRecipe ⟨n,h⟩) else .local (.clearCache 0)
/-- Chronological sum of the actual erased work payload lengths and EOF pops. -/
def workTime (w:RecipeWork→List Bool) : Nat→Nat
  | 0=>0
  | n+1=>workTime w n+(w (workRole ⟨n%47,Nat.mod_lt _ (by omega)⟩)).length+1
/-- Every real role drain advances the same actual cleanup source. -/
theorem work_step (s:S.Stack→List Bool) (w:RecipeWork→List Bool) (f:Fin 7→List Bool)
    (a:Aux→List Bool) (n:Nat) (hn:n<47) :
    Runs program ((w (workRole ⟨n,hn⟩)).length+1) (workPC n)
      (data s (workCleared w n) f a) (workPC (n+1)) (data s (workCleared w (n+1)) f a) := by
  have h:=work_call s w f a ⟨n,hn⟩
  have hp:workNext ⟨n,hn⟩=workPC (n+1):=by
    unfold workNext workPC
    by_cases hn':n<46
    · simp only [hn',show n+1<47 by omega,dite_eq_left]
    · have he:n=46:=by omega
      subst n;rfl
  rw [hp] at h
  simpa only [workPC,dite_eq_left hn] using h
/-- Exact actual trace erasing the first n fixed arithmetic roles. -/
theorem work_prefix (s:S.Stack→List Bool) (w:RecipeWork→List Bool) (f:Fin 7→List Bool)
    (a:Aux→List Bool) (n:Nat) (hn:n≤47) :
    Runs program (workTime w n) (workPC 0) (data s (workCleared w 0) f a)
      (workPC n) (data s (workCleared w n) f a) := by
  induction n with
  | zero=>exact SemiprimeD1StackProcedureTrace.runs_refl program _ _
  | succ n ih=>
    have hlt:n<47:=by omega
    have hm:n%47=n:=Nat.mod_eq_of_lt hlt
    have h:=runs_trans program _ _ _ _ _ _ _ _ (ih (by omega)) (work_step s w f a n hlt)
    simpa only [workTime,hm,Nat.add_assoc] using h
/-- Complete physical cleanup of every arithmetic register, scratch and output word. -/
theorem work_run (s:S.Stack→List Bool) (w:RecipeWork→List Bool) (f:Fin 7→List Bool)
    (a:Aux→List Bool) :
    Runs program (workTime w 47) (.local (.clearRecipe 0)) (data s w f a)
      (.local (.clearCache 0)) (data s (fun _=>[]) f a) := by
  have h:=work_prefix s w f a 47 (by omega)
  have hz:workCleared w 0=w:=by funext k;exact ite_eq_right (Nat.not_lt_zero _)
  have hp0:workPC 0=.local (.clearRecipe 0):=by simp [workPC]
  have hp47:workPC 47=.local (.clearCache 0):=by simp [workPC]
  simpa only [hz,hp0,hp47,workCleared_end] using h
end RiemannGaussian.SemiprimeD1StackOwnerCatalogueClear

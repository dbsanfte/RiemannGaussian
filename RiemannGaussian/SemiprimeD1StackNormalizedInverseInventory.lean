/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackNormalizedInverse
/-! # Exact literal physical operand and cleanup inventories of normalized inversion -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackNormalizedInverseInventory
open SemiprimeD1StackNormalizedInverse
/-- Every actual three-word copy is physically injective, independently of data. -/
theorem copy_injective (site : Copy) : Function.Injective (copyStack site) := by
  cases site with
  | remaining=>decide
  | terms=>decide
  | aIndex=>decide
  | bIndex=>decide
  | reader part=>cases part <;> decide
  | readIndex part=>cases part <;> decide
  | input part right den=>cases part <;> cases right <;> cases den <;> decide
  | output part den=>cases part <;> cases den <;> decide
/-- Both actual Field destinations are disjoint from input, scratch and validity. -/
theorem field_injective (site : Field) : Function.Injective (fieldStack site) := by
  cases site with
  | read part den=>cases part <;> cases den <;> decide
  | finish den=>cases den <;> decide
/-- Each real frame restores a distinct physical source and scratch. -/
theorem frame_injective (site : Frame) : Function.Injective (frameStack site) := by
  cases site <;> rename_i den <;> cases den <;> decide
/-- The35 literal cleanup roles cover distinct R36 words. -/
theorem rationalRole_injective : Function.Injective rationalRole := by decide
/-- Every non-template R36 word, including all retained original inputs/results, is physically swept. -/
theorem rationalRole_complete (k : R.Stack) (hk : k≠R.aux .template) : ∃i : Fin 35,rationalRole i=k := by
  revert k
  decide
/-- The actual W input is never swept by per-operation cleanup. -/
theorem rationalRole_not_template (i : Fin 35) : rationalRole i≠R.aux .template := by fin_cases i <;> decide
/-- Every signed/denominator cache field is listed, with no unseen shadow. -/
theorem regRole_complete (r : Reg) (den : Bool) : ∃i : Fin 8,regRole i=reg r den := by
  cases r <;> cases den <;> decide
/-- All actual controller work words appear in the final sweep. -/
theorem auxRole_complete (k : Aux) (ha : k≠.denominator) (hq : k≠.originalQ) (ho : k≠.output) :
    ∃i : Fin 11,auxRole i=aux k := by
  revert k
  decide
/-- All54 successful-path cleanup addresses exclude the original denominator array. -/
theorem workRole_not_denominator (i : Fin 54) : workRole i≠aux .denominator := by fin_cases i <;> decide
/-- All54 successful-path cleanup addresses exclude the original physical q markers. -/
theorem workRole_not_q (i : Fin 54) : workRole i≠aux .originalQ := by fin_cases i <;> decide
/-- Successful cleanup retains the acquired chronological output. -/
theorem workRole_not_output (i : Fin 54) : workRole i≠aux .output := by fin_cases i <;> decide
/-- Successful cleanup retains the actual W input cell-for-cell. -/
theorem workRole_not_template (i : Fin 54) : workRole i≠template := by fin_cases i <;> decide
/-- Exactly every other allocated physical role is visited by the paid final cleanup. -/
theorem workRole_complete (k : Stack) (ht : k≠template) (ha : k≠aux .denominator)
    (hq : k≠aux .originalQ) (ho : k≠aux .output) : ∃i : Fin 54,workRole i=k := by
  rcases k with k|k|k
  · obtain ⟨i,hi⟩:=rationalRole_complete k (by intro h;subst k;exact ht rfl)
    refine ⟨⟨i.val,by omega⟩,?_⟩
    have h : i.val<35:=i.isLt
    simp only [workRole,h,dite_true]
    exact congrArg rational hi
  · rcases k with ⟨r,den⟩
    obtain ⟨i,hi⟩:=regRole_complete r den
    refine ⟨⟨35+i.val,by omega⟩,?_⟩
    have h0 : ¬35+i.val<35:=by omega
    have h1 : 35+i.val<43:=by omega
    simp only [workRole,h0,h1,dite_false,dite_true]
    have he : (⟨35+i.val-35,by omega⟩ : Fin 8)=i := by apply Fin.ext;change 35+i.val-35=i.val;omega
    rw [he]
    exact hi
  · obtain ⟨i,hi⟩:=auxRole_complete k (by intro h;subst k;exact ha rfl)
      (by intro h;subst k;exact hq rfl) (by intro h;subst k;exact ho rfl)
    refine ⟨⟨43+i.val,by omega⟩,?_⟩
    have h0 : ¬43+i.val<35:=by omega
    have h1 : ¬43+i.val<43:=by omega
    simp only [workRole,h0,h1,dite_false]
    have he : (⟨43+i.val-43,by omega⟩ : Fin 11)=i := by apply Fin.ext;change 43+i.val-43=i.val;omega
    rw [he]
    exact hi
end RiemannGaussian.SemiprimeD1StackNormalizedInverseInventory

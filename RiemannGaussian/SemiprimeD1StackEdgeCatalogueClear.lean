/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackEdgeCatalogueEmit
import RiemannGaussian.SemiprimeD1StackEdgeCatalogueDispatch

/-! # Every parsed descriptor cache cell is physically cleared -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000
set_option synthInstance.maxSize 8192
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackEdgeCatalogueClear
open SemiprimeD1StackEdgeCatalogue SemiprimeD1StackEdgeCatalogueView
open SemiprimeD1StackEdgeCatalogueParse
open SemiprimeD1StackProcedureFragments (Runs)
open SemiprimeD1EdgeCatalogueEncoding (Record)

/-- Exact cache suffix still present after earlier slots were physically consumed. -/
def remaining (words:Record) (count:ℕ) : Record := fun j=>if j.val<count then [] else words j
/-- Clearing one actual field preserves all later cache words. -/
theorem remaining_update (words:Record) (part:Fin 5) :
    Function.update (remaining words part.val) part []=remaining words (part.val+1) := by
  funext j
  by_cases h:j=part
  · subst j;simp [remaining,Function.update]
  · have hn:j.val≠part.val:=by intro he;exact h (Fin.ext he)
    simp only [Function.update_of_ne h,remaining]
    by_cases hj:j.val<part.val
    · have hj':j.val<part.val+1:=by omega
      simp [hj,hj']
    · have hj':¬j.val<part.val+1:=by omega
      simp [hj,hj']
/-- Literal finite continuation after the current cache is empty. -/
def nextCache (part:Fin 5) : Label :=
  if h:part.val<4 then .inl (.clearCache ⟨part.val+1,by omega⟩) else .inl .parse
/-- Actual cell-by-cell clearing, including the EOF transition. -/
theorem clear_step (base:Cat.Stack→List Bool) (tape:List Bool) (words:Record) (part:Fin 5) (raw side:List Bool) :
    Runs program ((words part).length+1) (.inl (.clearCache part))
      (clean base tape (remaining words part.val) raw side) (nextCache part)
      (clean base tape (remaining words (part.val+1)) raw side) := by
  have h:=clear_run (words part) (.inl (.clearCache part)) (nextCache part) (cache part)
    (clean base tape (remaining words part.val) raw side)
    (by simp [clean,store,cache,remaining]) rfl
  change Runs program _ _ _ _ (Function.update (store base tape (remaining words part.val) (cleanWork raw side))
    (cache part) []) at h
  rw [update_cache,remaining_update] at h
  exact h
/-- All original parsed fields are consumed before the next record; none is discarded for free. -/
theorem caches_run (base:Cat.Stack→List Bool) (tape:List Bool) (words:Record) (raw side:List Bool) :
    Runs program (wordMass words+5) (.inl (.clearCache 0)) (clean base tape words raw side)
      (.inl .parse) (clean base tape (fun _=>[]) raw side) := by
  have h0:=clear_step base tape words 0 raw side
  have h1:=clear_step base tape words 1 raw side
  have h2:=clear_step base tape words 2 raw side
  have h3:=clear_step base tape words 3 raw side
  have h4:=clear_step base tape words 4 raw side
  have h:=h0.trans (h1.trans (h2.trans (h3.trans h4)))
  change Runs program _ _ (clean base tape (remaining words 0) raw side) (.inl .parse)
    (clean base tape (remaining words 5) raw side) at h
  have hz:remaining words 0=words:=by funext j;simp [remaining]
  have hf:remaining words 5=(fun _=>[]):=by funext j;simp [remaining,j.isLt]
  rw [hz,hf] at h
  have ht:((words 0).length+1+((words 1).length+1+((words 2).length+1+
      ((words 3).length+1+((words 4).length+1)))))=wordMass words+5:=by unfold wordMass;omega
  rw [ht] at h
  exact h
end RiemannGaussian.SemiprimeD1StackEdgeCatalogueClear

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPortCatalogueView
import RiemannGaussian.SemiprimeD1StackEdgeCatalogueClear
/-! # Actual cache and local-slot cleanup of the original port transducer -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 131072
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackPortCatalogueClear
open SemiprimeD1StackPortCatalogue SemiprimeD1StackPortCatalogueView
open SemiprimeD1StackProcedureFragments (Runs)
open SemiprimeD1EdgeCatalogueEncoding (Record)
open SemiprimeD1StackEdgeCatalogueClear (remaining remaining_update)
open SemiprimeD1StackEdgeCatalogueParse (wordMass)
open SemiprimeD1StackUnaryDivmod (unary)
/-- Literal finite continuation after the current cache is empty. -/
def nextCache (part:Fin 5) : Label :=
  if h:part.val<4 then .local (.clearCache ⟨part.val+1,by omega⟩) else .local .factorTick
/-- Actual cell-by-cell clearing, including the EOF transition. -/
theorem clear_step (base:V.Stack→List Bool) (tape:List Bool) (words:Record) (part:Fin 5) (raw slot edges factor occurrence rest:List Bool) :
    Runs program ((words part).length+1) (.local (.clearCache part))
      (clean base tape (remaining words part.val) raw slot edges factor occurrence rest) (nextCache part)
      (clean base tape (remaining words (part.val+1)) raw slot edges factor occurrence rest) := by
  have h:=clear_run (words part) (.local (.clearCache part)) (nextCache part) (cache part)
    (clean base tape (remaining words part.val) raw slot edges factor occurrence rest)
    (by simp [clean,store,cache,edgeStack,E.cache,remaining]) rfl
  change Runs program _ _ _ _ (Function.update (store base (remaining words part.val)
    (oldClean raw slot edges) (privateClean tape factor occurrence rest)) (cache part) []) at h
  rw [update_cache,remaining_update] at h
  exact h
/-- All original parsed fields are consumed before the next record; none is discarded for free. -/
theorem caches_run (base:V.Stack→List Bool) (tape:List Bool) (words:Record) (raw slot edges factor occurrence rest:List Bool) :
    Runs program (wordMass words+5) (.local (.clearCache 0)) (clean base tape words raw slot edges factor occurrence rest)
      (.local .factorTick) (clean base tape (fun _=>[]) raw slot edges factor occurrence rest) := by
  have h0:=clear_step base tape words 0 raw slot edges factor occurrence rest
  have h1:=clear_step base tape words 1 raw slot edges factor occurrence rest
  have h2:=clear_step base tape words 2 raw slot edges factor occurrence rest
  have h3:=clear_step base tape words 3 raw slot edges factor occurrence rest
  have h4:=clear_step base tape words 4 raw slot edges factor occurrence rest
  have h:=h0.trans (h1.trans (h2.trans (h3.trans h4)))
  change Runs program _ _ (clean base tape (remaining words 0) raw slot edges factor occurrence rest) (.local .factorTick)
    (clean base tape (remaining words 5) raw slot edges factor occurrence rest) at h
  have hz:remaining words 0=words:=by funext j;simp [remaining]
  have hf:remaining words 5=(fun _=>[]):=by funext j;simp [remaining,j.isLt]
  rw [hz,hf] at h
  have ht:((words 0).length+1+((words 1).length+1+((words 2).length+1+
      ((words 3).length+1+((words 4).length+1)))))=wordMass words+5:=by unfold wordMass;omega
  rw [ht] at h
  exact h
/-- The local-slot tally is physically consumed before the next original vertex. -/
theorem slot_run (base:V.Stack→List Bool) (tape:List Bool) (words:Record)
    (raw slot edges factor occurrence:List Bool) :
    Runs program (slot.length+1) (.local .clearSlot)
      (clean base tape words raw slot edges factor occurrence []) (.local (.clearCache 0))
      (clean base tape words raw [] edges factor occurrence []) := by
  have h:=clear_run slot (.local .clearSlot) (.local (.clearCache 0)) (oldAux .side)
    (clean base tape words raw slot edges factor occurrence []) rfl rfl
  rw [clean_slot] at h
  exact h
/-- Every original vertex increments the factor count, including zero-port factors. -/
theorem factor_run (base:V.Stack→List Bool) (tape raw edges:List Bool) (factor occurrence:ℕ) :
    Runs program 1 (.local .factorTick)
      (clean base tape (fun _=>[]) raw [] edges (unary factor) (unary occurrence) []) (.local .parse)
      (clean base tape (fun _=>[]) raw [] edges (unary (factor+1)) (unary occurrence) []) := by
  have h:=push_run (.local .factorTick) (.local .parse) (aux .factorOrdinal) true
    (clean base tape (fun _=>[]) raw [] edges (unary factor) (unary occurrence) []) rfl
  change Runs program _ _ _ _ (Function.update
    (clean base tape (fun _=>[]) raw [] edges (unary factor) (unary occurrence) [])
    (aux .factorOrdinal) (unary (factor+1))) at h
  rw [clean_factor] at h
  exact h
end RiemannGaussian.SemiprimeD1StackPortCatalogueClear

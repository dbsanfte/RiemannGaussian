/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPortScopeEmit
/-! # All nine actual cached words are physically cleared between port records -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 131072
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackPortScopeClear
open SemiprimeD1StackPortScopeRecords SemiprimeD1StackPortScopeView
open SemiprimeD1StackPortScopeEmit (wordMass)
open SemiprimeD1StackProcedureFragments (Runs)
/-- Actual suffix of the finite cached record after preceding words were popped. -/
def remaining (words:Record) (count:ℕ) : Record := fun j=>if j.val<count then [] else words j
/-- One physical cache write gives precisely the next remaining suffix. -/
theorem remaining_update (words:Record) (part:Fin 9) :
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
/-- Literal finite cache-clear continuation. -/
def nextCache (part:Fin 9) : Label :=
  if h:part.val<8 then .local (.clearCache ⟨part.val+1,by omega⟩) else .local .parse
/-- Every copied cache bit, including the acquired ID, is physically popped. -/
theorem clear_step (base:S.Stack→List Bool) (ports ids:List Bool) (words:Record) (part:Fin 9) (raw:List Bool) :
    Runs program ((words part).length+1) (.local (.clearCache part))
      (clean base ports ids (remaining words part.val) raw) (nextCache part)
      (clean base ports ids (remaining words (part.val+1)) raw) := by
  have h:=clear_run (words part) (.local (.clearCache part)) (nextCache part) (cache part)
    (clean base ports ids (remaining words part.val) raw)
    (by change remaining words part.val part=words part;simp [remaining]) rfl
  change Runs program _ _ _ _ (Function.update
    (store base (remaining words part.val) (cleanWork ports ids raw)) (cache part) []) at h
  rw [update_cache,remaining_update] at h
  exact h
/-- All real cached fields are consumed before the actual next record peek. -/
theorem caches_run (base:S.Stack→List Bool) (ports ids:List Bool) (words:Record) (raw:List Bool) :
    Runs program (wordMass words+9) (.local (.clearCache 0)) (clean base ports ids words raw)
      (.local .parse) (clean base ports ids (fun _=>[]) raw) := by
  have h0:=clear_step base ports ids words 0 raw
  have h1:=clear_step base ports ids words 1 raw
  have h2:=clear_step base ports ids words 2 raw
  have h3:=clear_step base ports ids words 3 raw
  have h4:=clear_step base ports ids words 4 raw
  have h5:=clear_step base ports ids words 5 raw
  have h6:=clear_step base ports ids words 6 raw
  have h7:=clear_step base ports ids words 7 raw
  have h8:=clear_step base ports ids words 8 raw
  have h:=h0.trans (h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans (h7.trans (h8))))))))
  change Runs program _ _ (clean base ports ids (remaining words 0) raw) (.local .parse)
    (clean base ports ids (remaining words 9) raw) at h
  have hz:remaining words 0=words:=by funext j;simp [remaining]
  have hf:remaining words 9=(fun _=>[]):=by funext j;simp [remaining,j.isLt]
  rw [hz,hf] at h
  have ht:((words 0).length+1+((words 1).length+1+((words 2).length+1+((words 3).length+1+((words 4).length+1+((words 5).length+1+((words 6).length+1+((words 7).length+1+((words 8).length+1)))))))))=wordMass words+9:=by unfold wordMass;omega
  change Runs program ((words 0).length+1+((words 1).length+1+((words 2).length+1+((words 3).length+1+((words 4).length+1+((words 5).length+1+((words 6).length+1+((words 7).length+1+((words 8).length+1))))))))) _ _ _ _ at h
  rw [ht] at h
  exact h
end RiemannGaussian.SemiprimeD1StackPortScopeClear

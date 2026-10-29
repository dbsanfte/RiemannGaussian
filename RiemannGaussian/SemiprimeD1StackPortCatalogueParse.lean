/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPortCataloguePrimitives
import RiemannGaussian.SemiprimeD1StackPortCatalogueView
import RiemannGaussian.SemiprimeD1StackEdgeCatalogueParse
/-! # Physical five-field parsing in the actual occurrence source -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 131072
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackPortCatalogueParse
open SemiprimeD1StackPortCatalogue SemiprimeD1StackPortCataloguePrimitives
open SemiprimeD1StackPortCatalogueView
open SemiprimeD1StackProcedureFragments (Runs)
open SemiprimeD1EdgeCatalogueEncoding (Record record)
open SemiprimeD1StackEdgeCatalogueParse (readPrefix suffix wordMass readPrefix_update suffix_cons)
/-- Current physical private reader plus all actually retained metadata/work roles. -/
def parsed (base:V.Stack→List Bool) (tape:List Bool) (words:Record)
    (oldWork:SemiprimeD1StackEdgeCatalogue.Aux→List Bool) (work:Aux→List Bool) : Stack→List Bool :=
  store base words oldWork (Function.update work .reader tape)
/-- Static continuation after each validity marker is physically consumed. -/
def nextField (part:Fin 5) : Label :=
  if h:part.val<4 then .local (.field ⟨part.val+1,by omega⟩) else .local .arity
/-- A real parser call followed by its real validity pop. -/
theorem field_step (base:V.Stack→List Bool) (words:Record) (part:Fin 5) (tail:List Bool)
    (oldWork:SemiprimeD1StackEdgeCatalogue.Aux→List Bool) (work:Aux→List Bool)
    (hs:oldWork .fieldScratch=[]) (hv:oldWork .valid=[]) :
    Runs program (8*(words part).length+8) (.local (.field part))
      (parsed base (suffix words part.val tail) (readPrefix words part.val) oldWork work)
      (nextField part) (parsed base (suffix words (part.val+1) tail) (readPrefix words (part.val+1)) oldWork work) := by
  let before:=parsed base (suffix words part.val tail) (readPrefix words part.val) oldWork work
  let after:=parsed base (suffix words (part.val+1) tail) (readPrefix words (part.val+1)) oldWork work
  have hf:=field_call part before (words part) (suffix words (part.val+1) tail)
    (by change suffix words part.val tail=_;exact suffix_cons words part tail)
    (by simp [before,parsed,store,cache,edgeStack,E.cache,readPrefix]) hs hv
  change Runs program _ _ _ _ (Function.update
    (Function.update (Function.update (store base (readPrefix words part.val) oldWork
      (Function.update work .reader (suffix words part.val tail)))
      (aux .reader) (suffix words (part.val+1) tail)) (cache part) (words part)) (oldAux .valid) [true]) at hf
  rw [update_aux,Function.update_idem,update_cache,readPrefix_update] at hf
  change Runs program _ _ before _ (Function.update after (oldAux .valid) [true]) at hf
  have hp:=pop_run (.local (.popValid part)) (nextField part) (oldAux .valid)
    (Function.update after (oldAux .valid) [true]) rfl
  rw [Function.update_self] at hp
  change Runs program _ _ _ _ (Function.update (Function.update after (oldAux .valid) [true]) (oldAux .valid) []) at hp
  rw [Function.update_idem] at hp
  have he:Function.update after (oldAux .valid) []=after:=by
    have hh:after (oldAux .valid)=[]:=hv
    rw [←hh]
    exact Function.update_eq_self _ _
  rw [he] at hp
  simpa only [show (8*(words part).length+7)+1=8*(words part).length+8 by omega] using hf.trans hp

/-- All five physical cached fields come from this actual tape, not a supplied descriptor answer. -/
theorem fields_run (base:V.Stack→List Bool) (words:Record) (tail:List Bool)
    (oldWork:SemiprimeD1StackEdgeCatalogue.Aux→List Bool) (work:Aux→List Bool)
    (hs:oldWork .fieldScratch=[]) (hv:oldWork .valid=[]) :
    Runs program (8*wordMass words+40) (.local (.field 0))
      (parsed base (record words tail) (fun _=>[]) oldWork work) (.local .arity)
      (parsed base tail words oldWork work) := by
  have h0:=field_step base words 0 tail oldWork work hs hv
  have h1:=field_step base words 1 tail oldWork work hs hv
  have h2:=field_step base words 2 tail oldWork work hs hv
  have h3:=field_step base words 3 tail oldWork work hs hv
  have h4:=field_step base words 4 tail oldWork work hs hv
  have h:=h0.trans (h1.trans (h2.trans (h3.trans h4)))
  have hz:readPrefix words 0=(fun _=>[]) := by funext j;simp [readPrefix]
  have hf:readPrefix words 5=words := by funext j;simp [readPrefix,j.isLt]
  change Runs program _ _ (parsed base (suffix words 0 tail) (readPrefix words 0) oldWork work)
    (nextField 4) (parsed base (suffix words 5 tail) (readPrefix words 5) oldWork work) at h
  rw [hz,hf] at h
  have ht:(8*(words 0).length+8+(8*(words 1).length+8+(8*(words 2).length+8+
      (8*(words 3).length+8+(8*(words 4).length+8)))))=8*wordMass words+40:=by
    unfold wordMass
    omega
  rw [ht] at h
  exact h
/-- Installing the actual reader in a clean loop state preserves every other counter. -/
theorem parsed_clean (base:V.Stack→List Bool) (tape:List Bool) (words:Record)
    (raw slot edges factor occurrence remaining:List Bool) :
    parsed base tape words (oldClean raw slot edges) (privateClean [] factor occurrence remaining)=
      clean base tape words raw slot edges factor occurrence remaining := by
  unfold parsed clean
  congr 1
  funext k
  cases k <;> simp [privateClean,Function.update]
/-- Real descriptor parsing in the actual loop store. -/
theorem fields_clean (base:V.Stack→List Bool) (words:Record) (tail:List Bool)
    (raw slot edges factor occurrence remaining:List Bool) :
    Runs program (8*wordMass words+40) (.local (.field 0))
      (clean base (record words tail) (fun _=>[]) raw slot edges factor occurrence remaining) (.local .arity)
      (clean base tail words raw slot edges factor occurrence remaining) := by
  have h:=fields_run base words tail (oldClean raw slot edges) (privateClean [] factor occurrence remaining) rfl rfl
  rw [parsed_clean,parsed_clean] at h
  exact h
end RiemannGaussian.SemiprimeD1StackPortCatalogueParse

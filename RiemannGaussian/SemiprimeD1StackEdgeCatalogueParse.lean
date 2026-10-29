/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackEdgeCatalogueView

/-! # Actual five-field descriptor parsing, with real validity-cell consumption -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000
set_option synthInstance.maxSize 8192
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackEdgeCatalogueParse
open SemiprimeD1StackEdgeCatalogue SemiprimeD1StackEdgeCatalogueComponents
open SemiprimeD1StackEdgeCatalogueView
open SemiprimeD1StackProcedureFragments (Runs)
open SemiprimeD1EdgeCatalogueEncoding (Record record)
open SemiprimeSourceHistogramKeyBits (frame)

/-- Actual fields already read at a finite stage. -/
def readPrefix (words:Record) (count:ℕ) : Record := fun j=>if j.val<count then words j else []
/-- Actual remaining framed fields in the same original order. -/
def suffix (words:Record) (part:ℕ) (tail:List Bool) : List Bool :=
  if part=0 then record words tail
  else if part=1 then frame (words 1) (frame (words 2) (frame (words 3) (frame (words 4) tail)))
  else if part=2 then frame (words 2) (frame (words 3) (frame (words 4) tail))
  else if part=3 then frame (words 3) (frame (words 4) tail)
  else if part=4 then frame (words 4) tail else tail
/-- Literal total copied payload in the five fields. -/
def wordMass (words:Record) : ℕ := (words 0).length+(words 1).length+(words 2).length+(words 3).length+(words 4).length
/-- Reading one field installs precisely its original finite cache slot. -/
theorem readPrefix_update (words:Record) (part:Fin 5) :
    Function.update (readPrefix words part.val) part (words part)=readPrefix words (part.val+1) := by
  funext j
  by_cases h:j=part
  · subst j;simp [readPrefix,Function.update]
  · have hn:j.val≠part.val:=by intro he;exact h (Fin.ext he)
    simp only [Function.update_of_ne h,readPrefix]
    by_cases hj:j.val<part.val
    · have hj':j.val<part.val+1:=by omega
      simp [hj,hj']
    · have hj':¬j.val<part.val+1:=by omega
      simp [hj,hj']
/-- Each actual next field is at the physical reader head. -/
theorem suffix_cons (words:Record) (part:Fin 5) (tail:List Bool) :
    suffix words part.val tail=frame (words part) (suffix words (part.val+1) tail) := by
  fin_cases part <;> rfl
/-- A real parser call followed by its real validity pop. -/
theorem field_step (base:Cat.Stack→List Bool) (words:Record) (part:Fin 5) (tail raw side:List Bool) :
    Runs program (8*(words part).length+8) (.inl (.field part))
      (clean base (suffix words part.val tail) (readPrefix words part.val) raw side)
      (afterField part) (clean base (suffix words (part.val+1) tail) (readPrefix words (part.val+1)) raw side) := by
  let before:=clean base (suffix words part.val tail) (readPrefix words part.val) raw side
  let after:=clean base (suffix words (part.val+1) tail) (readPrefix words (part.val+1)) raw side
  have hf:=field_call part before (words part) (suffix words (part.val+1) tail)
    (by rw [show before reader=suffix words part.val tail from store_reader _ _ _ _,suffix_cons])
    (by simp [before,clean,store,cache,readPrefix]) rfl rfl
  change Runs program _ _ _ _ (Function.update
    (Function.update (Function.update (store base (suffix words part.val tail) (readPrefix words part.val) (cleanWork raw side))
      reader (suffix words (part.val+1) tail)) (cache part) (words part)) (aux .valid) [true]) at hf
  rw [update_reader,update_cache,readPrefix_update] at hf
  change Runs program _ _ before _ (Function.update after (aux .valid) [true]) at hf
  have hp:=pop_run (.inl (.popValid part)) (afterField part) (aux .valid)
    (Function.update after (aux .valid) [true]) rfl
  rw [Function.update_self] at hp
  change Runs program _ _ _ _ (Function.update (Function.update after (aux .valid) [true]) (aux .valid) []) at hp
  rw [Function.update_idem] at hp
  have he:Function.update after (aux .valid) []=after:=by
    have hh:after (aux .valid)=[]:=rfl
    rw [←hh]
    exact Function.update_eq_self _ _
  rw [he] at hp
  simpa only [show (8*(words part).length+7)+1=8*(words part).length+8 by omega] using hf.trans hp

/-- All five physical cached fields come from this actual tape, not a supplied descriptor answer. -/
theorem fields_run (base:Cat.Stack→List Bool) (words:Record) (tail raw side:List Bool) :
    Runs program (8*wordMass words+40) (.inl (.field 0))
      (clean base (record words tail) (fun _=>[]) raw side) (.inl .copyTag)
      (clean base tail words raw side) := by
  have h0:=field_step base words 0 tail raw side
  have h1:=field_step base words 1 tail raw side
  have h2:=field_step base words 2 tail raw side
  have h3:=field_step base words 3 tail raw side
  have h4:=field_step base words 4 tail raw side
  have h:=h0.trans (h1.trans (h2.trans (h3.trans h4)))
  have hz:readPrefix words 0=(fun _=>[]) := by funext j;simp [readPrefix]
  have hf:readPrefix words 5=words := by funext j;simp [readPrefix,j.isLt]
  change Runs program _ _ (clean base (suffix words 0 tail) (readPrefix words 0) raw side)
    (afterField 4) (clean base (suffix words 5 tail) (readPrefix words 5) raw side) at h
  rw [hz,hf] at h
  have ht:(8*(words 0).length+8+(8*(words 1).length+8+(8*(words 2).length+8+
      (8*(words 3).length+8+(8*(words 4).length+8)))))=8*wordMass words+40:=by
    unfold wordMass
    omega
  rw [ht] at h
  exact h
end RiemannGaussian.SemiprimeD1StackEdgeCatalogueParse

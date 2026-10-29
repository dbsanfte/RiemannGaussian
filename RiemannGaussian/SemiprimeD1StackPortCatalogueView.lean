/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPortCatalogueComponents
import RiemannGaussian.SemiprimeD1PortCatalogueEncoding
/-! # Literal stores and local transitions of the actual occurrence producer -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 131072
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackPortCatalogueView
open SemiprimeD1StackPortCatalogue
open SemiprimeD1StackProcedureFragments (Runs one_base)
/-- All shared source roles, five parsed fields, old buffers and private counters are explicit. -/
def store (base:V.Stack→List Bool) (words:Fin 5→List Bool)
    (oldWork:SemiprimeD1StackEdgeCatalogue.Aux→List Bool) (work:Aux→List Bool) : Stack→List Bool
  | .inl (.inl k) => base k
  | .inl (.inr (.inl k)) => words k
  | .inl (.inr (.inr k)) => oldWork k
  | .inr k => work k
/-- Updating a parsed field changes no source metadata, counter or buffer. -/
theorem update_cache (base:V.Stack→List Bool) (words:Fin 5→List Bool)
    (oldWork:SemiprimeD1StackEdgeCatalogue.Aux→List Bool) (work:Aux→List Bool)
    (part:Fin 5) (word:List Bool) :
    Function.update (store base words oldWork work) (cache part) word=
      store base (Function.update words part word) oldWork work := by
  funext k
  rcases k with (k|k|k)|k
  · simp [store,cache,edgeStack,E.cache,Function.update]
  · by_cases h:k=part
    · subst k;simp [store,cache,edgeStack,E.cache,Function.update]
    · simp [store,cache,edgeStack,E.cache,Function.update,h]
  · simp [store,cache,edgeStack,E.cache,Function.update]
  · simp [store,cache,edgeStack,E.cache,Function.update]
/-- Updating an original physical buffer preserves all other roles. -/
theorem update_oldAux (base:V.Stack→List Bool) (words:Fin 5→List Bool)
    (oldWork:SemiprimeD1StackEdgeCatalogue.Aux→List Bool) (work:Aux→List Bool)
    (role:SemiprimeD1StackEdgeCatalogue.Aux) (word:List Bool) :
    Function.update (store base words oldWork work) (oldAux role) word=
      store base words (Function.update oldWork role word) work := by
  funext k
  rcases k with (k|k|k)|k
  · simp [store,oldAux,edgeStack,E.aux,Function.update]
  · simp [store,oldAux,edgeStack,E.aux,Function.update]
  · by_cases h:k=role
    · subst k;simp [store,oldAux,edgeStack,E.aux,Function.update]
    · simp [store,oldAux,edgeStack,E.aux,Function.update,h]
  · simp [store,oldAux,edgeStack,E.aux,Function.update]
/-- Updating a private reader/counter preserves the entire shared source. -/
theorem update_aux (base:V.Stack→List Bool) (words:Fin 5→List Bool)
    (oldWork:SemiprimeD1StackEdgeCatalogue.Aux→List Bool) (work:Aux→List Bool)
    (role:Aux) (word:List Bool) :
    Function.update (store base words oldWork work) (aux role) word=
      store base words oldWork (Function.update work role word) := by
  funext k
  cases k with
  | inl k => rcases k with k|k|k <;> simp [store,aux,Function.update]
  | inr k =>
    by_cases h:k=role
    · subst k;simp [store,aux,Function.update]
    · simp [store,aux,Function.update,h]
/-- Actual old work roles between component calls; the completed edge tape is retained. -/
def oldClean (raw slot edges:List Bool) : SemiprimeD1StackEdgeCatalogue.Aux→List Bool
  | .reversed => raw
  | .side => slot
  | .output => edges
  | _ => []
/-- Private physical counters and the unconsumed descriptor suffix. -/
def privateClean (tape factor occurrence remaining:List Bool) : Aux→List Bool
  | .reader => tape
  | .factorOrdinal => factor
  | .occurrenceOrdinal => occurrence
  | .remaining => remaining
  | _ => []
/-- Complete actual loop store; original metadata and edge output are preserved. -/
def clean (base:V.Stack→List Bool) (tape:List Bool) (words:Fin 5→List Bool)
    (raw slot edges factor occurrence remaining:List Bool) : Stack→List Bool :=
  store base words (oldClean raw slot edges) (privateClean tape factor occurrence remaining)
/-- Physical raw-output update affects no counter or source cache. -/
theorem clean_raw (base:V.Stack→List Bool) (tape:List Bool) (words:Fin 5→List Bool)
    (raw slot edges factor occurrence remaining next:List Bool) :
    Function.update (clean base tape words raw slot edges factor occurrence remaining) (oldAux .reversed) next=
      clean base tape words next slot edges factor occurrence remaining := by
  unfold clean
  rw [update_oldAux]
  congr 1
  funext k
  cases k <;> simp [oldClean,Function.update]
/-- Physical local-slot update is kept separate from occurrence and wire IDs. -/
theorem clean_slot (base:V.Stack→List Bool) (tape:List Bool) (words:Fin 5→List Bool)
    (raw slot edges factor occurrence remaining next:List Bool) :
    Function.update (clean base tape words raw slot edges factor occurrence remaining) (oldAux .side) next=
      clean base tape words raw next edges factor occurrence remaining := by
  unfold clean
  rw [update_oldAux]
  congr 1
  funext k
  cases k <;> simp [oldClean,Function.update]
/-- Literal physical remaining update retains all other cached fields. -/
theorem clean_remaining (base:V.Stack→List Bool) (tape:List Bool) (words:Fin 5→List Bool)
    (raw slot edges factor occurrence remaining next:List Bool) :
    Function.update (clean base tape words raw slot edges factor occurrence remaining) (aux .remaining) next=
      clean base tape words raw slot edges factor occurrence next := by
  unfold clean
  rw [update_aux]
  congr 1
  funext k
  cases k <;> simp [privateClean,Function.update]
/-- Literal physical occurrence update retains all other cached fields. -/
theorem clean_occurrence (base:V.Stack→List Bool) (tape:List Bool) (words:Fin 5→List Bool)
    (raw slot edges factor occurrence remaining next:List Bool) :
    Function.update (clean base tape words raw slot edges factor occurrence remaining) (aux .occurrenceOrdinal) next=
      clean base tape words raw slot edges factor next remaining := by
  unfold clean
  rw [update_aux]
  congr 1
  funext k
  cases k <;> simp [privateClean,Function.update]
/-- Literal physical factor update retains all other cached fields. -/
theorem clean_factor (base:V.Stack→List Bool) (tape:List Bool) (words:Fin 5→List Bool)
    (raw slot edges factor occurrence remaining next:List Bool) :
    Function.update (clean base tape words raw slot edges factor occurrence remaining) (aux .factorOrdinal) next=
      clean base tape words raw slot edges next occurrence remaining := by
  unfold clean
  rw [update_aux]
  congr 1
  funext k
  cases k <;> simp [privateClean,Function.update]
/-- Literal physical reader update retains all other cached fields. -/
theorem clean_reader (base:V.Stack→List Bool) (tape:List Bool) (words:Fin 5→List Bool)
    (raw slot edges factor occurrence remaining next:List Bool) :
    Function.update (clean base tape words raw slot edges factor occurrence remaining) (aux .reader) next=
      clean base next words raw slot edges factor occurrence remaining := by
  unfold clean
  rw [update_aux]
  congr 1
  funext k
  cases k <;> simp [privateClean,Function.update]
/-- A literal global push, including its actual data-cell allocation. -/
theorem push_run (pc next:Label) (stack:Stack) (bit:Bool) (data:Stack→List Bool)
    (hc:program pc=.base (.push stack bit next)) :
    Runs program 1 pc data next (Function.update data stack (bit::data stack)) := by
  exact one_base program pc next (.push stack bit next) data _ hc rfl rfl

/-- A literal global pop with one continuation, including actual EOF. -/
theorem pop_run (pc next:Label) (stack:Stack) (data:Stack→List Bool)
    (hc:program pc=.base (.pop stack next next next)) :
    Runs program 1 pc data next (Function.update data stack (data stack).tail) := by
  apply one_base program pc next (.pop stack next next next) data _ hc
  · cases h:(data stack).head? with
    | none => simp [B.execute,SemiprimeD1StackBytecode.choose,h]
    | some bit => cases bit <;> simp [B.execute,SemiprimeD1StackBytecode.choose,h]
  · rfl

/-- Every old limit byte is physically cleared; no stale field is discarded for free. -/
theorem clear_run (word:List Bool) (pc next:Label) (stack:Stack) (data:Stack→List Bool)
    (hw:data stack=word) (hc:program pc=.base (.pop stack next pc pc)) :
    Runs program (word.length+1) pc data next (Function.update data stack []) := by
  induction word generalizing data with
  | nil =>
    apply one_base program pc next (.pop stack next pc pc) data _ hc
    · simp [B.execute,SemiprimeD1StackBytecode.choose,hw]
    · change Function.update data stack (data stack).tail=_
      rw [hw,List.tail_nil]
  | cons bit word ih =>
    have h0:Runs program 1 pc data pc (Function.update data stack word):=by
      apply one_base program pc pc (.pop stack next pc pc) data _ hc
      · cases bit <;> simp [B.execute,SemiprimeD1StackBytecode.choose,hw]
      · change Function.update data stack (data stack).tail=_
        rw [hw,List.tail_cons]
    have h1:=ih (Function.update data stack word) (Function.update_self _ _ _)
    have h:=h0.trans h1
    rw [Function.update_idem] at h
    simpa only [List.length_cons,show 1+(word.length+1)=word.length+1+1 by omega] using h
end RiemannGaussian.SemiprimeD1StackPortCatalogueView

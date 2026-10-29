/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPacketInventoryPrimitives
import RiemannGaussian.SemiprimeD1StackPacketInventoryEncoding
/-! # Complete physical bank views of the actual sparse inventory
The component functions below are proof notations for fixed finite physical
banks. No function, native dictionary, row getter or callback enters sigma.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPacketInventoryView
open SemiprimeD1StackPacketInventory
namespace W
export SemiprimeD1StackSourceKeyFrequencyEncoding (Words bank)
end W
/-- All59 actual allocations, including all five repurposed global words. -/
def view (f:W.Words) (r:R.Stack→List Bool) (o:O.Stack→List Bool):Stack→List Bool:=
  Sum.elim (W.bank f) (Sum.elim r o)
/-- The complete21-role actual counter/lookup component is a direct physical projection. -/
theorem frequency_get (f:W.Words) (r:R.Stack→List Bool) (o:O.Stack→List Bool) (k:F.Stack):
    view f r o (frequencyStack k)=W.bank f k:=rfl
/-- Actual reader allocations include the two separately retained packet/history globals. -/
theorem reader_get (f:W.Words) (r:R.Stack→List Bool) (o:O.Stack→List Bool) (k:R.Stack):
    view f r o (readerAllocation k)=r k:=rfl
/-- Actual orientation allocations include the three separately retained catalogue/map globals. -/
theorem orientation_get (f:W.Words) (r:R.Stack→List Bool) (o:O.Stack→List Bool) (k:O.Stack):
    view f r o (orientationAllocation k)=o k:=rfl
/-- One actual source word update preserves all other58physical words. -/
theorem update_source (f:W.Words) (r:R.Stack→List Bool) (o:O.Stack→List Bool) (word:List Bool):
    Function.update (view f r o) (frequencyStack (F.aux .source)) word=
      view {f with source:=word} r o :=by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · rcases k with k|k <;> rfl
/-- One actual reader word update preserves all other58physical words. -/
theorem update_reader (f:W.Words) (r:R.Stack→List Bool) (o:O.Stack→List Bool) (word:List Bool):
    Function.update (view f r o) (frequencyStack (F.aux .reader)) word=
      view {f with reader:=word} r o :=by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · rcases k with k|k <;> rfl
/-- One actual raw word update preserves all other58physical words. -/
theorem update_raw (f:W.Words) (r:R.Stack→List Bool) (o:O.Stack→List Bool) (word:List Bool):
    Function.update (view f r o) (frequencyStack (F.aux .raw)) word=
      view {f with raw:=word} r o :=by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · rcases k with k|k <;> rfl
/-- One actual dictionary word update preserves all other58physical words. -/
theorem update_dictionary (f:W.Words) (r:R.Stack→List Bool) (o:O.Stack→List Bool) (word:List Bool):
    Function.update (view f r o) (frequencyStack (F.aux .dictionary)) word=
      view {f with dictionary:=word} r o :=by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · rcases k with k|k <;> rfl
/-- One actual count word update preserves all other58physical words. -/
theorem update_count (f:W.Words) (r:R.Stack→List Bool) (o:O.Stack→List Bool) (word:List Bool):
    Function.update (view f r o) (frequencyStack (F.aux .count)) word=
      view {f with count:=word} r o :=by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · rcases k with k|k <;> rfl
/-- One actual maximum word update preserves all other58physical words. -/
theorem update_maximum (f:W.Words) (r:R.Stack→List Bool) (o:O.Stack→List Bool) (word:List Bool):
    Function.update (view f r o) (frequencyStack (F.aux .maximum)) word=
      view {f with maximum:=word} r o :=by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · rcases k with k|k <;> rfl
/-- One actual incScratch word update preserves all other58physical words. -/
theorem update_incScratch (f:W.Words) (r:R.Stack→List Bool) (o:O.Stack→List Bool) (word:List Bool):
    Function.update (view f r o) (frequencyStack (F.aux .incScratch)) word=
      view {f with incScratch:=word} r o :=by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · rcases k with k|k <;> rfl
/-- One actual incNext word update preserves all other58physical words. -/
theorem update_incNext (f:W.Words) (r:R.Stack→List Bool) (o:O.Stack→List Bool) (word:List Bool):
    Function.update (view f r o) (frequencyStack (F.aux .incNext)) word=
      view {f with incNext:=word} r o :=by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · rcases k with k|k <;> rfl
/-- One actual trimScratch word update preserves all other58physical words. -/
theorem update_trimScratch (f:W.Words) (r:R.Stack→List Bool) (o:O.Stack→List Bool) (word:List Bool):
    Function.update (view f r o) (frequencyStack (F.aux .trimScratch)) word=
      view {f with trimScratch:=word} r o :=by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · rcases k with k|k <;> rfl
/-- One actual frameScratch word update preserves all other58physical words. -/
theorem update_frameScratch (f:W.Words) (r:R.Stack→List Bool) (o:O.Stack→List Bool) (word:List Bool):
    Function.update (view f r o) (frequencyStack (F.aux .frameScratch)) word=
      view {f with frameScratch:=word} r o :=by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · rcases k with k|k <;> rfl
/-- One actual query word update preserves all other58physical words. -/
theorem update_query (f:W.Words) (r:R.Stack→List Bool) (o:O.Stack→List Bool) (word:List Bool):
    Function.update (view f r o) (frequencyStack (F.lookupStack (.inr .query))) word=
      view {f with query:=word} r o :=by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · rcases k with k|k <;> rfl
/-- One actual lookupReader word update preserves all other58physical words. -/
theorem update_lookupReader (f:W.Words) (r:R.Stack→List Bool) (o:O.Stack→List Bool) (word:List Bool):
    Function.update (view f r o) (frequencyStack (F.lookupStack (.inr .reader))) word=
      view {f with lookupReader:=word} r o :=by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · rcases k with k|k <;> rfl
/-- One actual left word update preserves all other58physical words. -/
theorem update_left (f:W.Words) (r:R.Stack→List Bool) (o:O.Stack→List Bool) (word:List Bool):
    Function.update (view f r o) (frequencyStack (F.lookupStack (.inl .left))) word=
      view {f with left:=word} r o :=by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · rcases k with k|k <;> rfl
/-- One actual right word update preserves all other58physical words. -/
theorem update_right (f:W.Words) (r:R.Stack→List Bool) (o:O.Stack→List Bool) (word:List Bool):
    Function.update (view f r o) (frequencyStack (F.lookupStack (.inl .right))) word=
      view {f with right:=word} r o :=by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · rcases k with k|k <;> rfl
/-- One actual eqScratch word update preserves all other58physical words. -/
theorem update_eqScratch (f:W.Words) (r:R.Stack→List Bool) (o:O.Stack→List Bool) (word:List Bool):
    Function.update (view f r o) (frequencyStack (F.lookupStack (.inl .scratch))) word=
      view {f with eqScratch:=word} r o :=by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · rcases k with k|k <;> rfl
/-- One actual comparison word update preserves all other58physical words. -/
theorem update_comparison (f:W.Words) (r:R.Stack→List Bool) (o:O.Stack→List Bool) (word:List Bool):
    Function.update (view f r o) (frequencyStack (F.lookupStack (.inl .output))) word=
      view {f with comparison:=word} r o :=by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · rcases k with k|k <;> rfl
/-- One actual valid word update preserves all other58physical words. -/
theorem update_valid (f:W.Words) (r:R.Stack→List Bool) (o:O.Stack→List Bool) (word:List Bool):
    Function.update (view f r o) (frequencyStack (F.lookupStack (.inr .valid))) word=
      view {f with valid:=word} r o :=by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · rcases k with k|k <;> rfl
/-- One actual discard word update preserves all other58physical words. -/
theorem update_discard (f:W.Words) (r:R.Stack→List Bool) (o:O.Stack→List Bool) (word:List Bool):
    Function.update (view f r o) (frequencyStack (F.lookupStack (.inr .discard))) word=
      view {f with discard:=word} r o :=by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · rcases k with k|k <;> rfl
/-- One actual oldCount word update preserves all other58physical words. -/
theorem update_oldCount (f:W.Words) (r:R.Stack→List Bool) (o:O.Stack→List Bool) (word:List Bool):
    Function.update (view f r o) (frequencyStack (F.lookupStack (.inr .output))) word=
      view {f with oldCount:=word} r o :=by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · rcases k with k|k <;> rfl
/-- One actual fieldScratch word update preserves all other58physical words. -/
theorem update_fieldScratch (f:W.Words) (r:R.Stack→List Bool) (o:O.Stack→List Bool) (word:List Bool):
    Function.update (view f r o) (frequencyStack (F.lookupStack (.inr .fieldScratch))) word=
      view {f with fieldScratch:=word} r o :=by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · rcases k with k|k <;> rfl
/-- One actual copyScratch word update preserves all other58physical words. -/
theorem update_copyScratch (f:W.Words) (r:R.Stack→List Bool) (o:O.Stack→List Bool) (word:List Bool):
    Function.update (view f r o) (frequencyStack (F.lookupStack (.inr .copyScratch))) word=
      view {f with copyScratch:=word} r o :=by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · rcases k with k|k <;> rfl
/-- One actual allocated reader/global update changes no counter or orientation word. -/
theorem update_readerAllocation (f:W.Words) (r:R.Stack→List Bool) (o:O.Stack→List Bool) (part:R.Stack) (word:List Bool):
    Function.update (view f r o) (readerAllocation part) word=view f (Function.update r part word) o :=by
  funext k
  rcases k with k|k
  · rfl
  · rcases k with k|k
    · simp only [view,readerAllocation,Function.update_apply,Sum.inr.injEq,Sum.inl.injEq,Sum.elim_inr,Sum.elim_inl]
    · rfl
/-- One actual allocated orientation/global update changes no counter or reader word. -/
theorem update_orientationAllocation (f:W.Words) (r:R.Stack→List Bool) (o:O.Stack→List Bool) (part:O.Stack) (word:List Bool):
    Function.update (view f r o) (orientationAllocation part) word=view f r (Function.update o part word) :=by
  funext k
  rcases k with k|k
  · rfl
  · rcases k with k|k
    · rfl
    · simp only [view,orientationAllocation,Function.update_apply,Sum.inr.injEq,Sum.elim_inr]
end RiemannGaussian.SemiprimeD1StackPacketInventoryView

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceSelectionAcquire
/-! # Complete actual154-role source/cache boundaries and literal updates -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceSelectionAcquireView
open SemiprimeD1StackSourceSelectionAcquire
/-- An actual occurrences update preserves every other physical component and copy scratch. -/
theorem data_occurrences (occurrences:Occ.Stack→List Bool) (alphabet:Alpha.Stack→List Bool) (selector:Select.Stack→List Bool) (keys:Keys.Stack→List Bool) (scratch xs:List Bool) (k:Occ.Stack) :
    Function.update (data occurrences alphabet selector keys scratch) (occurrenceStack k) xs=data (Function.update occurrences k xs) alphabet selector keys scratch :=by
  funext p
  rcases p with p|p
  · simp only [data,occurrenceStack,Function.update_apply,Sum.elim_inl,Sum.inl.injEq]
  · rfl
/-- Every actual occurrences word has its identical physical source projection. -/
theorem occurrences_word (occurrences:Occ.Stack→List Bool) (alphabet:Alpha.Stack→List Bool) (selector:Select.Stack→List Bool) (keys:Keys.Stack→List Bool) (scratch:List Bool) (k:Occ.Stack) :
    data occurrences alphabet selector keys scratch (occurrenceStack k)=occurrences k :=rfl
/-- An actual alphabet update preserves every other physical component and copy scratch. -/
theorem data_alphabet (occurrences:Occ.Stack→List Bool) (alphabet:Alpha.Stack→List Bool) (selector:Select.Stack→List Bool) (keys:Keys.Stack→List Bool) (scratch xs:List Bool) (k:Alpha.Stack) :
    Function.update (data occurrences alphabet selector keys scratch) (alphabetStack k) xs=data occurrences (Function.update alphabet k xs) selector keys scratch :=by
  funext p
  rcases p with p|p
  · rfl
  · rcases p with p|p
    · simp only [data,alphabetStack,Function.update_apply,Sum.elim_inr,Sum.inr.injEq,Sum.elim_inl,Sum.inl.injEq]
    · rfl
/-- Every actual alphabet word has its identical physical source projection. -/
theorem alphabet_word (occurrences:Occ.Stack→List Bool) (alphabet:Alpha.Stack→List Bool) (selector:Select.Stack→List Bool) (keys:Keys.Stack→List Bool) (scratch:List Bool) (k:Alpha.Stack) :
    data occurrences alphabet selector keys scratch (alphabetStack k)=alphabet k :=rfl
/-- An actual selector update preserves every other physical component and copy scratch. -/
theorem data_selector (occurrences:Occ.Stack→List Bool) (alphabet:Alpha.Stack→List Bool) (selector:Select.Stack→List Bool) (keys:Keys.Stack→List Bool) (scratch xs:List Bool) (k:Select.Stack) :
    Function.update (data occurrences alphabet selector keys scratch) (selectorStack k) xs=data occurrences alphabet (Function.update selector k xs) keys scratch :=by
  funext p
  rcases p with p|p
  · rfl
  · rcases p with p|p
    · rfl
    · rcases p with p|p
      · simp only [data,selectorStack,Function.update_apply,Sum.elim_inr,Sum.inr.injEq,Sum.elim_inl,Sum.inl.injEq]
      · rfl
/-- Every actual selector word has its identical physical source projection. -/
theorem selector_word (occurrences:Occ.Stack→List Bool) (alphabet:Alpha.Stack→List Bool) (selector:Select.Stack→List Bool) (keys:Keys.Stack→List Bool) (scratch:List Bool) (k:Select.Stack) :
    data occurrences alphabet selector keys scratch (selectorStack k)=selector k :=rfl
/-- An actual keys update preserves every other physical component and copy scratch. -/
theorem data_keys (occurrences:Occ.Stack→List Bool) (alphabet:Alpha.Stack→List Bool) (selector:Select.Stack→List Bool) (keys:Keys.Stack→List Bool) (scratch xs:List Bool) (k:Keys.Stack) :
    Function.update (data occurrences alphabet selector keys scratch) (keyStack k) xs=data occurrences alphabet selector (Function.update keys k xs) scratch :=by
  funext p
  rcases p with p|p
  · rfl
  · rcases p with p|p
    · rfl
    · rcases p with p|p
      · rfl
      · rcases p with p|p
        · simp only [data,keyStack,Function.update_apply,Sum.elim_inr,Sum.inr.injEq,Sum.elim_inl,Sum.inl.injEq]
        · rfl
/-- Every actual keys word has its identical physical source projection. -/
theorem keys_word (occurrences:Occ.Stack→List Bool) (alphabet:Alpha.Stack→List Bool) (selector:Select.Stack→List Bool) (keys:Keys.Stack→List Bool) (scratch:List Bool) (k:Keys.Stack) :
    data occurrences alphabet selector keys scratch (keyStack k)=keys k :=rfl
end RiemannGaussian.SemiprimeD1StackSourceSelectionAcquireView


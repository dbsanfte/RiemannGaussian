/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceEnvironmentExtend
/-! # Literal physical boundary stores for retained source prefix environments -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceEnvironmentView
open SemiprimeD1StackSourceEnvironment SemiprimeD1StackSourceEnvironmentExtend
/-- All25words at source boundaries; every temporary not listed is physically EMPTY. -/
def view (dict key chosen q pfx reader reversed found lookupReader out:List Bool) :Stack→List Bool :=
  Sum.elim (L.data q lookupReader [] [] [] [] [] out) (fun k=>match k with
    | .dictionary=>dict | .nextKey=>key | .chosenID=>chosen | .prefix=>pfx | .reader=>reader
    | .reversedPrefix=>reversed | .found=>found | _=>[])
/-- One actual dictionary update retains every other physical source/cache/lookup word. -/
theorem view_dictionary (dict key chosen q pfx reader reversed found lookupReader out word:List Bool) :
    Function.update (view dict key chosen q pfx reader reversed found lookupReader out) (aux .dictionary) word=
      view word key chosen q pfx reader reversed found lookupReader out :=by
  funext k
  rcases k with k|k
  · rfl
  · cases k <;> rfl
/-- One actual nextKey update retains every other physical source/cache/lookup word. -/
theorem view_nextKey (dict key chosen q pfx reader reversed found lookupReader out word:List Bool) :
    Function.update (view dict key chosen q pfx reader reversed found lookupReader out) (aux .nextKey) word=
      view dict word chosen q pfx reader reversed found lookupReader out :=by
  funext k
  rcases k with k|k
  · rfl
  · cases k <;> rfl
/-- One actual chosenID update retains every other physical source/cache/lookup word. -/
theorem view_chosenID (dict key chosen q pfx reader reversed found lookupReader out word:List Bool) :
    Function.update (view dict key chosen q pfx reader reversed found lookupReader out) (aux .chosenID) word=
      view dict key word q pfx reader reversed found lookupReader out :=by
  funext k
  rcases k with k|k
  · rfl
  · cases k <;> rfl
/-- One actual prefix update retains every other physical source/cache/lookup word. -/
theorem view_prefix (dict key chosen q pfx reader reversed found lookupReader out word:List Bool) :
    Function.update (view dict key chosen q pfx reader reversed found lookupReader out) (aux .prefix) word=
      view dict key chosen q word reader reversed found lookupReader out :=by
  funext k
  rcases k with k|k
  · rfl
  · cases k <;> rfl
/-- One actual reader update retains every other physical source/cache/lookup word. -/
theorem view_reader (dict key chosen q pfx reader reversed found lookupReader out word:List Bool) :
    Function.update (view dict key chosen q pfx reader reversed found lookupReader out) (aux .reader) word=
      view dict key chosen q pfx word reversed found lookupReader out :=by
  funext k
  rcases k with k|k
  · rfl
  · cases k <;> rfl
/-- One actual reversedPrefix update retains every other physical source/cache/lookup word. -/
theorem view_reversedPrefix (dict key chosen q pfx reader reversed found lookupReader out word:List Bool) :
    Function.update (view dict key chosen q pfx reader reversed found lookupReader out) (aux .reversedPrefix) word=
      view dict key chosen q pfx reader word found lookupReader out :=by
  funext k
  rcases k with k|k
  · rfl
  · cases k <;> rfl
/-- One actual found update retains every other physical source/cache/lookup word. -/
theorem view_found (dict key chosen q pfx reader reversed found lookupReader out word:List Bool) :
    Function.update (view dict key chosen q pfx reader reversed found lookupReader out) (aux .found) word=
      view dict key chosen q pfx reader reversed word lookupReader out :=by
  funext k
  rcases k with k|k
  · rfl
  · cases k <;> rfl
/-- One actual lookup-reader update retains every private environment/prefix word. -/
theorem view_lookup_reader (dict key chosen q pfx reader reversed found lookupReader out word:List Bool) :
    Function.update (view dict key chosen q pfx reader reversed found lookupReader out) (lookupStack (.inr .reader)) word=
      view dict key chosen q pfx reader reversed found word out :=by
  funext k
  rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · rfl
/-- One actual lookup-output update retains every private environment/prefix word. -/
theorem view_lookup_output (dict key chosen q pfx reader reversed found lookupReader out word:List Bool) :
    Function.update (view dict key chosen q pfx reader reversed found lookupReader out) (lookupStack (.inr .output)) word=
      view dict key chosen q pfx reader reversed found lookupReader word :=by
  funext k
  rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · rfl
/-- Every extension work field is actually empty at the literal clean boundary. -/
theorem view_clear (dict key chosen q pfx reader reversed found lookupReader out:List Bool) :
    ExtendClear (view dict key chosen q pfx reader reversed found lookupReader out) :=by
  intro k hk
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with h|h|h|h|h|h|h <;> subst k <;> rfl
/-- Source initialization equals this literal all25word view without any next-key/dictionary answer. -/
theorem input_eq (pfx:List Bool) :input pfx=view [] [] [] [] pfx [] [] [] [] [] :=by
  funext k
  rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
end RiemannGaussian.SemiprimeD1StackSourceEnvironmentView

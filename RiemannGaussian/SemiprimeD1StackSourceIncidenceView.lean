/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceIncidencePrimitives
/-! # Exact retained-cache stores along one physical endpoint classification -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceIncidenceView
open SemiprimeD1StackSourceIncidence
namespace Env
export SemiprimeD1StackSourceEnvironmentView (view)
export SemiprimeD1StackSourceEnvironmentEncoding (dictionary variableKey)
end Env
/-- All47words during actual classification, preserving every other caller/private word. -/
def view (ids:List (List Bool)) (chosen pfx:List Bool) (privateWords:Aux→List Bool)
    (q left right comparison present returned:List Bool) :Stack→List Bool :=
  Sum.elim (Env.view (Env.dictionary ids) (Env.variableKey ids.length) chosen q pfx [] [] present [] returned)
    (fun k=>match k with | .eqLeft=>left | .eqRight=>right | .eqOutput=>comparison | _=>privateWords k)
/-- One physical q update preserves the entire other47-role bank. -/
theorem update_q (ids:List (List Bool)) (chosen pfx:List Bool) (privateWords:Aux→List Bool)
    (q left right comparison present returned word:List Bool) :
    Function.update (view ids chosen pfx privateWords q left right comparison present returned) (query) word=
      view ids chosen pfx privateWords word left right comparison present returned :=by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · cases k <;> rfl
/-- One physical left update preserves the entire other47-role bank. -/
theorem update_left (ids:List (List Bool)) (chosen pfx:List Bool) (privateWords:Aux→List Bool)
    (q left right comparison present returned word:List Bool) :
    Function.update (view ids chosen pfx privateWords q left right comparison present returned) (aux .eqLeft) word=
      view ids chosen pfx privateWords q word right comparison present returned :=by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · cases k <;> rfl
/-- One physical right update preserves the entire other47-role bank. -/
theorem update_right (ids:List (List Bool)) (chosen pfx:List Bool) (privateWords:Aux→List Bool)
    (q left right comparison present returned word:List Bool) :
    Function.update (view ids chosen pfx privateWords q left right comparison present returned) (aux .eqRight) word=
      view ids chosen pfx privateWords q left word comparison present returned :=by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · cases k <;> rfl
/-- One physical comparison update preserves the entire other47-role bank. -/
theorem update_comparison (ids:List (List Bool)) (chosen pfx:List Bool) (privateWords:Aux→List Bool)
    (q left right comparison present returned word:List Bool) :
    Function.update (view ids chosen pfx privateWords q left right comparison present returned) (aux .eqOutput) word=
      view ids chosen pfx privateWords q left right word present returned :=by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · cases k <;> rfl
/-- One physical present update preserves the entire other47-role bank. -/
theorem update_present (ids:List (List Bool)) (chosen pfx:List Bool) (privateWords:Aux→List Bool)
    (q left right comparison present returned word:List Bool) :
    Function.update (view ids chosen pfx privateWords q left right comparison present returned) (found) word=
      view ids chosen pfx privateWords q left right comparison word returned :=by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · cases k <;> rfl
/-- One physical returned update preserves the entire other47-role bank. -/
theorem update_returned (ids:List (List Bool)) (chosen pfx:List Bool) (privateWords:Aux→List Bool)
    (q left right comparison present returned word:List Bool) :
    Function.update (view ids chosen pfx privateWords q left right comparison present returned) (idOutput) word=
      view ids chosen pfx privateWords q left right comparison present word :=by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · cases k <;> rfl
/-- The actual complete environment projection is its canonical retained-cache lookup view. -/
theorem environment_projection (ids:List (List Bool)) (chosen pfx:List Bool) (privateWords:Aux→List Bool)
    (q left right comparison:List Bool) (k:SemiprimeD1StackSourceEnvironment.Stack) :
    view ids chosen pfx privateWords q left right comparison [] [] (environmentStack k)=
      (SemiprimeD1StackSourceEnvironmentExecution.lookupReady ids chosen q pfx).data k :=rfl
/-- Both actual endpoint namespaces retain precisely their originally parsed physical key bytes. -/
theorem key_projection (ids:List (List Bool)) (chosen pfx:List Bool) (privateWords:Aux→List Bool)
    (q left right comparison present returned:List Bool) (inner:Bool) (kind:Edge) :
    view ids chosen pfx privateWords q left right comparison present returned (key inner kind)=
      Sum.elim (fun _=>[]) privateWords (key inner kind) :=by
  cases inner <;> cases kind <;> rfl
end RiemannGaussian.SemiprimeD1StackSourceIncidenceView

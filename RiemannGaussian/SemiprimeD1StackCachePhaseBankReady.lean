/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackCachePhaseBankState
/-! # Exact physical four-input callee handoff
The outer parsers install ONLY the acquired reference and actual child bytes.
Every other per-phase callee field must have been physically cleared.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackCachePhaseBankReady
open SemiprimeD1StackCachePhaseBank
/-- Fixed actual current-reference port in the complete238-role bank. -/
def referenceRole:P.Stack:=P.restoreStack (SemiprimeD1StackCachePhase.Restore.heapStack .reference)
/-- Fixed actual current-child-tape port in the complete238-role bank. -/
def childRole:P.Stack:=P.foldStack (SemiprimeD1StackCachePhase.Fold.aux .children)
/-- The two real parsed fields produce EXACT the actual callee initial data, with no other prepared work. -/
theorem parsed_input (hp cn ref children:List Bool):
    Function.update (Function.update (P.input hp cn [] []) referenceRole ref) childRole children=P.input hp cn ref children:=by
  funext k
  rcases k with r|tail
  · rcases r with fresh|h
    · rfl
    · cases h <;> rfl
  · rcases tail with fold|tail
    · rcases fold with mul|tail
      · rfl
      · rcases tail with context|tail
        · rfl
        · rcases tail with unit|tail
          · rfl
          · rcases tail with add|a
            · rfl
            · cases a <;> rfl
    · rcases tail with blocks|u <;> rfl
end RiemannGaussian.SemiprimeD1StackCachePhaseBankReady

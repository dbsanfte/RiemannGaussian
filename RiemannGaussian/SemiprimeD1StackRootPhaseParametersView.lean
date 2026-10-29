/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootPhaseParametersCalls
/-! # Literal complete-bank update equations used by the actual cache trace -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootPhaseParametersView
open SemiprimeD1StackRootPhaseParameters SemiprimeD1StackRootPhaseParametersEncoding
/-- One physical reader write retains all other188 allocated words. -/
theorem update_reader (root:G.Stack→List Bool) (phase:P.Stack→List Bool)
    (reader index record heap counter reference history output next:List Bool) :
    Function.update (view root phase reader index record heap counter reference history output) (aux .reader) next=
      view root phase next index record heap counter reference history output :=by
  funext k
  rcases k with k|k
  · rfl
  · rcases k with k|k
    · rfl
    · cases k <;> rfl
/-- One physical index write retains all other188 allocated words. -/
theorem update_index (root:G.Stack→List Bool) (phase:P.Stack→List Bool)
    (reader index record heap counter reference history output next:List Bool) :
    Function.update (view root phase reader index record heap counter reference history output) (aux .index) next=
      view root phase reader next record heap counter reference history output :=by
  funext k
  rcases k with k|k
  · rfl
  · rcases k with k|k
    · rfl
    · cases k <;> rfl
/-- One physical record write retains all other188 allocated words. -/
theorem update_record (root:G.Stack→List Bool) (phase:P.Stack→List Bool)
    (reader index record heap counter reference history output next:List Bool) :
    Function.update (view root phase reader index record heap counter reference history output) (aux .record) next=
      view root phase reader index next heap counter reference history output :=by
  funext k
  rcases k with k|k
  · rfl
  · rcases k with k|k
    · rfl
    · cases k <;> rfl
/-- One physical heap write retains all other188 allocated words. -/
theorem update_heap (root:G.Stack→List Bool) (phase:P.Stack→List Bool)
    (reader index record heap counter reference history output next:List Bool) :
    Function.update (view root phase reader index record heap counter reference history output) (aux .heap) next=
      view root phase reader index record next counter reference history output :=by
  funext k
  rcases k with k|k
  · rfl
  · rcases k with k|k
    · rfl
    · cases k <;> rfl
/-- One physical counter write retains all other188 allocated words. -/
theorem update_counter (root:G.Stack→List Bool) (phase:P.Stack→List Bool)
    (reader index record heap counter reference history output next:List Bool) :
    Function.update (view root phase reader index record heap counter reference history output) (aux .counter) next=
      view root phase reader index record heap next reference history output :=by
  funext k
  rcases k with k|k
  · rfl
  · rcases k with k|k
    · rfl
    · cases k <;> rfl
/-- One physical reference write retains all other188 allocated words. -/
theorem update_reference (root:G.Stack→List Bool) (phase:P.Stack→List Bool)
    (reader index record heap counter reference history output next:List Bool) :
    Function.update (view root phase reader index record heap counter reference history output) (aux .reference) next=
      view root phase reader index record heap counter next history output :=by
  funext k
  rcases k with k|k
  · rfl
  · rcases k with k|k
    · rfl
    · cases k <;> rfl
/-- One physical history write retains all other188 allocated words. -/
theorem update_history (root:G.Stack→List Bool) (phase:P.Stack→List Bool)
    (reader index record heap counter reference history output next:List Bool) :
    Function.update (view root phase reader index record heap counter reference history output) (aux .refsHistory) next=
      view root phase reader index record heap counter reference next output :=by
  funext k
  rcases k with k|k
  · rfl
  · rcases k with k|k
    · rfl
    · cases k <;> rfl
/-- One physical output write retains all other188 allocated words. -/
theorem update_output (root:G.Stack→List Bool) (phase:P.Stack→List Bool)
    (reader index record heap counter reference history output next:List Bool) :
    Function.update (view root phase reader index record heap counter reference history output) (aux .refsOutput) next=
      view root phase reader index record heap counter reference history next :=by
  funext k
  rcases k with k|k
  · rfl
  · rcases k with k|k
    · rfl
    · cases k <;> rfl
/-- The physical parser validity flag is empty at every phase boundary. -/
theorem valid_empty (root:G.Stack→List Bool) (phase:P.Stack→List Bool)
    (reader index record heap counter reference history output:List Bool) :
    view root phase reader index record heap counter reference history output (aux .valid)=[] :=rfl
/-- Replacing the actual phase bank retains every source, grid and new-work word. -/
theorem replace_phase (root:G.Stack→List Bool) (phase next:P.Stack→List Bool)
    (reader index record heap counter reference history output:List Bool) :
    SemiprimeD1StackRootPhaseParametersCalls.replacePhase
      (view root phase reader index record heap counter reference history output) next=
      view root next reader index record heap counter reference history output :=rfl
end RiemannGaussian.SemiprimeD1StackRootPhaseParametersView

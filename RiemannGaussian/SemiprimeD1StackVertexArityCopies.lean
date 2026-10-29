/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackVertexArityView

/-! # Actual original-metadata copy and push stages for vertex arity -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000
set_option synthInstance.maxSize 8192
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackVertexArityCopies
open SemiprimeD1StackVertexArity SemiprimeD1StackVertexArityComponents SemiprimeD1StackVertexArityView
open SemiprimeD1StackProcedureFragments (Runs)
open SemiprimeD1StackUnaryDivmod (unary)

/-- Actual tag cache copy; every source word is physically restored. -/
theorem copy_tag (code index radius first second digits:ℕ) (arity tag multiplier right limit result:List Bool)
    (pc next:Label) (hc:program pc=.call (copyLabel .tag 0) next) :
    Runs program (5*code+4) pc (store (header code index radius first second digits) arity tag multiplier right limit result) next
      (store (header code index radius first second digits) arity (unary code++tag) multiplier right limit result) := by
  have h:=copy_call .tag (store (header code index radius first second digits) arity tag multiplier right limit result) rfl pc next hc
  change Runs program (5*(unary code).length+4) _ _ _
    (Function.update (data (header code index radius first second digits) (work arity tag multiplier right limit result))
      (aux .tagReader) (unary code++tag)) at h
  rw [update_aux,work_tagReader] at h
  rw [show (unary code).length=code by simp [unary]] at h
  exact h

/-- Actual radius cache copy; every source word is physically restored. -/
theorem copy_radius (code index radius first second digits:ℕ) (arity tag multiplier right limit result:List Bool)
    (pc next:Label) (hc:program pc=.call (copyLabel .radius 0) next) :
    Runs program (5*radius+4) pc (store (header code index radius first second digits) arity tag multiplier right limit result) next
      (store (header code index radius first second digits) (unary radius++arity) tag multiplier right limit result) := by
  have h:=copy_call .radius (store (header code index radius first second digits) arity tag multiplier right limit result) rfl pc next hc
  change Runs program (5*(unary radius).length+4) _ _ _
    (Function.update (data (header code index radius first second digits) (work arity tag multiplier right limit result))
      (aux .arity) (unary radius++arity)) at h
  rw [update_aux,work_arity] at h
  rw [show (unary radius).length=radius by simp [unary]] at h
  exact h

/-- Actual first cache copy; every source word is physically restored. -/
theorem copy_first (code index radius first second digits:ℕ) (arity tag multiplier right limit result:List Bool)
    (pc next:Label) (hc:program pc=.call (copyLabel .first 0) next) :
    Runs program (5*first+4) pc (store (header code index radius first second digits) arity tag multiplier right limit result) next
      (store (header code index radius first second digits) arity tag (unary first++multiplier) right limit result) := by
  have h:=copy_call .first (store (header code index radius first second digits) arity tag multiplier right limit result) rfl pc next hc
  change Runs program (5*(unary first).length+4) _ _ _
    (Function.update (data (header code index radius first second digits) (work arity tag multiplier right limit result))
      (aux .multiplier) (unary first++multiplier)) at h
  rw [update_aux,work_multiplier] at h
  rw [show (unary first).length=first by simp [unary]] at h
  exact h

/-- Actual second cache copy; every source word is physically restored. -/
theorem copy_second (code index radius first second digits:ℕ) (arity tag multiplier right limit result:List Bool)
    (pc next:Label) (hc:program pc=.call (copyLabel .second 0) next) :
    Runs program (5*second+4) pc (store (header code index radius first second digits) arity tag multiplier right limit result) next
      (store (header code index radius first second digits) arity tag (unary second++multiplier) right limit result) := by
  have h:=copy_call .second (store (header code index radius first second digits) arity tag multiplier right limit result) rfl pc next hc
  change Runs program (5*(unary second).length+4) _ _ _
    (Function.update (data (header code index radius first second digits) (work arity tag multiplier right limit result))
      (aux .multiplier) (unary second++multiplier)) at h
  rw [update_aux,work_multiplier] at h
  rw [show (unary second).length=second by simp [unary]] at h
  exact h

/-- Actual index cache copy; every source word is physically restored. -/
theorem copy_index (code index radius first second digits:ℕ) (arity tag multiplier right limit result:List Bool)
    (pc next:Label) (hc:program pc=.call (copyLabel .index 0) next) :
    Runs program (5*index+4) pc (store (header code index radius first second digits) arity tag multiplier right limit result) next
      (store (header code index radius first second digits) arity tag multiplier (unary index++right) limit result) := by
  have h:=copy_call .index (store (header code index radius first second digits) arity tag multiplier right limit result) rfl pc next hc
  change Runs program (5*(unary index).length+4) _ _ _
    (Function.update (data (header code index radius first second digits) (work arity tag multiplier right limit result))
      (aux .compareRight) (unary index++right)) at h
  rw [update_aux,work_compareRight] at h
  rw [show (unary index).length=index by simp [unary]] at h
  exact h

/-- Actual digits cache copy; every source word is physically restored. -/
theorem copy_digits (code index radius first second digits:ℕ) (arity tag multiplier right limit result:List Bool)
    (pc next:Label) (hc:program pc=.call (copyLabel .digits 0) next) :
    Runs program (5*digits+4) pc (store (header code index radius first second digits) arity tag multiplier right limit result) next
      (store (header code index radius first second digits) arity tag multiplier right (unary digits++limit) result) := by
  have h:=copy_call .digits (store (header code index radius first second digits) arity tag multiplier right limit result) rfl pc next hc
  change Runs program (5*(unary digits).length+4) _ _ _
    (Function.update (data (header code index radius first second digits) (work arity tag multiplier right limit result))
      (aux .compareLimit) (unary digits++limit)) at h
  rw [update_aux,work_compareLimit] at h
  rw [show (unary digits).length=digits by simp [unary]] at h
  exact h

/-- One actual output-marker push, preserving every other boundary word. -/
theorem push_arity (h:Source→List Bool) (arity tag multiplier right limit result:List Bool)
    (pc next:Label) (hc:program pc=.base (.push (aux .arity) true next)) :
    Runs program 1 pc (store h arity tag multiplier right limit result) next
      (store h (true::arity) tag multiplier right limit result) := by
  have hp:=push_run pc next (aux .arity) true (store h arity tag multiplier right limit result) hc
  change Runs program _ _ _ _
    (Function.update (data h (work arity tag multiplier right limit result)) (aux .arity) (true::arity)) at hp
  rw [update_aux,work_arity] at hp
  exact hp
end RiemannGaussian.SemiprimeD1StackVertexArityCopies

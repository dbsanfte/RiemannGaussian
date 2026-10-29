/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackCartesian4
import RiemannGaussian.SemiprimeD1StackLocalCall

/-! # Actual Cartesian Copy/Frame subcalls and their exact physical stores -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackCartesian4Components
open SemiprimeD1StackCartesian4
open SemiprimeD1StackProcedureFragments (Runs included_call)
open SemiprimeSourceHistogramKeyBits (frame)

/-- Literal twelve-role store; both actually used scratch words are empty here. -/
def store (limits indices:Fin 4→List Bool) (tag output:List Bool) : Stack→List Bool
  | .inl k => limits k
  | .inr (.inl k) => indices k
  | .inr (.inr k) => if k=2 then output else if k=3 then tag else []

/-- A physical index write changes exactly its actual Boolean word. -/
theorem store_index (limits indices:Fin 4→List Bool) (tag output word:List Bool) (level:Fin 4) :
    Function.update (store limits indices tag output) (indexStack level) word=
      store limits (Function.update indices level word) tag output := by
  funext k
  cases k with
  | inl k => simp [store,indexStack,Function.update]
  | inr k => cases k with
    | inl k =>
      by_cases h:k=level
      · subst k;simp [store,indexStack,Function.update]
      · simp [store,indexStack,Function.update,h]
    | inr k => simp [store,indexStack,Function.update]

/-- A physical output push/copy preserves all limit/index/tag words. -/
theorem store_output (limits indices:Fin 4→List Bool) (tag output word:List Bool) :
    Function.update (store limits indices tag output) (aux 2) word=store limits indices tag word := by
  funext k
  cases k with
  | inl k => simp [store,aux,Function.update]
  | inr k => cases k with
    | inl k => simp [store,aux,Function.update]
    | inr k => fin_cases k <;> simp [store,aux,Function.update]

/-- Actual Copy input, including its empty physical scratch. -/
theorem copy_input (level:Fin 4) (data:Stack→List Bool) (ht:data (aux 0)=[]) :
    Link.DataRel (copyStack level) data
      (SemiprimeD1StackCopy.payload (data (limitStack level)) (data (indexStack level)) []) data := by
  constructor
  · intro k;fin_cases k <;> simp [copyStack,SemiprimeD1StackCopy.payload,ht]
  · intro k _;rfl

/-- Actual returned Copy data, with every auxiliary field preserved. -/
theorem copy_output (level:Fin 4) (data:Stack→List Bool) (ht:data (aux 0)=[]) :
    Link.DataRel (copyStack level) data
      (SemiprimeD1StackCopy.payload (data (limitStack level))
        (data (limitStack level)++data (indexStack level)) [])
      (Function.update data (indexStack level) (data (limitStack level)++data (indexStack level))) := by
  change data (.inr (.inr 0))=[] at ht
  constructor
  · intro k
    fin_cases level <;> fin_cases k <;>
      simp [copyStack,limitStack,indexStack,aux,SemiprimeD1StackCopy.payload,ht,Function.update]
  · intro k hk
    have hn:k≠indexStack level:=by intro he;exact hk 1 he.symm
    exact Function.update_of_ne hn _ _

/-- Each loop level acquires its own limit by an ACTUAL included Copy call. -/
theorem copy_call (level:Fin 4) (data:Stack→List Bool) (ht:data (aux 0)=[]) :
    Runs program (5*(data (limitStack level)).length+4) (.inl (.entry level)) data (.inl (.drop level))
      (Function.update data (indexStack level) (data (limitStack level)++data (indexStack level))) := by
  apply included_call program (copyStack level) (copyLabel level) (copyStack_injective level)
    SemiprimeD1StackCopy.code 0 (fun _=>rfl) (.inl (.entry level)) (.inl (.drop level)) rfl
    (5*(data (limitStack level)).length+3)
    (SemiprimeD1StackCopy.state 0 none (data (limitStack level)) (data (indexStack level)) [])
    (SemiprimeD1StackCopy.done (data (limitStack level)) (data (limitStack level)++data (indexStack level)))
  · rfl
  · rfl
  · exact SemiprimeD1StackCopy.copy_words _ _ none
  · exact copy_input level data ht
  · exact copy_output level data ht

/-- The concrete copied limit replaces an ACTUALLY empty index. -/
theorem copy_empty (level:Fin 4) (limits indices:Fin 4→List Bool) (tag output:List Bool)
    (hi:indices level=[]) :
    Runs program (5*(limits level).length+4) (.inl (.entry level)) (store limits indices tag output)
      (.inl (.drop level)) (store limits (Function.update indices level (limits level)) tag output) := by
  have h:=copy_call level (store limits indices tag output) rfl
  change Runs program (5*(limits level).length+4) _ _ _
    (Function.update (store limits indices tag output) (indexStack level) (limits level++indices level)) at h
  rw [hi,List.append_nil,store_index] at h
  exact h

/-- The actual Frame operand projection includes its empty physical scratch. -/
theorem frame_input (part:Fin 5) (data:Stack→List Bool) (ht:data (aux 1)=[]) :
    Link.DataRel (frameStack part) data
      (SemiprimeD1StackFrame.payload (data (fieldSource part)) (data (aux 2)) []) data := by
  constructor
  · intro k;fin_cases k <;> simp [frameStack,SemiprimeD1StackFrame.payload,ht]
  · intro k _;rfl

/-- Returning Frame data preserve the actual field word and every other stack. -/
theorem frame_output (part:Fin 5) (data:Stack→List Bool) (ht:data (aux 1)=[]) :
    Link.DataRel (frameStack part) data
      (SemiprimeD1StackFrame.payload (data (fieldSource part)) (frame (data (fieldSource part)) (data (aux 2))) [])
      (Function.update data (aux 2) (frame (data (fieldSource part)) (data (aux 2)))) := by
  change data (.inr (.inr 1))=[] at ht
  constructor
  · intro k
    fin_cases part <;> fin_cases k <;>
      simp [frameStack,fieldSource,indexStack,aux,SemiprimeD1StackFrame.payload,ht,Function.update]
  · intro k hk
    have hn:k≠aux 2:=by intro he;exact hk 1 he.symm
    exact Function.update_of_ne hn _ _

/-- Every Cartesian record field is produced by the real included Frame procedure. -/
theorem frame_call (part:Fin 5) (data:Stack→List Bool) (ht:data (aux 1)=[]) :
    Runs program (6*(data (fieldSource part)).length+5) (.inl (.fields part)) data (nextField part)
      (Function.update data (aux 2) (frame (data (fieldSource part)) (data (aux 2)))) := by
  apply included_call program (frameStack part) (frameLabel part) (frameStack_injective part)
    SemiprimeD1StackFrame.code 0 (fun _=>rfl) (.inl (.fields part)) (nextField part) rfl
    (6*(data (fieldSource part)).length+4)
    (SemiprimeD1StackFrame.state 0 none (data (fieldSource part)) (data (aux 2)) [])
    (SemiprimeD1StackFrame.done (data (fieldSource part)) (frame (data (fieldSource part)) (data (aux 2))))
  · rfl
  · rfl
  · exact SemiprimeD1StackFrame.frame_words _ _ none
  · exact frame_input part data ht
  · exact frame_output part data ht

/-- Each complete physical field call retains all current indices. -/
theorem frame_store (part:Fin 5) (limits indices:Fin 4→List Bool) (tag output:List Bool) :
    Runs program (6*((store limits indices tag output) (fieldSource part)).length+5)
      (.inl (.fields part)) (store limits indices tag output) (nextField part)
      (store limits indices tag (frame ((store limits indices tag output) (fieldSource part)) output)) := by
  have h:=frame_call part (store limits indices tag output) rfl
  change Runs program _ _ _ _
    (Function.update (store limits indices tag output) (aux 2)
      (frame ((store limits indices tag output) (fieldSource part)) output)) at h
  rw [store_output] at h
  exact h
end RiemannGaussian.SemiprimeD1StackCartesian4Components

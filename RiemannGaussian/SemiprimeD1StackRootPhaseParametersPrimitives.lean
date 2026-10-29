/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootPhaseParametersEncoding
/-! # Real copied operands, complete stopped-bank frames and literal private cleanup -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1500000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootPhaseParametersPrimitives
open SemiprimeD1StackRootPhaseParameters SemiprimeD1StackRootPhaseParametersEncoding
open SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
/-- Composition executes fragments of this same fixed188-role source program. -/
theorem compose {m n:Nat} {pc mid next:Label} {before middle after:Stack→List Bool}
    (h:Runs program m pc before mid middle) (g:Runs program n mid middle next after) :
    Runs program (m+n) pc before next after :=runs_trans program _ _ _ _ _ _ _ _ h g
/-- The actual source and destination differ at every paid copy site. -/
theorem copy_target_ne_source (site:Fin 5) : copyTarget site≠copySource site :=by fin_cases site <;> decide
/-- Each actual paid source-copy destination differs from its restoration scratch. -/
theorem copy_target_ne_scratch (site:Fin 5) : copyTarget site≠aux .copyScratch :=by fin_cases site <;> decide
/-- Actual paid source copies retain all other188 data words and outer return cells. -/
theorem copy_call (site:Fin 5) (bank:Stack→List Bool)
    (hd:bank (copyTarget site)=[]) (hs:bank (aux .copyScratch)=[]) :
    Runs program (5*(bank (copySource site)).length+4) (.copySite site) bank (afterCopy site)
      (Function.update bank (copyTarget site) (bank (copySource site))) :=by
  apply included_call program (copyStack site) (Label.copy site) (copy_injective site)
    SemiprimeD1StackCopy.code 0 (fun _=>rfl) (.copySite site) (afterCopy site) rfl
    (5*(bank (copySource site)).length+3)
    (SemiprimeD1StackCopy.state 0 none (bank (copySource site)) [] [])
    (SemiprimeD1StackCopy.done (bank (copySource site)) (bank (copySource site)++[]))
  · rfl
  · rfl
  · exact SemiprimeD1StackCopy.copy_words _ [] none
  · constructor
    · intro i;fin_cases i
      · rfl
      · exact hd
      · exact hs
    · intro k _;rfl
  · constructor
    · intro i;fin_cases i
      · change Function.update bank (copyTarget site) (bank (copySource site)) (copySource site)=_
        simp only [Function.update_of_ne (Ne.symm (copy_target_ne_source site))]
        rfl
      · change Function.update bank (copyTarget site) (bank (copySource site)) (copyTarget site)=_
        simp only [Function.update_same,List.append_nil]
        rfl
      · change Function.update bank (copyTarget site) (bank (copySource site)) (aux .copyScratch)=[]
        rw [Function.update_of_ne (Ne.symm (copy_target_ne_scratch site)),hs]
    · intro k hk
      apply Function.update_of_ne
      intro h
      exact hk 1 h.symm
/-- One physically paid stopped-word frame changes only the actual record stack. -/
theorem frame_call (position:Fin 49) (h:position.val<48) (bank:Stack→List Bool)
    (hs:bank (aux .copyScratch)=[]) :
    let i:Fin 48:=⟨47-position.val,by omega⟩
    Runs program (6*(bank (phaseStack (I.role i))).length+5) (.serialize position) bank
      (.serialize ⟨position.val+1,by omega⟩)
      (Function.update bank (aux .record) (frame (bank (phaseStack (I.role i))) (bank (aux .record)))) :=by
  dsimp only
  let i:Fin 48:=⟨47-position.val,by omega⟩
  apply included_call program (frameStack i) (Label.frame i) (frame_injective i)
    SemiprimeD1StackFrame.code 0 (fun _=>rfl) (.serialize position)
    (.serialize ⟨position.val+1,by omega⟩) (by simp only [program,dite_eq_left h];rfl)
    (6*(bank (phaseStack (I.role i))).length+4)
    (SemiprimeD1StackFrame.state 0 none (bank (phaseStack (I.role i))) (bank (aux .record)) [])
    (SemiprimeD1StackFrame.done (bank (phaseStack (I.role i)))
      (frame (bank (phaseStack (I.role i))) (bank (aux .record))))
  · rfl
  · rfl
  · exact SemiprimeD1StackFrame.frame_words _ _ none
  · constructor
    · intro k;fin_cases k
      · rfl
      · rfl
      · exact hs
    · intro k _;rfl
  · constructor
    · intro k;fin_cases k
      · change Function.update bank (aux .record) _ (phaseStack (I.role i))=bank (phaseStack (I.role i))
        exact Function.update_of_ne (by simp [phaseStack,aux]) _ _
      · change Function.update bank (aux .record) _ (aux .record)=_
        exact Function.update_same _ _ _
      · change Function.update bank (aux .record) _ (aux .copyScratch)=[]
        rw [Function.update_of_ne (by decide : aux .copyScratch≠aux .record),hs]
    · intro k hk
      apply Function.update_of_ne
      intro he
      exact hk 1 he.symm
/-- The finite serialization sentinel is one actual jump, not a count oracle. -/
theorem serialization_end (bank:Stack→List Bool) : Runs program 1 (.serialize 48) bank .allocate bank :=by
  apply one_base program _ _ (.jump .allocate) _ _ rfl
  · rfl
  · rfl
/-- Every private cleanup loop physically visits and consumes its complete word. -/
theorem clear_call (position:Fin 52) (h:position.val<51) (bank:Stack→List Bool) :
    Runs program ((bank (clearStack ⟨position.val,h⟩)).length+1) (.clear position) bank
      (.clear ⟨position.val+1,by omega⟩) (Function.update bank (clearStack ⟨position.val,h⟩) []) :=by
  have hd:=SemiprimeD1StackPhysicalLoops.drain program (.clear position) (.clear ⟨position.val+1,by omega⟩)
    (clearStack ⟨position.val,h⟩) (by simp only [program,dite_eq_left h]) bank (bank (clearStack ⟨position.val,h⟩))
  simpa only [Function.update_eq_self] using hd
/-- The fixed cleanup sentinel returns to the physical vector-header reader. -/
theorem cleanup_end (bank:Stack→List Bool) : Runs program 1 (.clear 51) bank .header bank :=by
  apply one_base program _ _ (.jump .header) _ _ rfl
  · rfl
  · rfl
end RiemannGaussian.SemiprimeD1StackRootPhaseParametersPrimitives

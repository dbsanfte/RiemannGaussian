/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootPhaseFreshRecordsEncoding
/-! # Literal alias-preserving bank updates, physical pointer copies and record framing -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootPhaseFreshRecordsPrimitives
open SemiprimeD1StackRootPhaseFreshRecords SemiprimeD1StackRootPhaseFreshRecordsEncoding
open SemiprimeD1StackProcedureTrace
namespace Link
export SemiprimeD1StackMultiplierLink (DataRel data_update data_unique)
end Link
/-- Trace fragments compose on the SAME fixed345-role source and retain outer frames. -/
theorem compose {m n:Nat} {pc mid next:Label} {before middle after:Stack→List Bool}
    (h:Runs program m pc before mid middle) (g:Runs program n mid middle next after) :
    Runs program (m+n) pc before next after :=runs_trans program _ _ _ _ _ _ _ _ h g
/-- A logical client change touches only the actual included client addresses.
The three unused raw alias-shadows and all other caller words retain their bytes. -/
theorem view_rel (root:R.Stack→List Bool) (before after:Q.Stack→List Bool) (w:Aux→List Bool) :
    Link.DataRel cacheStack (view root before w) after (view root after w) :=by
  constructor
  · intro k;exact view_cache _ _ _ _
  · intro k hk
    rcases k with k|k
    · rcases k with k|k
      · rfl
      · rcases k with k|k
        · rfl
        · cases k <;> first | rfl | exact (hk I.sourceHeap rfl).elim | exact (hk I.sourceCounter rfl).elim
    · rcases k with k|k
      · rcases k with k|k
        · rcases k with k|k
          · exact (hk (.inl (.inl k)) rfl).elim
          · cases k with
            | heap | counter | reference=>rfl
            | reader=>exact (hk (.inl (.inr .reader)) rfl).elim
            | depth=>exact (hk (.inl (.inr .depth)) rfl).elim
            | referenceWork=>exact (hk (.inl (.inr .referenceWork)) rfl).elim
            | temporary=>exact (hk (.inl (.inr .temporary)) rfl).elim
            | fieldScratch=>exact (hk (.inl (.inr .fieldScratch)) rfl).elim
            | output=>exact (hk (.inl (.inr .output)) rfl).elim
            | valid=>exact (hk (.inl (.inr .valid)) rfl).elim
        · exact (hk (.inr k) rfl).elim
      · cases k <;> first | rfl | exact (hk I.sourceReference rfl).elim
/-- One actual included-client write has precisely its alias-preserving whole-bank effect. -/
theorem update_cache (root:R.Stack→List Bool) (q:Q.Stack→List Bool) (w:Aux→List Bool)
    (k:Q.Stack) (word:List Bool) :
    Function.update (view root q w) (cacheStack k) word=view root (Function.update q k word) w :=by
  have h0:=view_rel root q q w
  have h1:=Link.data_update cacheStack cache_injective (view root q w) q (view root q w) h0 k word
  exact Link.data_unique cacheStack (view root q w) (Function.update q k word) _ _ h1
    (view_rel root q (Function.update q k word) w)
/-- A caller auxiliary write other than the shared source pointer leaves client data intact. -/
theorem update_aux (root:R.Stack→List Bool) (q:Q.Stack→List Bool) (w:Aux→List Bool)
    (k:Aux) (hk:k≠.pointer) (word:List Bool) :
    Function.update (view root q w) (aux k) word=view root q (Function.update w k word) :=by
  funext slot
  rcases slot with slot|slot
  · rfl
  · rcases slot with slot|slot
    · rfl
    · cases k <;> cases slot <;> first | rfl | exact (hk rfl).elim
/-- A real pointer parse writes the SAME actual source reference input, never a predicted ordinal. -/
theorem update_pointer (root:R.Stack→List Bool) (q:Q.Stack→List Bool) (w:Aux→List Bool) (word:List Bool) :
    Function.update (view root q w) (aux .pointer) word=view root (Function.update q I.sourceReference word) w :=
  update_cache root q w I.sourceReference word
/-- The single real preserving copy consumes/reconstructs the actual complete source reference vector. -/
theorem copy_call (bank:Stack→List Bool) (hd:bank (aux .reader)=[]) (hs:bank (aux .copyScratch)=[]) :
    Runs program (5*(bank (rootStack R.output)).length+4) .copy bank .seedHeader
      (Function.update bank (aux .reader) (bank (rootStack R.output))) :=by
  apply included_call program copyStack Label.copier copy_injective SemiprimeD1StackCopy.code 0
    (fun _=>rfl) .copy .seedHeader rfl (5*(bank (rootStack R.output)).length+3)
    (SemiprimeD1StackCopy.state 0 none (bank (rootStack R.output)) [] [])
    (SemiprimeD1StackCopy.done (bank (rootStack R.output)) (bank (rootStack R.output)++[]))
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
      · rfl
      · simp only [List.append_nil]
        rfl
      · change Function.update bank (aux .reader) _ (aux .copyScratch)=[]
        rw [Function.update_of_ne (by decide :aux .copyScratch≠aux .reader),hs]
    · intro k hk
      exact Function.update_of_ne (fun h=>hk 1 h.symm) _ _
/-- Every85-word record frame pays its actual input cells, source restoration,
record writes, delimiter and real return while retaining every other field. -/
theorem frame_call (position:Fin 86) (h:position.val<85) (bank:Stack→List Bool)
    (hs:bank (aux .copyScratch)=[]) :
    let i:Fin 85:=⟨84-position.val,by omega⟩
    Runs program (6*(bank (freshStack (I.role i))).length+5) (.serialize position) bank
      (.serialize ⟨position.val+1,by omega⟩)
      (Function.update bank (aux .record)
        (SemiprimeSourceHistogramKeyBits.frame (bank (freshStack (I.role i))) (bank (aux .record)))) :=by
  dsimp only
  let i:Fin 85:=⟨84-position.val,by omega⟩
  apply included_call program (frameStack i) (Label.frame i) (frame_injective i)
    SemiprimeD1StackFrame.code 0 (fun _=>rfl) (.serialize position)
    (.serialize ⟨position.val+1,by omega⟩) (by simp only [program,dite_eq_left h];rfl)
    (6*(bank (freshStack (I.role i))).length+4)
    (SemiprimeD1StackFrame.state 0 none (bank (freshStack (I.role i))) (bank (aux .record)) [])
    (SemiprimeD1StackFrame.done (bank (freshStack (I.role i)))
      (SemiprimeSourceHistogramKeyBits.frame (bank (freshStack (I.role i))) (bank (aux .record))))
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
      · change Function.update bank (aux .record) _ (freshStack (I.role i))=bank (freshStack (I.role i))
        exact Function.update_of_ne (by rw [fresh_private];simp [cachePrivate,aux]) _ _
      · change Function.update bank (aux .record) _ (aux .record)=_
        exact Function.update_same _ _ _
      · change Function.update bank (aux .record) _ (aux .copyScratch)=[]
        rw [Function.update_of_ne (by decide :aux .copyScratch≠aux .record),hs]
    · intro k hk
      exact Function.update_of_ne (fun he=>hk 1 he.symm) _ _
/-- One literal finite serialization-sentinel jump. -/
theorem serialization_end (bank:Stack→List Bool) :Runs program 1 (.serialize 85) bank .allocate bank :=by
  apply one_base program _ _ (.jump .allocate) _ _ rfl
  · rfl
  · rfl
/-- Every physical clear position pops ALL actual bytes and pays its own EOF read. -/
theorem clear_call (position:Fin 146) (h:position.val<145) (bank:Stack→List Bool) :
    Runs program ((bank (clearStack ⟨position.val,h⟩)).length+1) (.clear position) bank
      (.clear ⟨position.val+1,by omega⟩) (Function.update bank (clearStack ⟨position.val,h⟩) []) :=by
  have hd:=SemiprimeD1StackPhysicalLoops.drain program (.clear position) (.clear ⟨position.val+1,by omega⟩)
    (clearStack ⟨position.val,h⟩) (by simp only [program,dite_eq_left h]) bank (bank (clearStack ⟨position.val,h⟩))
  simpa only [Function.update_eq_self] using hd
/-- One literal finite cleanup-sentinel jump back to the physical pointer header. -/
theorem cleanup_end (bank:Stack→List Bool) :Runs program 1 (.clear 145) bank .header bank :=by
  apply one_base program _ _ (.jump .header) _ _ rfl
  · rfl
  · rfl
end RiemannGaussian.SemiprimeD1StackRootPhaseFreshRecordsPrimitives

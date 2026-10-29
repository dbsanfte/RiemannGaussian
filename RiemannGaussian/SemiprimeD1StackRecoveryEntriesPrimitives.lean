/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryEntriesState
/-! # Paid row copy, finite source-bit transitions, all drains and physical logging
Every helper is an actual source trace of the SAME25-role caller program.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackRecoveryEntriesPrimitives
open SemiprimeD1StackRecoveryEntries SemiprimeD1StackRecoveryEntriesState
open SemiprimeD1StackProcedureTrace
/-- Actual trace composition retains every real saved return cell. -/
theorem join {m n:Nat} {pc mid next:Label} {before between after:Stack → List Bool}
    (h:Runs program m pc before mid between) (g:Runs program n mid between next after):
    Runs program (m+n) pc before next after:=runs_trans program m n pc mid next before between after h g
/-- Actual retained row copy, with all copy work and real call/return charged. -/
theorem copy_run (children:List Bool) (w:Aux → List Bool):
    Runs program (5*(w .rows).length+4) (.local .start) (data children w) (.local .sentinel)
      (data children (Function.update w .reader (w .rows++w .reader))):=by
  rw [data_update]
  let before:=SemiprimeD1StackCopy.state 0 none (w .rows) (w .reader) []
  let after:=SemiprimeD1StackCopy.done (w .rows) (w .rows++w .reader)
  have hi:SemiprimeD1StackMultiplierLink.DataRel copyStack (data children w) before.store (data children w):=by
    constructor
    · intro k;fin_cases k <;> rfl
    · intro k _;rfl
  have ho:=SemiprimeD1StackMultiplierLink.data_update copyStack copy_injective (data children w) before.store (data children w) hi (1:Fin 3) (w .rows++w .reader)
  have he:Function.update before.store 1 (w .rows++w .reader)=after.store:=by funext k;fin_cases k <;> rfl
  rw [he] at ho
  exact included_call program copyStack Label.copy copy_injective SemiprimeD1StackCopy.code 0 (fun _=>rfl)
    (.local .start) (.local .sentinel) rfl (5*(w .rows).length+3) before after _ _ rfl rfl
    (SemiprimeD1StackCopy.copy_words _ _ none) hi ho
/-- One real external-word push, with no supplied result tape. -/
theorem push_run (pc next:Label) (k:Aux) (bit:Bool) (children:List Bool) (w:Aux → List Bool)
    (hp:program pc=.base (.push (aux k) bit next)):
    Runs program 1 pc (data children w) next (data children (Function.update w k (bit::w k))):=by
  rw [data_update]
  exact one_base program pc next (.push (aux k) bit next) _ _ hp rfl rfl
/-- Actual pop reads a real source bit or EOF. -/
theorem pop_run (pc empty low high:Label) (k:Aux) (children:List Bool) (w:Aux → List Bool) (word:List Bool)
    (hp:program pc=.base (.pop (aux k) empty low high)) (hw:w k=word):
    Runs program 1 pc (data children w) (SemiprimeD1StackBytecode.choose empty low high word.head?)
      (data children (Function.update w k word.tail)):=by
  rw [data_update]
  apply one_base program _ _ _ _ _ hp
  · simp only [SemiprimeD1StackBytecode.execute,data_aux,hw]
  · simp only [SemiprimeD1StackBytecode.execute,data_aux,hw]
/-- Actual peek chooses only on the physical selected-row leading bit, preserving every payload byte. -/
theorem peek_run (pc empty low high:Label) (k:Aux) (children:List Bool) (w:Aux → List Bool) (word:List Bool)
    (hp:program pc=.base (.peek (aux k) empty low high)) (hw:w k=word):
    Runs program 1 pc (data children w) (SemiprimeD1StackBytecode.choose empty low high word.head?) (data children w):=by
  apply one_base program _ _ _ _ _ hp
  · simp only [SemiprimeD1StackBytecode.execute,data_aux,hw]
  · rfl
/-- Every per-row metadata, selected-cache and child cleanup bit is physically consumed. -/
theorem drain_run (pc next:Label) (k:Aux) (children:List Bool) (w:Aux → List Bool) (word:List Bool)
    (hp:program pc=.base (.pop (aux k) next pc pc)) (hw:w k=word):
    Runs program (word.length+1) pc (data children w) next (data children (Function.update w k [])):=by
  induction word generalizing w with
  | nil=>simpa only [List.length_nil,Nat.zero_add,List.head?_nil,List.tail_nil,SemiprimeD1StackBytecode.choose]
      using pop_run pc next pc pc k children w [] hp hw
  | cons bit word ih=>
    have h0:=pop_run pc next pc pc k children w (bit::word) hp hw
    have h1:=ih (Function.update w k word) (Function.update_self _ _ _)
    have h:=join (by cases bit <;> exact h0) h1
    simpa only [Function.update_idem,List.length_cons,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using h
end RiemannGaussian.SemiprimeD1StackRecoveryEntriesPrimitives

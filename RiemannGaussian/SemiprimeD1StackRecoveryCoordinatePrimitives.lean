/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryCoordinateState
/-! # Paid phase-bank copy, finite source-bit transitions, all drains and physical logging
Every helper is an actual source trace of the SAME21-role caller program.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackRecoveryCoordinatePrimitives
open SemiprimeD1StackRecoveryCoordinate SemiprimeD1StackRecoveryCoordinateState
open SemiprimeD1StackProcedureTrace
/-- Actual trace composition retains every real saved return cell. -/
theorem join {m n:Nat} {pc mid next:Label} {before between after:Stack → List Bool}
    (h:Runs program m pc before mid between) (g:Runs program n mid between next after):
    Runs program (m+n) pc before next after:=runs_trans program m n pc mid next before between after h g
/-- Actual retained phase-bank copy, with all copy work and real call/return charged. -/
theorem copy_run (key:List Bool) (w:Role → List Bool):
    Runs program (5*(w .phases).length+4) (.local .start) (data key w) (.local .sentinel)
      (data key (Function.update w .reader (w .phases++w .reader))):=by
  rw [data_update]
  let before:=SemiprimeD1StackCopy.state 0 none (w .phases) (w .reader) []
  let after:=SemiprimeD1StackCopy.done (w .phases) (w .phases++w .reader)
  have hi:SemiprimeD1StackMultiplierLink.DataRel copyStack (data key w) before.store (data key w):=by
    constructor
    · intro k;fin_cases k <;> rfl
    · intro k _;rfl
  have ho:=SemiprimeD1StackMultiplierLink.data_update copyStack copy_injective (data key w) before.store (data key w) hi (1:Fin 3) (w .phases++w .reader)
  have he:Function.update before.store 1 (w .phases++w .reader)=after.store:=by funext k;fin_cases k <;> rfl
  rw [he] at ho
  exact included_call program copyStack Label.copy copy_injective SemiprimeD1StackCopy.code 0 (fun _=>rfl)
    (.local .start) (.local .sentinel) rfl (5*(w .phases).length+3) before after _ _ rfl rfl
    (SemiprimeD1StackCopy.copy_words _ _ none) hi ho
/-- One real external-word push, with no supplied result tape. -/
theorem push_run (pc next:Label) (k:Role) (bit:Bool) (key:List Bool) (w:Role → List Bool)
    (hp:program pc=.base (.push (address k) bit next)):
    Runs program 1 pc (data key w) next (data key (Function.update w k (bit::w k))):=by
  rw [data_update]
  exact one_base program pc next (.push (address k) bit next) _ _ hp rfl (by simp only [SemiprimeD1StackBytecode.execute,data_get])
/-- Actual pop reads a real source bit or EOF. -/
theorem pop_run (pc empty low high:Label) (k:Role) (key:List Bool) (w:Role → List Bool) (word:List Bool)
    (hp:program pc=.base (.pop (address k) empty low high)) (hw:w k=word):
    Runs program 1 pc (data key w) (SemiprimeD1StackBytecode.choose empty low high word.head?)
      (data key (Function.update w k word.tail)):=by
  rw [data_update]
  apply one_base program _ _ _ _ _ hp
  · simp only [SemiprimeD1StackBytecode.execute,data_get,hw]
  · simp only [SemiprimeD1StackBytecode.execute,data_get,hw]
/-- Every per-row parser/logger cleanup bit is physically consumed. -/
theorem drain_run (pc next:Label) (k:Role) (key:List Bool) (w:Role → List Bool) (word:List Bool)
    (hp:program pc=.base (.pop (address k) next pc pc)) (hw:w k=word):
    Runs program (word.length+1) pc (data key w) next (data key (Function.update w k [])):=by
  induction word generalizing w with
  | nil=>simpa only [List.length_nil,Nat.zero_add,List.head?_nil,List.tail_nil,SemiprimeD1StackBytecode.choose]
      using pop_run pc next pc pc k key w [] hp hw
  | cons bit word ih=>
    have h0:=pop_run pc next pc pc k key w (bit::word) hp hw
    have h1:=ih (Function.update w k word) (Function.update_self _ _ _)
    have h:=join (by cases bit <;> exact h0) h1
    simpa only [Function.update_idem,List.length_cons,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using h
end RiemannGaussian.SemiprimeD1StackRecoveryCoordinatePrimitives

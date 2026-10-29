/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackCachePhaseBankPrimitives
import RiemannGaussian.SemiprimeD1StackCachePhaseBankClearEncoding
/-! # Physical complete236-word cleanup between actual phase calls
Every allocated callee word is visited by a finite source label. Heap/counter
are skipped by real jumps; every other payload and final EOF pop is executed.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackCachePhaseBankCleanup
open SemiprimeD1StackCachePhaseBank SemiprimeD1StackCachePhaseBankState
open SemiprimeD1StackCachePhaseBankPrimitives SemiprimeD1StackCachePhaseBankClearEncoding
open SemiprimeD1StackProcedureTrace
/-- Proof-side position in the finite cleanup code; no unbounded position inhabits runtime sigma. -/
def labelAt (aborted:Bool) (n:Nat):Label:=
  if h:n<238 then .local (.clear aborted ⟨n,h⟩) else .local (if aborted then .abortAux 0 else .header)
/-- Literal finite next label agrees with the proof-side successor. -/
theorem next_eq (aborted:Bool) (i:Fin 238):nextClear aborted i=labelAt aborted (i.val+1):=rfl
/-- One actual skipped retained port or one full physical drain advances the exact bank prefix. -/
theorem step_run (aborted:Bool) (bank:P.Stack→List Bool) (w:Aux→List Bool) (i:Fin 238):
    Runs program (portTime bank (I.role i)) (labelAt aborted i.val) (data (through bank i.val) w)
      (labelAt aborted (i.val+1)) (data (through bank (i.val+1)) w):=by
  have hlabel:labelAt aborted i.val=.local (.clear aborted i):=by
    unfold labelAt
    rw [dite_eq_left i.isLt]
  rw [hlabel,←next_eq]
  cases hp:persistent (I.role i) with
  | true=>
    rw [through_skip bank i hp]
    simp only [portTime,hp,ite_true]
    exact jump_run (.clear aborted i) (nextClear aborted i) _ (by simp [program,hp])
  | false=>
    have h0:=drain_loop (.clear aborted i) (nextClear aborted i) (cached (I.role i))
      (by simp [program,hp]) (data (through bank i.val) w) (bank (I.role i)) (through_current bank i)
    rw [←data_update_cached,←through_clear bank i hp] at h0
    simpa only [portTime,hp,Bool.false_eq_true,ite_false] using h0
/-- Entire remaining real finite sweep, retaining every actual outer word and all real returns. -/
theorem remaining_run (aborted:Bool) (bank:P.Stack→List Bool) (w:Aux→List Bool)
    (remaining n:Nat) (hn:n+remaining=238):
    Runs program (sweepTime bank n) (labelAt aborted n) (data (through bank n) w)
      (labelAt aborted 238) (data (cleared bank) w):=by
  induction remaining generalizing n with
  | zero=>
    have he:n=238:=by omega
    subst n
    rw [sweepTime_all,through_all]
    exact runs_refl program _ _
  | succ remaining ih=>
    have hi:n<238:=by omega
    let i:Fin 238:=⟨n,hi⟩
    have h0:=step_run aborted bank w i
    have h1:=ih (n+1) (by omega)
    have h:=join h0 h1
    rw [sweepTime_step bank i]
    exact h
/-- Both normal/rejection paths physically sweep every236 nonpersistent callee word before proceeding. -/
theorem source_run (aborted:Bool) (bank:P.Stack→List Bool) (w:Aux→List Bool):
    Runs program (sweepTime bank 0) (.local (.clear aborted 0)) (data bank w)
      (.local (if aborted then .abortAux 0 else .header)) (data (cleared bank) w):=by
  have h:=remaining_run aborted bank w 238 0 rfl
  rw [through_zero] at h
  exact h
end RiemannGaussian.SemiprimeD1StackCachePhaseBankCleanup

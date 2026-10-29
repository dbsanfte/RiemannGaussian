/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackBinarySquareRootCalls
import RiemannGaussian.SemiprimeD1StackBinarySquareRootSweep
/-! # Actual borrow dispatch, candidate installation and full private cleanup -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackBinarySquareRootDecision
open SemiprimeD1StackBinarySquareRoot SemiprimeD1StackBinarySquareRootEncoding
open SemiprimeD1StackBinarySquareRootPrimitives SemiprimeD1StackBinarySquareRootCalls
open SemiprimeD1StackBinarySquareRootSweep SemiprimeD1StackProcedureTrace
/-- Consuming the actual borrow flag chooses the actual branch in one transition. -/
theorem branch_run (bits p r : List Bool) :
    Runs program 1 (ctl .decide) (tested bits p r)
      (if E.rejects bits r p then ctl (.clear 0) else ctl .clearRoot) (selected bits p r r) := by
  apply one_base program _ _ (.pop (SemiprimeD1StackBinarySquareRoot.compare W.output)
    (ctl (.clear 0)) (ctl .clearRoot) (ctl (.clear 0))) _ _ rfl
  · change some (SemiprimeD1StackBytecode.choose (ctl (.clear 0)) (ctl .clearRoot) (ctl (.clear 0))
      (some (E.rejects bits r p)))=some _
    cases h:E.rejects bits r p <;> rfl
  · change Function.update (tested bits p r) (SemiprimeD1StackBinarySquareRoot.compare W.output) []=selected bits p r r
    rw [tested,bank_compare]
    have h : Function.update (W.store [] [] [] [] [E.rejects bits r p]) W.output []=(fun _ => []) := by
      funext k
      rcases k with k|k
      · cases k <;> rfl
      · cases k;rfl
    rw [h]
    rfl
/-- Acceptance physically clears the old raw root before copying the candidate. -/
theorem clear_root (bits p r : List Bool) :
    Runs program (r.length+1) (ctl .clearRoot) (selected bits p r r)
      (ctl .acceptCopy) (selected bits p r []) := by
  have h:=SemiprimeD1StackPhysicalLoops.drain program (ctl .clearRoot) (ctl .acceptCopy) (aux .root) rfl
    (selected bits p r r) r
  have he : Function.update (selected bits p r r) (aux .root) r=selected bits p r r := Function.update_eq_self _ _
  rw [he] at h
  have ho : Function.update (selected bits p r r) (aux .root) []=selected bits p r [] := by
    rw [selected,bank_aux,words_update]
    rfl
  rw [ho] at h
  exact h
/-- The actual trial word is copied only on the accepting path. -/
theorem accept_copy (bits p r : List Bool) :
    Runs program (5*(E.trial r p).length+4) (ctl .acceptCopy) (selected bits p r [])
      (ctl (.clear 0)) (selected bits p r (E.trial r p)) := by
  have h:=copy_call .accepted (ctl .acceptCopy) (ctl (.clear 0)) rfl (selected bits p r [])
    (E.trial r p) [] rfl rfl rfl
  change Runs program _ _ _ _ (Function.update _ (aux .root) (_++[])) at h
  rw [List.append_nil,selected,bank_aux,words_update] at h
  exact h
/-- Exact branch-dependent clock includes the actual pop and any erasure/copy. -/
def decisionTime (bits p r : List Bool) : ℕ :=
  if E.rejects bits r p then 1 else 1+(r.length+1)+(5*(E.trial r p).length+4)
/-- Both actual branches install exactly the raw root prescribed by comparison. -/
theorem decision_run (bits p r : List Bool) :
    Runs program (decisionTime bits p r) (ctl .decide) (tested bits p r)
      (ctl (.clear 0)) (selected bits p r (E.nextWord bits r p)) := by
  have h:=branch_run bits p r
  cases hr:E.rejects bits r p
  · simp only [hr,Bool.false_eq_true,ite_false] at h
    simpa only [decisionTime,E.nextWord,hr,Bool.false_eq_true,ite_false] using
      join (join h (clear_root bits p r)) (accept_copy bits p r)
  · simpa only [decisionTime,E.nextWord,hr,ite_true] using h
/-- Exact clock for one real greedy-bit iteration through the full18-word sweep. -/
def iterationTime (bits p r : List Bool) : ℕ :=
  testTime bits p r+decisionTime bits p r+sweepTime (selected bits p r (E.nextWord bits r p)) 18
/-- Entire actual bit test leaves a clean33-role boundary before shifting power. -/
theorem iteration_run (bits p r : List Bool) :
    Runs program (iterationTime bits p r) (ctl .rootCopy) (idle bits p r)
      (ctl .shift) (idle bits p (E.nextWord bits r p)) := by
  have h0:=test_call bits p r
  have h1:=decision_run bits p r
  have h2:=sweep_run (selected bits p r (E.nextWord bits r p)) 18 (by omega)
  rw [show sweepLabel 18=ctl .shift from rfl] at h2
  dsimp only [selected] at h2
  rw [swept_bank] at h2
  exact join (join h0 h1) h2
end RiemannGaussian.SemiprimeD1StackBinarySquareRootDecision

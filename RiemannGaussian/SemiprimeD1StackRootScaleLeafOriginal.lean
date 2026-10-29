/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootScaleLeafBounds
/-! # Exact original s, integer sqrt(lambda), and leafSize from only binary N
Both the complete N-only entry and the acquired-cache ready entry execute the
same literal scale/root/division source. No input schedule parameter, scale,
root, leaf threshold, quotient or arithmetic clock is supplied.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeD1StackRootScaleLeafOriginal
open SemiprimeD1StackRootScaleLeaf SemiprimeD1StackRootScaleLeafComponents
open SemiprimeD1StackRootScaleLeafExecution SemiprimeD1StackRootScaleLeafArithmetic
open SemiprimeMacroParameters SemiprimeBitArithmetic
namespace Old
export SemiprimeD1StackRootScheduleOriginal (originalLambda width_original lambda_eq)
end Old
/-- ENTIRE acquired15-role cache is retained, including every old work/shadow field. -/
theorem retained_cache (bits : List Bool) (j : R.Stack) :
    result bits (rootStack j)=SemiprimeD1StackRootScheduleExecution.result bits j :=rfl
/-- Original N is retained as the identical binary input word. -/
theorem input_preserved (bits : List Bool) :result bits (rootStack (R.boot .input))=bits :=rfl
/-- The actual twenty-round scale is the SAME original s=2^20*ell. -/
theorem scale_original_word (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) :
    result bits (aux .scale)=D.unary (SemiprimeD1PublicPackingReady.scale (bitLength (bitValue bits))) :=by
  change D.unary (scale bits.length)=_
  rw [scale_original,Old.width_original bits hc]
/-- The physical odd-subtraction counter is the EXACT floor integer sqrt of
original lambda, not the older radix approximation or an unexecuted Nat.sqrt. -/
theorem root_original_word (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) :
    result bits (aux .root)=D.unary (Nat.sqrt (Old.originalLambda (bitValue bits))) :=by
  change D.unary (root bits.length)=_
  unfold root
  rw [Old.lambda_eq bits hc]
/-- The original literal leaf threshold is present in the actual output role. -/
theorem leaf_original_word (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) :
    result bits (aux .leaf)=D.unary (SemiprimeD1Schedule.leafSize
      (SemiprimeD1PublicPackingReady.scale (bitLength (bitValue bits))) (Old.originalLambda (bitValue bits))) :=by
  change D.unary (leaf bits.length)=_
  rw [leaf_original,Old.lambda_eq bits hc,Old.width_original bits hc]
/-- The actual positive divider is retained as paid metadata; all other fresh
divider/input/copy/remainder/quotient words are physically empty. -/
theorem divider_work (bits : List Bool) :
    result bits (divStack .input)=[] ∧ result bits (divStack .copied)=[] ∧
    result bits (divStack .scratch)=[] ∧ result bits (divStack .quotient)=[] ∧
    result bits (divStack .remainder)=[] ∧ result bits (aux .scratch)=[] ∧
    result bits (divStack .divisor)=D.unary (root bits.length+1) :=by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
/-- Whole N-only source and exact original s/root/leaf hold together on the
actual same fixed program, with no prepared acquired-cache assumption. -/
theorem source_run_original (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) :
    ∃t≤10000000000000*(bitLength (bitValue bits)+1)^3,∃finish,
      SemiprimeD1StackCalls.run program t (initial bits)=some finish ∧ finish=done bits ∧
      finish.data (rootStack (R.boot .input))=bits ∧
      finish.data (aux .scale)=D.unary (SemiprimeD1PublicPackingReady.scale (bitLength (bitValue bits))) ∧
      finish.data (aux .root)=D.unary (Nat.sqrt (Old.originalLambda (bitValue bits))) ∧
      finish.data (aux .leaf)=D.unary (SemiprimeD1Schedule.leafSize
        (SemiprimeD1PublicPackingReady.scale (bitLength (bitValue bits))) (Old.originalLambda (bitValue bits))) ∧
      ∀j:R.Stack,finish.data (rootStack j)=SemiprimeD1StackRootScheduleExecution.result bits j :=by
  obtain ⟨t,ht,hr⟩:=source_run bits
  rw [runBound,Old.width_original bits hc] at ht
  exact ⟨t,ht,done bits,hr,rfl,input_preserved bits,scale_original_word bits hc,
    root_original_word bits hc,leaf_original_word bits hc,retained_cache bits⟩
/-- READY source continuation retains every actually acquired old cache cell;
it does not repeat the original-N/root metadata procedure. -/
theorem ready_run_original (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) :
    ∃t≤1000000000000*(bitLength (bitValue bits)+1)^3,∃finish,
      SemiprimeD1StackCalls.run program t (ready bits)=some finish ∧ finish=done bits ∧
      finish.data (aux .leaf)=D.unary (SemiprimeD1Schedule.leafSize
        (SemiprimeD1PublicPackingReady.scale (bitLength (bitValue bits))) (Old.originalLambda (bitValue bits))) ∧
      ∀j:R.Stack,finish.data (rootStack j)=SemiprimeD1StackRootScheduleExecution.result bits j :=by
  obtain ⟨t,ht,hr⟩:=ready_run bits
  rw [readyBound,Old.width_original bits hc] at ht
  exact ⟨t,ht,done bits,hr,rfl,leaf_original_word bits hc,retained_cache bits⟩
/-- Genuine one-input finite-machine cubic certificate in original bitlength. -/
noncomputable def originalInTime (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) :
    StateTransition.EvalsToInTime machine.step (Turing.initList machine bits)
      (some (SemiprimeD1StackCalls.configuration (done bits)))
      (10000000000000*(bitLength (bitValue bits)+1)^3) :=by
  let h:=acquireInTime bits
  simpa only [runBound,Old.width_original bits hc] using h
/-- The same actual ready-machine execution has its OWN smaller cubic clock. -/
noncomputable def readyOriginalInTime (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) :
    StateTransition.EvalsToInTime machine.step (SemiprimeD1StackCalls.configuration (ready bits))
      (some (SemiprimeD1StackCalls.configuration (done bits)))
      (1000000000000*(bitLength (bitValue bits)+1)^3) :=by
  let h:=readyInTime bits
  simpa only [readyBound,Old.width_original bits hc] using h
/-- Every whole-source physical prefix counts ALL25 roles and all real frames. -/
theorem original_prefix_cells (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (fuel : Nat) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel] (some (Turing.initList machine bits))=some cfg) :
    (∑j:Stack,(cfg.stk (some j)).length)+(cfg.stk none).length≤1000000000000000*(bitLength (bitValue bits)+1)^3 :=by
  have h:=(SemiprimeD1StackRootScaleLeafBounds.machine_prefix_cells bits fuel cfg hr).trans
    (SemiprimeD1StackRootScaleLeafBounds.polynomial_space bits)
  simpa only [Old.width_original bits hc] using h
/-- Same full inventory for the actual cached ready entry, with no old field omitted. -/
theorem ready_original_prefix_cells (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (fuel : Nat) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (ready bits)))=some cfg) :
    (∑j:Stack,(cfg.stk (some j)).length)+(cfg.stk none).length≤1000000000000000*(bitLength (bitValue bits)+1)^3 :=by
  have h:=(SemiprimeD1StackRootScaleLeafBounds.ready_machine_prefix_cells bits fuel cfg hr).trans
    (SemiprimeD1StackRootScaleLeafBounds.ready_polynomial_space bits)
  simpa only [Old.width_original bits hc] using h
end RiemannGaussian.SemiprimeD1StackRootScaleLeafOriginal

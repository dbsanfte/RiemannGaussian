/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootScheduleBounds
/-! # Exact original root schedule metadata from canonical binary N
This is an actual N-only source for lambda, root levels/exponent and the
minimum-level guard. Materialized scale s and the square-root leaf threshold
remain separate, precisely stated acquisition obligations.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeD1StackRootScheduleOriginal
open SemiprimeD1StackRootSchedule SemiprimeD1StackRootScheduleExecution
open SemiprimeD1StackRootScheduleStages SemiprimeD1StackRootScheduleArithmetic
open SemiprimeMacroParameters SemiprimeBitArithmetic
/-- The SAME original root logarithm, a specification only, never a runtime supplier. -/
def originalLambda (N : Nat) : Nat :=Nat.clog 2 (SemiprimeD1PublicPackingReady.scale (bitLength N)+2)
/-- Physical WIDTH equals the original canonical input bitlength, including zero. -/
theorem width_original (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) :
    bits.length=bitLength (bitValue bits) :=SemiprimeD1BinaryBootstrap.canonical_width bits hc
/-- Exact comparison of the acquired real size-loop result with original clog2. -/
theorem lambda_eq (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) :
    lambda bits.length=originalLambda (bitValue bits) :=by
  rw [lambda_original,width_original bits hc]
  rfl
/-- Original N remains a binary word, byte for byte, throughout acquisition. -/
theorem input_preserved (bits : List Bool) : result bits (boot .input)=bits :=rfl
/-- Exact actual original logarithm markers. -/
theorem lambda_original_word (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) :
    result bits (aux .lambda)=D.unary (originalLambda (bitValue bits)) :=by
  change D.unary (lambda bits.length)=_
  exact congrArg D.unary (lambda_eq bits hc)
/-- Exact original root valuation count, in actual retained physical cells. -/
theorem levels_original_word (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) :
    result bits (aux .levels)=D.unary (SemiprimeD1Schedule.levels (originalLambda (bitValue bits)) 0) :=by
  change D.unary (levels bits.length)=_
  exact congrArg D.unary ((levels_original bits.length).trans
    (congrArg (fun l=>SemiprimeD1Schedule.levels l 0) (lambda_eq bits hc)))
/-- Exact original root packet exponent, physically acquired by two paid copies. -/
theorem exponent_original_word (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) :
    result bits (aux .exponent)=D.unary (SemiprimeD1Schedule.exponent (originalLambda (bitValue bits)) 0) :=by
  change D.unary (exponent bits.length)=_
  exact congrArg D.unary ((exponent_original bits.length).trans
    (congrArg (fun l=>SemiprimeD1Schedule.exponent l 0) (lambda_eq bits hc)))
/-- Exact original minimum-level guard; every log/division/write was executed. -/
theorem minimum_original_word (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) :
    result bits (aux .minimum)=D.unary (SemiprimeD1PrecisionEnvelope.minimumLevels (originalLambda (bitValue bits))) :=by
  change D.unary (minimum bits.length)=_
  exact congrArg D.unary ((minimum_original bits.length).trans
    (congrArg SemiprimeD1PrecisionEnvelope.minimumLevels (lambda_eq bits hc)))
/-- Actual original bit-width remains available for the rest of the controller. -/
theorem retained_width (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) :
    result bits (boot .width)=D.unary (bitLength (bitValue bits)) :=by
  change D.unary bits.length=_
  exact congrArg D.unary (width_original bits hc)
/-- The physically acquired original nonzero flag is retained too. -/
theorem retained_nonzero (bits : List Bool) : result bits (boot .nonzero)=[Boot.seenOne bits] :=rfl
/-- All actual divider work is empty; only its physically seeded two-marker divisor remains. -/
theorem divider_work_empty (bits : List Bool) (k : D.Stack) (hk : k≠.divisor) :
    result bits (divStack k)=[] :=by
  cases k with
  | divisor=>exact (hk rfl).elim
  | input=>rfl
  | copied=>rfl
  | scratch=>rfl
  | quotient=>rfl
  | remainder=>rfl
/-- The real copy-restoration and original-word reversal work is also empty. -/
theorem scratch_empty (bits : List Bool) :
    result bits (aux .scratch)=[] ∧ result bits (boot .reverse)=[] :=⟨rfl,rfl⟩
/-- One actual N-only machine has its own fixed cubic original-bitlength clock. -/
noncomputable def originalInTime (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) :
    StateTransition.EvalsToInTime machine.step (Turing.initList machine bits)
      (some (SemiprimeD1StackCalls.configuration (done bits)))
      (100000000*(bitLength (bitValue bits)+1)^3) :=by
  let h:=acquireInTime bits
  simpa only [runBound,width_original bits hc] using h
/-- The source execution and all four exact original schedule values hold together. -/
theorem source_run_original (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) :
    ∃t≤100000000*(bitLength (bitValue bits)+1)^3,∃finish,
      SemiprimeD1StackCalls.run program t (initial bits)=some finish ∧ finish=done bits ∧
      finish.data (boot .input)=bits ∧
      finish.data (aux .lambda)=D.unary (originalLambda (bitValue bits)) ∧
      finish.data (aux .levels)=D.unary (SemiprimeD1Schedule.levels (originalLambda (bitValue bits)) 0) ∧
      finish.data (aux .exponent)=D.unary (SemiprimeD1Schedule.exponent (originalLambda (bitValue bits)) 0) ∧
      finish.data (aux .minimum)=D.unary (SemiprimeD1PrecisionEnvelope.minimumLevels (originalLambda (bitValue bits))) :=by
  obtain ⟨t,ht,hr⟩:=source_run bits
  rw [runBound,width_original bits hc] at ht
  exact ⟨t,ht,done bits,hr,rfl,input_preserved bits,lambda_original_word bits hc,
    levels_original_word bits hc,exponent_original_word bits hc,minimum_original_word bits hc⟩
/-- Every actual one-input prefix counts all15 Boolean roles and real return cells. -/
theorem original_prefix_cells (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (fuel : Nat) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel] (some (Turing.initList machine bits))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤
      2000000000*(bitLength (bitValue bits)+1)^3 :=by
  have h:=(SemiprimeD1StackRootScheduleBounds.machine_prefix_cells bits fuel cfg hr).trans
    (SemiprimeD1StackRootScheduleBounds.polynomial_space bits)
  simpa only [width_original bits hc] using h
end RiemannGaussian.SemiprimeD1StackRootScheduleOriginal

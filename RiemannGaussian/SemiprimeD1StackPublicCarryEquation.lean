/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicCarryGuards
/-! # Actual four-field record assembly and whole INTEGER carry call
The record is built by four real Frame procedures from the acquired operands
and target. No prepared record or integer-equation verdict is an input.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 4096
namespace RiemannGaussian.SemiprimeD1StackPublicCarryEquation
open SemiprimeD1StackPublicCarry SemiprimeD1StackPublicCarryState SemiprimeD1StackPublicCarryPrimitives
open SemiprimeD1StackProcedureTrace
/-- Exact physical four-field byte order, specified after actual framing. -/
def record (context : T.Stack→List Bool) (raw : List Bool) : List Bool :=
  SemiprimeD1StackCarryEquation.record (coefficient context raw) (previous context raw) (target context) (next context raw) []
/-- Actual record phase; all original operand caches are still retained here. -/
def framed (context : T.Stack→List Bool) (raw : List Bool) : Payload := set (ready context raw) .vector (record context raw)
/-- The real operand drains leave fresh parser destinations for the whole carry call. -/
def cleared (context : T.Stack→List Bool) (raw : List Bool) : Payload :=
  set (set (set (framed context raw) .coefficient []) .previous []) .next []
/-- Complete actual frame-call count, including preserving every input cache. -/
def framesBudget (context : T.Stack→List Bool) (raw : List Bool) : ℕ :=
  (6*(next context raw).length+5)+(6*(target context).length+5)+
    (6*(previous context raw).length+5)+(6*(coefficient context raw).length+5)
/-- Four actual Frame calls construct coefficient/previous/target/next order by
prepending in reverse. The target is the ACTUALLY ACQUIRED public target word. -/
theorem frames_run (context : T.Stack→List Bool) (raw : List Bool) :
    Runs program (framesBudget context raw) (.frame 3) (view context (ready context raw))
      (.clear true 0) (view context (framed context raw)) := by
  let p:=ready context raw
  let p1:=set p .vector (SemiprimeSourceHistogramKeyBits.frame (next context raw) [])
  let p2:=set p1 .vector (SemiprimeSourceHistogramKeyBits.frame (target context) p1.vector)
  let p3:=set p2 .vector (SemiprimeSourceHistogramKeyBits.frame (previous context raw) p2.vector)
  have h0 : Runs program (6*(next context raw).length+5) (.frame 3) (view context p) (.frame 2) (view context p1) :=
    frame_call 3 context p rfl
  have h1 : Runs program (6*(target context).length+5) (.frame 2) (view context p1) (.frame 1) (view context p2) :=
    frame_call 2 context p1 rfl
  have h2 : Runs program (6*(previous context raw).length+5) (.frame 1) (view context p2) (.frame 0) (view context p3) :=
    frame_call 1 context p2 rfl
  have h3 : Runs program (6*(coefficient context raw).length+5) (.frame 0) (view context p3) (.clear true 0)
      (view context (framed context raw)) := frame_call 0 context p3 rfl
  exact runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ h0 h1) h2) h3
/-- Exact physical integer-equation procedure count, no native clock transport. -/
def equationBudget (context : T.Stack→List Bool) (raw : List Bool) : ℕ :=
  SemiprimeD1StackCarryEquationExecution.totalTime (radix context) (coefficient context raw) (previous context raw)
    (target context) (next context raw)+1
/-- The WHOLE actual integer carry procedure consumes the just-built physical
record and actual radix cache, producing only its actually computed Boolean. -/
theorem equation_run (context : T.Stack→List Bool) (raw : List Bool) :
    Runs program (equationBudget context raw) .equation (view context (cleared context raw)) .done
      (view context (clean context raw (equationAnswer context raw))) := by
  apply SemiprimeD1StackProcedureCallsTrace.included_call program carryStack Label.carry carry_injective
    Q.program (.read 0) (fun _=>rfl) .equation .done rfl
    (SemiprimeD1StackCarryEquationExecution.totalTime (radix context) (coefficient context raw)
      (previous context raw) (target context) (next context raw))
    (Q.initial (record context raw) (radix context))
    (SemiprimeD1StackCarryEquationExecution.done (radix context) (coefficient context raw) (previous context raw)
      (target context) (next context raw) []) _ _ rfl rfl rfl rfl
    (SemiprimeD1StackCarryEquationExecution.source_run (radix context) (coefficient context raw)
      (previous context raw) (target context) (next context raw) [])
  · constructor
    · intro k;cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k;cases k <;> rfl
    · intro k hk;rcases k with k|k
      · rfl
      · cases k <;> first | rfl | exact (hk .input rfl).elim | exact (hk .output rfl).elim
/-- Both actual branches pay the original operand-cache drains. -/
def clearBudget (context : T.Stack→List Bool) (raw : List Bool) : ℕ :=
  (coefficient context raw).length+(previous context raw).length+(next context raw).length+3
/-- Complete real success body: actual four frames, drains, then INTEGER procedure. -/
theorem success_run (context : T.Stack→List Bool) (raw : List Bool) :
    Runs program (framesBudget context raw+clearBudget context raw+equationBudget context raw)
      (.frame 3) (view context (ready context raw)) .done (view context (clean context raw (equationAnswer context raw))) := by
  have h0:=frames_run context raw
  have h1 : Runs program (clearBudget context raw) (.clear true 0) (view context (framed context raw)) .equation
      (view context (cleared context raw)) := clear_words true context (framed context raw)
  exact runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ h0 h1) (equation_run context raw)
/-- Actual rejected branch physically writes false, then clears all three words. -/
theorem reject_run (context : T.Stack→List Bool) (raw : List Bool) :
    Runs program (1+clearBudget context raw) .reject (view context (ready context raw)) .done
      (view context (clean context raw false)) := by
  have h0:=push_aux .reject (.clear false 0) .output false rfl context (ready context raw)
  have h1 : Runs program (clearBudget context raw) (.clear false 0)
      (view context (set (ready context raw) .output [false])) .done (view context (clean context raw false)) :=
    clear_words false context (set (ready context raw) .output [false])
  exact runs_trans program _ _ _ _ _ _ _ _ h0 h1
end RiemannGaussian.SemiprimeD1StackPublicCarryEquation

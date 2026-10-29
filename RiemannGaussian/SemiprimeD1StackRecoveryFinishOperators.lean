/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryFinishProjection
/-! # Actual existing scalar operators and raw floor increment inside recovery
Every lemma uses the real fixed source trace and real call/return. Its clock
is the executed operator clock, never an old native arithmetic report.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackRecoveryFinishOperators
open SemiprimeD1StackRecoveryFinish SemiprimeD1StackRecoveryFinishState
open SemiprimeD1StackRecoveryFinishProjection SemiprimeD1StackProcedureTrace
namespace ME
export SemiprimeD1StackJetScalarMulExecution (totalTime result)
end ME
namespace AE
export SemiprimeD1StackJetScalarAddExecution (totalTime result)
end AE
/-- Exact actual modular-product call clock, including its actual outer invocation. -/
def multiplyTime (v:Values):Nat:=ME.totalTime (v .mulLeft) (v .mulRight) (v .width)+1
/-- Exact literal canonical output of the real modular-product source. -/
def multiplyWord (v:Values):List Bool:=ME.result (v .mulLeft) (v .mulRight) (v .width)
/-- Actual modular multiplication consumes both operands and clears every private work role. -/
theorem multiply_call (pc next:Label) (v:Values)
    (hc:program pc=.call (.multiply .start) next)
    (hw:v .reduceWidth=[]) (hi:v .reduceInput=[]) (ho:v .output=[]):
    Runs program (multiplyTime v) pc (data v) next (data (multiplied v (multiplyWord v))):=by
  apply SemiprimeD1StackProcedureCallsTrace.included_call program main Label.multiply Sum.inl_injective
    M.program .start (fun _=>rfl) pc next hc
    (ME.totalTime (v .mulLeft) (v .mulRight) (v .width))
    (SemiprimeD1StackJetScalarMul.state (some .start) none none (v .mulLeft) (v .mulRight) [] [] [] [] [] [] [] (v .width) [])
    (SemiprimeD1StackJetScalarMul.state none none none [] [] [] [] [] [] (multiplyWord v) [] [] (v .width) [])
    _ _ rfl rfl rfl rfl (SemiprimeD1StackJetScalarMulExecution.source_run _ _ _)
  · constructor
    · intro k
      rw [data_main]
      simp only [hw,hi,ho]
      rfl
    · intro k _;rfl
  · constructor
    · intro k
      rw [data_main]
      simp [multiplied,hw,hi]
      rfl
    · intro k hk
      exact multiplied_other v (multiplyWord v) k hk
/-- Exact actual modular-adder call clock, including its outer invocation. -/
def addTime (v:Values):Nat:=AE.totalTime (v .addLeft) (v .addRight) (v .width)+1
/-- Exact literal compact output of the real modular-adder source. -/
def addWord (v:Values):List Bool:=AE.result (v .addLeft) (v .addRight) (v .width)
/-- Actual modular addition shares and preserves the physically supplied WIDTH. -/
theorem add_call (pc next:Label) (v:Values)
    (hc:program pc=.call (.add .start) next) (ho:v .addOutput=[]):
    Runs program (addTime v) pc (data v) next (data (added v (addWord v))):=by
  apply SemiprimeD1StackProcedureCallsTrace.included_call program addStack Label.add add_injective
    A.program .start (fun _=>rfl) pc next hc
    (AE.totalTime (v .addLeft) (v .addRight) (v .width))
    (SemiprimeD1StackJetScalarAdd.state (some .start) none none (v .addLeft) (v .addRight) [] [] (v .width) [])
    (SemiprimeD1StackJetScalarAdd.state none none none [] [] [] (addWord v) (v .width) [])
    _ _ rfl rfl rfl rfl (SemiprimeD1StackJetScalarAddExecution.source_run _ _ _)
  · constructor
    · intro k
      rw [data_add,ho]
      rfl
    · intro k _;rfl
  · constructor
    · intro k
      rw [data_add]
      simp [added]
      rfl
    · intro k hk
      exact added_other v (addWord v) k hk
/-- Exact raw increment/sum word, with no precision reduction before floor rounding. -/
def rawWord (v:Values):List Bool:=(SemiprimeBitArithmetic.addBits (v .addLeft) (v .addRight) false).bits
/-- Actual raw-adder source clock plus the actual caller invocation. -/
def rawTime (v:Values):Nat:=3*(max (v .addLeft).length (v .addRight).length+1)+2*(rawWord v).length+3
/-- Actual raw binary addition supplies the full negative-floor magnitude increment. -/
theorem raw_call (pc next:Label) (v:Values)
    (hc:program pc=.call (.rawAdd (.start false)) next) (ho:v .addOutput=[]):
    Runs program (rawTime v) pc (data v) next (data (added v (rawWord v))):=by
  apply included_call program rawStack Label.rawAdd raw_injective Raw.code (.start false)
    (fun _=>rfl) pc next hc (3*(max (v .addLeft).length (v .addRight).length+1)+2*(rawWord v).length+2)
    (SemiprimeD1StackAdder.state (some (.start false)) none (v .addLeft) (v .addRight) [] [])
    (SemiprimeD1StackAdder.state none none [] [] [] (rawWord v)) _ _ rfl rfl
    (SemiprimeD1StackAdderExecution.source_run _ _ false)
  · constructor
    · intro k
      rw [data_raw,ho]
      rfl
    · intro k _;rfl
  · constructor
    · intro k
      rw [data_raw]
      simp [added]
      rfl
    · intro k hk
      exact raw_other v (rawWord v) k hk
/-- Exact canonical output of the direct physical reducer. -/
def reduceWord (v:Values):List Bool:=
  (SemiprimeD1JetScalarBits.reduce (v .reduceWidth).length (v .reduceInput)).bits
/-- Actual reducer prefix/trim source clock plus its actual caller invocation. -/
def reduceTime (v:Values):Nat:=
  SemiprimeD1StackReduceExecution.trimTime ((v .reduceInput).take (v .reduceWidth).length).reverse+
    SemiprimeD1StackReduceExecution.prefixTime (v .reduceInput) (v .reduceWidth)+1
/-- Actual direct reduction consumes its physical input/counter and clears all reducer work. -/
theorem reduce_call (pc next:Label) (v:Values)
    (hc:program pc=.call (.reduce .take) next) (ho:v .output=[]):
    Runs program (reduceTime v) pc (data v) next (data (reduced v (reduceWord v))):=by
  apply included_call program reduceStack Label.reduce reduce_injective R.code .take (fun _=>rfl) pc next hc
    (SemiprimeD1StackReduceExecution.trimTime ((v .reduceInput).take (v .reduceWidth).length).reverse+
      SemiprimeD1StackReduceExecution.prefixTime (v .reduceInput) (v .reduceWidth))
    (SemiprimeD1StackReduce.state (some .take) none (v .reduceInput) (v .reduceWidth) [] [])
    (SemiprimeD1StackReduce.state none none [] [] [] (reduceWord v)) _ _ rfl rfl
    (SemiprimeD1StackReduceExecution.source_run _ _)
  · constructor
    · intro k
      rw [data_reduce,ho]
      rfl
    · intro k _;rfl
  · constructor
    · intro k
      rw [data_reduce]
      simp [reduced]
      rfl
    · intro k hk
      exact reduced_other v (reduceWord v) k hk
end RiemannGaussian.SemiprimeD1StackRecoveryFinishOperators

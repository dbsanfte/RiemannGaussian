/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicTransformWords
/-! # Computed physical input/output canonicality guards
Both guards execute on ACTUAL produced vectors, with actual short-circuit
rejection. No canonicality/truth/word-vector answer is an endpoint premise.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackPublicTransformGuards
open SemiprimeD1StackPublicTransform SemiprimeD1StackPublicTransformState SemiprimeD1StackPublicTransformWords
open SemiprimeD1StackPublicTransformPrimitives SemiprimeD1StackProcedureTrace
open SemiprimeD1TensorTapeCodec (vectorBits)
/-- Input canonicality answer of the actually acquired first vector. -/
def inputFlag (root : R.Stack→List Bool) (raw : List Bool) (second : Bool) : Bool :=
  SemiprimeD1StackVectorCanonicalExecution.answer (modulusWord root) (inputs root raw second)
/-- Output canonicality answer of the actually acquired second vector. -/
def outputFlag (root : R.Stack→List Bool) (raw : List Bool) (second : Bool) : Bool :=
  SemiprimeD1StackVectorCanonicalExecution.answer (modulusWord root) (outputs root raw second)
/-- Actual first encoded-vector copy into the retained dot input cache. -/
def dotCached (root : R.Stack→List Bool) (raw : List Bool) (second inverse : Bool) : Parts :=
  copied (bothAcquired root raw second inverse) (.vector false 0)
/-- Actual input-vector copy into the real canonicality checker. -/
def inputReady (root : R.Stack→List Bool) (raw : List Bool) (second inverse : Bool) : Parts :=
  copied (dotCached root raw second inverse) (.vector false 1)
/-- Actual completed input guard; the returned bit is still physically present. -/
def inputChecked (root : R.Stack→List Bool) (raw : List Bool) (second inverse : Bool) : Parts :=
  {inputReady root raw second inverse with checker:=
    (SemiprimeD1StackVectorCanonicalExecution.done (inputs root raw second) (modulusWord root)).data}
/-- The actual input guard bit has been popped to select control. -/
def inputPopped (root : R.Stack→List Bool) (raw : List Bool) (second inverse : Bool) : Parts :=
  set (inputChecked root raw second inverse) (.guard .output) []
/-- Every byte of old checker input cache is physically drained before reuse. -/
def inputCleared (root : R.Stack→List Bool) (raw : List Bool) (second inverse : Bool) : Parts :=
  set (inputPopped root raw second inverse) (.guard .cache) []
/-- The actual output vector is copied into the now-empty checker cache. -/
def outputReady (root : R.Stack→List Bool) (raw : List Bool) (second inverse : Bool) : Parts :=
  copied (inputCleared root raw second inverse) (.vector true 1)
/-- Completed actual output guard, with its physical Boolean result present. -/
def outputChecked (root : R.Stack→List Bool) (raw : List Bool) (second inverse : Bool) : Parts :=
  {outputReady root raw second inverse with checker:=
    (SemiprimeD1StackVectorCanonicalExecution.done (outputs root raw second) (modulusWord root)).data}
/-- The output guard's ACTUAL bit is popped before the loop is permitted. -/
def outputPopped (root : R.Stack→List Bool) (raw : List Bool) (second inverse : Bool) : Parts :=
  set (outputChecked root raw second inverse) (.guard .output) []
/-- Actual output-vector copy into the retained physical reader cache. -/
def outputCached (root : R.Stack→List Bool) (raw : List Bool) (second inverse : Bool) : Parts :=
  copied (outputPopped root raw second inverse) (.vector true 2)
/-- Actual loop count is copied from the acquired dot count-marker cache. -/
def loopReady (root : R.Stack→List Bool) (raw : List Bool) (second inverse : Bool) : Parts :=
  copied (outputCached root raw second inverse) .remaining
/-- BOTH originally produced vectors are paid actual copies, not a native cache. -/
theorem dot_copy (root : R.Stack→List Bool) (raw : List Bool) (second inverse : Bool) :
    Runs program (5*(vectorBits (inputs root raw second)).length+4) .copyInputDot
      (data (bothAcquired root raw second inverse)) .copyGuardInput (data (dotCached root raw second inverse)) :=
  copy_run (.vector false 0) .copyInputDot .copyGuardInput rfl (bothAcquired root raw second inverse) rfl rfl
/-- Real input-guard cache copy. -/
theorem input_copy (root : R.Stack→List Bool) (raw : List Bool) (second inverse : Bool) :
    Runs program (5*(vectorBits (inputs root raw second)).length+4) .copyGuardInput
      (data (dotCached root raw second inverse)) .guardInput (data (inputReady root raw second inverse)) :=
  copy_run (.vector false 1) .copyGuardInput .guardInput rfl (dotCached root raw second inverse) rfl rfl
/-- The real input guard receives the actual producer bytes and acquired M. -/
theorem input_initial (root : R.Stack→List Bool) (raw : List Bool) (second inverse : Bool) :
    (inputReady root raw second inverse).checker=(V.initial (vectorBits (inputs root raw second)) (modulusWord root)).data := by
  funext k;cases k <;> rfl
/-- WHOLE real input guard, including every actually visited field/read/comparison. -/
theorem input_call (root : R.Stack→List Bool) (raw : List Bool) (second inverse : Bool) :
    ∃t≤SemiprimeD1StackVectorCanonicalExecution.timeBound (inputs root raw second) (modulusWord root)+1,
      Runs program t .guardInput (data (inputReady root raw second inverse)) .branchInput
        (data (inputChecked root raw second inverse)) := by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackVectorCanonicalExecution.source_run (inputs root raw second) (modulusWord root)
  refine ⟨t+1,Nat.add_le_add_right ht 1,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program Stack.guard Label.check
    (by intro i j h;exact Stack.guard.inj h) V.program .start (fun _=>rfl) .guardInput .branchInput rfl t
    (V.initial (vectorBits (inputs root raw second)) (modulusWord root))
    (SemiprimeD1StackVectorCanonicalExecution.done (inputs root raw second) (modulusWord root)) _ _ rfl rfl rfl rfl hr
  · constructor
    · intro k;exact congrFun (input_initial root raw second inverse) k
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk;cases k <;> first | rfl | exact (hk _ rfl).elim
/-- Actual input verdict controls reject/continue, without a truth premise. -/
theorem input_branch (root : R.Stack→List Bool) (raw : List Bool) (second inverse : Bool) :
    Runs program 1 .branchInput (data (inputChecked root raw second inverse))
      (if inputFlag root raw second then .clearGuard else .reject) (data (inputPopped root raw second inverse)) := by
  have h:=pop .branchInput .bad .reject .clearGuard (.guard .output) rfl (data (inputChecked root raw second inverse))
  have hv : data (inputChecked root raw second inverse) (.guard .output)=[inputFlag root raw second] := rfl
  rw [hv,←data_set] at h
  cases he : inputFlag root raw second <;> simpa only [inputPopped,he,List.head?_cons,List.tail_cons,SemiprimeD1StackBytecode.choose,Bool.false_eq_true,ite_true,ite_false] using h
/-- The entire earlier cache is REALLY popped before the output cache is copied. -/
theorem clear_input (root : R.Stack→List Bool) (raw : List Bool) (second inverse : Bool) :
    Runs program ((vectorBits (inputs root raw second)).length+1) .clearGuard (data (inputPopped root raw second inverse))
      .copyGuardOutput (data (inputCleared root raw second inverse)) := by
  have h:=drain .clearGuard .copyGuardOutput (.guard .cache) rfl (data (inputPopped root raw second inverse))
  have hv : data (inputPopped root raw second inverse) (.guard .cache)=vectorBits (inputs root raw second) := rfl
  rw [hv,←data_set] at h;exact h
/-- Real output-vector cache copy, including preservation/restoration of source. -/
theorem output_copy (root : R.Stack→List Bool) (raw : List Bool) (second inverse : Bool) :
    Runs program (5*(vectorBits (outputs root raw second)).length+4) .copyGuardOutput
      (data (inputCleared root raw second inverse)) .guardOutput (data (outputReady root raw second inverse)) :=
  copy_run (.vector true 1) .copyGuardOutput .guardOutput rfl (inputCleared root raw second inverse) rfl rfl
/-- Output guard receives the actual second produced vector, not output truth. -/
theorem output_initial (root : R.Stack→List Bool) (raw : List Bool) (second inverse : Bool) :
    (outputReady root raw second inverse).checker=(V.initial (vectorBits (outputs root raw second)) (modulusWord root)).data := by
  funext k;cases k <;> rfl
/-- WHOLE real output guard. -/
theorem output_call (root : R.Stack→List Bool) (raw : List Bool) (second inverse : Bool) :
    ∃t≤SemiprimeD1StackVectorCanonicalExecution.timeBound (outputs root raw second) (modulusWord root)+1,
      Runs program t .guardOutput (data (outputReady root raw second inverse)) .branchOutput
        (data (outputChecked root raw second inverse)) := by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackVectorCanonicalExecution.source_run (outputs root raw second) (modulusWord root)
  refine ⟨t+1,Nat.add_le_add_right ht 1,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program Stack.guard Label.check
    (by intro i j h;exact Stack.guard.inj h) V.program .start (fun _=>rfl) .guardOutput .branchOutput rfl t
    (V.initial (vectorBits (outputs root raw second)) (modulusWord root))
    (SemiprimeD1StackVectorCanonicalExecution.done (outputs root raw second) (modulusWord root)) _ _ rfl rfl rfl rfl hr
  · constructor
    · intro k;exact congrFun (output_initial root raw second inverse) k
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk;cases k <;> first | rfl | exact (hk _ rfl).elim
/-- Actual output guard verdict chooses reject/physical loop setup. -/
theorem output_branch (root : R.Stack→List Bool) (raw : List Bool) (second inverse : Bool) :
    Runs program 1 .branchOutput (data (outputChecked root raw second inverse))
      (if outputFlag root raw second then .copyOutputCache else .reject) (data (outputPopped root raw second inverse)) := by
  have h:=pop .branchOutput .bad .reject .copyOutputCache (.guard .output) rfl (data (outputChecked root raw second inverse))
  have hv : data (outputChecked root raw second inverse) (.guard .output)=[outputFlag root raw second] := rfl
  rw [hv,←data_set] at h
  cases he : outputFlag root raw second <;> simpa only [outputPopped,he,List.head?_cons,List.tail_cons,SemiprimeD1StackBytecode.choose,Bool.false_eq_true,ite_true,ite_false] using h
/-- Output read cache is acquired ONCE from actual producer bytes. -/
theorem reader_copy (root : R.Stack→List Bool) (raw : List Bool) (second inverse : Bool) :
    Runs program (5*(vectorBits (outputs root raw second)).length+4) .copyOutputCache
      (data (outputPopped root raw second inverse)) .copyLoop (data (outputCached root raw second inverse)) :=
  copy_run (.vector true 2) .copyOutputCache .copyLoop rfl (outputPopped root raw second inverse) rfl rfl
/-- The literal output loop count is actually copied from acquired n markers. -/
theorem loop_copy (root : R.Stack→List Bool) (raw : List Bool) (second inverse : Bool) :
    Runs program (5*(countWord root second).length+4) .copyLoop
      (data (outputCached root raw second inverse)) .loop (data (loopReady root raw second inverse)) :=
  copy_run .remaining .copyLoop .loop rfl (outputCached root raw second inverse) rfl rfl
/-- Exact branch-dependent physical frontend result, specified AFTER real guards. -/
def frontResult (root : R.Stack→List Bool) (raw : List Bool) (second inverse : Bool) : Parts :=
  if inputFlag root raw second then
    if outputFlag root raw second then loopReady root raw second inverse else outputPopped root raw second inverse
  else inputPopped root raw second inverse
/-- Complete own frontend allowance, including both real guards and all copies
and cache draining, although rejected executions visit only their prefix. -/
def frontBudget (root : R.Stack→List Bool) (raw : List Bool) (second : Bool) : ℕ :=
  (5*(vectorBits (inputs root raw second)).length+4)+(5*(vectorBits (inputs root raw second)).length+4)+
    (SemiprimeD1StackVectorCanonicalExecution.timeBound (inputs root raw second) (modulusWord root)+1)+1+
    ((vectorBits (inputs root raw second)).length+1)+(5*(vectorBits (outputs root raw second)).length+4)+
    (SemiprimeD1StackVectorCanonicalExecution.timeBound (outputs root raw second) (modulusWord root)+1)+1+
    (5*(vectorBits (outputs root raw second)).length+4)+(5*(countWord root second).length+4)
/-- ENTIRE real two-guard frontend: accepted cases computed BOTH canonicality
checks; actual early rejection is proved for every failed Boolean, without advice. -/
theorem front_run (root : R.Stack→List Bool) (raw : List Bool) (second inverse : Bool) :
    ∃t≤frontBudget root raw second,Runs program t .copyInputDot (data (bothAcquired root raw second inverse))
      (if inputFlag root raw second && outputFlag root raw second then .loop else .reject)
      (data (frontResult root raw second inverse)) := by
  obtain ⟨u,hu,hg0⟩:=input_call root raw second inverse
  have hp:=runs_trans program _ _ _ _ _ _ _ _
    (runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ (dot_copy root raw second inverse)
      (input_copy root raw second inverse)) hg0) (input_branch root raw second inverse)
  cases hi : inputFlag root raw second with
  | false=>
    have hh : Runs program ((5*(vectorBits (inputs root raw second)).length+4)+
        (5*(vectorBits (inputs root raw second)).length+4)+u+1)
        .copyInputDot (data (bothAcquired root raw second inverse)) .reject (data (inputPopped root raw second inverse)) := by
      simpa only [hi,Bool.false_eq_true,ite_false] using hp
    refine ⟨(5*(vectorBits (inputs root raw second)).length+4)+
      (5*(vectorBits (inputs root raw second)).length+4)+u+1,?_,?_⟩
    · unfold frontBudget;omega
    · simpa only [frontResult,hi,Bool.false_and,Bool.false_eq_true,ite_false] using hh
  | true=>
    have hp' : Runs program ((5*(vectorBits (inputs root raw second)).length+4)+
        (5*(vectorBits (inputs root raw second)).length+4)+u+1)
        .copyInputDot (data (bothAcquired root raw second inverse)) .clearGuard (data (inputPopped root raw second inverse)) := by
      simpa only [hi,ite_true] using hp
    obtain ⟨v,hv,hg1⟩:=output_call root raw second inverse
    have hs:=runs_trans program _ _ _ _ _ _ _ _
      (runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _
        (clear_input root raw second inverse) (output_copy root raw second inverse)) hg1) (output_branch root raw second inverse)
    have hh:=runs_trans program _ _ _ _ _ _ _ _ hp' hs
    cases ho : outputFlag root raw second with
    | false=>
      have hh' : Runs program (((5*(vectorBits (inputs root raw second)).length+4)+
          (5*(vectorBits (inputs root raw second)).length+4)+u+1)+
          (((vectorBits (inputs root raw second)).length+1)+(5*(vectorBits (outputs root raw second)).length+4)+v+1))
          .copyInputDot (data (bothAcquired root raw second inverse)) .reject (data (outputPopped root raw second inverse)) := by
        simpa only [ho,Bool.false_eq_true,ite_false] using hh
      refine ⟨((5*(vectorBits (inputs root raw second)).length+4)+
        (5*(vectorBits (inputs root raw second)).length+4)+u+1)+
        (((vectorBits (inputs root raw second)).length+1)+(5*(vectorBits (outputs root raw second)).length+4)+v+1),?_,?_⟩
      · unfold frontBudget;omega
      · simpa only [frontResult,hi,ho,Bool.true_and,Bool.false_eq_true,ite_true,ite_false] using hh'
    | true=>
      have hh' : Runs program (((5*(vectorBits (inputs root raw second)).length+4)+
          (5*(vectorBits (inputs root raw second)).length+4)+u+1)+
          (((vectorBits (inputs root raw second)).length+1)+(5*(vectorBits (outputs root raw second)).length+4)+v+1))
          .copyInputDot (data (bothAcquired root raw second inverse)) .copyOutputCache (data (outputPopped root raw second inverse)) := by
        simpa only [ho,ite_true] using hh
      have hlast:=runs_trans program _ _ _ _ _ _ _ _
        (runs_trans program _ _ _ _ _ _ _ _ hh' (reader_copy root raw second inverse)) (loop_copy root raw second inverse)
      refine ⟨(((5*(vectorBits (inputs root raw second)).length+4)+
        (5*(vectorBits (inputs root raw second)).length+4)+u+1)+
        (((vectorBits (inputs root raw second)).length+1)+(5*(vectorBits (outputs root raw second)).length+4)+v+1))+(5*(vectorBits (outputs root raw second)).length+4)+
        (5*(countWord root second).length+4),?_,?_⟩
      · unfold frontBudget;omega
      · simpa only [frontResult,hi,ho,Bool.true_and,ite_true] using hlast
end RiemannGaussian.SemiprimeD1StackPublicTransformGuards

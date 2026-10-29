/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootRecursiveControlEncoding

/-! # One original-input run acquiring and executing the exact root branch
Both included executions are concrete, balanced traces of fixed programs.
Their real calls, return frames and final halt are counted explicitly.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 131072
namespace RiemannGaussian.SemiprimeD1StackRootRecursiveControlExecution
open SemiprimeD1StackRootRecursiveControl SemiprimeD1StackRootRecursiveControlEncoding
open SemiprimeD1StackProcedureTrace
open SemiprimeBitArithmetic (bitValue)
local notation "ctl" => (Sum.inl : Control→Label)
attribute [local irreducible] SemiprimeD1StackRootParametersExecution.result values parentExponent
/-- Own complete clock: the actual original-input source, actual gate and both real calls. -/
def runBound (bits:List Bool) : Nat := SemiprimeD1StackRootParameters.runBound bits+
  GS.runBound (parentExponent bits) (values bits)+3
/-- One real call acquires all original root operands from N alone. -/
theorem source_call (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    ∃t≤SemiprimeD1StackRootParameters.runBound bits,
      Runs program (t+1) (ctl .start) (input bits) (ctl .gate) (afterSource bits) := by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackRootParametersExecution.source_run bits hc hN
  refine ⟨t,ht,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program sourceStack sourceLabel Sum.inl_injective
    P.program (.inl .start) (fun _=>rfl) (ctl .start) (ctl .gate) rfl t
    (P.initial bits) (P.done bits) _ _ rfl rfl rfl rfl hr
  · constructor
    · intro k;rfl
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk;cases k with
      | inl k=>exact (hk k rfl).elim
      | inr k=>rfl
/-- The actual source output, not prepared advice, supplies every guard/successor operand. -/
theorem gate_call (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) :
    ∃t≤GS.runBound (parentExponent bits) (values bits),
      Runs program (t+1) (ctl .gate) (afterSource bits) (ctl .done) (result bits) := by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackRecursiveScheduleExecution.source_run (parentExponent bits) (values bits)
  refine ⟨t,ht,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program gateStack gateLabel gate_injective
    G.program (.inl .start) (fun _=>rfl) (ctl .gate) (ctl .done) rfl t
    (GS.initial (parentExponent bits) (values bits)) (GS.done (parentExponent bits) (values bits))
    _ _ rfl rfl rfl rfl hr
  · constructor
    · exact initial_projection bits hc
    · intro k _;rfl
  · constructor
    · exact result_projection bits hc
    · intro k hk;cases k with
      | inl k=>rfl
      | inr k=>exact (hk (freshRole k) (freshRole_mapped k)).elim
/-- Entire original-N source and original branch run in the same fixed program. -/
theorem source_trace (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    ∃t,t+1≤runBound bits ∧ Runs program t (ctl .start) (input bits) (ctl .done) (result bits) := by
  obtain ⟨s,hs,h0⟩:=source_call bits hc hN
  obtain ⟨g,hg,h1⟩:=gate_call bits hc
  refine ⟨(s+1)+(g+1),?_,runs_trans program _ _ _ _ _ _ _ _ h0 h1⟩
  unfold runBound
  omega
/-- Genuine complete original-input execution includes all acquisition, conditional work and halt. -/
theorem source_run (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    ∃t≤runBound bits,SemiprimeD1StackCalls.run program t (initial bits)=some (done bits) := by
  obtain ⟨t,ht,h⟩:=source_trace bits hc hN
  obtain ⟨finish,hf,hs⟩:=h [] (initial bits) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program (ctl .done) rfl (result bits) [] finish hs
  refine ⟨t+1,ht,?_⟩
  rw [SemiprimeD1StackReturnLink.run_add,hf,Option.bind_some]
  exact hh
end RiemannGaussian.SemiprimeD1StackRootRecursiveControlExecution

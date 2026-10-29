/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1TensorTapeFieldBytecode
import RiemannGaussian.SemiprimeD1StackReturnLink

/-! # Actual finite field-parser procedure
The compiled literal parser is included in one fixed caller program. A real
return frame is pushed and popped, the actual validity bit is written, and the
caller halts. No parser opcode or semantic submachine call is assumed.
-/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1TensorTapeFieldProcedure
namespace F
export SemiprimeD1TensorTapeFieldBytecode (Stack Label code active initial final)
end F
namespace C
export SemiprimeD1StackCalls (State run configuration)
end C
open SemiprimeD1StackReturnLink

/-- Fixed caller plus actual compiled parser instruction table. -/
def program := code (F.active .tagPop (none,false)) F.code

/-- One fixed finite procedure machine; every data alphabet is Bool and return tags are fixed. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine
  (.inl (.input:SemiprimeD1TensorTapeFieldMachine.Stack))
  (.inl (.output:SemiprimeD1TensorTapeFieldMachine.Stack)) (.inr false) program

/-- Complete acquired parser-call execution with its own physical return stack. -/
theorem parse_run (xs extra:List Bool) :
    C.run program (SemiprimeD1TensorTapeFieldExecution.fieldSteps xs+4)
      (SemiprimeD1StackReturnLink.initial (F.initial xs extra).store)=
      some (SemiprimeD1StackReturnLink.final (F.final xs extra).store) := by
  exact linked_run (F.active .tagPop (none,false)) F.code
    (SemiprimeD1TensorTapeFieldExecution.fieldSteps xs+2)
    (F.initial xs extra).store (F.final xs extra).store
    (SemiprimeD1TensorTapeFieldBytecode.parse_run xs extra)

/-- Real finite-machine procedure time includes both call and return. -/
def parseInTime (xs extra:List Bool) :
    StateTransition.EvalsToInTime machine.step
      (C.configuration (SemiprimeD1StackReturnLink.initial (F.initial xs extra).store))
      (some (C.configuration (SemiprimeD1StackReturnLink.final (F.final xs extra).store)))
      (4*xs.length+10) := by
  apply SemiprimeD1StackCalls.evalsCorrect
    (.inl (.input:SemiprimeD1TensorTapeFieldMachine.Stack))
    (.inl (.output:SemiprimeD1TensorTapeFieldMachine.Stack)) (.inr false) program
  refine ⟨⟨SemiprimeD1TensorTapeFieldExecution.fieldSteps xs+4,parse_run xs extra⟩,?_⟩
  change SemiprimeD1TensorTapeFieldExecution.fieldSteps xs+4 ≤ 4*xs.length+10
  have h:=SemiprimeD1TensorTapeFieldExecution.fieldSteps_le xs
  omega

/-- Actual framed call, preserving suffix/output and physically returning a true validity bit. -/
def framedInTime (word tail extra:List Bool) :
    StateTransition.EvalsToInTime machine.step
      (C.configuration (SemiprimeD1StackReturnLink.initial
        (F.initial (SemiprimeSourceHistogramKeyBits.frame word tail) extra).store))
      (some (C.configuration (SemiprimeD1StackReturnLink.final
        (F.final (SemiprimeSourceHistogramKeyBits.frame word tail) extra).store)))
      (8*word.length+8) := by
  apply SemiprimeD1StackCalls.evalsCorrect
    (.inl (.input:SemiprimeD1TensorTapeFieldMachine.Stack))
    (.inl (.output:SemiprimeD1TensorTapeFieldMachine.Stack)) (.inr false) program
  refine ⟨⟨8*word.length+8,?_⟩,le_refl _⟩
  have h:=parse_run (SemiprimeSourceHistogramKeyBits.frame word tail) extra
  change C.run program (8*word.length+8)
    (SemiprimeD1StackReturnLink.initial (F.initial (SemiprimeSourceHistogramKeyBits.frame word tail) extra).store)=
    some (SemiprimeD1StackReturnLink.final (F.final (SemiprimeSourceHistogramKeyBits.frame word tail) extra).store)
  rw [SemiprimeD1TensorTapeFieldBounds.fieldSteps_frame] at h
  have ht:8*word.length+4+4=8*word.length+8:=by omega
  rw [ht] at h
  exact h

/-- Actual reached procedure states have bounds on all four Boolean data stacks. -/
theorem prefix_data_bound (xs extra:List Bool) (fuel:ℕ)
    (out:C.State F.Stack (F.Label⊕Bool))
    (hr:C.run program fuel (SemiprimeD1StackReturnLink.initial (F.initial xs extra).store)=some out) :
    ∀k,(out.data k).length ≤ xs.length+extra.length+fuel := by
  apply run_data_bound program fuel (xs.length+extra.length) _ out ?_ hr
  intro k
  cases k with
  | inl k => cases k <;> simp [SemiprimeD1StackReturnLink.initial,F.initial,
      SemiprimeD1TensorTapeFieldMachine.contents]
  | inr k => cases k; simp [SemiprimeD1StackReturnLink.initial,F.initial]

/-- Every reached actual procedure-machine prefix counts Boolean payload and real return frames. -/
theorem machine_prefix_cells (xs extra:List Bool) (fuel:ℕ) (cfg:machine.Cfg)
    (hr:(fun cfg=>cfg.bind machine.step)^[fuel]
      (some (C.configuration (SemiprimeD1StackReturnLink.initial (F.initial xs extra).store)))=some cfg) :
    (cfg.stk (some (.inl (.input:SemiprimeD1TensorTapeFieldMachine.Stack)))).length+
      (cfg.stk (some (.inl (.scratch:SemiprimeD1TensorTapeFieldMachine.Stack)))).length+
      (cfg.stk (some (.inl (.output:SemiprimeD1TensorTapeFieldMachine.Stack)))).length+
      (cfg.stk (some (.inr ()))).length+(cfg.stk none).length ≤
      5*(xs.length+extra.length+fuel) := by
  let start:C.State F.Stack (F.Label⊕Bool):=SemiprimeD1StackReturnLink.initial (F.initial xs extra).store
  have he:=SemiprimeD1StackCalls.run_correct
    (.inl (.input:SemiprimeD1TensorTapeFieldMachine.Stack))
    (.inl (.output:SemiprimeD1TensorTapeFieldMachine.Stack)) (.inr false) program fuel start
  change (C.run program fuel start).map C.configuration=
    (fun cfg=>cfg.bind machine.step)^[fuel] (some (C.configuration start)) at he
  cases hc:C.run program fuel start with
  | none => rw [hc,hr] at he;cases he
  | some out =>
    rw [hc,hr] at he
    have hcfg:C.configuration out=cfg:=Option.some.inj he
    rw [←hcfg]
    have h:=prefix_data_bound xs extra fuel out hc
    have h0:=h (.inl (.input:SemiprimeD1TensorTapeFieldMachine.Stack))
    have h1:=h (.inl (.scratch:SemiprimeD1TensorTapeFieldMachine.Stack))
    have h2:=h (.inl (.output:SemiprimeD1TensorTapeFieldMachine.Stack))
    have h3:=h (.inr ())
    have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel start out hc
    change out.frames.length ≤ 0+fuel at hf
    change (out.data (.inl (.input:SemiprimeD1TensorTapeFieldMachine.Stack))).length+
      (out.data (.inl (.scratch:SemiprimeD1TensorTapeFieldMachine.Stack))).length+
      (out.data (.inl (.output:SemiprimeD1TensorTapeFieldMachine.Stack))).length+
      (out.data (.inr ())).length+out.frames.length ≤ _
    omega
end RiemannGaussian.SemiprimeD1TensorTapeFieldProcedure
